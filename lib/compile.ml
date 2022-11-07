open Asm.Directive
open S_exp
open Util

type symtab =
  int Symtab.symtab

(** Constants used for tagging values at runtime. *)

let num_shift = 2
let num_mask = 0b11
let num_tag = 0b00

let bool_shift = 7
let bool_mask = 0b1111111
let bool_tag = 0b0011111

let heap_mask = 0b111
let pair_tag = 0b010
let nil_tag = 0b11111111

(** [function_label name] returns the label for use in referring to a function
    named by [name]. *)
let function_label : string -> string =
  fun s ->
    let nasm_char c =
      begin match c with
        | 'a' .. 'z'
        | 'A' .. 'Z'
        | '0' .. '9'
        | '_'
        | '$'
        | '#'
        | '@'
        | '~'
        | '.'
        | '?' ->
            c

        | _ ->
            '_'
      end
    in
    Printf.sprintf
      "function_%s_%d"
      (String.map nasm_char s)
      (Hashtbl.hash s)

(** [operand_of_num x] returns the runtime representation of the number [x] as
    an operand for instructions. *)
let operand_of_num : int -> operand =
  fun x ->
    Imm ((x lsl num_shift) lor num_tag)

(** [operand_of_bool b] returns the runtime representation of the boolean [b] as
    an operand for instructions. *)
let operand_of_bool : bool -> operand =
  fun b ->
    Imm (((if b then 1 else 0) lsl bool_shift) lor bool_tag)

(** [operand_of_nil] is the runtime representation of [Nil]. *)
let operand_of_nil =
  Imm nil_tag

let zf_to_bool =
  [ Mov (Reg Rax, Imm 0)
  ; Setz (Reg Rax)
  ; Shl (Reg Rax, Imm bool_shift)
  ; Or (Reg Rax, Imm bool_tag)
  ]

let setl_bool =
  [ Mov (Reg Rax, Imm 0)
  ; Setl (Reg Rax)
  ; Shl (Reg Rax, Imm bool_shift)
  ; Or (Reg Rax, Imm bool_tag)
  ]

let stack_address : int -> operand =
  fun index ->
    MemOffset (Imm index, Reg Rsp)

let ensure : directive list -> string -> directive list =
  fun condition err_msg ->
    let msg_label = gensym "emsg" in
    let continue_label = gensym "continue" in
    condition
      @ [ Je continue_label
        ; LeaLabel (Reg Rdi, msg_label)
        ; Jmp "lisp_error"
        ; Label msg_label
        ; DqString err_msg
        ; Label continue_label
        ]

let ensure_type : int -> int -> operand -> s_exp -> directive list =
  fun mask tag op e ->
    ensure
      [ Mov (Reg R8, op)
      ; And (Reg R8, Imm mask)
      ; Cmp (Reg R8, Imm tag)
      ]
      (string_of_s_exp e)

let ensure_num : operand -> s_exp -> directive list =
  ensure_type num_mask num_tag

let ensure_pair : operand -> s_exp -> directive list =
  ensure_type heap_mask pair_tag

let align_stack_index : int -> int =
  fun stack_index ->
    if stack_index mod 16 = -8 then
      stack_index
    else
      stack_index - 8

(** [compile_0ary_primitive e prim] produces x86-64 instructions for the
    zero-ary primitive operation named by [prim]; if [prim] isn't a valid
    zero-ary operation, it raises an exception using the s-expression [e]. *)
let compile_0ary_primitive : int -> s_exp -> string -> directive list =
  fun stack_index e prim ->
    begin match prim with
      | "read-num" ->
          [ Mov (stack_address stack_index, Reg Rdi)
          ; Add (Reg Rsp, Imm (align_stack_index stack_index))
          ; Call "read_num"
          ; Sub (Reg Rsp, Imm (align_stack_index stack_index))
          ; Mov (Reg Rdi, stack_address stack_index)
          ]

      | "newline" ->
          [ Mov (stack_address stack_index, Reg Rdi)
          ; Add (Reg Rsp, Imm (align_stack_index stack_index))
          ; Call "print_newline"
          ; Sub (Reg Rsp, Imm (align_stack_index stack_index))
          ; Mov (Reg Rdi, stack_address stack_index)
          ; Mov (Reg Rax, operand_of_bool true)
          ]

      | _ ->
          raise (Error.Stuck e)
    end

(** [compile_unary_primitive e prim] produces x86-64 instructions for the unary
    primitive operation named by [prim]; if [prim] isn't a valid unary
    operation, it raises an exception using the s-expression [e]. *)
let compile_unary_primitive : int -> s_exp -> string -> directive list =
  fun stack_index e prim ->
    begin match prim with
      | "add1" ->
          ensure_num (Reg Rax) e
            @ [Add (Reg Rax, operand_of_num 1)]

      | "sub1" ->
          ensure_num (Reg Rax) e
            @ [Sub (Reg Rax, operand_of_num 1)]

      | "zero?" ->
          [Cmp (Reg Rax, operand_of_num 0)]
            @ zf_to_bool

      | "num?" ->
          [ And (Reg Rax, Imm num_mask)
          ; Cmp (Reg Rax, Imm num_tag)
          ] @ zf_to_bool

      | "not" ->
          [ Cmp (Reg Rax, operand_of_bool false)
          ] @ zf_to_bool

      | "pair?" ->
          [ And (Reg Rax, Imm heap_mask)
          ; Cmp (Reg Rax, Imm pair_tag)
          ] @ zf_to_bool

      | "left" ->
          ensure_pair (Reg Rax) e
            @ [Mov (Reg Rax, MemOffset (Reg Rax, Imm (-pair_tag)))]

      | "right" ->
          ensure_pair (Reg Rax) e
            @ [Mov (Reg Rax, MemOffset (Reg Rax, Imm (-pair_tag + 8)))]

      | "empty?" ->
          [ Cmp (Reg Rax, operand_of_nil)
          ] @ zf_to_bool

      | "print" ->
          [ Mov (stack_address stack_index, Reg Rdi)
          ; Mov (Reg Rdi, Reg Rax)
          ; Add (Reg Rsp, Imm (align_stack_index stack_index))
          ; Call "print_value"
          ; Sub (Reg Rsp, Imm (align_stack_index stack_index))
          ; Mov (Reg Rdi, stack_address stack_index)
          ; Mov (Reg Rax, operand_of_bool true)
          ]

      | _ ->
          raise (Error.Stuck e)
    end

(** [compile_binary_primitive stack_index e prim] produces x86-64 instructions
    for the binary primitive operation named by [prim] given a stack index of
    [stack_index]; if [prim] isn't a valid binary operation, it raises an error
    using the s-expression [e]. *)
let compile_binary_primitive : int -> s_exp -> string -> directive list =
  fun stack_index e prim ->
    begin match prim with
      | "+" ->
          ensure_num (Reg Rax) e
            @ ensure_num (stack_address stack_index) e
            @ [Add (Reg Rax, stack_address stack_index)]

      | "-" ->
          ensure_num (Reg Rax) e
            @ ensure_num (stack_address stack_index) e
            @ [ Mov (Reg R8, Reg Rax)
              ; Mov (Reg Rax, stack_address stack_index)
              ; Sub (Reg Rax, Reg R8)
              ]

      | "=" ->
          ensure_num (Reg Rax) e
            @ ensure_num (stack_address stack_index) e
            @ [Cmp (stack_address stack_index, Reg Rax)]
            @ zf_to_bool

      | "<" ->
          ensure_num (Reg Rax) e
            @ ensure_num (stack_address stack_index) e
            @ [Cmp (stack_address stack_index, Reg Rax)]
            @ setl_bool

      | "pair" ->
          [ Mov (Reg R8, stack_address stack_index)
          ; Mov (MemOffset (Reg Rdi, Imm 0), Reg R8)
          ; Mov (MemOffset (Reg Rdi, Imm 8), Reg Rax)
          ; Mov (Reg Rax, Reg Rdi)
          ; Or (Reg Rax, Imm pair_tag)
          ; Add (Reg Rdi, Imm 16)
          ]

      | _ ->
          raise (Error.Stuck e)
    end

let align : int -> int -> int =
  fun n alignment ->
    if n mod alignment = 0 then
      n
    else
      n + (alignment - (n mod alignment))

(** [compile_expr defns tab stack_index e] produces x86-64 instructions for the
    expression [e] given a list of definitions [defns], a symtab [tab], and
    stack index [stack_index]. *)
let rec compile_expr :
 defn list -> symtab -> int -> s_exp -> directive list =
  fun defns tab stack_index e ->
    begin match e with
      | Num x ->
          [Mov (Reg Rax, operand_of_num x)]

      | Sym "true" ->
          [Mov (Reg Rax, operand_of_bool true)]

      | Sym "false" ->
          [Mov (Reg Rax, operand_of_bool false)]

      | Sym var when Symtab.mem var tab ->
          [Mov (Reg Rax, stack_address (Symtab.find var tab))]

      | Lst [] ->
          [Mov (Reg Rax, operand_of_nil)]

      | Lst [Sym "apply"; Sym f; expr] when is_defn defns f ->
        let iterate_label = gensym "iterate" in 
        let list_check_label = gensym "listcheck" in
        let passed_check_label = gensym "passedlistcheck" in
        let stack_base = align_stack_index (stack_index + 8) in 
        (* let defn = get_defn defns f in  *)
        (* let args_pusher : int -> directive list =
          fun n ->
            let repeat_label = gensym "repeat" in
            let end_repeat_label = gensym "endrepeat" in
            [Mov (Reg R11, Reg Rax)]
            @ [Mov (Reg R10, Imm n)]
            @ [Label repeat_label]
            @ [Mov (Reg R8, Reg R11)]
            @ [Mov (Reg )]
            @ [Label end_repeat_label]
        in *)

        compile_expr defns tab stack_index expr
        (* R11 stores address of current list element being checked *)
        (* R10 keeps a counter of how many args were pushed to stack *)
          @ [Mov (Reg R11, Reg Rax)]
          (* @ [Mov (Reg R10, Imm 2)] *)
          @ [Mov (Reg R10, Imm 3)]
          @ [Jmp list_check_label]

          (* move the right element of the pair into R11 and push left to stack *)
          @ [Label iterate_label]
          (* move current stack index in r8 *)
          @ [Mov (Reg R8, Imm stack_base)]
          @ [Add (Reg R8, Reg Rsp)]
          (* use r9 to temporarily store 8 x r10 *)
          @ [Mov (Reg R9, Reg R10)]
          @ [Shl (Reg R9, Imm 3)]
          (* set r8 to be address to push to *)
          @ [Sub (Reg R8, Reg R9)]


          (* move left element to r9 *)
          @ [Mov (Reg R9, MemOffset (Reg R11, Imm (-pair_tag)))]
          (* push to stack *)
          @ [Mov (MemOffset (Reg R8, Imm 0), Reg R9)]
          (* increment counter r10 *)
          @ [Add (Reg R10, Imm 1)]
          @ [Mov (Reg R11, MemOffset (Reg R11, Imm (-pair_tag + 8)))]

          (* first check if r11 is a pair, if it is,
             push the left element to stack and move the right element into r11 *)
          @ [Label list_check_label]
          @ [Mov (Reg R8, Reg R11)]
          @ [And (Reg R8, Imm heap_mask)]
          @ [Cmp (Reg R8, Imm pair_tag)]
          @ [Je iterate_label]
          (* else check if its nil *)
          @ [Mov (Reg R8, Reg R11)]
          @ [And (Reg R8, Imm nil_tag)]
          @ [Cmp (Reg R8, Imm nil_tag)]
          @ [Je passed_check_label]
          @ [Jmp "lisp_error"]
          
          (* passed list check and args already pushed, call f *)
          @ [Label passed_check_label]

          (* first we push the number of args to the stack *)
          @ [Sub (Reg R10, Imm 3)]
          @ [Mov (MemOffset (Reg Rsp, Imm (stack_base - 16)), Reg R10)]
          @ [Add (Reg Rsp, Imm stack_base)]
          @ [Call (function_label f)]
          @ [Sub (Reg Rsp, Imm stack_base)]


      | Lst [Sym "if"; test_expr; then_expr; else_expr] ->
          let then_label = gensym "then" in
          let else_label = gensym "else" in
          let continue_label = gensym "continue" in
          compile_expr defns tab stack_index test_expr
            @ [Cmp (Reg Rax, operand_of_bool false)]
            @ [Je else_label]
            @ [Label then_label]
            @ compile_expr defns tab stack_index then_expr
            @ [Jmp continue_label]
            @ [Label else_label]
            @ compile_expr defns tab stack_index else_expr
            @ [Label continue_label]

      | Lst [Sym "let"; Lst [Lst [Sym var; exp]]; body] ->
          compile_expr defns tab stack_index exp
            @ [Mov (stack_address stack_index, Reg Rax)]
            @ compile_expr defns
                (Symtab.add var stack_index tab)
                (stack_index - 8) body

      | Lst (Sym "do" :: exps) when List.length exps > 0 ->
          List.concat_map (compile_expr defns tab stack_index) exps

      | Lst (Sym f :: args) when is_defn defns f ->
          let stack_base = align_stack_index (stack_index + 8) in
          (* let defn = get_defn defns f in *)
          (* if Option.is_none defn.rest && List.length args = List.length defn.args then *)
            let compiled_args =
              args
                |> List.mapi
                     ( fun i arg ->
                         (* compile_expr defns tab (stack_base - ((i + 2) * 8)) arg *)
                         compile_expr defns tab (stack_base - ((i + 3) * 8)) arg
                           @ [ Mov
                                 (* ( stack_address (stack_base - ((i + 2) * 8)) *)
                                 ( stack_address (stack_base - ((i + 3) * 8))
                                 , Reg Rax
                                 )
                             ]
                     )
                |> List.concat
            in
            compiled_args
              (* also push the number of args pushed *)
              @ [Mov (MemOffset (Reg Rsp, Imm (stack_base - 16)), Imm (List.length args))]
              @ [ Add (Reg Rsp, Imm stack_base)
                ; Call (function_label f)
                ; Sub (Reg Rsp, Imm stack_base)
                ]
          (* else *)
          (* if Option.is_some defn.rest && List.length args >= List.length defn.args then
            let num_regular_args = List.length defn.args in 
            let is_regular_arg : int -> s_exp -> bool =
              fun index _ ->
                if index < num_regular_args then true else false
            let is_variadic_arg : int -> s_exp -> bool
            []
          else *)
            (* raise (Error.Stuck e) *)

        | Lst [Sym f] ->
            compile_0ary_primitive stack_index e f

      | Lst [Sym f; arg] ->
          compile_expr defns tab stack_index arg
            @ compile_unary_primitive stack_index e f

      | Lst [Sym f; arg1; arg2] ->
          compile_expr defns tab stack_index arg1
            @ [Mov (stack_address stack_index, Reg Rax)]
            @ compile_expr defns tab (stack_index - 8) arg2
            @ compile_binary_primitive stack_index e f
      | e ->
          raise (Error.Stuck e)
    end

(** [compile_defn defns defn] produces X86-64 instructions for the function
    definition [defn] given a list of definitions [defns]. **)
let compile_defn : defn list -> defn -> directive list =
  fun defns defn ->
      let ftab =
        defn.args
          (* |> List.mapi (fun i arg -> (arg, (i + 1) * -8)) *)
          |> List.mapi (fun i arg -> (arg, (i + 2) * -8))
          |> Symtab.of_list
      in
      if Option.is_some defn.rest then 
        let variadic_ftab = Symtab.add (Option.get defn.rest) (((List.length defn.args) + 2) * -8) ftab in 
        let continue_label = gensym "continue" in
        let variadic_loop_label = gensym "variadicloop" in
        [Label (function_label defn.name)]
        @ [Mov (Reg R8, stack_address(-8))]
        @ [Cmp (Reg R8, Imm (List.length defn.args))]
        @ [Jl "lisp_error"]
        
        (* R9 will hold current arg index *)
        @ [Mov (Reg R9, Imm (List.length defn.args))]
        
        @ [Mov (Reg R11, stack_address(-8))]
        (* @ [Cmp (Reg R8, Imm (List.length defn.args))] *)
        
        @ [Mov (Reg R8, Imm (((List.length defn.args) + 2) * -8))]
        @ [Add (Reg R8, Reg Rsp)]
        @ [Cmp (Reg R11, Imm (List.length defn.args))]
        @ [Je continue_label]
        (* do one iteration of loop before setting r8 and running checks and loops *)
        @ [Mov (Reg R11, Reg R9)]
        @ [Shl (Reg R11, Imm 3)]
        @ [Mov (Reg R10, Reg Rsp)]
        @ [Sub (Reg R10, Imm 8)]
        @ [Sub (Reg R10, Reg R11)]
        @ [Mov (Reg R10, MemOffset (Reg R10, Imm 0))]
        @ [Mov (MemOffset (Reg Rdi, Imm 0), Reg R10)]
        (* now that the value is added to the heap, we can overwrite its value on the stack with pointer to pair *)
        @ [Mov (Reg R10, Reg Rdi)]
        @ [Or (Reg R10, Imm pair_tag)]
        @ [Mov (MemOffset (Reg R8, Imm 0), Reg R10)]

        @ [Mov (Reg R8, Reg Rdi)]
        @ [Add (Reg R8, Imm 8)]
        @ [Add (Reg Rdi, Imm 16)]
        @ [Add (Reg R9, Imm 1)]
        @ [Cmp (Reg R9, stack_address(-8))]
        @ [Jng variadic_loop_label]
        @ [Jmp continue_label]

        @ [Label variadic_loop_label]
        (* R10 will act as a temp register to hold memory values *)
        (* R8 will now store the current working pointer *)
        @ [Mov (Reg R10, Reg Rdi)]
        @ [Or (Reg R10, Imm pair_tag)]
        @ [Mov (MemOffset (Reg R8, Imm 0), Reg R10)]
        @ [Mov (Reg R11, Reg R9)]
        @ [Shl (Reg R11, Imm 3)]
        @ [Mov (Reg R10, Reg Rsp)]
        @ [Sub (Reg R10, Imm 8)]
        @ [Sub (Reg R10, Reg R11)]
        (* R10 now holds address of current index of stack *)
        (* now add that to the left of the pair *)
        @ [Mov (Reg R10, MemOffset (Reg R10, Imm 0))]
        @ [Mov (MemOffset (Reg Rdi, Imm 0), Reg R10)]
        (* set r8 to point to right side of pair *)
        @ [Mov (Reg R8, Reg Rdi)]
        @ [Add (Reg R8, Imm 8)]
        (* increment heap pointer *)
        @ [Add (Reg Rdi, Imm 16)]
        (* increment counter r9 and begin check *)
        @ [Add (Reg R9, Imm 1)]
        @ [Cmp (Reg R9, stack_address(-8))]
        (* if <= repeat else add nil and go to continue label *)
        @ [Jng variadic_loop_label]
        (* @ [Mov (MemOffset (Reg R8, Imm 0), Imm nil_tag)] *)
        @ [Jmp continue_label]

        @ [Label continue_label]

        (* @ [Mov (MemOffset (Reg Rsp, Imm (((List.length defn.args) + 2) * -8)), Reg Rax)] *)
        @ [Mov (MemOffset (Reg R8, Imm 0), Imm nil_tag)]
        @ compile_expr defns variadic_ftab ((List.length defn.args + 3) * -8) defn.body
        @ [Ret]

      else

      [Label (function_label defn.name)]
      (* check that the correct number of args have been pushed, else lisp_error *)
        @ [Mov (Reg R8, stack_address(-8))]
        @ [Cmp (Reg R8, Imm (List.length defn.args))]
        @ [Jne "lisp_error"]

      (* end of error checking *)
        (* @ compile_expr defns ftab ((List.length defn.args + 1) * -8) defn.body *)
        (* account for an additional arg number pushed to stack *)
        @ compile_expr defns ftab ((List.length defn.args + 2) * -8) defn.body
        @ [Ret]

(** [compile exps] produces x86-64 instructions, including frontmatter, for the
    list of expressions [exps]. *)
let compile : s_exp list -> directive list =
  fun exps ->
    let (defns, body) = defns_and_body exps in
      [ Global "lisp_entry"
      ; Extern "lisp_error"
      ; Extern "read_num"
      ; Extern "print_value"
      ; Extern "print_newline"
      ; Section "text"
      ] @ List.concat_map (compile_defn defns) defns
        @ [Label "lisp_entry"]
        @ compile_expr defns Symtab.empty (-8) body
        @ [Ret]
