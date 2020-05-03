#use "semantic-analyser.ml";;

let () = Printexc.record_backtrace true;;

module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> (constant * (int * string)) list
  val make_fvars_tbl : expr' list -> (string * int) list
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> int -> string
end;;

module Code_Gen : CODE_GEN = struct

exception X_not_generated;;

let nil_size = 1;;
let void_size = 1;;
let char_size = 2;;
let bool_size = 2;;
let number_size = 9;;
let string_size str_len = 9 + str_len;;
let symbol_size = 9;;
let vector_size num_of_elements = 9 + (8 * num_of_elements);;
let pair_size = 17;;
let closure_size = 17;;



let rec find_free_vars lst e = match e with 
  | Var'(VarFree v1) -> e :: lst
  | BoxSet'(x,y) -> (find_free_vars lst y)
  | If'(test,alt,elsee) -> (find_free_vars lst test) @ (find_free_vars lst alt) @ (find_free_vars lst elsee)
  | Seq'(seq) -> List.concat (List.map (find_free_vars lst) seq)
  | Set'(var,value) -> (find_free_vars lst var) @ (find_free_vars lst value)
  | Def'(var,value) -> (find_free_vars lst var) @ (find_free_vars lst value)
  | Or'(seq) -> List.concat (List.map (find_free_vars lst) seq)
  | LambdaSimple'(vars,body) -> (find_free_vars lst body) 
  | LambdaOpt'(vars,variadic,body) -> (find_free_vars lst body) 
  | Applic'(rand,rator) -> (find_free_vars lst rand) @ List.concat (List.map (find_free_vars lst) rator)
  | ApplicTP'(rand,rator) -> (find_free_vars lst rand) @ List.concat (List.map (find_free_vars lst) rator)
  | _ -> lst ;;

  let get_string exp = 
    match exp with
    | Var'(VarFree (v1)) -> v1
    | _ -> raise X_syntax_error;; 

  let rec range i j = if i > j then [] else i :: (range (i+1) j);;

  let rec find_consts lst e = match e with
  | Const'(x) -> lst @ [x]
  | BoxSet'(x,y) -> (find_consts lst y)
  | If'(test,alt,elsee) -> (find_consts lst test) @ (find_consts lst alt) @ (find_consts lst elsee)
  | Seq'(seq) -> List.concat (List.map (find_consts lst) seq)
  | Set'(var,value) -> (find_consts lst var) @ (find_consts lst value)
  | Def'(var,value) -> (find_consts lst var) @ (find_consts lst value)
  | Or'(seq) -> List.concat (List.map (find_consts lst) seq)
  | LambdaSimple'(vars,body) -> (find_consts lst body) 
  | LambdaOpt'(vars,variadic,body) -> (find_consts lst body) 
  | Applic'(rand,rator) -> (find_consts lst rand) @ List.concat (List.map (find_consts lst) rator)
  | ApplicTP'(rand,rator) -> (find_consts lst rand) @ List.concat (List.map (find_consts lst) rator)
  | _ -> lst ;;

  let extending_constants lst = 
    let rec make_extension = function 
      | [] -> []
      | Sexpr(Symbol x):: xs -> let str = Sexpr(String x) in 
          (str :: [Sexpr(Symbol x)]) @ (make_extension xs)
      | Sexpr(Pair(x,y)) :: xs -> let car = [Sexpr(x)] in
                                   let cdr = [Sexpr(y)] in
                                    ((make_extension car) @ (make_extension cdr) @
                                    car @ cdr @ [Sexpr(Pair(x,y))]) @ (make_extension xs) 
      | Sexpr(Vector(x))::xs -> (List.fold_left (fun a b -> a @(make_extension[Sexpr(b)])) [] x) @ [(Sexpr(Vector(x)))] @ (make_extension xs)
      | Sexpr(x)::xs -> Sexpr(x) :: (make_extension xs)
      | x::xs -> x :: (make_extension xs)in
    let removed_dups = List.fold_left (fun a b -> if(List.mem b a) then a else a@[b]) [] (make_extension lst) in 
    removed_dups;;

  let get_address x lst =
    match x with 
    | Void-> 0
    | Sexpr(a) -> let (a,b,c)= List.find (fun tuple -> 
        match tuple with 
        | (Void,_,_) -> false
        | (Sexpr(w),q,z) -> (sexpr_eq a w)) lst in 
        b
    ;;
  
  let get_ascii x =  let tl = (List.hd(List.rev x)) in
                     let new_lst = (List.rev(List.tl(List.rev x))) in
                     (List.fold_left (fun a b -> a ^ (string_of_int(int_of_char b)) ^ ",") "" new_lst) ^ (string_of_int(int_of_char tl)) ;;
  
  let rec set_type offset lst = function
  |Void::xs ->set_type (offset + void_size) (lst @ [(Void, offset, "MAKE_VOID")]) xs
  |Sexpr(Nil)::xs -> set_type (offset + nil_size) (lst @ [(Sexpr(Nil), offset, "MAKE_NIL")]) xs
  |Sexpr(Bool false)::xs -> set_type (offset + bool_size) (lst @ [(Sexpr(Bool false), offset, "MAKE_BOOL(0)")]) xs
  |Sexpr(Bool true)::xs -> set_type (offset + bool_size) (lst @ [(Sexpr(Bool true), offset, "MAKE_BOOL(1)")]) xs
  |Sexpr(Char x)::xs -> set_type (offset + char_size) (lst @ [(Sexpr(Char x), offset, "MAKE_LITERAL_CHAR(" ^ (string_of_int (int_of_char x)) ^ ")")]) xs
  |Sexpr(String x)::xs -> begin match (String.length x) with
      | 0 -> set_type (offset + (string_size (String.length x)))
             (lst @ [(Sexpr(String x), offset, "MAKE_LITERAL_STRING " ^ "\"\"")]) xs
      | _ -> set_type (offset + (string_size (String.length x)))
             (lst @ [(Sexpr(String x), offset, "MAKE_LITERAL_STRING " ^ (get_ascii(string_to_list x)))]) xs end
  |Sexpr(Number(Int x))::xs -> set_type (offset + number_size) 
      (lst @ [(Sexpr(Number(Int x)), offset, "MAKE_LITERAL_INT(" ^ (string_of_int x) ^")")])  xs
  |Sexpr(Number(Float x))::xs -> set_type (offset + number_size) 
      (lst @ [(Sexpr(Number(Float x)), offset, "MAKE_LITERAL_FLOAT(" ^ (string_of_float x) ^")")]) xs
  |Sexpr(Pair(x,y))::xs ->  set_type (offset + pair_size)
      (lst @ [(Sexpr(Pair(x,y)), offset, "MAKE_LITERAL_PAIR(const_tbl+"^(string_of_int (get_address (Sexpr(x)) lst)) ^", const_tbl+"^(string_of_int(get_address (Sexpr(y)) lst))^")")]) xs
  |Sexpr(Symbol(x))::xs ->  set_type (offset + symbol_size)
      (lst @ [(Sexpr(Symbol(x))), offset, 
             "MAKE_LITERAL_SYMBOL(const_tbl+"^ (string_of_int (get_address (Sexpr(String x)) lst))  ^")"]) xs
  |Sexpr(Vector(x))::xs -> 
    begin match x with 
    | [] -> set_type (offset + (vector_size (List.length x)))
            (lst @ [(Sexpr(Vector(x))), offset,
            "MAKE_LITERAL_VECTOR "]) xs
    | first::rest -> let first = (string_of_int (get_address (Sexpr(first)) lst)) in
                     let ans  = List.fold_left (fun a  b -> (a ^ ",const_tbl+" ^ (string_of_int(get_address (Sexpr(b)) lst )))) ("const_tbl+"^first) rest in
                     set_type (offset + (vector_size (List.length x)))
                     (lst @ [(Sexpr(Vector(x))), offset,
                     "MAKE_LITERAL_VECTOR " ^ans]) xs end
  |_-> lst;;


  let make ast = 
    let const_list = (find_consts [] ast) in 
    let removed_dups = List.fold_right (fun a b -> if(List.mem a b) then b else a::b)  const_list  [] in
    let extended_list = (extending_constants removed_dups) in
    extended_list;;


    let add_const a = Const(a);;
    let get_const_address consts_tbl const = let (a,(b,c)) = (List.find (fun (a,(b,c)) -> (expr_eq (add_const a) (add_const const) )) consts_tbl) in
                                "const_tbl+" ^ (string_of_int b) ;;
    let get_fvar_address fvars_tbl const pred=  let (a,b) = (List.find (fun (a,b) -> a = const) fvars_tbl) in
                                if pred = true then (string_of_int b) else "fvar_tbl+" ^ (string_of_int b);;

    let make_consts_tbl asts = 
      let the_list = [Void ; Sexpr(Nil) ; Sexpr(Bool (false)) ; Sexpr(Bool (true))] in
      let const_list = List.fold_left (fun a b -> let ans = (make b) in a @ ans) [] asts in
      let const_list = the_list @ const_list in
      let removed_dups = List.fold_left (fun a b -> if(List.mem b a) then a else a@ [b] ) [] const_list   in
      let const_list = (set_type 0 [] removed_dups) in
      let const_list = List.fold_left (fun lst (a,b,c) -> let ans = (a,(b,c)) in 
                                                          lst @ [ans]) [] const_list in
      const_list;;

    let primitive_names_to_labels = 
        ["boolean?", "is_boolean"; "float?", "is_float"; "integer?", "is_integer"; "pair?", "is_pair";
         "null?", "is_null"; "char?", "is_char"; "vector?", "is_vector"; "string?", "is_string";
         "procedure?", "is_procedure"; "symbol?", "is_symbol"; "string-length", "string_length";
         "string-ref", "string_ref"; "string-set!", "string_set"; "make-string", "make_string";
         "vector-length", "vector_length"; "vector-ref", "vector_ref"; "vector-set!", "vector_set";
         "make-vector", "make_vector"; "symbol->string", "symbol_to_string"; 
         "char->integer", "char_to_integer"; "integer->char", "integer_to_char"; "eq?", "is_eq";
         "+", "bin_add"; "*", "bin_mul"; "-", "bin_sub"; "/", "bin_div"; "<", "bin_lt"; "=", "bin_equ" ; 
         "car","car";"cdr","cdr";"set-car!","set_car";"set-cdr!","set_cdr";"cons","cons";"apply","apply"];;

    let get_prim s = List.map (fun (a,b) -> a) s ;;
    let count = ref 0 ;;
    let counter reset= 
      if reset then fun ()->( count:= 0);!count 
               else fun ()->( count:= !count +1);!count 
    ;;

    let make_fvars_tbl asts = 
      let answer = List.map (find_free_vars []) asts in 
      let answer = List.concat answer in
      let prim = (get_prim primitive_names_to_labels) in
      let string_list = List.map get_string answer in
      let set = List.sort_uniq String.compare string_list in
      let lst = prim @ set in
      let product = (List.combine lst (range 0 ((List.length lst) - 1 ))) in
      product;;

    let rec generate consts fvars e depth = match e with
    | Const'(c) -> "mov rax," ^ (get_const_address consts c) ^ "\n"
    | Seq'(x) -> (List.fold_left (fun a b -> a ^ (generate consts fvars b depth) ^ "\n") "" x) ^ "\n"
    | If'(test,alt,elsee) -> let x = (counter false ()) in 
                              (generate consts fvars test depth) ^  "\n" ^ "cmp rax, SOB_FALSE" ^ "\n" ^ 
                              "je Lelse" ^ (string_of_int(x)) ^ "\n" ^
                               (generate consts fvars alt depth) ^ "\n" ^
                              "jmp Lexit" ^ (string_of_int(x)) ^ "\n" ^ "Lelse" ^ (string_of_int(x)) ^ ":\n" ^ (generate consts fvars elsee depth)
                              ^ "\n" ^ "Lexit" ^ (string_of_int(x)) ^ ":" ^ "\n"
    | Or'(x) -> let count = (counter false ()) in
                let tl = (List.hd(List.rev x)) in
                let new_lst = (List.rev(List.tl(List.rev x))) in
                (List.fold_left (fun a b -> a ^ (generate consts fvars b depth) ^ "\n" ^ 
                                  "cmp rax, SOB_FALSE" ^ "\n" ^ "jne Lexit" ^ (string_of_int(count)) ^ "\n") "" new_lst)
                ^ (generate consts fvars tl depth) ^ "\n" ^ "Lexit" ^ (string_of_int(count)) ^ ":" ^ "\n"
    | Def'((Var'(VarFree(x))),value) -> (generate consts fvars value depth) ^ "\n" ^ "mov qword [" 
                                       ^ (get_fvar_address fvars x false) ^ "*WORD_SIZE], rax" ^ "\n" ^ "mov rax, SOB_VOID" ^ "\n"
    | Var'(VarParam(_, minor)) -> "mov rax, qword [rbp + 8*(4+" ^ (string_of_int(minor)) ^ ")]" ^ "\n"
    | Set'(Var'(VarParam(_, minor)), e) -> (generate consts fvars e depth) ^ "\n" ^ "mov qword [rbp + 8* (4+"
                                           ^ (string_of_int(minor)) ^ ")], rax" ^ "\n" ^
                                           "mov rax, SOB_VOID" ^ "\n"
    | Var'(VarBound(_, major, minor)) -> "mov rax, qword [rbp + 8*2]"  ^ "\n" ^
                                         "mov rax, qword [rax + 8*" ^ (string_of_int(major)) ^ "]\n" ^
                                         "mov rax, qword [rax + 8*" ^ (string_of_int(minor)) ^ "]" ^ "\n"
    
    | Set'(Var'(VarBound(_,major,minor)),e) -> (generate consts fvars e depth) ^ "\n" ^ 
                                              "mov rbx, qword [rbp + 8*2]" ^ "\n" ^ 
                                              "mov rbx, qword [rbx + 8*" ^ (string_of_int(major)) ^ "]\n" ^
                                              "mov qword [rbx + 8*" ^ (string_of_int(minor)) ^ "], rax" ^ "\n" ^
                                              "mov rax, SOB_VOID" ^ "\n"
    | Var'(VarFree(v)) -> "mov rax, FVAR(" ^ (get_fvar_address fvars v true) ^ ")\n"
    | Set'(Var'(VarFree(v)),e) -> (generate consts fvars e depth) ^ "\n" ^
                                  "mov qword [" ^ (get_fvar_address fvars v false) ^ "*WORD_SIZE], rax" ^ "\n" ^
                                  "mov rax, SOB_VOID" ^ "\n"
    | Box'(v)-> let var = Var'(v) in
                (generate consts fvars var depth) ^
                "MALLOC r10, WORD_SIZE\n" ^
                "mov [r10], rax\n" ^
                "mov rax,r10\n"
    | BoxGet'(v) -> let var = Var'(v) in
                    (generate consts fvars var depth) ^ "\n" ^ "mov rax, qword [rax]\n"
    | BoxSet'(v,e) -> let var = Var'(v) in
                      (generate consts fvars e depth) ^ "\n" ^ "push rax"  ^ "\n" ^ 
                      (generate consts fvars var depth) ^ "\n" ^ "pop qword [rax]" ^ "\n" ^
                      "mov rax, SOB_VOID" ^ "\n"
    | LambdaSimple'(lst,body) -> let count = (counter false ()) in
                              begin match depth with
                              | 0 -> "MAKE_CLOSURE(rax, SOB_NIL,Lcode" ^ (string_of_int(count)) ^ ")" ^ "\n"
                               ^ "jmp Lcont" ^ (string_of_int(count)) ^ "\n" ^ 
                                 "Lcode" ^ (string_of_int(count))^ ":\n" ^
                                 "push rbp\n" ^
                                 "mov rbp, rsp\n" ^ 
                                 (generate consts fvars body (depth+1)) ^"\n" ^
                                  "leave\n" ^ 
                                  "ret\n" ^
                                  "Lcont" ^ (string_of_int(count)) ^ ":\n"
                              | _ -> "MALLOC r8, " ^ (string_of_int ((depth+1)*8)) ^ "\n" ^
                                     "mov r9, 0\n" ^
                                     "mov r10, 1\n" ^
                                     "mov r11, qword [rbp+ 2*8]\n" ^
                                     "LoopExt" ^ (string_of_int(count)) ^ ":\n" ^
                                     "lea r12, [r8 + 8 * r10] \n" ^
                                     "lea r13, [r11 + 8 * r9] \n" ^
                                     "mov r13, [r13] \n" ^
                                     "mov [r12], r13 \n" ^
                                     "inc r9\n" ^ 
                                     "inc r10\n" ^
                                     "cmp r10, " ^ (string_of_int (depth+1)) ^ "\n" ^
                                     "jl LoopExt" ^ (string_of_int(count)) ^ "\n" ^
                                     "mov r9, qword [rbp+ 3*8]\n" ^
                                     "lea r10, [r9*8]\n" ^ 
                                     "MALLOC r11, r10\n" ^ 
                                     "mov r12, 0 \n" ^
                                     "LoopParams" ^ (string_of_int(count)) ^ ":\n" ^ 
                                     "cmp r12, r9 \n" ^
                                     "je Endofparams" ^ (string_of_int(count)) ^ "\n" ^
                                     "lea r10, [rbp + 4*8 + r12*8]\n " ^
                                     "mov r10, [r10]\n " ^ 
                                     "lea r13, [r11 + r12*8]\n " ^
                                     "mov [r13], r10 \n " ^
                                     "inc r12 \n" ^
                                     "jmp LoopParams" ^ (string_of_int(count)) ^ "\n" ^
                                     "Endofparams" ^ (string_of_int(count)) ^ ":\n" ^
                                     "mov qword[r8], r11 \n" ^ 
                                     "MAKE_CLOSURE(rax, r8,Lcode" ^ (string_of_int(count)) ^ ")" ^ "\n" ^
                                     "jmp Lcont" ^ (string_of_int(count)) ^ "\n" ^
                                     "Lcode" ^ (string_of_int(count))^ ":\n" ^ 
                                     "push rbp\n" ^ 
                                     "mov rbp, rsp\n" ^ 
                                     (generate consts fvars body (depth+1)) ^ "\n" ^
                                     "leave\n" ^ 
                                     "ret\n" ^ 
                                     "Lcont" ^ (string_of_int(count)) ^ ":\n"
                                    end
                              
                              
    | Applic'(proc,lst) -> let n = "push " ^ (string_of_int((List.length lst)+1)) ^ "\n" in 
                           let count = (counter false ()) in
                           let args = List.fold_right (fun a b -> b ^ (generate consts fvars a depth) ^ "\n push rax\n" ) lst "push SOB_NIL\n" in
                           let proc = (generate consts fvars proc depth) in
                           args ^ n ^ "\n" ^ proc ^ "\n" ^
                           "cmp TYPE(rax), T_CLOSURE\n" ^
                           "jne Error" ^ (string_of_int(count)) ^ "\n" ^
                           "CLOSURE_ENV rcx,rax \n" ^ 
                           "push rcx\n" ^ 
                           "CLOSURE_CODE rcx,rax\n" ^
                           "call rcx\n" ^
                           "add rsp, 8*1\n" ^
                           "pop rbx\n" ^
                           "shl rbx, 3\n" ^
                           "add rsp, rbx\n" ^
                           "jmp End" ^ (string_of_int(count)) ^ "\n" ^
                           "Error" ^ (string_of_int(count)) ^ ":\n" ^ "xor rax,rax\n" ^ "mov rax,[rax]\n" ^
                           "End" ^ (string_of_int(count)) ^ ":\n"
    | ApplicTP'(proc,lst) -> let n = "push " ^(string_of_int((List.length lst)+1)) ^ "\n" in
                             let count = (counter false ()) in
                             let args = List.fold_right (fun a b -> b ^ (generate consts fvars a depth) ^ "\n push rax\n" ) lst "push SOB_NIL\n" in
                             let proc = (generate consts fvars proc depth) in
                             args ^ n ^ "\n" ^ proc ^ "\n" ^
                             "cmp TYPE(rax), T_CLOSURE\n" ^
                             "jne Error" ^ (string_of_int(count)) ^ "\n" ^
                             "CLOSURE_ENV rbx,rax \n" ^ 
                             "push rbx\n" ^ 
                             "push qword [rbp + 8*1]\n" ^
                             "mov r9, qword[rbp]\n" ^ 
                             "SHIFT_FRAME(" ^ (string_of_int((List.length lst)+4)) ^ ")\n" ^
                             "mov rbp, r9\n" ^
                             "CLOSURE_CODE rbx,rax\n" ^ 
                             "jmp rbx\n" ^ 
                             "Error" ^ (string_of_int(count)) ^ ":\n" ^ "xor rax,rax\n" ^ "mov rax,[rax]\n"
    | LambdaOpt'(vars,variadic,body) -> let count = (counter false ()) in
                             begin match depth with 
                             | 0 -> "MAKE_CLOSURE(rax, SOB_NIL,Lcode" ^ (string_of_int(count)) ^ ")" ^ "\n"
                             ^ "jmp Lcont" ^ (string_of_int(count)) ^ "\n" ^ 
                             "Lcode" ^ (string_of_int(count))^ ":\n" ^
                             "push rbp\n"^
                             "mov rbp, rsp\n"^
                             "mov r8, "^(string_of_int(List.length vars))^" ;num of args\n" ^
                             "mov r9, qword[rbp + 8*3] ;args + list_length \n" ^
                             "dec r9\n"^
                             "mov r10, SOB_NIL ; '() \n" ^
                             "while"^ (string_of_int(count)) ^":\n" ^ 
                             "cmp r9, r8 ;if args+list = list \n"^
                             "je .adjust\n" ^
                             "mov r11, qword[rbp + r9*8 + 3*8]\n" ^
                             "MAKE_PAIR(r12,r11,r10)\n"^
                             "mov r10, r12 \n"^
                             "dec r9 \n"^
                             "jmp while"^ (string_of_int(count))^"\n"^
                             ".adjust:\n"^
                             "mov qword[rbp + 4*8 +"^(string_of_int(List.length vars))^"*8], r10 \n"^
                             "mov rbp, rsp \n"^
                             (generate consts fvars body (depth+1)) ^"\n" ^
                             "leave \n"^
                             "ret \n"^
                             "Lcont" ^ (string_of_int(count)) ^ ":\n"
                             | _ ->"MALLOC r8, " ^ (string_of_int ((depth+1)*8)) ^ "\n" ^
                             "mov r9, 0\n" ^
                             "mov r10, 1\n" ^
                             "mov r11, qword [rbp+ 2*8]\n" ^
                             "LoopExt" ^ (string_of_int(count)) ^ ":\n" ^
                             "lea r12, [r8 + 8 * r10] \n" ^
                             "lea r13, [r11 + 8 * r9] \n" ^
                             "mov r13, [r13] \n" ^
                             "mov [r12], r13 \n" ^
                             "inc r9\n" ^ 
                             "inc r10\n" ^
                             "cmp r10, " ^ (string_of_int (depth+1)) ^ "\n" ^
                             "jl LoopExt" ^ (string_of_int(count)) ^ "\n" ^
                             "mov r9, qword [rbp+ 3*8]\n" ^
                             "lea r10, [r9*8]\n" ^ 
                             "MALLOC r11, r10\n" ^ 
                             "mov r12, 0 \n" ^
                             "LoopParams" ^ (string_of_int(count)) ^ ":\n" ^ 
                             "cmp r12, r9 \n" ^
                             "je Endofparams" ^ (string_of_int(count)) ^ "\n" ^
                             "lea r10, [rbp + 4*8 + r12*8]\n " ^
                             "mov r10, [r10]\n " ^ 
                             "lea r13, [r11 + r12*8]\n " ^
                             "mov [r13], r10 \n " ^
                             "inc r12 \n" ^
                             "jmp LoopParams" ^ (string_of_int(count)) ^ "\n" ^
                             "Endofparams" ^ (string_of_int(count)) ^ ":\n" ^
                             "mov qword[r8], r11 \n" ^ 
                             "MAKE_CLOSURE(rax, r8,Lcode" ^ (string_of_int(count)) ^ ")" ^ "\n" ^
                             "jmp Lcont" ^ (string_of_int(count)) ^ "\n" ^
                             "Lcode" ^ (string_of_int(count))^ ":\n" ^
                             "push rbp\n"^
                             "mov rbp, rsp\n"^
                             "mov r8, "^(string_of_int(List.length vars))^" ;num of args\n" ^
                             "mov r9, qword[rbp + 8*3] ;args + list_length \n" ^
                             "dec r9\n"^
                             "mov r10, SOB_NIL ; '() \n" ^
                             "while"^ (string_of_int(count)) ^":\n" ^ 
                             "cmp r9, r8 ;if args+list = list \n"^
                             "je .adjust\n" ^
                             "mov r11, qword[rbp + r9*8 + 3*8]\n" ^
                             "MAKE_PAIR(r12,r11,r10)\n"^
                             "mov r10, r12 \n"^
                             "dec r9 \n"^
                             "jmp while"^ (string_of_int(count))^"\n"^
                             ".adjust:\n"^
                             "mov qword[rbp + 4*8 +"^(string_of_int(List.length vars))^"*8], r10 \n"^
                             "mov rbp, rsp \n"^
                             (generate consts fvars body (depth+1)) ^"\n" ^
                             "leave \n"^
                             "ret \n"^
                             "Lcont" ^ (string_of_int(count)) ^ ":\n"
                            end
    | _ -> "mov rax, SOB_TRUE" ;;

  end;; 


  
  

