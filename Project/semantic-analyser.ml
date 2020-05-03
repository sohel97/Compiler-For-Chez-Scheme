(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

 #use "tag-parser.ml";;

 type var = 
   | VarFree of string
   | VarParam of string * int
   | VarBound of string * int * int;;
 
 type expr' =
   | Const' of constant
   | Var' of var
   | Box' of var
   | BoxGet' of var
   | BoxSet' of var * expr'
   | If' of expr' * expr' * expr'
   | Seq' of expr' list
   | Set' of expr' * expr'
   | Def' of expr' * expr'
   | Or' of expr' list
   | LambdaSimple' of string list * expr'
   | LambdaOpt' of string list * string * expr'
   | Applic' of expr' * (expr' list)
   | ApplicTP' of expr' * (expr' list);;
 
 let rec expr'_eq e1 e2 =
   match e1, e2 with
   | Const' Void, Const' Void -> true
   | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
   | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
   | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
   | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
   | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                             (expr'_eq th1 th2) &&
                                               (expr'_eq el1 el2)
   | (Seq'(l1), Seq'(l2)
   | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
   | (Set'(var1, val1), Set'(var2, val2)
   | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                              (expr'_eq val1 val2)
   | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
      (List.for_all2 String.equal vars1 vars2) &&
        (expr'_eq body1 body2)
   | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
      (String.equal var1 var2) &&
        (List.for_all2 String.equal vars1 vars2) &&
          (expr'_eq body1 body2)
   | Applic'(e1, args1), Applic'(e2, args2)
   | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
    (expr'_eq e1 e2) &&
      (List.for_all2 expr'_eq args1 args2)
   | Box'(var1), Box'(var2) -> expr'_eq (Var'(var1)) (Var'(var2))
   | BoxGet'(var1), BoxGet'(var2) -> expr'_eq (Var'(var1)) (Var'(var2))
   | BoxSet'(var1,expr1), BoxSet'(var2,expr2) -> (expr'_eq (Var'(var1)) (Var'(var2))) && (expr'_eq (expr1) (expr2))
   | _ -> false;;
   
                        
 exception X_syntax_error;;
 
 module type SEMANTICS = sig
   val run_semantics : expr -> expr'
   val annotate_lexical_addresses : expr -> expr'
   val annotate_tail_calls : expr' -> expr'
   val box_set : expr' -> expr'
 end;;
 
 module Semantics : SEMANTICS = struct
 
 
 let safe_find pred lst = 
   try Some(List.find pred lst)
   with Not_found -> None;;
   
 
 let cartesian l l' a =
   List.concat (List.map (fun e -> List.map (fun e' -> (e,e')) l') l)  ;;
   
 let rec range i j = if i > j then [] else i :: (range (i+1) j);;
 let make_body = function
   | [] -> Const' Void
   | x::[]  -> x
   | xs -> Seq' xs;;
 
 let var_lexical_address params bound x = 
   if (List.mem x params) then 
       let lst = (List.combine params (range 0 ((List.length params) - 1 ))) in
       let (a, b) = (List.find (fun (a,b)-> String.equal x a) lst) in
       Var'(VarParam(a,b)) 
   else 
     let ans = List.combine bound (range 0 ((List.length bound) - 1)) in 
     let ans = safe_find(fun (my_list, layer)-> List.mem x my_list) ans in
     match ans with 
     |Some(my_list, layer) ->  let lst = (List.combine my_list (range 0 ((List.length my_list) - 1 ))) in
                               let (my_var, index) = (List.find (fun (a,b)-> String.equal x a) lst) in    
                               Var'(VarBound(my_var, layer, index))
     |None -> Var'(VarFree (x));;
 
 
 let rec lexical_address params bound = function 
   | Const(x) -> Const'(x)
   | If(test,alt,elsee) -> If'((lexical_address params bound test) , (lexical_address params bound alt),( lexical_address params bound elsee))
   | Seq (lst) -> Seq' (List.map (lexical_address params bound) lst) 
   | Set(expr1,expr2) -> Set'((lexical_address params bound expr1), (lexical_address params bound expr2))
   | Def (Var(x), value) -> Def'(Var'(VarFree(x)),(lexical_address params bound value))
   | Or (lst) -> Or' (List.map (lexical_address params bound) lst)
   | LambdaSimple(vars,body) -> LambdaSimple' (vars, (lexical_address vars (params::bound) body))
   | LambdaOpt(vars,variadic,body) -> let param_list =  (List.rev (variadic::(List.rev vars))) in
                                      LambdaOpt'(vars,variadic, (lexical_address param_list (params::bound) body)) 
   | Applic(rator, rands) -> Applic'((lexical_address params bound rator), (List.map (lexical_address params bound) rands))
   | Var(x)-> (var_lexical_address params bound x) 
   | _ -> raise X_syntax_error;;
 
 let rec tail_calls tp e = match e with 
 | Const'(x) -> e
 | Var'(x) -> e
 | Box'(x) -> e
 | BoxGet'(x) -> e
 | BoxSet'(x,y) -> e
 | If'(test,alt,elsee) -> If' ((tail_calls false test) , (tail_calls tp alt) , (tail_calls tp elsee))
 | Def'(var,value) -> Def' (var , (tail_calls  tp value))
 | Or'(lst) -> let last = (List.hd(List.rev lst)) in
               let first = (List.rev(List.tl(List.rev lst))) in
               Or' ((List.map (tail_calls false) first) @ [(tail_calls tp last)])
 | Seq'(lst) -> let last = (List.hd(List.rev lst)) in
                let first = (List.rev(List.tl(List.rev lst))) in
                Seq' ((List.map (tail_calls false) first) @ [(tail_calls tp last)])
 | Set'(var,value) -> Set' (var, (tail_calls false value))
 | LambdaSimple'(vars,body) -> LambdaSimple'(vars, (tail_calls true body))
 | LambdaOpt'(vars,variadic,body) -> LambdaOpt'(vars,variadic,(tail_calls true body))
 | Applic'(rand,rator) -> begin match tp with
                           | true -> ApplicTP'((tail_calls false rand), (List.map (tail_calls false) rator))
                           | false -> Applic' ((tail_calls false rand), (List.map (tail_calls false) rator)) end
 | ApplicTP'(rand,rator) -> raise X_syntax_error;;                     
 
 
 let count = ref 0 ;;
 
 let counter reset= 
   if reset then fun ()->( count:= 0);!count 
            else fun ()->( count:= !count +1);!count 
 ;;
 
 
 let occurs_as_read = 
   
 let rec occurs_in_read var path = function
   | Var'(VarParam (v1,mn1))        -> if (var = v1) then [path] else []
   | Var'(VarBound (v1,mj1,mn1))    -> if (var = v1) then [path] else []
   | If'(test,alt,elsee)            -> (occurs_in_read var path test ) @
                                       (occurs_in_read var path alt  ) @
                                       (occurs_in_read var path elsee)
   | Or'(lst)                       -> 
   List.fold_right (fun a b -> (occurs_in_read var path a )@ b) lst []
   | Seq'(lst)                      ->
   List.fold_right (fun a b -> (occurs_in_read var path a )@ b) lst []
   | Def'(v,value) -> (occurs_in_read var path v) @ (occurs_in_read var path value)
   | BoxSet' (v,expr)-> (occurs_in_read var path expr)
   | Set'(v,value)                  -> (occurs_in_read var path value)
   | LambdaSimple'(vars,body)       ->  
                                       if (List.mem var vars) then []
                                       else (occurs_in_read var ([(counter false())] @ path) body)
   | LambdaOpt'(vars,variadic,body) -> 
                                       if (List.mem var (variadic::vars)) then []
                                       else (occurs_in_read var ([(counter false())] @ path) body)
   | Applic'(rator, rands)          -> (occurs_in_read var path rator) @
     List.fold_right (fun a b -> (occurs_in_read var path a )@ b) rands []
   | ApplicTP'(rator, rands)        -> (occurs_in_read var path rator) @
     List.fold_right (fun a b -> (occurs_in_read var path a )@ b) rands []                               
   | _ -> [] in
   occurs_in_read;;
 
   let count2 = ref 0 ;;
   let counter2 reset= 
   if reset then fun ()->( count2:= 0);!count2 
            else fun ()->( count2:= !count2 +1);!count2 ;; 

   let occurs_as_write = 
   let rec occurs_in_write var path = function 
   | If'(test,alt,elsee) -> (occurs_in_write var path  test ) @
                            (occurs_in_write var path alt  ) @
                            (occurs_in_write var path elsee)
   | Or'(lst)            ->
   List.fold_right (fun a b -> (occurs_in_write var path a )@ b) lst []
   | Seq'(lst)           ->
   List.fold_right (fun a b -> (occurs_in_write var path a )@ b) lst []
   | Def'(v,value) -> (occurs_in_write var path v) @ (occurs_in_write var path value)
   | BoxSet' (v,expr)-> (occurs_in_write var path expr)
   | Set'(Var'(VarFree (v1)),value) ->  if (v1 = var) then [path]
                                        else (occurs_in_write var path value)
   | Set'(Var'(VarParam (v1,mn1)),value) ->  if (v1 = var) then [path] 
                                             else (occurs_in_write var path value)
   | Set'(Var'(VarBound (v1,mj1,mn1)),value) -> if (v1 = var) then[path] 
                                                else (occurs_in_write var path value)
   | LambdaSimple'(vars,body)       -> if (List.mem var vars) then []
                                       else (occurs_in_write var  ([(counter2 false())]@path) body)
   | LambdaOpt'(vars,variadic,body) -> if (List.mem var (variadic::vars)) then []
                                       else (occurs_in_write var  ([(counter2 false())]@path) body)
   | Applic'(rator, rands)          -> (occurs_in_write var path rator) @
   List.fold_right (fun a b -> (occurs_in_write var path a )@ b) rands []  
                                       
   | ApplicTP'(rator, rands)        -> (occurs_in_write var path rator) @
   List.fold_right (fun a b -> (occurs_in_write var path a )@ b) rands []
 
   | _ -> []  in 
   occurs_in_write;;
   
 
   let rec has_ancestor v1 v2 = 
     if (v1 =[] || v2 = []) then true
     else let same_rib = (List.hd v1 = List.hd v2) in
         if same_rib != true  
         then has_ancestor (List.tl v1) (List.tl v2)
         else false;;
 
   let check_common_ancestor pair = 
     match pair with
     |([],[]) -> false
     |(v1,[]) -> true
     |([],v2) -> true
     |(v1, v2) -> if((List.hd(List.rev v1)) = (List.hd(List.rev v2))) then false 
       else  has_ancestor (List.tl(List.rev v1)) (List.tl(List.rev v2));;
       
 
    let common_ancestor var body = 
     let read_occurences  = (occurs_as_read var [] body) in
     let write_occurences = (occurs_as_write var [] body) in
     let reset  = (counter true()) + (counter2 true()) in
     let pairs_list = cartesian read_occurences write_occurences reset in
     List.fold_right (fun a b -> (check_common_ancestor a) || b) pairs_list false;; 
 
   let rec is_bound var = function 
   | Var'(VarParam (v1,mn1)) -> false
   | Var'(VarBound (v1,mj1,mn1)) -> if (v1 = var) then true  else false
   | If'(test,alt,elsee) -> (is_bound var test ) ||
                            (is_bound var alt  ) ||
                            (is_bound var elsee)
   | Or'(lst)    -> ormap (is_bound var) lst
   | Seq'(lst)   -> ormap (is_bound var) lst
   | LambdaSimple'(vars,body)       -> if (List.mem var vars) then false
                                       else (is_bound var body)
   | LambdaOpt'(vars,variadic,body) -> if (List.mem var (variadic::vars)) then false
                                       else (is_bound var body)
   | Applic'(rator, rands)          -> (is_bound var rator) ||
                                       ormap (is_bound var) rands
   | ApplicTP'(rator, rands)        -> (is_bound var rator) ||
                                       ormap (is_bound var) rands
   | Set'(v, value) -> (is_bound var v) || (is_bound var value)
   | _ -> false;;
 
 
 
   let annotate_lexical_addresses e = (lexical_address [] [[]] e);;
   let annotate_tail_calls e = (tail_calls false e);;
   let rec get_adrress vars v loc= 
     if vars = [] then -1 else 
     if List.hd vars = v then loc else get_adrress (List.tl vars) v (loc+1);;
   let box_set e = 
     let box_set_pred lambda_body = (fun var ->  (common_ancestor var lambda_body) &&
     
                                                 
                                                 (is_bound var lambda_body)) in
     let rec box_set_func vars_to_box e = 
     match e with 
     |Const' _-> e
     |Box' _-> e
     |BoxGet' _-> e
     | Var'(VarParam (v1,mn1)) -> if (List.mem v1 vars_to_box) 
                                     then BoxGet'(VarParam(v1,mn1))
                                     else e
     | Var'(VarBound (v1,mj1,mn1)) ->if (List.mem v1 vars_to_box) 
                                        then BoxGet'(VarBound (v1,mj1,mn1))
                                        else e
     |Var'(VarFree v)-> e
     |BoxSet'(v,e)-> BoxSet'(v, box_set_func vars_to_box e)
     | If'(test,alt,elsee) -> If'((box_set_func vars_to_box test ),
                                 (box_set_func vars_to_box alt  ),
                                 (box_set_func vars_to_box elsee))
     | Def'(var,value) -> Def'((box_set_func vars_to_box var), (box_set_func vars_to_box value))
     | Or'(lst)    -> Or'(List.map (box_set_func vars_to_box) lst)
     | Seq'(lst)   -> Seq'(List.map (box_set_func vars_to_box) lst)                                         
     | Set'(Var'(VarParam (v1,mn1)), value) -> if (List.mem v1 vars_to_box)
         then BoxSet'(VarParam (v1,mn1),(box_set_func vars_to_box value))
         else  Set'(Var'(VarParam (v1,mn1)), (box_set_func vars_to_box value))
     | Set'(Var'(VarBound (v1,mj1,mn1)),value) -> if (List.mem v1 vars_to_box)
         then BoxSet'(VarBound (v1,mj1,mn1),(box_set_func vars_to_box value))
         else  Set'(Var'(VarBound (v1,mj1,mn1)), (box_set_func vars_to_box value))
     | Set'(Var'(VarFree(v)),e)-> Set'(Var'(VarFree(v)),box_set_func vars_to_box e)
     | LambdaSimple'(vars,body) -> 
       let params_to_box = List.filter (box_set_pred body) vars in
       let vars_to_box   = List.filter (fun var -> not (List.mem var vars)) vars_to_box in
       let body = (box_set_func (vars_to_box @ params_to_box) body) in
       let add_to_seq    = (List.map 
                           (fun (a)->let b = (get_adrress vars a 0) in
                           (Set' (Var' (VarParam (a,b)),Box' (VarParam (a,b)))))  
                           params_to_box) in
       let body = make_body (add_to_seq @ [body]) in
       LambdaSimple'(vars,body)
     | LambdaOpt'(varss,variadic,body) ->
       let vars = varss@[variadic] in 
       let params_to_box = List.filter (box_set_pred body) vars in
       let vars_to_box   = List.filter (fun var -> not (List.mem var vars)) vars_to_box in
       let body = (box_set_func (vars_to_box @ params_to_box) body) in
       let add_to_seq    = (List.map 
                           (fun (a)->let b = (get_adrress vars a 0) in
                           (Set' (Var' (VarParam (a,b)),Box' (VarParam (a,b)))))  
                           params_to_box) in
       let body = make_body (add_to_seq @ [body]) in
       LambdaOpt'(varss,variadic,body)
     | Applic'(rator, rands)    -> Applic'((box_set_func vars_to_box rator),
                                         (List.map (box_set_func vars_to_box) rands))
     | ApplicTP'(rator, rands)  -> ApplicTP'((box_set_func vars_to_box rator),
                                         (List.map (box_set_func vars_to_box) rands))
     | e -> e in
     box_set_func [] e ;;
   let run_semantics expr =
     box_set
        (annotate_tail_calls
          (annotate_lexical_addresses expr));;
     
   end;;