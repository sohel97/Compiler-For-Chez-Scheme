(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

 #use "reader.ml";;
 #use "pc.ml";;
 open Reader;;
 open PC;;
 
 type constant =
   | Sexpr of sexpr
   | Void
 
 type expr =
   | Const of constant
   | Var of string
   | If of expr * expr * expr
   | Seq of expr list
   | Set of expr * expr
   | Def of expr * expr
   | Or of expr list
   | LambdaSimple of string list * expr
   | LambdaOpt of string list * string * expr
   | Applic of expr * (expr list);;
 
 let rec expr_eq e1 e2 =
   match e1, e2 with
   | Const Void, Const Void -> true
   | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
   | Var(v1), Var(v2) -> String.equal v1 v2
   | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                             (expr_eq th1 th2) &&
                                               (expr_eq el1 el2)
   | (Seq(l1), Seq(l2)
     | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
   | (Set(var1, val1), Set(var2, val2)
     | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                              (expr_eq val1 val2)
   | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
      (List.for_all2 String.equal vars1 vars2) &&
        (expr_eq body1 body2)
   | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
      (String.equal var1 var2) &&
        (List.for_all2 String.equal vars1 vars2) &&
          (expr_eq body1 body2)
   | Applic(e1, args1), Applic(e2, args2) ->
      (expr_eq e1 e2) &&
        (List.for_all2 expr_eq args1 args2)
   | _ -> false;;
   
                        
 exception X_syntax_error;;
 
 module type TAG_PARSER = sig
   val tag_parse_expression : sexpr -> expr
   val tag_parse_expressions : sexpr list -> expr list
 end;; (* signature TAG_PARSER *)
 
 module Tag_Parser : TAG_PARSER = struct
 
 
 
 (* work on the tag parser starts here *)

 let reserved_word_list =
   ["and"; "begin"; "cond"; "define"; "else";
    "if"; "lambda"; "let"; "let*"; "letrec"; "or";
    "quasiquote"; "quote"; "set!"; "unquote";
    "unquote-splicing"];; 
 
 
 let rec from_pairs_to_list = function
   | Nil -> []
   | Pair(x,Nil)->[x] 
   | Pair (x,y) -> x :: (from_pairs_to_list y) 
   | _ -> raise X_syntax_error ;;
 
   let list_to_pairs ls = 
    List.fold_right
   (fun a b -> Pair(a , b))
    ls
    Nil ;;
   let rec from_pairs_to_list_improper = function
   | Pair(x,Pair(y,z))-> x :: (from_pairs_to_list_improper (Pair(y,z))) 
   | Pair (x,y) -> x :: y::[] 
   | _ -> raise X_syntax_error ;;
 
 let rec is_proper = function
   | Nil -> true
   | Pair(x,Nil) -> true
   | Pair(x,y) -> (is_proper y)
   | _ -> false;;
 
 
   let rec seq_tag_parser f list =
     match list with
     | [] -> Const(Void)
     | x::[] -> (f x)
     | x -> Seq (List.map f x) ;;

     let get_first  = function
     |Pair (Symbol(x), Pair (y, Nil))-> x
     |_-> raise X_syntax_error;;
   
   let get_second = function
     |Pair (Symbol(x), Pair (y, Nil))-> y
     |_-> raise X_syntax_error;;
 
 
   let get_string s =
     match s with 
     | Symbol(x)-> x 
     | _ -> raise X_syntax_error ;;
     
 (***********MACROS ********************************************)
   let rec and_macro f x = 
     match x with 
   | Nil -> Const (Sexpr (Bool true))
   | Pair(x,Nil) -> (f x)
   | Pair(x,Pair(a,b)) -> let p = Pair(a,b) in
                         If (f x , (and_macro f p) , Const (Sexpr (Bool false)))
   |_-> raise X_syntax_error ;;

   let rec let_macro f x = 
    match x with
    | Pair(Nil , body) -> Applic((f (Pair(Symbol "lambda",(Pair(Nil,body))))), [])
    | Pair(args ,body)-> let arglist = List.rev (from_pairs_to_list args) in
                         let args   = List.fold_left (fun acc a -> 
                                                      match a with
                                                      | (Pair(x,_)) -> (Pair(x, acc))
                                                      | _ -> raise X_syntax_error) Nil arglist in
                         let values = List.fold_left (fun acc a -> 
                                                        match a with 
                                                        | (Pair(_,(Pair(x,Nil)))) -> x::acc
                                                        | (Pair(_,(Pair(Symbol("quote"),(Pair(x,Nil)))))) -> (Pair(Symbol("quote"),(Pair(x,Nil))))::acc
                                                        | _ -> raise X_syntax_error) [] arglist in
                         let values = List.map f values in
                         Applic((f (Pair(Symbol "lambda",(Pair(args,body))))), values) 
    | _ -> raise X_syntax_error ;;

    let rec let_star_macro f x = 
      begin match x with 
      | Pair(args ,body)-> let arglist = (from_pairs_to_list args) in
                         let values = List.fold_left (fun acc a -> 
                                                        begin match a with 
                                                        | (Pair(_,(Pair(x,Nil)))) -> x::acc
                                                        | _ -> raise X_syntax_error end) [] arglist in
                         let num_of_args = List.length values in
                         if(num_of_args < 2 ) then let sexpr = Pair(Symbol ("let"), Pair(args,body)) in
                                                    (f sexpr) 
                         else begin match args with
                          | Pair(first, rest) -> let sexpr = (Pair(Symbol ("let"), (Pair ((Pair(first,Nil)), (Pair(Pair (Symbol ("let*"), Pair(rest,body)),Nil)))))) in
                                                (f sexpr)
                          | _ -> raise X_syntax_error end
        | _ -> raise  X_syntax_error end;;

      let rec letrec_macro f x = 
        match x with
        | Pair(args ,body)-> 
          let arglist    = (from_pairs_to_list args) in
          let set_args   = List.map (fun (arg) -> Pair(Symbol "set!",arg)) arglist in
          let body_list  = (from_pairs_to_list body) in 
          let body_list  = List.append set_args body_list in
          let body_pairs = (list_to_pairs body_list) in
          let args = List.map (fun x -> match x with
                                        | (Pair(x,y))->Pair(x,(Pair(Symbol("quote"),Pair(Symbol("whatever"),Nil))))
                                        | _ -> raise X_syntax_error) (from_pairs_to_list args) in
          let args = (list_to_pairs args) in
          let sexpr = (Pair(Symbol ("let"), (Pair (args, body_pairs)))) in
          (f sexpr)
        | _ -> raise X_syntax_error ;;

      let define_macro f x =
        match x with
        | Pair(Pair(var,args),body)->let lambda = (Pair (Symbol("lambda"),Pair(args, body))) in
                      let define_exp = Pair(Symbol("define"),Pair(var,Pair(lambda,Nil))) in
                      (f define_exp)
        | _ -> raise X_syntax_error ;;



    let rec quasi_macro x = 
      match x with
      | Nil ->  Pair(Symbol("quote"),Pair(x,Nil))
      | Symbol(a)-> Pair(Symbol("quote"),Pair(x,Nil))
      | Pair(Symbol ("unquote"),Pair(sexpr,Nil)) -> sexpr
      | Pair(Symbol ("unquote-splicing"),Pair(sexpr,Nil)) -> raise X_syntax_error
      | Vector(a) ->  let pairs = (list_to_pairs (List.map quasi_macro a)) in
                      Pair(Symbol "vector",pairs)
      | Pair((Pair((Symbol("unquote-splicing")), (Pair(a, Nil)))), b) -> 
              (Pair((Symbol("append")),(Pair(a, (Pair((quasi_macro b), Nil))))))
      | Pair(a, (Pair((Symbol("unquote-splicing")), (Pair(b, Nil))))) ->
              (Pair((Symbol("cons")), (Pair((quasi_macro a), (Pair(b, Nil))))))
      | Pair(a,b) -> (Pair((Symbol("cons")), (Pair((quasi_macro a), (Pair((quasi_macro b), Nil))))))
      | elsee-> elsee ;;   
      
      
      let rec cond_macro = function
      | Nil -> Nil
      | Pair(Pair(Symbol ("else"),rib),Nil) -> Pair (Symbol ("begin"),rib)
      
      |Pair(Pair(x,Pair(Symbol("=>"),y)),Nil) -> (Pair (Symbol "let",
                                            Pair
                                             (Pair (Pair (Symbol "value", Pair (x, Nil)),
                                               Pair
                                                (Pair (Symbol "f",
                                                  Pair (Pair (Symbol "lambda", Pair (Nil,y)),
                                                   Nil)),
                                                Nil)),
                                             Pair
                                              (Pair (Symbol "if",
                                                Pair (Symbol "value",
                                                 Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)), Nil))),
                                              Nil))))
        | Pair(Pair(x,Pair(Symbol("=>"),y)),ribs) -> 
              Pair (Symbol "let",
              Pair
               (Pair (Pair (Symbol "value", Pair (x, Nil)),
                 Pair
                  (Pair (Symbol "f",
                    Pair (Pair (Symbol "lambda", Pair (Nil, y)),
                     Nil)),
                  Pair
                   (Pair (Symbol "rest",
                     Pair (Pair (Symbol "lambda", Pair (Nil, Pair ((cond_macro ribs), Nil))),
                      Nil)),
                   Nil))),
               Pair
                (Pair (Symbol "if",
                  Pair (Symbol "value",
                   Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)),
                    Pair (Pair (Symbol "rest", Nil), Nil)))),
                Nil)))
    
      |Pair(Pair(test,alt),Nil) -> (Pair (Symbol "if",Pair(test,Pair(Pair(Symbol("begin"),alt),Nil))))

      |Pair(Pair(test,alt),elsee) -> (Pair (Symbol "if",Pair(test,Pair(Pair(Symbol("begin"),alt),Pair ((cond_macro elsee), Nil)))))
      
      | _ -> raise X_syntax_error ;;
 (***********MACROS ********************************************)

  
 
   let rec duplicate = function
     | [] -> true
     | list-> let fst = List.hd list in
             let f_list = List.filter (fun x ->(String.equal x fst)) (List.tl list) in
           if(List.length f_list != 0 ) then false 
           else (duplicate (List.tl list)) ;;
 
   let rec add_begin = function
     | Pair(Symbol ("begin"),x)-> Pair(Symbol ("begin"),x)
     | x -> Pair(Pair(Symbol ("begin"),x),Nil) ;;
   
  
 
  let rec tag_parser = function 
   | Number(x) -> Const (Sexpr (Number(x)))
   | Char (x) -> Const (Sexpr (Char (x)))
   | Bool (x) -> Const (Sexpr (Bool (x)))
   | String (x) -> Const (Sexpr (String (x)))
   | Pair(Symbol("quote"),Pair(a,Nil)) -> Const (Sexpr (a))
 
     
   (********* Var Tag Parser***********************************)
  
     | Symbol(x) -> if (List.mem x reserved_word_list) then raise X_syntax_error
                    else Var x 
 
   (********* if Tag Parser***********************************)
 
   | Pair(Symbol("if"),Pair(test,Pair(x,Pair(y,Nil)))) -> If (tag_parser test , tag_parser x , tag_parser y) 
   | Pair(Symbol("if"),Pair(test,Pair(x,Nil))) -> If (tag_parser test, tag_parser x , Const(Void)) 
 
   (********* set Tag Parser***********************************) 
 
   | Pair(Symbol("set!"),Pair(Symbol(x),Pair(sec,Nil))) -> let first = Symbol(x) in 
                                                           Set (tag_parser first , tag_parser sec)
 
     (********* Define Tag Parser***********************************) 
   | Pair(Symbol("define"),Pair(Symbol(x),Pair(sec,Nil))) -> let first = Symbol(x) in
                                                             Def (tag_parser first , tag_parser sec) 
 
   (********* Sequence Tag Parser***********************************) 
   | Pair (Symbol ("begin"),x) -> (seq_tag_parser tag_parser (from_pairs_to_list x))
 
   (********* LambdaSimple Tag Parser***********************************) 
   | Pair (Symbol ("lambda"),Pair(arglist,body)) ->
     begin match body with 
     | Nil -> raise X_syntax_error
     | _ ->
       let body = (add_begin body) in
       let body = match body with 
       | Pair(body, Nil)-> body
       | _ -> raise X_syntax_error in
     begin  match arglist with 
       | Nil->LambdaSimple([] , (tag_parser body))
       | (Pair(x,y)) ->
         if(is_proper arglist) then 
           let arglist = List.map get_string (from_pairs_to_list arglist) in
          if(duplicate arglist) then LambdaSimple(arglist , (tag_parser body))
           else raise X_syntax_error 
         else 
           let arglist = List.map get_string (from_pairs_to_list_improper arglist) in
            if (duplicate arglist) then 
            let length = List.length arglist in
            let s = List.nth arglist (length-1) in
            let arglist = List.rev(List.tl(List.rev arglist)) in
            LambdaOpt(arglist,s, (tag_parser body))
            else raise X_syntax_error
       | Symbol(x) -> LambdaOpt([] , x , (tag_parser body))
       | _ -> raise X_syntax_error end
     end
   
   | Pair (Symbol ("or"), Nil) -> Const (Sexpr (Bool false))
   | Pair (Symbol ("or"),Pair(x,Nil)) -> (tag_parser x)
   |  Pair (Symbol ("or"),Pair(x,Pair(a,b))) -> 
       let x = Pair(x,Pair(a,b)) in
       let ls = (from_pairs_to_list x) in
       Or (List.map tag_parser ls)
 
   
   | Pair (Symbol ("and"), x) -> (and_macro tag_parser x)
   | Pair (Symbol ("let"), x) -> (let_macro tag_parser x)
   | Pair (Symbol ("let*"),x) -> (let_star_macro tag_parser x)
   | Pair (Symbol ("letrec"),x) -> (letrec_macro tag_parser x)
   | Pair (Symbol ("define"),x) -> (define_macro tag_parser x)
   |  Pair (Symbol ("quasiquote"),Pair(x,Nil)) -> (tag_parser (quasi_macro x))
   | Pair (Symbol ("cond"),x) -> (tag_parser (cond_macro x))
     
   | Pair(app,params) -> 
       let params = (from_pairs_to_list params) in
       Applic ((tag_parser app) ,((List.map tag_parser params)))
 
   | _ -> raise X_syntax_error ;;
                                                               
 
 let tag_parse_expression sexpr = (tag_parser sexpr);;
  let tag_parse_expressions sexpr = List.map tag_parse_expression sexpr;;
    end;; 
 (*******************************888888888*************************************************************)
  (* struct Tag_Parser *)
 