
(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)

 #use "pc.ml";;
 open PC;;
 exception X_not_yet_implemented;;
 exception X_this_should_not_happen;;
   
 type number =
   | Int of int
   | Float of float;;
   
 type sexpr =
   | Bool of bool
   | Nil
   | Number of number
   | Char of char
   | String of string
   | Symbol of string
   | Pair of sexpr * sexpr
   | Vector of sexpr list;;
 
   let rec sexpr_eq s1 s2 =
    match s1, s2 with
    | Bool(b1), Bool(b2) -> b1 = b2
    | Nil, Nil -> true
    | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
    | Number(Int n1), Number(Int n2) -> n1 = n2
    | Char(c1), Char(c2) -> c1 = c2
    | String(s1), String(s2) -> s1 = s2
    | Symbol(s1), Symbol(s2) -> s1 = s2
    | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
    | Vector(l1), Vector(l2) -> if ((List.length(l1)) != (List.length (l2))) then false
                                  else List.for_all2 sexpr_eq l1 l2
    | _ -> false;;
   
 module Reader: sig
   val read_sexpr : string -> sexpr
   val read_sexprs : string -> sexpr list
 end
 = struct

 let normalize_scheme_symbol str =
   let s = string_to_list str in
   if (andmap
   (fun ch -> (ch = (Char.lowercase_ascii ch)))
   s) then str
   else Printf.sprintf "|%s|" str;;
 
 let nt_line_comment = 
   let nt_semicolon = char ';' in
   let nt_end = pack nt_end_of_input (fun ch -> '\n')  in
   let nt_end = disj nt_end  (char '\n')  in
   let nt_chars = star (diff nt_any nt_end) in 
   let nt = caten nt_semicolon nt_chars in
   let nt = caten nt nt_end in 
   let nt = pack nt (fun ch -> Nil) in
   nt;;
 
   let nt_whitespace_reader = 
     let nt_whitespace_reader = pack nt_whitespace (fun x-> Nil) in
     nt_whitespace_reader;;
 
 let rec remove_exps hash_list sexpr_list = 
 match hash_list with 
 | [] -> sexpr_list
 | ["#;"]->(List.tl   sexpr_list)
 | "#;"::tl->
     if ((List.length (List.tl sexpr_list)) > 0) then (remove_exps (List.tl hash_list) (List.tl  sexpr_list))
     else []
 |_ -> raise X_no_match ;;
 
 
 
 let nt_fboolean = pack(word_ci "#f")(fun ch->Bool false) ;;
 let nt_tboolean = pack(word_ci "#t")(fun ch->Bool true) ;;
 let nt_boolean = disj nt_fboolean nt_tboolean ;;
 
 let nt_symbol = 
   let symbols = disj_list[char '!';char '$';char '^';char '*';
                           char '-';char '_';char '=';char '+';
                           char '<';char '>';char '?';char '/';
                           char ':'] in
   let nt = disj symbols (range '0' '9') in
   let nt = disj nt (range 'a' 'z') in
   let nt = disj nt (range 'A' 'Z') in
   let nt = plus nt in
   let nt  = pack nt (fun x-> Symbol (String.lowercase_ascii(list_to_string x))) in
   nt;;
 
 let nt_sign_reader   = disj (pack (char '+')(fun ch -> 1)) (pack (char '-')(fun ch -> -1));;
 let nt_plus_digit = (plus(range '0' '9'));;
 let nt_plus_hex_digit = (plus(disj (range_ci 'a' 'f')(range '0' '9')));;
 let nt_star_hex_digit = (star(disj (range_ci 'a' 'f')(range '0' '9')));;
 let nt_star_digit = (star(range '0' '9'));;
 
 let nt_int = 
   let nt_maybe = maybe nt_sign_reader in
   let nt_sign = pack nt_maybe (fun res-> match res with
   | None -> 1
   | Some(sign) -> sign) in
    let nt_int = caten nt_sign nt_plus_digit in
    let nt_int = pack nt_int (fun (sign,digits)-> Int(sign * (int_of_string(list_to_string digits)))) in
   nt_int;;
 
 let nt_hex_int =
   let nt_hex = (word_ci "#x") in
   let nt_maybe = maybe nt_sign_reader in
   let nt_sign = pack nt_maybe (fun res-> match res with
   | None -> 1
   | Some(sign) -> sign) in
    let nt_hex_int = caten (caten nt_hex  nt_sign )nt_plus_hex_digit in
    let nt_hex_int = pack nt_hex_int (fun ((hex,sign),digits)-> Int(sign * (int_of_string("0x"^list_to_string digits)))) in
    nt_hex_int;;
 
 let nt_float = 
   let nt_maybe = maybe nt_sign_reader in
   let nt_sign = pack nt_maybe (fun res-> match res with
   | None -> 1
   | Some(sign) -> sign) in
   let nt_float = caten nt_sign nt_plus_digit in
   let nt_float = caten (caten nt_float (char '.')) nt_plus_digit in
   let nt_float = pack nt_float (fun (((sign , first_digs) , dot) ,  rest_digs)->
     Float((float_of_int sign) *. 
     (float_of_string((list_to_string first_digs)^(Char.escaped dot)^(list_to_string rest_digs)))) )  in
   nt_float;;
 
   let nt_hex_float = 
     let nt_hex = (word_ci "#x") in
     let nt_maybe = maybe nt_sign_reader in
     let nt_sign = pack nt_maybe (fun res-> match res with
     | None -> 1
     | Some(sign) -> sign) in
     let nt_hex_float = caten (caten nt_hex  nt_sign)nt_plus_hex_digit in
     let nt_hex_float = caten (caten nt_hex_float (char '.')) nt_plus_hex_digit in
     let nt_hex_float = pack nt_hex_float (fun ((((hex,sign) , first_digs) , dot) ,  rest_digs)->
       Float((float_of_int sign) *. 
       (float_of_string("0x"^(list_to_string first_digs)^(Char.escaped dot)^(list_to_string rest_digs)))) ) in
     nt_hex_float;;
 
 
 let nt_number_not_followed = 
   let nt_int = disj nt_hex_int nt_int in
   let nt_float = disj nt_hex_float nt_float in
   let nt_number_not_followed = disj nt_float nt_int in
   let nt_number_not_followed  = not_followed_by nt_number_not_followed nt_symbol in
   let nt_number_not_followed = pack nt_number_not_followed (fun x-> Number x) in
   nt_number_not_followed;;
 
   let nt_number_followed = 
     let nt_int = disj nt_hex_int nt_int in
     let nt_float = disj nt_hex_float nt_float in
     let nt_number_followed = disj nt_float nt_int in
     let nt_number_followed = pack nt_number_followed (fun x-> Number x) in
     nt_number_followed;;
 
 let get_number s = match s with
   | Number(x) -> x 
   | _ -> raise X_no_match;;
 let get_string s = match s with
   | Int(x) -> string_of_int x
   | Float(x) -> string_of_float x ;;
 
 let nt_scientific = 
   let e = char_ci 'e' in
   let nt_scientific = caten nt_number_followed e in 
   let nt_scientific = caten nt_scientific nt_number_not_followed in
   let nt_scientific = pack nt_scientific (fun ((x, y), z)->(
    (get_string(get_number x)) ^ "e" ^ (get_string(get_number z))  ) )in
   let nt_scientific = pack nt_scientific (fun x-> Float (float_of_string x)) in
   let nt_scientific = pack nt_scientific (fun x-> Number x ) in
   nt_scientific ;;
 
 let nt_char_prefix = (word "#\\");;
 let nt_visible_char = const (fun ch -> ch > ' ');;
 let nt_named_char = 
    let nt_newline = pack (word_ci "newline") (fun x -> '\n') in
    let nt_nul = pack (word_ci "nul") (fun x -> '\000') in
    let nt_page = pack (word_ci "page") (fun x -> '\012') in
    let nt_return = pack (word_ci "return") (fun x -> '\r') in
    let nt_space = pack (word_ci "space") (fun x -> ' ') in
    let nt_tab = pack (word_ci "tab") (fun x -> '\t') in
    let nt_named_char = disj_list [nt_newline ; nt_nul ; nt_page ; nt_return ; nt_space ; nt_tab] in
    nt_named_char;;
 let nt_hex_char = pack (caten (char_ci 'x') nt_plus_hex_digit) 
   (fun (first,rest) -> (Char.chr (int_of_string ("0" ^ (Char.escaped first) ^(list_to_string rest)))));;
 
 let nt_char =  
   let nt = caten nt_char_prefix (disj_list [nt_named_char ; nt_hex_char ; nt_visible_char]) in 
   let nt = pack nt (fun (a,b)-> Char b) in
   nt;;
 
   let nt_literal_char = const (fun ch -> ch != '\\' && ch != '\"');;
   let nt_meta_char =  
     let nt_newline = pack (word_ci "\\n") (fun x -> '\n') in
     let nt_nul = pack (word_ci "\\nul") (fun x -> '\000') in
     let nt_page = pack (word_ci "\\f") (fun x -> '\012') in
     let nt_return = pack (word_ci "\\r") (fun x -> '\r') in
     let nt_tab = pack (word_ci "\\t") (fun x -> '\t') in
     let nt_backslash = pack (word_ci "\\\\") (fun x -> '\\') in
     let nt_quote = pack (word_ci "\\\"") (fun x -> '\"') in
     let nt_meta_char = disj_list [nt_quote;nt_newline; nt_nul; nt_page; 
                                   nt_return; nt_tab; nt_backslash] in
     nt_meta_char;;
     let nt_double_quote = char '\"';;
   let nt_hex_prefix = (word_ci "\\x");;
 
   let nt_string = 
     let nt = caten nt_hex_prefix nt_plus_hex_digit in
     let nt = caten nt (char ';') in
     let nt = pack nt (fun ((a, b) ,c)->(Char.chr (int_of_string  ("0x" ^ (list_to_string b)) ))) in
     let nt1 = disj nt_meta_char nt_literal_char in
     let nt = disj nt nt1 in
     let nt_string = star nt in
     let nt_string = caten nt_double_quote nt_string in 
     let nt_string = caten nt_string nt_double_quote in 
     let nt_string = pack nt_string (fun ((a,b),c)->String (list_to_string b)) in
     nt_string;;
  
     let lp = char '(' ;;
     let rp = char ')' ;;

       let rec proper_list s = match s with 
       | [] -> Nil
       | head::tail -> Pair(head, proper_list tail) ;;
 
       let rec improper_list s =        
        match s with 
       | [] -> raise X_no_match
       | head::tail::[] -> Pair(head,tail)
       | head :: tail -> Pair(head, improper_list tail) ;;
 
       let appending s x = List.append s [x];;
 
    
   let nt_atomic_sexpr = disj_list [nt_boolean;nt_scientific; nt_number_not_followed ; nt_char ; nt_string ; nt_symbol] ;;
 
     
   let rec nt_proper_list s = 
       let nt_proper_list = pack (caten lp (caten (star nt_sexpr) rp)) (fun (a,(b,c))-> proper_list b) in  
       nt_proper_list s 
 
     and nt_nest_list s = 
      let junk_list = disj nt_line_comment nt_whitespace_reader in
      let star_junk = star junk_list in
      let nt_nest_list = caten star_junk lp in
      let nt_nest_list = caten nt_nest_list (star nt_nested_sexpr) in
      let nt_nest_list = caten nt_nest_list star_junk in
      let nt_nest_list = caten nt_nest_list (word "...") in
      let nt_nest_list =  pack nt_nest_list (fun ((((a,b),c),d),e)-> proper_list c) in
      nt_nest_list s
      
    and nt_nested_list s =
      let nt_nested_list = caten lp (star nt_nested_sexpr) in
      let nt_nested_list = caten nt_nested_list (maybe rp) in
      let nt_nested_list = pack nt_nested_list (fun ((a,b),c)-> proper_list b) in 
      nt_nested_list s
    
    and nt_nest_dotted_list s = 
      let nt_nest_dotted_list = caten lp (plus nt_nested_sexpr) in 
      let nt_nest_dotted_list = caten nt_nest_dotted_list (char '.') in 
      let nt_nest_dotted_list = caten nt_nest_dotted_list nt_nested_sexpr in 
      let nt_nest_dotted_list = caten nt_nest_dotted_list (word "...") in 
      let nt_nest_dotted_list = pack nt_nest_dotted_list (fun (((((a,b),c),d),e)) -> appending b d) in
      let nt_nest_dotted_list = pack nt_nest_dotted_list (fun a -> improper_list a) in
      nt_nest_dotted_list s 

    and nt_nested_dotted_list s = 
      let nt_nested_dotted_list = caten lp (plus nt_nested_sexpr) in 
      let nt_nested_dotted_list = caten nt_nested_dotted_list (char '.') in 
      let nt_nested_dotted_list = caten nt_nested_dotted_list nt_nested_sexpr in 
      let nt_nested_dotted_list = caten nt_nested_dotted_list (maybe rp) in
      let nt_nested_dotted_list = pack nt_nested_dotted_list (fun (((((a,b),c),d),e)) -> appending b d) in
      let nt_nested_dotted_list = pack nt_nested_dotted_list (fun a -> improper_list a) in
      nt_nested_dotted_list s

      and nt_nest_bracket_list s =
      let junk_list = disj nt_line_comment nt_whitespace_reader in
      let star_junk = star junk_list in
      let lp = char '[' in 
      let nt_nest_bracket_list = caten star_junk lp in
      let nt_nest_bracket_list = caten nt_nest_bracket_list (star nt_nested_sexpr) in
      let nt_nest_bracket_list = caten nt_nest_bracket_list star_junk in
      let nt_nest_bracket_list = caten nt_nest_bracket_list (word "...") in
      let nt_nest_bracket_list =  pack nt_nest_bracket_list (fun ((((a,b),c),d),e)-> proper_list c) in
      nt_nest_bracket_list s
      
      and nt_nested_bracked_list s =
      let lp = char '[' in 
      let rp = char ']' in
      let nt_nested_bracked_list = caten lp (star nt_nested_sexpr) in
      let nt_nested_bracked_list = caten nt_nested_bracked_list (maybe rp) in
      let nt_nested_bracked_list = pack nt_nested_bracked_list (fun ((a,b),c)-> proper_list b) in 
      nt_nested_bracked_list s
      
      and nt_nest_bracket_dotted_list s = 
      let lp = char '[' in 
      let nt_nest_bracket_dotted_list = caten lp (plus nt_nested_sexpr) in 
      let nt_nest_bracket_dotted_list = caten nt_nest_bracket_dotted_list (char '.') in 
      let nt_nest_bracket_dotted_list = caten nt_nest_bracket_dotted_list nt_nested_sexpr in 
      let nt_nest_bracket_dotted_list = caten nt_nest_bracket_dotted_list (word "...") in 
      let nt_nest_bracket_dotted_list = pack nt_nest_bracket_dotted_list (fun (((((a,b),c),d),e)) -> appending b d) in
      let nt_nest_bracket_dotted_list = pack nt_nest_bracket_dotted_list (fun a -> improper_list a) in
      nt_nest_bracket_dotted_list s 
      
      and nt_nested_bracket_dotted_list s = 
      let lp = char '[' in 
      let rp = char ']' in
      let nt_nested_bracket_dotted_list = caten lp (plus nt_nested_sexpr) in 
      let nt_nested_bracket_dotted_list = caten nt_nested_bracket_dotted_list (char '.') in 
      let nt_nested_bracket_dotted_list = caten nt_nested_bracket_dotted_list nt_nested_sexpr in 
      let nt_nested_bracket_dotted_list = caten nt_nested_bracket_dotted_list (maybe rp) in
      let nt_nested_bracket_dotted_list = pack nt_nested_bracket_dotted_list (fun (((((a,b),c),d),e)) -> appending b d) in
      let nt_nested_bracket_dotted_list = pack nt_nested_bracket_dotted_list (fun a -> improper_list a) in
      nt_nested_bracket_dotted_list s

    and nt_nest_vector s = 
      let prefix = word "#(" in
      let star_nested_sexp = star nt_nested_sexpr in
      let nt_vector = caten prefix star_nested_sexp in
      let nt_vector = caten nt_vector (word "...") in
      let nt_vector = pack nt_vector (fun ((a,b),c)-> Vector b) in 
      nt_vector s 
    
    and nt_nested_vector s = 
      let prefix = word "#(" in
      let star_nested_sexp = star nt_nested_sexpr in
      let nt_vector = caten prefix star_nested_sexp in
      let nt_vector = caten nt_vector (maybe rp) in
      let nt_vector = pack nt_vector (fun ((a,b),c)-> Vector b) in 
      nt_vector s 
    
      and nt_nested_quoted s = 
      let quote =  char '\'' in 
      let nt_nested_quoted = caten quote nt_nested_sexpr in 
      let nt_nested_quoted = pack nt_nested_quoted (fun (a,b)-> Pair(Symbol("quote") , Pair(b,Nil))) in 
      nt_nested_quoted s
  
    and nt_nested_quasi_quoted s = 
      let quasi_quote =  char '`' in 
      let nt_nested_quasi_quoted = caten quasi_quote nt_nested_sexpr in 
      let nt_nested_quasi_quoted = pack nt_nested_quasi_quoted (fun (a,b)-> Pair(Symbol("quasiquote") , Pair(b,Nil))) in 
      nt_nested_quasi_quoted s
  
    and nt_nested_unquoted s = 
        let unquote =  char ',' in 
        let nt_nested_unquoted = caten unquote nt_nested_sexpr in 
        let nt_nested_unquoted = pack nt_nested_unquoted (fun (a,b)-> Pair(Symbol("unquote") , Pair(b,Nil)))  in 
        nt_nested_unquoted s
  
    and nt_nested_unquoted_spliced s = 
      let unquoted_spliced  =  caten (char ',') (char '@') in 
      let nt_nested_unquoted_spliced = caten unquoted_spliced  nt_nested_sexpr in 
      let nt_nested_unquoted_spliced = pack nt_nested_unquoted_spliced (fun ((a,b),c)->Pair(Symbol("unquote-splicing") , Pair(c,Nil)))  in 
      nt_nested_unquoted_spliced s
    
      and nt_nested_sexpr s =
      let nt_nested_sexpr =  disj_list [nt_nested_unquoted_spliced; nt_nested_unquoted ;nt_nested_quasi_quoted; 
                                        nt_nested_quoted ;nt_nested_bracket_dotted_list ; nt_nested_bracked_list ;
                                        nt_nested_vector; nt_nested_dotted_list; nt_nested_list; nt_atomic_sexpr] in 
      let junk_list = disj nt_line_comment nt_whitespace_reader in
      let star_junk = star junk_list in
      let nt_nested_sexpr = caten star_junk nt_nested_sexpr in 
      let nt_nested_sexpr = caten nt_nested_sexpr star_junk in
      let nt_nested_sexpr = pack nt_nested_sexpr (fun ((a,b),c) -> b) in
      nt_nested_sexpr s
     
      and nt_proper_bracket s = 
      let junk_list = disj nt_line_comment nt_whitespace_reader in
      let star_junk = star junk_list in
      let lb = char '[' in
      let rb = char ']' in 
      let nt_proper_bracket = caten star_junk lb in
      let nt_proper_bracket = caten nt_proper_bracket star_junk in
      let nt_proper_bracket = caten nt_proper_bracket (star nt_sexpr) in
      let nt_proper_bracket = caten nt_proper_bracket star_junk in
      let nt_proper_bracket = caten nt_proper_bracket rb in
      let nt_proper_bracket = caten nt_proper_bracket star_junk in
      let nt_proper_bracket = pack nt_proper_bracket (fun ((((((a,b),c),d),e),f),g) -> proper_list d) in  
      nt_proper_bracket s
 
   and nt_improper_list s = 
     let dot = char '.' in
     let plus_sexp = plus nt_sexpr in
     let nt_improper_list = caten lp plus_sexp in
     let nt_improper_list = caten nt_improper_list dot in
     let nt_improper_list = caten nt_improper_list nt_sexpr in
     let nt_improper_list = caten nt_improper_list rp in
     let nt_improper_list = pack nt_improper_list (fun (((((a,b),c),d),e)) -> appending b d) in
     let nt_improper_list = pack nt_improper_list (fun a -> improper_list a) in
     nt_improper_list s
 
     and nt_improper_bracket s = 
     let lb = char '[' in
     let rb = char ']' in 
     let dot = char '.' in
     let plus_sexp = plus nt_sexpr in
     let nt_improper_bracket = caten lb plus_sexp in
     let nt_improper_bracket = caten nt_improper_bracket dot in
     let nt_improper_bracket = caten nt_improper_bracket nt_sexpr in
     let nt_improper_bracket = caten nt_improper_bracket rb in
     let nt_improper_bracket = pack nt_improper_bracket (fun (((((a,b),c),d),e)) -> appending b d) in
     let nt_improper_bracket = pack nt_improper_bracket (fun a -> improper_list a) in
     nt_improper_bracket s
     
   and nt_vector s = 
     let junk_list = disj nt_line_comment nt_whitespace_reader in
     let star_junk = star junk_list in
     let prefix = word "#(" in
     let star_sexp = star nt_sexpr in
     let nt_vector = caten star_junk prefix in
     let nt_vector = caten nt_vector star_junk in
     let nt_vector = caten nt_vector star_sexp in
     let nt_vector = caten nt_vector star_junk in
     let nt_vector = caten nt_vector rp in
     let nt_vector = pack nt_vector (fun (((((a,b),c),d),e),f)-> Vector d) in 
     nt_vector s 

 
   and nt_quoted s = 
     let quote =  char '\'' in 
     let nt_quoted = caten quote nt_sexpr in 
     let nt_quoted = pack nt_quoted (fun (a,b)-> Pair(Symbol("quote") , Pair(b,Nil))) in 
     nt_quoted s
 
   and nt_quasi_quoted s = 
     let quasi_quote =  char '`' in 
     let nt_quasi_quoted = caten quasi_quote nt_sexpr in 
     let nt_quasi_quoted = pack nt_quasi_quoted (fun (a,b)-> Pair(Symbol("quasiquote") , Pair(b,Nil))) in 
     nt_quasi_quoted s
 
   and nt_unquoted s = 
       let unquote =  char ',' in 
       let nt_unquoted = caten unquote nt_sexpr in 
       let nt_unquoted = pack nt_unquoted (fun (a,b)-> Pair(Symbol("unquote") , Pair(b,Nil)))  in 
       nt_unquoted s
 
   and nt_unquoted_spliced s = 
     let unquoted_spliced  =  caten (char ',') (char '@') in 
     let nt_unquoted_spliced = caten unquoted_spliced  nt_sexpr in 
     let nt_unquoted_spliced = pack nt_unquoted_spliced (fun ((a,b),c)->Pair(Symbol("unquote-splicing") , Pair(c,Nil)))  in 
     nt_unquoted_spliced s
 
   and nt_sepxr_comment s = 
       let nt_sepxr_comment = word "#;" in
       let nt_sepxr_comment = caten nt_sepxr_comment nt_sexpr in
       let nt_sepxr_comment = caten nt_sepxr_comment nt_sexpr in
       let nt_sepxr_comment = pack nt_sepxr_comment (fun ((a,b),c) -> c ) in
       nt_sepxr_comment s 

    and nt_dots s = 
      let nt_dots = word "..." in
      let nt_dots = pack nt_dots (fun x -> Nil) in
      nt_dots s
       
    and  nt_nil s = 
       let junk_list = disj_list  [nt_sepxr_comment; nt_line_comment; nt_whitespace_reader] in
       let star_junk = star junk_list in
       let nt_nil = caten lp star_junk in
       let nt_nil = caten nt_nil rp in
       let nt_nil = pack nt_nil (fun x -> Nil) in 
       nt_nil s 
       
   and nt_sexpr s = 
     let nt_nested_sexpr = disj_list[nt_nest_list; nt_nest_dotted_list; nt_nest_bracket_list;
                                     nt_nest_bracket_dotted_list; nt_nest_vector ] in 
     let sexpr_list = disj_list [nt_proper_list ; nt_improper_list ; nt_atomic_sexpr; 
                                 nt_vector ; nt_quoted ; nt_quasi_quoted ; nt_unquoted ; nt_unquoted_spliced ;  nt_nil;nt_sepxr_comment ;
                                 nt_proper_bracket; nt_improper_bracket ; nt_nested_sexpr] in 
     let junk_list = disj_list [nt_line_comment; nt_whitespace_reader ;nt_dots ]in
     let star_junk = star junk_list in
     let nt_sexpr = caten star_junk sexpr_list in 
     let nt_sexpr = caten nt_sexpr star_junk in
     let nt_sexpr = pack nt_sexpr (fun ((a,b),c) -> b) in
     nt_sexpr s ;;
 
 (*************************************END OF CODE *********************************)
 
 
 
 let read_sexpr string = 
    let (answer,rest) = nt_sexpr (string_to_list string) in
    match rest with
    | [] -> answer
    | _ -> raise X_no_match ;;
  
  let read_sexprs string = 
   let (answer,s) = star nt_sexpr (string_to_list string) in 
   answer;;
  
  end;; (*struct Reader *)


 
 
 
 
 
   
 