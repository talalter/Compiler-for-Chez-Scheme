#use "reader.ml";;

type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;
exception X_worng;;


let rec proper_or_improper = function
    | ScmNil -> true           
    | ScmPair(car,cdr) -> proper_or_improper cdr 
    | _ -> false 


let remove_list lst = match lst with
| [x] -> x
| _ ->  ScmVoid

(*let get_second = function
|lambda::second::third -> second
let get_third = function
|lambda::second::third -> third*)

let remove_scm_symbol symbol = 
    match symbol with
    | ScmSymbol (str) -> str
    | _ -> raise (X_syntax_error (symbol, "This shouldnt happen"))

(* takes list of sexpr and return proper list of sexpr connecting them
val y : sexpr = ScmNumber (ScmReal 1.23)
val x : sexpr = ScmBoolean true
val lst : sexpr list = [ScmBoolean true; ScmNumber (ScmReal 1.23)]
list_to_proper_list lst;;
- : sexpr = ScmPair (ScmBoolean true, ScmPair (ScmNumber (ScmReal 1.23), ScmNil))
*)
let rec list_to_proper_list = function
| [] -> ScmNil
| hd::[] -> ScmPair (hd, ScmNil)
| hd::tl -> ScmPair (hd, list_to_proper_list tl);;


(* takes list of sexpr and return improper list of sexpr connecting them
val y : sexpr = ScmNumber (ScmReal 1.23)
val x : sexpr = ScmBoolean true
val lst : sexpr list = [ScmBoolean true; ScmNumber (ScmReal 1.23)]
list_to_improper_list lst;;
- : sexpr = ScmPair (ScmBoolean true, ScmNumber (ScmReal 1.23))
*)


let rec list_to_improper_list = function
| [] -> raise X_proper_list_error
| hd::[] -> hd
| hd::tl -> ScmPair (hd, list_to_improper_list tl);;


let rec scm_append scm_list sexpr =
match scm_list with
| ScmNil -> sexpr
| ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
| _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"))

let rec scm_map f sexpr =
match sexpr with
| ScmNil -> ScmNil
| ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
| _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
match sexpr1, sexpr2 with
| ScmNil, ScmNil -> ScmNil
| ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
| _, _ ->
    let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
    raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
| ScmNil -> []
| sexpr ->  []

let rec scm_is_list = function
| ScmPair (hd, tl) -> scm_is_list tl
| ScmNil -> true
| _ -> false

let rec scm_list_length = function
| ScmPair (hd, tl) -> 1 + (scm_list_length tl)
| ScmNil -> 0
| sexpr -> 0



let rec untag expr =
let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

let untag_lambda_opt vars var body =
let vars = match vars with
| [] -> ScmSymbol var
| _ -> list_to_improper_list (untag_vars (vars@[var])) in
list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in

match expr with
| (ScmConst (ScmSymbol(_) as sexpr)
    | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
| ScmConst s -> s
| ScmVar (name) -> ScmSymbol(name)
| ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
| ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
| ScmSeq(exprs) -> untag_tagged_list "begin" exprs
| ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
| ScmDef (var, value) -> untag_tagged_list "define" [var; value]
| ScmOr (exprs) -> untag_tagged_list "or" exprs
| ScmLambdaSimple (vars, ScmSeq(body)) ->
    let vars = list_to_proper_list (untag_vars vars) in
    let body = List.map untag body in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
| ScmLambdaSimple (vars, body) ->
    let vars = list_to_proper_list (untag_vars vars) in
    list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
| ScmLambdaOpt (vars, var, ScmSeq(body)) ->
    let body = List.map untag body in
    untag_lambda_opt vars var body
| ScmLambdaOpt (vars, var, body) ->
    let body = [untag body] in
    untag_lambda_opt vars var body
| ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;


let rec string_of_expr expr =
string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
match n1, n2 with
| ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
        numerator1 = numerator2 && denominator1 = denominator2
| ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
| _, _ -> false

let rec sexpr_eq s1 s2 =
match s1, s2 with
| (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
| ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
| ScmChar(char1), ScmChar(char2) -> char1 = char2
| ScmString(string1), ScmString(string2) -> String.equal string1 string2
| ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
| ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
| ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
| ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
| _, _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
  | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
  | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                            (expr_eq dit1 dit2) &&
                                              (expr_eq dif1 dif2)
  | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
        List.for_all2 expr_eq exprs1 exprs2
  | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
        (expr_eq var1 var2) && (expr_eq val1 val2)
  | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
     (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
  | _ -> false;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
end;; 

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;

let rec tag_parse_expression sexpr =

let sexpr = macro_expand sexpr in
match sexpr with 
(*first 6 matches are for ScmConst
7 ScmVar
8-9 ScmIf
10-12 ScmOr
13 lambda*)
| ScmNil -> ScmConst ScmVoid 
| ScmVoid -> ScmConst sexpr
| ScmBoolean(_) -> ScmConst sexpr
| ScmChar(_) -> ScmConst sexpr
| ScmNumber(_) -> ScmConst sexpr
| ScmString (_) -> ScmConst sexpr
| ScmVector (_) -> ScmConst sexpr
| ((ScmPair (ScmSymbol "quote", (ScmPair (x, ScmNil))))) -> ScmConst x
| ScmSymbol (str) -> (*if (List.mem str reserved_word_list)
                     then raise (X_syntax_error (sexpr, "X_reserved_word"))                                                                                
                     else*) ScmVar str  
| (ScmPair (ScmSymbol "if" ,ScmPair (test, ScmPair (dit, ScmPair (dif, ScmNil)))))-> ScmIf((tag_parse_expression test) ,(tag_parse_expression dit),  (tag_parse_expression dif)) 
| (ScmPair (ScmSymbol "if", ScmPair (test, ScmPair (dit, ScmNil)))) -> ScmIf ((tag_parse_expression test) ,(tag_parse_expression dit), (tag_parse_expression ScmVoid)) 
| (ScmPair (ScmSymbol "or", ScmNil)) -> ScmConst (ScmBoolean false)
| (ScmPair (ScmSymbol "or", ScmPair (x, ScmNil))) -> (tag_parse_expression x)
| (ScmPair (ScmSymbol "or", x)) -> ScmOr(make_args_list x)
| ScmPair (ScmSymbol "lambda", ScmPair(args, body)) ->  make_lambda args body
| ScmPair (ScmSymbol "define",ScmPair(ScmSymbol(vall),ScmPair(var,ScmNil))) -> ScmDef(ScmVar vall,tag_parse_expression var) (*normal define*)
| ScmPair (ScmSymbol "define" ,ScmPair(ScmPair(ScmSymbol(vall),args),body)) -> ScmDef(ScmVar vall, (make_lambda args body))
| ScmPair (ScmSymbol "set!", ScmPair(ScmSymbol(var),ScmPair(vall,ScmNil))) -> ScmSet(ScmVar (var),tag_parse_expression vall)
| ScmPair (ScmSymbol "begin", ScmPair(x,ScmNil)) -> tag_parse_expression x
| ScmPair (ScmSymbol "begin", rest) -> ScmSeq (make_args_list rest)
| ScmPair (a,b) -> (ScmApplic (tag_parse_expression a, make_args_list b))


and macro_expand sexpr =
match sexpr with
| ScmPair (ScmSymbol "cond", rest) -> expand_cond rest
| ScmPair (ScmSymbol "and", rest) -> expand_and rest
| ScmPair (ScmSymbol "let", rest) -> expand_let rest
| ScmPair (ScmSymbol "let*", rest) -> expand_let_star rest
| ScmPair (ScmSymbol "letrec" ,rest) -> expand_letrec rest
| ScmPair (ScmSymbol "quasiquote", ScmPair(rest,ScmNil)) -> expand_quasi rest
| _ -> sexpr




and pair_to_car sexpr = 
match sexpr with
|ScmPair(car,_) -> car
|_ -> ScmNil

and pair_to_cdr sexpr = 
match sexpr with
|ScmPair(_,cdr) -> cdr
|_ -> ScmNil


and reduce_pair = function
|ScmPair(x,ScmNil) -> x
|_ ->ScmNil


and help_for_let_v ribs = 
match ribs with
|ScmPair(ScmPair(v_n,_),rest_ribs) -> v_n::help_for_let_v rest_ribs
| _ -> []


and help_for_let_exprs ribs =
match ribs with
|ScmPair(ScmPair(_,expr_n),rest_ribs) -> expr_n :: help_for_let_exprs rest_ribs
|_ -> []


and expand_let sexpr = 
    match sexpr with
    | ScmPair (ribs,body) -> 
        if (sexpr_eq body ScmNil)
        then ScmPair(ScmPair(ScmSymbol "lambda", ScmPair(list_to_proper_list (help_for_let_v ribs), body)),ScmNil)                                                                               
        else ScmPair(ScmPair(ScmSymbol "lambda", ScmPair(list_to_proper_list (help_for_let_v ribs), body)),list_to_proper_list (List.map reduce_pair (help_for_let_exprs ribs))) 
    | _ -> ScmNil

    
and expand_let_star sexpr =
match sexpr with
| ScmPair(ScmNil, body) -> expand_let sexpr
| ScmPair(ScmPair(rib, ScmNil), body) ->  expand_let sexpr
| ScmPair(ScmPair(rib1, rest_ribs), body) ->
    expand_let (ScmPair(ScmPair(rib1, ScmNil), ScmPair(expand_let_star (ScmPair(rest_ribs, body)),ScmNil)))
| _ ->  ScmNil


and expand_quasi sexpr = 
    match sexpr with
    | ScmSymbol(symbol) -> ScmPair(ScmSymbol("quote"), sexpr)
    | ScmPair(ScmSymbol("unquote-splicing"), _) -> ScmPair (ScmSymbol ("quote"), sexpr)

    | ScmPair(a,b) -> (match a with
        | ScmPair(ScmSymbol("unquote-splicing"), ScmPair(sexpr, ScmNil)) ->
            ScmPair(ScmSymbol("append"),ScmPair(sexpr, expand_quasi b))
        | _ -> ScmPair(ScmSymbol("cons"), ScmPair(expand_quasi a, expand_quasi b)))
    | _ -> sexpr
(* 
    | ScmPair(ScmPair(ScmSymbol "unquote", ScmPair(exp, ScmNil)), ScmNil) -> 
        Printf.printf "=== quasi , ===: %s\n" (string_of_sexpr exp); 
        exp
    | ScmPair(ScmPair(ScmSymbol "unquote-splicing", ScmPair(exp, ScmNil)), ScmNil) ->
        Printf.printf "=== quasi ,@ ===: %s\n" (string_of_sexpr exp); 
        ScmPair (ScmSymbol "quote", ScmPair(pair_to_car sexpr, ScmNil))
    (* | ScmPair(ScmVector(sexpr_list), ScmNil) ->  *)
    | ScmPair(exp, ScmNil) -> 
        Printf.printf "=== quasi symbol ===: %s\n" (string_of_sexpr exp); 
        ScmPair (ScmSymbol "quote", sexpr)
    | ScmPair(exp1, exp2) ->
        Printf.printf "=== quasi pair ===\n"; 
        match exp1, exp2 with
        | ScmPair(ScmSymbol "unquote-splicing", ScmPair(exp, ScmNil)), _ ->
            ScmPair(ScmSymbol("append"), ScmPair(exp, ScmPair(expand_quasi exp2, ScmNil)))
        | _ -> ScmPair(ScmSymbol("cons"), ScmPair(expand_quasi exp1, ScmPair(expand_quasi exp2, ScmNil))) *)


and expand_letrec sexpr = 
match sexpr with
|ScmPair(ScmNil,rest) -> expand_let (ScmPair(ScmNil,rest))
| ScmPair(ribs,body) ->
    let all_f_values = help_for_let_v ribs in       (* get symbols list of the bindings of letrec *)
    let all_exprs_values = help_for_let_exprs ribs in       (* get expression list of the bindings of letrec *)
    let all_f_values_After_whatever = list_to_proper_list (add_whatever all_f_values) in (* create proper list of ((f1 'whatever) (f2 'whatever) ... ) *)
    let all_set_values = List.map2 add_set all_f_values all_exprs_values in
    let body = reduce_pair body in 
    (* let empty_let = ScmPair(ScmSymbol "let", ScmPair(ScmNil, body)) in *)
    let new_let_body = list_to_proper_list (all_set_values@[body]) in
    let final_let = ScmPair(ScmSymbol "let", ScmPair(all_f_values_After_whatever, new_let_body)) in
    macro_expand final_let
| _ -> raise X_worng

and add_whatever lst = List.map (fun f -> ScmPair(f, ScmPair(ScmPair(ScmSymbol("quote"), ScmPair(ScmSymbol("whatever"), ScmNil)), ScmNil))) lst

and add_set f_value expr_value = ScmPair (ScmSymbol "set!", ScmPair(f_value, expr_value))

and expand_cond rest =
match rest with
|ScmPair(ScmPair(ScmSymbol("else"), rest),_) ->  ScmPair(ScmSymbol("begin"), rest)
|ScmPair(ScmPair(test, ScmPair(ScmSymbol "=>", ScmPair(expr_f, ScmNil))), rest_ribs) ->
    let rest = expand_cond rest_ribs in
    let expaned = 
            ScmPair
            (ScmSymbol "let",
            ScmPair
            (ScmPair
                (ScmPair (ScmSymbol "value", ScmPair(test, ScmNil)),
                ScmPair
                (ScmPair
                    (ScmSymbol "f",
                    ScmPair
                    (ScmPair
                        (ScmSymbol "lambda",
                        ScmPair (ScmNil, ScmPair (expr_f, ScmNil))),
                    ScmNil)),
                ScmPair
                    (ScmPair
                    (ScmSymbol "rest",
                    ScmPair
                        (ScmPair
                        (ScmSymbol "lambda",
                        ScmPair (ScmNil, ScmPair (rest, ScmNil))),
                        ScmNil)),
                    ScmNil))),
            ScmPair
                (ScmPair
                (ScmSymbol "if",
                ScmPair
                    (ScmSymbol "value",
                    ScmPair
                    (ScmPair
                        (ScmPair (ScmSymbol "f", ScmNil),
                        ScmPair (ScmSymbol "value", ScmNil)),
                    ScmPair (ScmPair (ScmSymbol "rest", ScmNil), ScmNil)))),
                ScmNil))) in
    macro_expand expaned
    |ScmPair(ScmPair(test, body), rest_ribs) ->
        ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(ScmPair(ScmSymbol("begin"), body),ScmPair(expand_cond rest_ribs,ScmNil))))                                                               
    | ScmNil -> ScmNil
    | ScmPair(x,ScmNil) -> x
    | _ -> raise (X_syntax_error (rest, "not recognized"))

and expand_and sexpr =
match sexpr with
|ScmNil -> ScmBoolean true
|ScmPair (car,ScmNil) -> car
|ScmPair (car , cdr) -> ScmPair(ScmSymbol("if"), ScmPair(car, ScmPair((expand_and cdr), ScmPair (ScmBoolean(false), ScmNil)))) 
| _ -> ScmNil

and make_args_list sexpr = List.map tag_parse_expression (scm_list_to_list sexpr)

and create_simple_lambda args body = 
    match (scm_list_length body) with
    |1 ->  ScmLambdaSimple(List.map remove_scm_symbol (scm_list_to_list args), 
                            tag_parse_expression (remove_list (scm_list_to_list body)))
    |_ ->  ScmLambdaSimple(List.map remove_scm_symbol (scm_list_to_list args),
                        ScmSeq (List.map tag_parse_expression (scm_list_to_list body)))

and create_args_list = function
    |ScmSymbol(str) -> ([], (str))
    |ScmPair(ScmSymbol(car), ScmSymbol(cdr)) -> ([car], (cdr))
    |ScmPair(ScmSymbol(car), cdr) -> 
        let (mst, rst) = 
        create_args_list cdr in (car :: mst, rst)
    |_ -> (["lalalalalala"],"lalala")    


and create_optional_lambda args body =
   let args_list = create_args_list args in
   let must = fst args_list in
   let rest = snd args_list in
   match body with
   |ScmPair(_ ,ScmPair _ ) -> ScmLambdaOpt (must,rest,ScmSeq 
                            (List.map 
                            tag_parse_expression
                            (scm_list_to_list body)))
   |_ -> ScmLambdaOpt (must,rest, 
                            tag_parse_expression (remove_list (scm_list_to_list body)))

and create_variadic_lambda args body = 
    let str = match args with
        |ScmSymbol (str) -> str
        |_ -> "lalalala"
    in match body with
   |ScmPair(_ ,ScmPair _ ) -> ScmLambdaOpt ([],str,ScmSeq 
                            (List.map 
                            tag_parse_expression
                            (scm_list_to_list body)))
   |_ -> ScmLambdaOpt ([],str, 
                            tag_parse_expression (remove_list (scm_list_to_list body)))

and make_lambda args body = 
    match (proper_or_improper args) with
    | true -> create_simple_lambda args body    
    | false -> match args with
        | ScmSymbol (_) -> create_variadic_lambda args body
        | _ -> create_optional_lambda args body


end;;
