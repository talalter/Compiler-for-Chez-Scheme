(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)

 #use "tag-parser.ml";;

 exception X_not_yet_implemented;;
 exception X_this_should_not_happen;;
 exception X_syntax_error of expr * string;;

 type var' = 
   | VarFree of string
   | VarParam of string * int
   | VarBound of string * int * int;;
 
 type expr' =
   | ScmConst' of sexpr
   | ScmVar' of var'
   | ScmBox' of var'
   | ScmBoxGet' of var'
   | ScmBoxSet' of var' * expr'
   | ScmIf' of expr' * expr' * expr'
   | ScmSeq' of expr' list
   | ScmSet' of var' * expr'
   | ScmDef' of var' * expr'
   | ScmOr' of expr' list
   | ScmLambdaSimple' of string list * expr'
   | ScmLambdaOpt' of string list * string * expr'
   | ScmApplic' of expr' * (expr' list)
   | ScmApplicTP' of expr' * (expr' list);;
 

 let list_remove_last_element = function
 | [] -> []
 | lst -> List.rev (List.tl (List.rev lst));;
 
 
 let var_eq v1 v2 =
 match v1, v2 with
   | VarFree (name1), VarFree (name2) -> String.equal name1 name2
   | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
     major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
   | VarParam (name1, index1), VarParam (name2, index2) ->
        index1 = index2 && (String.equal name1 name2)
   | _ -> false
 
 let rec expr'_eq e1 e2 =
   match e1, e2 with
   | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
   | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
   | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) -> (expr'_eq test1 test2) &&
                                             (expr'_eq dit1 dit2) &&
                                               (expr'_eq dif1 dif2)
   | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
         List.for_all2 expr'_eq exprs1 exprs2
   | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
         (var_eq var1 var2) && (expr'_eq val1 val2)
   | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
      (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
   | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
      (String.equal var1 var2) &&
        (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
   | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
      (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
   | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
       (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
   | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
   | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
   | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
   | _ -> false;;
 
 
 module type SEMANTIC_ANALYSIS = sig
   val annotate_lexical_addresses : expr -> expr'
   val annotate_tail_calls : expr' -> expr'
   val box_set : expr' -> expr'
   val run_semantics : expr -> expr'
   
 end;; (* end of module type SEMANTIC_ANALYSIS *)
 
 module Semantic_Analysis : SEMANTIC_ANALYSIS = struct
 
 (* # lookup_in_rib 3 [1;2;3;4;5];; 
         - : int option = Some 2   *)
   let rec lookup_in_rib name = function
     | [] -> None
     | name' :: rib ->
        if name = name'
        then Some(0)
        else (match (lookup_in_rib name rib) with
              | None -> None
              | Some minor -> Some (minor + 1));;
 
 (* # lookup_in_env 2 [[1;2];[3;4]];;
       - : (int * int) option = Some (0, 1)      *)
   let rec lookup_in_env name = function
     | [] -> None
     | rib :: env ->
        (match (lookup_in_rib name rib) with
         | None ->
            (match (lookup_in_env name env) with
             | None -> None
             | Some(major, minor) -> Some(major + 1, minor))
         | Some minor -> Some(0, minor));;
 

   let tag_lexical_address_for_var name params env = 
    match (lookup_in_rib name params) with
    | None ->
      (match (lookup_in_env name env) with
        | None -> VarFree name
        | Some(major, minor) -> VarBound(name, major, minor))
    | Some minor -> VarParam(name, minor);;
 
  (* run this first! *)
 
  
   let annotate_lexical_addresses pe =       
     let rec run pe params env =
       match pe with
       | ScmConst (var) ->  ScmConst' (var)
       | ScmVar (var) ->  ScmVar' (tag_lexical_address_for_var var params env)
       | ScmIf (test, do_if_true, do_if_false) -> 
           ScmIf' ((run test params env),
                   (run do_if_true params env),
                   (run do_if_false params env))
       | ScmSeq (lst) -> ScmSeq' (List.map (fun e -> (run e params env)) lst)
       | ScmOr (lst) -> ScmOr' (List.map (fun e -> (run e params env)) lst)
       | ScmDef (var, value) -> ScmDef' ((tag_lexical_address_for_var (string_of_expr var) params env),
                                        (run value params env))
       | ScmSet (var, value) ->  ScmSet' ((tag_lexical_address_for_var (string_of_expr var) params env),
                                        (run value params env))
       | ScmApplic (app, args) ->  ScmApplic' (run app params env, (List.map (fun e -> (run e params env)) args))                                     
       | ScmLambdaSimple (lambda_params, lambda_body) -> 
           ScmLambdaSimple' (lambda_params,
                            (run lambda_body lambda_params (params::env)))
       | ScmLambdaOpt (lambda_params, opt, body) -> ScmLambdaOpt' (lambda_params, opt,
                                                   (run body (lambda_params@[opt]) ((params@[opt])::env)))
       (*| _ -> raise (X_syntax_error (pe, "Not implemented yet"))*)
     in 
     run pe [] [];;
 
   let rec rdc_rac s =
     match s with
     | [e] -> ([], e)
     | e :: s ->
        let (rdc, rac) = rdc_rac s
        in (e :: rdc, rac)
     | _ -> raise X_this_should_not_happen;;
   
 
   
 
 
   (* run this second! *)
    let annotate_tail_calls pe =
     let rec run pe in_tail =
       match pe with
        | ScmConst'(var) -> pe
        | ScmVar'(var) -> pe
        | ScmIf'(test, do_if_true, do_if_false) ->  ScmIf' ((run test false),
                                                           (run do_if_true in_tail),
                                                           (run do_if_false in_tail))
        | ScmLambdaSimple'(lambda_params, lambda_body) -> 
           ScmLambdaSimple'(lambda_params, run lambda_body true)
        | ScmLambdaOpt'(lambda_params, opt_params, lambda_body)->
           ScmLambdaOpt'(lambda_params, opt_params, run lambda_body true)
        | ScmApplic'(app, args) -> 
           if (in_tail)
           then (ScmApplicTP'((run app false, 
                            List.map (fun x -> run x false) args)))
           else (ScmApplic'((run app false, 
                            List.map (fun x -> run x false) args)))
        | ScmSet' (var, value) ->  ScmSet'(var, run value false)
        | ScmDef' (var, value) ->  ScmDef' (var, run value false)
        | ScmSeq' (lst) ->  (help_for_exprs_tag_list_seq lst in_tail)
        | ScmOr' (lst) ->  (help_for_exprs_tag_list_or lst in_tail)
        | _ -> raise X_this_should_not_happen 
 
     and help_for_exprs_tag_list_seq lst in_tail =  
     if (in_tail)
     then 
       let (_, last) = rdc_rac lst in
       let last = (run last in_tail) in
       let rest = (List.map (fun exp -> (run exp false)) (list_remove_last_element lst)) in
       ScmSeq'(rest@[last])
     else
       let seq_list = (List.map (fun exp -> (run exp in_tail)) lst) in
       ScmSeq'(seq_list)

     and help_for_exprs_tag_list_or lst in_tail =  
     if (in_tail)
     then 
       let (_, last) = rdc_rac lst in
       let last = (run last in_tail) in
       let rest = (List.map (fun exp -> (run exp false)) (list_remove_last_element lst)) in
       ScmOr'(rest@[last])
     else
       let seq_list = (List.map (fun exp -> (run exp in_tail)) lst) in
       ScmOr'(seq_list)  
 
     in 
     run pe false;;
 


   (* ================== *)
   (* ===== Boxing ===== *)
   (* ================== *)



   (* ref int -> unit()  *)
   let update_ref deep_index = deep_index:=!deep_index + 1 
   let keep_ref deep_index =  deep_index:=!deep_index


   (** string * expr' * int list * int * ref int -> int list' *)
   let rec find_reads param body acc index latest_index =
    match body with
    | ScmConst' (_) ->  acc
    | ScmVar' (VarFree(_)) -> acc
    | ScmVar' (VarParam(name,_)) ->  if name = param
                                    then  [index] @ acc
                                    else acc
    | ScmVar' (VarBound(name, _,_)) ->  if name = param
                                      then [index] @ acc
                                      else acc
    | ScmIf' (test, dit, dif) -> acc @ (find_reads param test [] index latest_index) @ (find_reads param dit [] index latest_index) @ (find_reads param dif [] index latest_index )
    | ScmSeq' (lst) ->  acc @ List.flatten (List.map (fun expr -> find_reads param expr [] index latest_index) lst)
    | ScmOr' (lst) ->  acc @ List.flatten (List.map (fun expr -> find_reads param expr [] index latest_index) lst)
    | ScmDef' (var, value) ->  acc @ find_reads param value [] index latest_index
    | ScmSet' (var, value) ->  acc @ find_reads param value [] index latest_index
    | ScmApplic' (app, lst) ->  acc @ List.flatten (List.map (fun expr -> find_reads param expr [] index latest_index) (app::lst))
    | ScmApplicTP' (app, lst) ->   acc @ List.flatten (List.map (fun expr -> find_reads param expr [] index latest_index) (app::lst))
    | ScmLambdaSimple' (params, body) ->  if (List.mem param params)
                                         then acc
                                         else acc @ (find_reads param body [] (if (index = 0)
                                                                               then (update_ref latest_index; !latest_index)
                                                                               else index)
                                                                               latest_index)
    | ScmLambdaOpt' (params,opt, body) -> if (List.mem param (params@[opt]))
                                          then acc
                                          else acc @ (find_reads param body [] (if (index = 0)
                                                                               then (update_ref latest_index; !latest_index)
                                                                               else index) latest_index)
    | _ -> raise X_this_should_not_happen


   (** string * expr' * int list * int * ref int -> int list' *)
   let rec find_writes param body acc index latest_index = 
      match body with
      | ScmConst' (_) ->  acc
      | ScmVar' (_) ->  acc
      | ScmIf' (test, dit, dif) ->  acc @ (find_writes param dit [] index latest_index) @ (find_writes param dit [] index latest_index) @ (find_reads param dif [] index latest_index )
      | ScmSeq' (lst) ->  acc @ List.flatten (List.map (fun expr -> find_writes param expr [] index latest_index) lst)
      | ScmOr' (lst) ->  acc @ List.flatten (List.map (fun expr -> find_writes param expr [] index latest_index) lst)
      | ScmDef' (var, value) ->  acc @ find_writes param value [] index latest_index
      | ScmSet' (VarFree(name),_) ->  if name = param
                                     then [index] @ acc
                                     else acc
      | ScmSet' (VarParam(name,_),_) ->   if name = param
                                          then  [index] @ acc
                                          else acc
      | ScmSet' (VarBound(name,_,_),_) ->   if name = param
                                            then  [index] @ acc
                                            else acc
      | ScmApplic' (app, lst) ->  acc @ List.flatten (List.map (fun expr -> find_writes param expr [] index latest_index) (app::lst))
      | ScmApplicTP' (app, lst) ->  acc @ List.flatten (List.map (fun expr -> find_writes param expr [] index latest_index) (app::lst))
      | ScmLambdaSimple' (params, body) ->  if (List.mem param params)
                                            then acc
                                            else acc @ (find_writes param body [] (if (index = 0)
                                                                                  then (update_ref latest_index; !latest_index)
                                                                                  else index) latest_index)
      | ScmLambdaOpt' (params,opt, body) -> if (List.mem param (params@[opt]))
                                            then acc
                                            else acc @ (find_writes param body [] (if (index = 0)
                                                                                   then (update_ref latest_index; !latest_index)
                                                                                   else index) latest_index)
      | _ -> raise X_this_should_not_happen


      (** int list -> int list *)
    let rec remove_duplicates  = function
      | [] -> []
      | h::t -> if (List.mem h t)
                then remove_duplicates t
                else h::remove_duplicates t



    (** int list * int list -> bool *)
    let rec decide_should_box reads writes =
      if (List.length reads = 0 || List.length writes = 0)
      then false
      else if (List.length reads = 1 && reads=writes)
           then false
           else true



    (** string * expr' -> bool *)
    let should_box param body = 
      let index_deep_write = ref 0 in
      let index_deep_read = ref 0 in
      let writes = List.rev (remove_duplicates (find_writes param body [] 0 index_deep_write)) in
      let reads = List.rev (remove_duplicates (  find_reads param body [] 0 index_deep_read)) in
      decide_should_box reads writes   

    (** string -> expr' -> expr' *)
    let rec add_box_sets_and_gets param expr = 
      match expr with
      | ScmConst' (_) -> expr
      | ScmVar' (VarFree (_)) -> expr
      | ScmVar' (VarParam(name,minor)) -> if name = param
                                          then ScmBoxGet' (VarParam(name,minor))
                                          else expr
      | ScmVar' (VarBound(name, major,minor)) -> if name = param
                                                 then ScmBoxGet' (VarBound(name, major,minor))
                                                 else expr
      | ScmSet' (VarFree(name) ,value) -> expr
      | ScmSet' (VarParam(name,minor),value) -> if name = param
                                                then ScmBoxSet' ((VarParam(name,minor), add_box_sets_and_gets param value))
                                                else expr
      | ScmSet' (VarBound(name,major,minor),value) -> if name = param
                                                      then ScmBoxSet'((VarBound(name,major,minor),add_box_sets_and_gets param value))
                                                      else expr
      | ScmIf' (test,dit,dif) -> ScmIf' (add_box_sets_and_gets param test, add_box_sets_and_gets param dit, add_box_sets_and_gets param dif)
      | ScmSeq' (lst) -> ScmSeq'(List.map (fun expr -> (add_box_sets_and_gets param expr)) lst)
      | ScmOr' (lst) -> ScmOr' (List.map (fun expr -> (add_box_sets_and_gets param expr)) lst)
      | ScmDef' (var,value) -> ScmDef'(var, add_box_sets_and_gets param value)
      | ScmApplic'(app,args) -> ScmApplic'(add_box_sets_and_gets param app, List.map (fun expr -> (add_box_sets_and_gets param expr)) args)
      | ScmApplicTP'(app,args) -> ScmApplicTP'(add_box_sets_and_gets param app, List.map (fun expr -> (add_box_sets_and_gets param expr)) args)
      | ScmLambdaSimple'(params,body) -> if (List.mem param params)
                                         then expr 
                                         else ScmLambdaSimple'(params, add_box_sets_and_gets param body)
      | ScmLambdaOpt'(params,opt,body) -> if (List.mem param (params@[opt]))
                                          then expr
                                          else ScmLambdaOpt'(params,opt, add_box_sets_and_gets param body)
      | _ -> raise X_this_should_not_happen
                                       
 

    (** (string * int) list -> expr' list *)
    let rec generate_expr_list boxed_params =
      match boxed_params with
      | [] -> []
      | h::t -> let param = fst h in
                let index = snd h in
                [ScmSet'(VarParam (param, index), ScmBox'(VarParam(param, index)))] @ generate_expr_list t 


    (**expr' list * expr' -> ScmSeq' *)
    let add_scm_seq lst body = match body with
    | ScmSeq'(body) -> ScmSeq' (lst@body) 
    | _ -> body 


    (** string * string list * int -> int*)
    let rec check_index_of_param param lambda_params counter = 
      match lambda_params with
        | [] -> counter
        | hd::tl -> if param = hd
                    then counter
                    else check_index_of_param param tl counter+1


    (**string list * string list -> (string*int) list*)
    let rec generate_tuples_of_param_and_index lambda_params boxed_params = 
      match boxed_params with
        | [] -> []
        | h::t -> let index_of_param = check_index_of_param h lambda_params 0 in
                  let param_with_his_index = (h, index_of_param) in
                  param_with_his_index :: generate_tuples_of_param_and_index lambda_params t

    

    (** ScmVar' -> string *)
    let get_name_of_var var =
      match var with
      | ScmVar' (VarFree(var)) -> var
      | ScmVar' (VarParam(var,_)) -> var
      | ScmVar' (VarBound(var,_,_)) -> var
      | _ -> raise X_this_should_not_happen


         

    let rec box_set expr = 
      match expr with
        | ScmConst' (_) -> expr
        | ScmVar' (_) ->  expr
        | ScmSet' (var,value) ->  ScmSet'(var, box_set value)
        | ScmIf' (test,dit,dif) ->  ScmIf' (box_set test, box_set dit, box_set dif)
        | ScmSeq' (lst) ->  ScmSeq'(List.map (fun expr -> (box_set expr)) lst)
        | ScmOr' (lst) ->  ScmOr' (List.map (fun expr -> (box_set expr)) lst)
        | ScmDef' (var,value) ->  ScmDef'(var, box_set value)
        | ScmApplic'(app,args) ->  ScmApplic'(box_set app, List.map (fun expr -> (box_set  expr)) args)
        | ScmApplicTP'(app,args) ->  ScmApplicTP'(box_set  app, List.map (fun expr -> (box_set  expr)) args)
        | ScmLambdaSimple'(params,body) -> 
          let params_to_box = List.filter (fun param -> should_box param body) params in
          let box_params = (List.fold_left 
                            (fun expr param -> add_box_sets_and_gets param expr)
                            (box_set body)
                            params_to_box) in 
          let add_to_lambda_body = generate_expr_list (generate_tuples_of_param_and_index params params_to_box) in
          let add_to_lambda_body = add_scm_seq add_to_lambda_body box_params in  
          ScmLambdaSimple'(params, add_to_lambda_body)
        | ScmLambdaOpt'(params,opt,body) -> 
          let params_to_box = List.filter (fun param -> should_box param body) (params@[opt]) in
          let box_params = (List.fold_left 
                            (fun expr param -> add_box_sets_and_gets param expr)
                            body
                            params_to_box) in 
          let add_to_lambda_body = generate_expr_list (generate_tuples_of_param_and_index params params_to_box) in
          let add_to_lambda_body = add_scm_seq add_to_lambda_body box_params in  
          ScmLambdaOpt'(params,opt, add_to_lambda_body)
        | _ -> expr


    let run_semantics expr =
     box_set
       (annotate_tail_calls
          (annotate_lexical_addresses expr))
 
 end;; (*end of module Semantic_Analysis*)











