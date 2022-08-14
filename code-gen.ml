#use "semantic-analyser.ml";;
exception X_syntax_error of expr' * string;;
exception X_worng_label;;
(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (sexpr * (int * string)) list
  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (sexpr * (int * string)) list -> (string * int) list -> expr' -> string
end;;


module Code_Gen : CODE_GEN = struct

(** make_consts_tbl: *)

  let library_functions = 
    ["*"; "+"; "-"; "/"; "<"; "="; ">";
    "append"; "apply"; "boolean?"; "car"; "cdr"; "char->integer"; "char?"; "cons"; "cons*"; "denominator"; 
    "eq?"; "equal?"; "exact->inexact"; "flonum?"; "fold-left"; "fold-right"; "gcd"; "integer?"; "integer->char"; 
    "length"; "list"; "list?"; "make-string"; "map"; 
    "not"; "null?"; "number?"; "numerator"; "pair?"; "procedure?"; "rational?"; 
    "set-car!"; "set-cdr!"; "string->list"; "string-length"; "string-ref"; "string-set!"; "string?"; 
    "symbol?"; "symbol->string"; "zero?"]

  let update_ref deep_index how_much= deep_index:=!deep_index + how_much 

  let rec find_free_vars_in_expr expr free_var_list = 
  match expr with
    | ScmConst' (_) ->  free_var_list
    | ScmVar' (VarFree(name)) ->  [name]
    | ScmVar' (VarParam(_,_)) -> free_var_list
    | ScmVar' (VarBound(_, _,_)) -> free_var_list
    | ScmBox'(_) -> free_var_list
    | ScmBoxGet' (_) -> free_var_list
    | ScmBoxSet' (_,expr) -> free_var_list @ find_free_vars_in_expr expr []
    | ScmIf' (test, dit, dif) ->
         free_var_list @ (find_free_vars_in_expr test []) @ (find_free_vars_in_expr dit []) @ (find_free_vars_in_expr dif [])
    | ScmSeq' (lst) -> free_var_list @ List.flatten (List.map (fun expr -> find_free_vars_in_expr expr [] ) lst)
    | ScmOr' (lst) -> free_var_list @ List.flatten (List.map (fun expr -> find_free_vars_in_expr expr []) lst)
    | ScmDef' (VarFree(var), value) -> [var] @ free_var_list @ find_free_vars_in_expr value []
    | ScmSet' (var, value) -> free_var_list @ find_free_vars_in_expr value []
    | ScmApplic' (app, lst) -> free_var_list @ List.flatten (List.map (fun expr -> find_free_vars_in_expr expr []) (app::lst))
    | ScmApplicTP' (app, lst) ->  free_var_list @ List.flatten (List.map (fun expr -> find_free_vars_in_expr expr []) (app::lst))
    | ScmLambdaSimple' (params, body) -> free_var_list @ find_free_vars_in_expr body []
    | ScmLambdaOpt' (params,opt, body) -> free_var_list @ find_free_vars_in_expr body []
    | _ -> raise X_this_should_not_happen

  let rec run_on_list_to_search_for_free_vars_in_expr exprs_tag_list = match exprs_tag_list with
  | [] -> []
  | hd::tl -> let search_for_free_vars_in_expr = find_free_vars_in_expr hd [] in
              search_for_free_vars_in_expr @ run_on_list_to_search_for_free_vars_in_expr tl


  let add_offset_to_lst lst counter = 
     List.map (fun x -> update_ref counter 1; (x , !counter)) lst



   (** int list -> int list *)
  let rec remove_duplicates old_lst new_list =
  match old_lst with
    | [] -> new_list 
    | hd::tl -> if (List.mem hd new_list)
                then remove_duplicates tl new_list
                else remove_duplicates tl (new_list@[hd])


  let flow_to_generate_fvars_table asts =
     let free_vars_table = run_on_list_to_search_for_free_vars_in_expr asts in 
     let free_vars_table = library_functions@free_vars_table in 
     let free_vars_table = (remove_duplicates free_vars_table []) in
     let counter = ref (-1) in 
     add_offset_to_lst free_vars_table counter



 



  let rec expand_const_table sexpr  = match sexpr with
    | ScmVoid -> [sexpr]
    | ScmNil ->  [sexpr]
    | ScmBoolean(_) -> [sexpr]
    | ScmChar(_) -> [sexpr]
    | ScmString(_) -> [sexpr]
    | ScmNumber(_) ->  [sexpr]
    | ScmSymbol(str) ->  [ScmString(str)] @ [sexpr]
    | ScmVector(lst) ->  List.flatten (List.map (fun x-> expand_const_table x ) lst) @ [sexpr]
    | ScmPair(sexpr1 , sexpr2) -> (expand_const_table sexpr1 ) @ (expand_const_table sexpr2 ) @ [sexpr]



  let rec find_const_vars_in_expr expr' const_var_list = 
  match expr' with
    | ScmConst' (sexpr) ->  expand_const_table sexpr 
    | ScmVar' (_) ->  const_var_list 
    | ScmBox'(_) -> const_var_list 
    | ScmBoxGet' (_) ->  const_var_list 
    | ScmBoxSet' (_,expr) ->  const_var_list @ find_const_vars_in_expr expr []
    | ScmIf' (test, dit, dif) -> 
         const_var_list @ (find_const_vars_in_expr test []) @ (find_const_vars_in_expr dit []) @ (find_const_vars_in_expr dif [])
    | ScmSeq' (lst) ->  const_var_list @ List.flatten (List.map (fun expr -> find_const_vars_in_expr expr [] ) lst)
    | ScmOr' (lst) ->  const_var_list @ List.flatten (List.map (fun expr -> find_const_vars_in_expr expr []) lst)
    | ScmDef' (var, value) ->  const_var_list @ find_const_vars_in_expr value []
    | ScmSet' (var, value) ->  const_var_list @ find_const_vars_in_expr value []
    | ScmApplic' (app, lst) ->  const_var_list @ List.flatten (List.map (fun expr -> find_const_vars_in_expr expr []) (app::lst))
    | ScmApplicTP' (app, lst) ->   const_var_list @ List.flatten (List.map (fun expr -> find_const_vars_in_expr expr []) (app::lst))
    | ScmLambdaSimple' (params, body) ->  const_var_list @ find_const_vars_in_expr body []
    | ScmLambdaOpt' (params,opt, body) ->  const_var_list @ find_const_vars_in_expr body []

  
  let rec run_on_list_to_search_for_const_vars_in_expr exprs_tag_list = match exprs_tag_list with
  | [] -> []
  | hd::tl -> let search_for_const_vars_in_expr = find_const_vars_in_expr hd [] in
              search_for_const_vars_in_expr @ run_on_list_to_search_for_const_vars_in_expr tl


  let bytes_for_each_sexpr sexpr = match sexpr with

    | ScmVoid -> 1 
    | ScmNil -> 1 
    | ScmBoolean(_) -> 2 
    | ScmChar(_) -> 2
    | ScmString(str) -> 1 + 8 + String.length str
    | ScmNumber(ScmRational(_)) -> 1+8+8
    | ScmNumber(ScmReal(_)) -> 1+8
    | ScmSymbol(str) -> 1 + 8   
    | ScmVector(lst) -> 1 + 8 + (List.length lst) * 8
    | ScmPair(sexpr1 , sexpr2) ->  1+8+8  (*bytes_for_each_sexpr sexpr1 + bytes_for_each_sexpr sexpr2*)



  let rec search_for_offset sexpr table_of_sexpr_and_offset =
    match table_of_sexpr_and_offset with
    | [] -> (-1)
    | hd::tl -> match sexpr with
                |ScmSymbol(string) -> if (sexpr_eq (fst hd) (ScmString(string)))
                                      then (snd hd)
                                      else search_for_offset sexpr tl

                |_ -> if (sexpr_eq (fst hd) sexpr)
                      then (snd hd)
                      else search_for_offset sexpr tl


  let rec vector_handler lst sexpr_to_offset = 
    match lst with
    | [] -> ""
    | h::t -> "const_tbl+ " ^ (string_of_int(search_for_offset h sexpr_to_offset))^ " ," ^ (vector_handler t sexpr_to_offset)


  let match_assam_code_to_sexpr sexpr sexpr_to_offset= 

    match sexpr with
    | ScmVoid -> "db T_VOID" 
    | ScmNil ->  "db T_NIL"
    | ScmBoolean(false) -> "db T_BOOL, 0"
    | ScmBoolean(true) -> "db T_BOOL, 1"
    | ScmChar(x) ->  "MAKE_LITERAL_CHAR(" ^ (string_of_int(Char.code x)) ^")"
    | ScmString(str) -> Printf.sprintf "MAKE_LITERAL_STRING \""^ str ^"\"" 
    | ScmNumber(ScmRational(numerator,denomerator)) -> Printf.sprintf "MAKE_LITERAL_RATIONAL(%d, %d)" numerator denomerator
    | ScmNumber(ScmReal(num)) -> "MAKE_LITERAL_FLOAT(" ^ (string_of_float num) ^")"
    | ScmSymbol(str) -> Printf.sprintf "MAKE_LITERAL_SYMBOL(const_tbl+%d)" (search_for_offset sexpr sexpr_to_offset)
    | ScmPair(sexpr1 , sexpr2) -> "MAKE_LITERAL_PAIR(const_tbl+" ^ (string_of_int (search_for_offset sexpr1 sexpr_to_offset))^
                                  ", const_tbl+"^ (string_of_int(search_for_offset sexpr2 sexpr_to_offset))^")"

    | ScmVector(lst) -> "MAKE_LITERAL_VECTOR " ^ (vector_handler lst sexpr_to_offset)

  

  





  let rec run_on_list_to_find_assambly_code expr_list sexpr_and_offset=  
    match expr_list with
    | [] -> []
    | hd::tl -> match_assam_code_to_sexpr hd sexpr_and_offset:: run_on_list_to_find_assambly_code tl sexpr_and_offset 



  let rec run_on_list_to_find_offsets sexprs_list offset_counter =
      match sexprs_list with
      | [] -> []
      | hd::tl -> offset_counter :: run_on_list_to_find_offsets tl (offset_counter + bytes_for_each_sexpr hd)

  


  let flow_to_generate_constvars_table asts = 
    let const_var_table = run_on_list_to_search_for_const_vars_in_expr asts in
    let const_var_table = [ScmVoid;ScmNil;ScmBoolean(false);ScmBoolean(true)]@const_var_table in
    let const_var_table = remove_duplicates const_var_table [] in
    let offset_list = (run_on_list_to_find_offsets const_var_table 0) in 
    let sexpr_and_offset = List.combine const_var_table offset_list in 
    let assambly_list = run_on_list_to_find_assambly_code const_var_table sexpr_and_offset in 
    let offset_and_assambly = List.combine offset_list assambly_list in 
    List.combine const_var_table offset_and_assambly
    



  let make_consts_tbl asts = flow_to_generate_constvars_table asts
  let make_fvars_tbl asts = flow_to_generate_fvars_table asts



  let find_const_offset e consts =
    let ((_, (offset, _))) = 
      List.find
      (fun (sexpr, (offset, sob)) -> sexpr_eq e sexpr)
      consts in
    offset



  let if_counter = ref 0
  let or_counter = ref (-1)
  let lambda_simple_counter = ref (0)
  let lambda_opt_counter = ref (0)
  let applicTP_counter = ref (0)
  let applic_counter = ref (0)


  let make_label label_name =
    match label_name with
    | "Lexit_Or" -> update_ref or_counter 1;Printf.sprintf "Lexit_Or%d"  !or_counter
    
    | "Lelse_If" -> Printf.sprintf "Lelse_If%d" !if_counter
    | "Lexit_If" ->  Printf.sprintf "Lexit_If%d" !if_counter

    | "Lloop_LambdaSimple" -> Printf.sprintf "Lloop_LambdaSimple%d" !lambda_simple_counter
    | "Lcode_LambdaSimple" -> Printf.sprintf "Lcode_LambdaSimple%d" !lambda_simple_counter
    | "Lclosure_LambdaSimple" -> Printf.sprintf "Lclosure_LambdaSimple%d" !lambda_simple_counter
    | "Lcont_LambdaSimple" -> Printf.sprintf "Lcont_LambdaSimple%d" !lambda_simple_counter
    | "LcreateMinor_LambdaSimple" -> Printf.sprintf "LcreateMinor_LambdaSimple%d" !lambda_simple_counter

    | "Lloop_LambdaOpt" -> Printf.sprintf "Lloop_LambdaOpt%d" !lambda_opt_counter
    | "Lcode_LambdaOpt" -> Printf.sprintf "Lcode_LambdaOpt%d" !lambda_opt_counter
    | "Lclosure_LambdaOpt" -> Printf.sprintf "Lclosure_LambdaOpt%d" !lambda_opt_counter
    | "Lcont_LambdaOpt" -> Printf.sprintf "Lcont_LambdaOpt%d" !lambda_opt_counter
    | "LcreateMinor_LambdaOpt" -> Printf.sprintf "LcreateMinor_LambdaOpt%d" !lambda_opt_counter
    | "LfixStackLoop_LambdaOpt" -> Printf.sprintf "LfixStackLoop_LambdaOpt%d" !lambda_opt_counter
    | "LfixStackEnd_LambdaOpt" -> Printf.sprintf "LfixStackEnd_LambdaOpt%d" !lambda_opt_counter

    | "Lloop_ApplicTP" -> Printf.sprintf "Lloop_ApplicTP%d"  !applicTP_counter
    | "Lloop_end_ApplicTP" -> Printf.sprintf "Lloop_end_ApplicTP%d"  !applicTP_counter

    | _ -> raise X_worng_label


(* r8 = pointer to NEW extended env *)
(* r9 = pointer to CURRENT lexical env *)
(* r11 = helper register *)
let rec copy_minors_assem depth index = 
  match depth  with
  | 0 -> "\n"
  | _ ->  "mov r11, [r9+WORD_SIZE*" ^ (string_of_int index) ^ "]\n" ^
          "mov [r8+WORD_SIZE*(" ^ (string_of_int index) ^ "+1)], r11\n" ^ 
          (copy_minors_assem (depth-1) (index + 1)) 


let generate consts fvars e =
  let rec run consts fvars e depth =
    match e with
    | ScmConst'(sexpr) -> Printf.sprintf "mov rax, const_tbl+%d\n" (find_const_offset sexpr consts)
    | ScmVar'(VarParam(str, minor)) -> Printf.sprintf "mov rax, qword [rbp+8*(4+%d)]\n" minor
    | ScmSet'(VarParam(str, minor), exp) -> 
        let generate_exp = run consts fvars exp depth in
        ";; ===== Start ScmSet(VarParam) =====\n" ^
        generate_exp ^ Printf.sprintf 
                        "mov qword [rbp+8*(4+%d)], rax\n
                        mov rax, SOB_VOID_ADDRESS\n" minor ^
        ";; ===== End ScmSet(VarParam) =====\n" 


    | ScmVar'(VarBound(str, major, minor)) -> 
        Printf.sprintf 
          "mov rax, qword [rbp+8*2]\n
          mov rax, qword [rax+8*%d]\n
          mov rax, qword [rax+8*%d]\n" major minor

    | ScmSet'(VarBound(str, major, minor), exp) -> 
        let generate_exp = run consts fvars exp depth in
        generate_exp ^ Printf.sprintf 
                          "mov rbx, qword [rbp+8*2]\n
                          mov rbx, qword [rbx+8*%d]\n
                          mov qword [rbx+8*%d], rax\n
                          mov rax, SOB_VOID_ADDRESS\n" major minor

    | ScmVar'(VarFree(str)) -> 
        Printf.sprintf "mov rax, qword [fvar_tbl+8*%d]\n" (List.assoc str fvars)

    | ScmSet'(VarFree(str), expr) -> 
        ";; ===== Start ScmSet(VarFree) =====\n" ^
        let generate_exp = (run consts fvars expr depth) in
        generate_exp ^ Printf.sprintf 
                        "mov qword [fvar_tbl+8*%d], rax\n
                        mov rax, SOB_VOID_ADDRESS\n" (List.assoc str fvars) ^
        ";; ===== End ScmSet(VarFree) =====\n"


    | ScmSeq'(lst) -> List.fold_left 
                        (fun str1 str2 -> str1 ^ str2)
                        ""
                        (List.map (fun exp -> run consts fvars exp depth) lst)

    |ScmDef'(VarFree(str),expr) -> 
      let var_expr_code = run consts fvars expr depth in 
      var_expr_code ^ Printf.sprintf "mov qword [fvar_tbl+8*%d], rax\n
                                      mov rax, SOB_VOID_ADDRESS\n" (List.assoc str fvars)

    |ScmIf'(test, dit, dif) ->
      let l_else = make_label "Lelse_If" in 
      let l_exit = make_label "Lexit_If" in 
      update_ref if_counter 1;
      let generate_exp_test =run consts fvars test depth in
      let generate_exp_dit = run consts fvars dit depth in
      let generate_exp_dif = run consts fvars dif depth in
        generate_exp_test ^
        "cmp rax, SOB_FALSE_ADDRESS\n" ^
        "je "^ l_else ^ "\n" ^
        generate_exp_dit ^
        "jmp " ^ l_exit ^ "\n"^
        l_else ^ ":\n" ^
        generate_exp_dif ^
        l_exit ^ ":\n" 

    | ScmOr'(lst) -> 
      (match (List.length lst) with
      | 0 -> Printf.sprintf "mov rax, SOB_FALSE_ADDRESS\n"
      | 1 -> run consts fvars (List.hd lst) depth
      | len -> 
          let lexit_Or_label = (make_label "Lexit_Or") in
          let list_without_last = List.rev (List.tl (List.rev lst)) in
          let last_exp = List.hd (List.rev lst) in
          (String.concat
            "\n"
            (List.map 
              (fun exp -> (run consts fvars exp depth) ^ 
                          "cmp rax, SOB_FALSE_ADDRESS\n
                          jne " ^ lexit_Or_label ^ "\n") 
              list_without_last)) ^
          (run consts fvars last_exp depth) ^
          lexit_Or_label ^ ":\n")

    | ScmBox'(var) -> 
        ";; ===== Start ScmBox =====\n" ^
        "push rsi\n" ^
        (run consts fvars (ScmVar'(var)) depth) ^
        "MALLOC rsi, WORD_SIZE\n" ^
        "mov qword [rsi], rax\n" ^
        "mov rax, rsi\n" ^
        "pop rsi\n" ^
        ";; ===== End ScmBox =====\n"


    | ScmBoxGet'(var) -> 
      ";; ===== Start ScmBoxGet =====\n" ^
      (run consts fvars (ScmVar'(var)) depth) ^ "mov rax, qword [rax]\n" ^
      ";; ===== End ScmBoxGet =====\n"

    | ScmBoxSet'(var, exp) -> 
        ";; ===== Start ScmBoxSet =====\n" ^
        (run consts fvars exp depth) ^
        "push rax\n" ^
        (run consts fvars (ScmVar'(var)) depth) ^
        "pop qword [rax]\n" ^
        "mov rax, SOB_VOID_ADDRESS\n" ^
        ";; ===== End ScmBoxSet =====\n"
 
    |ScmLambdaSimple'(params,body) ->
      let l_loop = make_label "Lloop_LambdaSimple" in 
      let l_code = make_label "Lcode_LambdaSimple" in 
      let l_closure = make_label "Lclosure_LambdaSimple" in 
      let l_cont = make_label "Lcont_LambdaSimple" in
      let l_createMinor = make_label "LcreateMinor_LambdaSimple" in 
      update_ref lambda_simple_counter 1;
      let create_ext_env = 
        if (depth == 0)
          then
            "MALLOC r8, WORD_SIZE\n" ^
            "mov qword [r8], SOB_NIL_ADDRESS\n"
          else
            (";; ===== Start ScmLambdaSimple' #" ^ (string_of_int !lambda_simple_counter) ^ " =====\n" ^
            ";; ===== Allocate memory Ext Env of ScmLambdaSimple' #" ^ (string_of_int !lambda_simple_counter) ^ " =====\n" ^
            "MALLOC r8, " ^ (string_of_int(depth+1)) ^ "*WORD_SIZE\n" ^ (* r8 = pointer to NEW extended environment *)
            ";; ===== Start copy of lexical environment of ScmLambdaSimple' #" ^ (string_of_int !lambda_simple_counter) ^ " =====\n" ^
            ";; ===== Start copy of minors in lexical environment of ScmLambdaSimple' #" ^ (string_of_int !lambda_simple_counter) ^ " =====\n" ^
            "mov r9, [rbp + 2*WORD_SIZE]\n" ^ (* r9 = pointer to CURRENT lexical env *)
            (copy_minors_assem depth 0) ^     (* Copy lexical environment *)
            ";; ===== Start copy of params in lexical environment of ScmLambdaSimple' #" ^ (string_of_int !lambda_simple_counter) ^ " =====\n" ^
            ";; ===== Allocate memory for minor[0](params) of ScmLambdaSimple' #" ^ (string_of_int !lambda_simple_counter) ^ " =====\n" ^
            "mov rbx, [rbp + 3*WORD_SIZE]\n" ^      (* rbx = arg count *)
            "cmp rbx, 0\n" ^
            "jne " ^ l_createMinor ^ "\n" ^
            "mov qword [r8], SOB_NIL_ADDRESS\n" ^    (* If there are no params, place SOB_NIL_ADDRESS and do not create minor[0] *)
            "jmp " ^ l_closure ^ "\n" ^
            l_createMinor ^ ":\n" ^
            "inc rbx\n" ^       (* Reserve one WORD_SIZE for Magic *)
            "shl rbx, 3\n" ^    (* Multiple count by WORD_SIZE for memory allocation *)
            "MALLOC r11, rbx\n" ^ (* r11 = pointer to new minor for params *)
            ";; ===== Paste address to newly allocated minor[0] in Ext Env of ScmLambdaSimple' #" ^ (string_of_int !lambda_simple_counter) ^ " =====\n" ^
            "mov [r8], r11\n" ^  (* Paste address to newly allocated minor[0] in Ext Env *)
            "shr rbx, 3\n" ^     (* Divide memory size by WORD_SIZE to get back arg_count (including Magic) *)
            "mov rcx, 0\n" ^
            "mov r12, rbp\n" ^    (* r12 = address of param[0] in stack *)
            "add r12, 32\n" ^
            l_loop ^ ":\n" ^
            "cmp rcx, rbx\n" ^
            "je " ^ l_closure ^ "\n" ^
            "mov rdi, [r12+rcx*WORD_SIZE]\n" ^
            "mov [r11+rcx*WORD_SIZE], rdi\n" ^
            "add rcx, 1\n" ^
            "jmp " ^ l_loop ^ "\n" ^
            ";; ===== End copy of params in lexical environment of ScmLambdaSimple' #" ^ (string_of_int !lambda_simple_counter) ^ " =====\n") in

        create_ext_env ^
        ";; ===== Start closure creation of ScmLambdaSimple' #" ^ (string_of_int !lambda_simple_counter) ^ " =====\n" ^
        l_closure ^ ":\n" ^
        "MAKE_CLOSURE(rax, r8, " ^ l_code ^ ")\n" ^
        "jmp " ^ l_cont ^ "\n" ^
        ";; ===== End closure creation of ScmLambdaSimple' #" ^ (string_of_int !lambda_simple_counter) ^ " =====\n" ^
        ";; ===== Start code of ScmLambdaSimple' #" ^ (string_of_int !lambda_simple_counter) ^ " =====\n" ^
        l_code ^ ":\n" ^
        "push rbp\n" ^
        "mov rbp, rsp\n" ^
        ";; ===== Start generate body of ScmLambdaSimple' #" ^ (string_of_int !lambda_simple_counter) ^ " =====\n" ^
        (run consts fvars body (depth + 1)) ^
        ";; ===== End generate body of ScmLambdaSimple' #" ^ (string_of_int !lambda_simple_counter) ^ " =====\n" ^
        "leave\n" ^
        "ret\n" ^
        ";; ===== End code of ScmLambdaSimple' #" ^ (string_of_int !lambda_simple_counter) ^ " =====\n" ^
        l_cont ^ ":\n" ^
        ";; ===== End ScmLambdaSimple' #" ^ (string_of_int !lambda_simple_counter) ^ " =====\n"


    |ScmLambdaOpt'(params, opt, body) ->
      let l_loop = make_label "Lloop_LambdaOpt" in 
      let l_code = make_label "Lcode_LambdaOpt" in 
      let l_closure = make_label "Lclosure_LambdaOpt" in 
      let l_cont = make_label "Lcont_LambdaOpt" in 
      let l_createMinor = make_label "LcreateMinor_LambdaOpt" in 
      let l_fixStackLoop = make_label "LfixStackLoop_LambdaOpt" in 
      let l_fixStackEnd = make_label "LfixStackEnd_LambdaOpt" in 
      update_ref lambda_opt_counter 1;
      let create_ext_env = 
        if (depth == 0)
          then
            "MALLOC r8, WORD_SIZE\n" ^
            "mov qword [r8], SOB_NIL_ADDRESS\n"
          else
            (";; ===== Start ScmLambdaOpt' #" ^ (string_of_int !lambda_opt_counter) ^ " =====\n" ^
            ";; ===== Allocate memory Ext Env of ScmLambdaOpt' #" ^ (string_of_int !lambda_opt_counter) ^ " =====\n" ^
            "MALLOC r8, " ^ (string_of_int(depth+1)) ^ "*WORD_SIZE\n" ^ (* r8 = pointer to NEW extended environment *)
            ";; ===== Start copy of lexical environment of ScmLambdaOpt' #" ^ (string_of_int !lambda_opt_counter) ^ " =====\n" ^
            ";; ===== Start copy of minors in lexical environment of ScmLambdaOpt' #" ^ (string_of_int !lambda_opt_counter) ^ " =====\n" ^
            "mov r9, [rbp + 2*WORD_SIZE]\n" ^ (* r9 = pointer to CURRENT lexical env *)
            (copy_minors_assem depth 0) ^     (* Copy lexical environment *)
            ";; ===== Start copy of params in lexical environment of ScmLambdaOpt' #" ^ (string_of_int !lambda_opt_counter) ^ " =====\n" ^
            ";; ===== Allocate memory for minor[0](params) of ScmLambdaOpt' #" ^ (string_of_int !lambda_opt_counter) ^ " =====\n" ^
            "mov rbx, [rbp + 3*WORD_SIZE]\n" ^      (* rbx = arg count *)
            "cmp rbx, 0\n" ^
            "jne " ^ l_createMinor ^ "\n" ^
            "mov qword [r8], SOB_NIL_ADDRESS\n" ^    (* If there are no params, place SOB_NIL_ADDRESS and do not create minor[0] *)
            "jmp " ^ l_closure ^ "\n" ^
            l_createMinor ^ ":\n" ^
            "inc rbx\n" ^       (* Reserve one WORD_SIZE for Magic *)
            "shl rbx, 3\n" ^    (* Multiple count by WORD_SIZE for memory allocation *)
            "MALLOC r11, rbx\n" ^ (* r11 = pointer to new minor for params *)
            ";; ===== Paste address to newly allocated minor[0] in Ext Env of ScmLambdaOpt' #" ^ (string_of_int !lambda_opt_counter) ^ " =====\n" ^
            "mov [r8], r11\n" ^  (* Paste address to newly allocated minor[0] in Ext Env *)
            "shr rbx, 3\n" ^     (* Divide memory size by WORD_SIZE to get back arg_count (including Magic) *)
            "mov rcx, 0\n" ^
            "mov r12, rbp\n" ^    (* r12 = address of param[0] in stack *)
            "add r12, 32\n" ^
            l_loop ^ ":\n" ^
            "cmp rcx, rbx\n" ^
            "je " ^ l_closure ^ "\n" ^
            "mov rdi, [r12+rcx*WORD_SIZE]\n" ^
            "mov [r11+rcx*WORD_SIZE], rdi\n" ^
            "add rcx, 1\n" ^
            "jmp " ^ l_loop ^ "\n" ^
            ";; ===== End copy of params in lexical environment of ScmLambdaOpt' #" ^ (string_of_int !lambda_opt_counter) ^ " =====\n") in

        create_ext_env ^
        ";; ===== Start closure creation of ScmLambdaOpt' #" ^ (string_of_int !lambda_opt_counter) ^ " =====\n" ^
        l_closure ^ ":\n" ^
        "MAKE_CLOSURE(rax, r8, " ^ l_code ^ ")\n" ^
        "jmp " ^ l_cont ^ "\n" ^
        ";; ===== End closure creation of ScmLambdaOpt' #" ^ (string_of_int !lambda_opt_counter) ^ " =====\n" ^
        ";; ===== Start code of ScmLambdaOpt' #" ^ (string_of_int !lambda_opt_counter) ^ " =====\n" ^

        l_code ^ ":\n" ^

        "mov rbx, " ^ (string_of_int (List.length params)) ^ "\n" ^          (* rbx = params_length *)
        "mov rdx, qword [rsp + 2*WORD_SIZE]\n" ^                             (* rdx = arg_count *)
        "cmp rbx, rdx\n"^
        "je " ^ l_fixStackEnd ^ "\n" ^
        "mov rcx, rdx\n" ^         
        "sub rcx, rbx\n" ^                                                    (** rcx hold opt params number *)
        (* "sub rcx, 1\n" ^                                                   rcx = arg_count - params_length *)
        ";cmp rcx, 0\n" ^
        ";je " ^ l_fixStackEnd ^ "\n" ^

        ";dec rdx\n" ^                                   (* rdx = arg_count-1 *)
        ";add rdx, 3\n" ^
        ";mov rcx, "^(string_of_int ((List.length params) - 1))^"\n"^
        "mov rax, SOB_NIL_ADDRESS\n" ^                                (* Skip to args[0] on stack *)
        ";mov rsi, qword [rsp + rdx*WORD_SIZE]\n" ^      (* rsi = args[arg_count-1] *)
        ";MAKE_PAIR(rax, rsi, SOB_NIL_ADDRESS)\n" ^      (* rax = pointer to created pair *)

        l_fixStackLoop ^ ":\n" ^
        "mov rdi, rax\n" ^                              (* rdi = pointer of last pair *)
        "mov rsi, qword [rsp + ("^ (string_of_int ((List.length params) + 3 - 1)) ^"+rcx)*WORD_SIZE]\n" ^      (* rsi = args[rdx-1] *)
        "MAKE_PAIR(rax, rsi, rdi)\n" ^
        ";dec rdx\n" ^
        "loop " ^ l_fixStackLoop ^ "\n" ^

        ";;inc rbx\n" ^                                   (* rbx = new arg_count is params_length + 1 *)
        ";;mov qword [rsp + 2*WORD_SIZE], rbx\n" ^        (* Set arg_count on stack to rbx *)

        ";;add rbx, 2\n" ^                                (* rbx = points to args[arg_count-1]  *)
        "mov qword [rsp + "^(string_of_int ((List.length params) + 3))^"*WORD_SIZE], rax\n" ^      (* Set args[arg_count-1] to point to rax (pointer to last created pair) *)

        l_fixStackEnd ^ ":\n" ^

        "push rbp\n" ^
        "mov rbp, rsp\n" ^
        ";; ===== Start generate body of ScmLambdaOpt' #" ^ (string_of_int !lambda_opt_counter) ^ " =====\n" ^
        (run consts fvars body (depth + 1)) ^
        ";; ===== End generate body of ScmLambdaOpt' #" ^ (string_of_int !lambda_opt_counter) ^ " =====\n" ^
        "leave\n" ^
        "ret\n" ^
        ";; ===== End code of ScmLambdaOpt' #" ^ (string_of_int !lambda_opt_counter) ^ " =====\n" ^
        l_cont ^ ":\n" ^
        ";; ===== End ScmLambdaOpt' #" ^ (string_of_int !lambda_opt_counter) ^ " =====\n"
    


    |ScmApplic'(proc, args) -> 
      update_ref applic_counter 1;
      ";; ===== Start ScmApplic' #" ^ (string_of_int !applic_counter) ^ " =====\n" ^
      ";; ===== Push Magic Nil for ScmApplic' #" ^ (string_of_int !applic_counter) ^ " =====\n" ^
      "push qword SOB_NIL_ADDRESS\n" ^
      ";; ===== Start push args of ScmApplic' #" ^ (string_of_int !applic_counter) ^ " =====\n" ^
      (List.fold_left
        (fun str1 str2 -> str1 ^ str2)
        ""
        (List.map 
          (fun exp -> (run consts fvars exp depth) ^ "push rax\n")
          (List.rev args))) ^
      ";; ===== End push args of ScmApplic' #" ^ (string_of_int !applic_counter) ^ " =====\n" ^
      ";; ===== Push number of args of ScmApplic' #" ^ (string_of_int !applic_counter) ^ " =====\n" ^
      "push " ^ (string_of_int (List.length args)) ^ "\n"^
      ";; ===== Generate proc of ScmApplic' #" ^ (string_of_int !applic_counter) ^ " =====\n" ^
      (run consts fvars proc depth) ^
      ";; ===== Set ENV of ScmApplic' #" ^ (string_of_int !applic_counter) ^ " =====\n" ^
      "CLOSURE_ENV r8, rax\n"^ 
      "push r8\n"^ 
      ";; ===== call to code proc of ScmApplic' #" ^ (string_of_int !applic_counter) ^ " =====\n" ^
      "CLOSURE_CODE r8, rax\n"^
      "call r8\n"^
      ";; ===== Return from code of ScmApplic' #" ^ (string_of_int !applic_counter) ^ " =====\n" ^
      "add rsp, 8\n" ^
      "pop rbx\n" ^
      "shl rbx, 3\n" ^
      "add rsp, rbx\n" ^
      "add rsp, WORD_SIZE\n" ^    (* Remove Magic from stack *)
      ";; ===== End of ScmApplic' #" ^ (string_of_int !applic_counter) ^ " =====\n"

    |ScmApplicTP'(proc, args) -> 
      let l_loop = make_label "Lloop_ApplicTP" in 
      let l_loop_end = make_label "Lloop_end_ApplicTP" in 
      update_ref applicTP_counter 1;
      ";; ===== Start ScmApplicTP' #" ^ (string_of_int !applicTP_counter) ^ " =====\n" ^
      ";; ===== Push Magic Nil for ScmApplicTP' #" ^ (string_of_int !applicTP_counter) ^ " =====\n" ^
      "push qword SOB_NIL_ADDRESS\n" ^
      ";; ===== Start push args of ScmApplicTP' #" ^ (string_of_int !applicTP_counter) ^ " =====\n" ^
      (List.fold_left
        (fun str1 str2 -> str1 ^ str2)
        ""
        (List.map 
          (fun exp -> (run consts fvars exp depth) ^ "push rax\n")
          (List.rev args))) ^
      ";; ===== End push args of ScmApplicTP' #" ^ (string_of_int !applicTP_counter) ^ " =====\n" ^
      ";; ===== Push number of args of ScmApplicTP' #" ^ (string_of_int !applicTP_counter) ^ " =====\n" ^
      "push " ^ (string_of_int (List.length args))^"\n" ^
      ";; ===== Generate proc of ScmApplicTP' #" ^ (string_of_int !applicTP_counter) ^ " =====\n" ^
      (run consts fvars proc depth) ^
      ";; ===== Set ENV of ScmApplicTP' #" ^ (string_of_int !applicTP_counter) ^ " =====\n" ^
      "CLOSURE_ENV r8, rax\n" ^ 
      "push r8\n" ^
      ";; ===== Push ret addr of ScmApplicTP' #" ^ (string_of_int !applicTP_counter) ^ " =====\n" ^
      "push qword [rbp + 8 * 1]\n" ^    (* old ret addr *)

      "mov rdi, rbp\n" ^      (* Save current rbp in rdi *)
      "mov rdi, [rdi]\n" ^    (* Dereferece rbp *)
      "push rdi\n" ^          (* Push to copy in SHIFT_FRAME *)

      ";; ===== Start SHIFT_FRAME of ScmApplicTP' #" ^ (string_of_int !applicTP_counter) ^ "=====\n" ^
      "mov rsi, rax\n" ^   (* Backup rax *)
      "SHIFT_FRAME " ^ (string_of_int ((List.length args) + 5)) ^ "\n" ^
      ";; ===== End SHIFT_FRAME of ScmApplicTP' #" ^ (string_of_int !applicTP_counter) ^ " =====\n" ^

      ";; Move control to the new frame after overrinding the old frame\n" ^
      "cmp rax, 0\n" ^
      "je " ^ l_loop_end ^ "\n" ^
      "mov rcx, rax\n" ^
      "mov rax, WORD_SIZE\n" ^
      "cmp rcx, 0\n" ^
      "jg " ^ l_loop ^ "\n" ^
      "neg rcx\n" ^
      "mov rax, -WORD_SIZE\n" ^
      l_loop ^ ":\n" ^
      "add rbp, rax\n" ^
      "loop " ^ l_loop ^ "\n" ^
      l_loop_end ^ ":\n" ^

      "mov rsp, rbp\n" ^
      "add rsp, WORD_SIZE\n" ^
      "mov rbp, rdi\n" ^ (* added 15.01.22 (ahikam) *)
      ";; ===== call to code proc of ScmApplicTP' #" ^ (string_of_int !applicTP_counter) ^ " =====\n" ^
      "mov rax, rsi\n" ^    (* Restore rax *)
      "CLOSURE_CODE r8, rax\n"^
      "jmp r8\n" ^
      ";; ===== End of ScmApplicTP' #" ^ (string_of_int !applicTP_counter) ^ " =====\n"
    | _ -> raise X_this_should_not_happen

  in run consts fvars e 0 

end;;
