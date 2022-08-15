(*
   This module contains code to generate the low-level implementation of
   parts of the standard library procedures.
   The module works by defining a hierarchy of templates, which call each other
   to form complete routines. See the inline comments below for more information
   on the templates and the individual routines.
   Note that the implementation below contain no error handling or correctness-checking
   of any kind. This is because we will not test your compilers on invalid input.
   However, adding correctness-checking and error handling *as general templates* would be
   rather simple.
 *)
module type PRIMS = sig
  val procs : string;;
end

module Prims : PRIMS = struct
  (* This is the most basic routine template. It takes a body and label name, and
     creates the standard x86-64 bit routine form.
     All other templates and routine-generation functions depend on this template. *)
  let make_routine label body =
    label ^ ":
       push rbp
       mov rbp, rsp 
       " ^ body ^ "
         pop rbp
         ret";;
  
  let make_apply label body =
    label ^":\n" ^body

  (* Many of the low-level stdlib procedures are predicate procedures, which perform 
     some kind of comparison, and then return one of the constants sob_true or sob_false.
     Since this pattern repeats so often, we have a template that takes a body, and a type
     of condition to test for jump, and generates an assembly snippet that evaluated the body,
     and return true or false, depending on the type of condition. *)
  let return_boolean jcc body =
    body ^ "
      " ^ jcc ^ " .true
       mov rax, SOB_FALSE_ADDRESS
       jmp .return
       .true:
       mov rax, SOB_TRUE_ADDRESS
       .return:";;

  (* 
     Many of the predicates just test some kind of equality (or, equivalently, if the 
     zero flag is set), so this is an auxiliary function dedicated to equality-testing predicates. 
     Note how we make use of currying here.
   *)
  let return_boolean_eq = return_boolean "je";;
  
  (* 
     Almost all of the stdlib function take 1 or more arguments. Since all of the variadic procedures
     are implemented in the high-level scheme library code (found in stdlib.scm), we only have to deal
     with 1,2 or 3 arguments.
     These helper functions inject instructions to get parameter values off the stack and into registers
     to work with.
     The argument register assignment follows the x86 64bit Unix ABI, because there needs to be *some*
     kind of consistency, so why not just use the standard ABI.
     See page 22 in https://raw.githubusercontent.com/wiki/hjl-tools/x86-psABI/x86-64-psABI-1.0.pdf
     *** FIXME: There's a typo here: PVAR(0) should be rdi, PVAR(1) should be rsi, according to the ABI     
   *)
  let make_unary label body = make_routine label ("mov rsi, PVAR(0)\n\t" ^ body);;
  let make_binary label body = make_unary label ("mov rdi, PVAR(1)\n\t" ^ body);;
  let make_tertiary label body = make_binary label ("mov rdx, PVAR(2)\n\t" ^ body);;

  (* All of the type queries in scheme (e.g., null?, pair?, char?, etc.) are equality predicates
     that are implemented by comparing the first byte pointed to by PVAR(0) to the relevant type tag.
     so the only unique bits of each of these predicates are the name of the routine (i.e., the label), 
     and the type tag we expect to find.
     The implementation of the type-queries generator is slightly more complex, since a template and a label
     name aren't enough: we need to generate a routine for every (label * type_tag) pair (e.g., the routine 
     `is_boolean` should test for the T_BOOL type tag).
     We have a list of pairs, associating each predicate label with the correct type tag, and map the templating 
     function over this list. Note that the query template function makes use of some of the other templating 
     functions defined above: `make_unary` (predicates take only one argument) and `return_boolean_eq` (since 
     these are equality-testing predicates).
   *)
  let type_queries =
    let queries_to_types = [
        "boolean", "T_BOOL"; "flonum", "T_FLOAT"; "rational", "T_RATIONAL"; "pair", "T_PAIR";
        "null", "T_NIL"; "char", "T_CHAR"; "string", "T_STRING"; "symbol", "T_SYMBOL";
        "procedure", "T_CLOSURE"
      ] in
    let single_query name type_tag =
      make_unary (name ^ "?")
        (return_boolean_eq ("mov sil, byte [rsi]\n\tcmp sil, " ^ type_tag)) in
    String.concat "\n\n" (List.map (fun (a, b) -> single_query a b) queries_to_types);;

  (* The rational number artihmetic operators have to normalize the fractions they return,
     so a GCD implementation is needed. Now there are two options: 
     1) implement only a scheme-procedure-like GCD, and allocate rational number scheme objects for the 
        intermediate numerator and denominator values of the fraction to be returned, call GCD, decompose
        the returned fraction, perform the divisions, and allocate the final fraction to return
     2) implement 2 GCDs: a low-level gcd that only implements the basic GCD loop, which is used by the rational 
        number arithmetic operations; and a scheme-procedure-like GCD to be wrapped by the stdlib GCD implementation.
    
     The second option is more efficient, and doesn't cost much, in terms of executable file bloat: there are only 4
     routines that inline the primitive gcd_loop: add, mul, div, and gcd.
     Note that div the inline_gcd embedded in div is dead code (the instructions are never executed), so a more optimized
     version of prims.ml could cut the duplication down to only 3 places (add, mul, gcd).
   *)
  let inline_gcd =
    ".gcd_loop:
     and rdi, rdi
     jz .end_gcd_loop
     cqo
     idiv rdi
     mov rax, rdi
     mov rdi, rdx
     jmp .gcd_loop	
     .end_gcd_loop:";;

  (* The arithmetic operation implementation is multi-tiered:
     - The low-level implementations of all operations are binary, e.g. (+ 1 2 3) and (+ 1) are not 
       supported in the low-level implementation.
     - The low-level implementations only support same-type operations, e.g. (+ 1 2.5) is not supported
       in the low-level implementation. This means each operation has two low-level implementations, one
       for floating-point operands, and one for fractional operands.
     - Each pair of low-level operation implementations is wrapped by a dispatcher which decides which 
       of the two implementations to call (by probing the types of the operands).
     - The high-level implementations (see stdlib.scm) make use of a high-level dispatcher, that is in charge
       of performing type conversions as necessary to satisfy the pre-conditions of the low-level implementations.
     
     Operations on floating-point operands:
     -------------------------------------
     The implementations of binary floating point arithmetic operations contain almost identical code. The
     differences are the name (label) of the routines, and the arithmetic instruction applied to 
     the two arguments. Other than that, they are all the same: binary routines which load the values
     pointed at by PVAR(0) and PVAR(1) into SSE2 registers, compute the operation, create a new sob_float
     on the heap with the result, and store the address of the sob_float in rax as the return value.
     This allows us to easily abstract this code into a template that requires a label name and its matching
     arithmetic instruction (which are paired up in the op_map).
     Operations on fractional operands:
     ----------------------------------
     The addition and multiplication operations on rational numbers are similar to each other: both load 2 arguments,
     both deconstruct the arguments into numerator and denominator, both allocate a sob_rational to store the result
     on the heap, and both move the address of this sob_rational into rax as the return value. The only differences 
     are the routine name (label), and the implementation of the arithmetic operation itself.
     This allows us to easily abstract this code into a template that requires a label name and its matching
     arithmetic instruction (which are paired up in the op_map).
     
     Unlike in the case of floating point arithmetic, rational division is treated differently, and is implemented by
     using the identity (a/b) / (c/d) == (a/b) * (d/c).
     This is done by inverting the second arg (in PVAR(1)) and tail-calling fraction multiplication (`jmp mul`).
     Comparators:
     ------------
     While the implementation of the Comparators is slightly more complex, since they make use of `return_boolean`,
     the idea is the same as the arithmetic operators.
     A couple of things to note:
     - `eq.flt` can collapse to a bitwise comparison (like in the case of integers in C), while `eq.rat` involves
       comparing the numerator and denominator separately, due to our fraction representation using 128 bits
       and not 64 bits.
     - `lt.flt` does not handle NaN, +inf and -inf correctly. This allows us to use `return_boolean jl` for both the
       floating-point and the fraction cases. For a fully correct implementation, `lt.flt` should make use of
       the `ucomisd` opcode and `return_boolean jb` instead (see https://www.felixcloutier.com/x86/ucomisd for
       more information).
   *)
  let numeric_ops =
    let numeric_op name flt_body rat_body body_wrapper =      
      make_binary name
        (body_wrapper
           ("mov dl, byte [rsi]
             cmp dl, T_FLOAT
	     jne ." ^ name ^ "_rat
             " ^ flt_body ^ "
             jmp .op_return
          ." ^ name ^ "_rat:
             " ^ rat_body ^ "
          .op_return:")) in      
    let arith_map = [
        "MAKE_RATIONAL(rax, rdx, rdi)
         mov PVAR(1), rax
         pop rbp
         jmp mul", "divsd", "div";
        
        "imul rsi, rdi
	 imul rcx, rdx", "mulsd", "mul";
        
        "imul rsi, rdx
	 imul rdi, rcx
	 add rsi, rdi
	 imul rcx, rdx", "addsd", "add";
      ] in
    let arith name flt_op rat_op =
      numeric_op name
        ("FLOAT_VAL rsi, rsi 
          movq xmm0, rsi
          FLOAT_VAL rdi, rdi 
          movq xmm1, rdi
	  " ^ flt_op ^ " xmm0, xmm1
          movq rsi, xmm0
          MAKE_FLOAT(rax, rsi)")
        ("DENOMINATOR rcx, rsi
	  DENOMINATOR rdx, rdi
	  NUMERATOR rsi, rsi
	  NUMERATOR rdi, rdi
          " ^ rat_op ^ "
	  mov rax, rcx
	  mov rdi, rsi
          " ^ inline_gcd ^ "
	  mov rdi, rax
	  mov rax, rsi
	  cqo
	  idiv rdi
	  mov rsi, rax
	  mov rax, rcx
	  cqo
	  idiv rdi
	  mov rcx, rax
          cmp rcx, 0
          jge .make_rat
          imul rsi, -1
          imul rcx, -1
          .make_rat:
          MAKE_RATIONAL(rax, rsi, rcx)") in
    let comp_map = [
        (* = *)
        return_boolean_eq,
        "NUMERATOR rcx, rsi
	 NUMERATOR rdx, rdi
	 cmp rcx, rdx
	 jne .false
	 DENOMINATOR rcx, rsi
	 DENOMINATOR rdx, rdi
	 cmp rcx, rdx
         .false:",
        "FLOAT_VAL rsi, rsi
	 FLOAT_VAL rdi, rdi
	 cmp rsi, rdi", "eq";

        (* < *)
        return_boolean "jl",
        "DENOMINATOR rcx, rsi
	 DENOMINATOR rdx, rdi
	 NUMERATOR rsi, rsi
	 NUMERATOR rdi, rdi
	 imul rsi, rdx
	 imul rdi, rcx
	 cmp rsi, rdi",
        "FLOAT_VAL rsi, rsi
	 movq xmm0, rsi
	 FLOAT_VAL rdi, rdi
	 movq xmm1, rdi
	 cmpltpd xmm0, xmm1
         movq rsi, xmm0
         cmp rsi, 0", "lt";
      ] in
    let comparator comp_wrapper name flt_body rat_body = numeric_op name flt_body rat_body comp_wrapper in
    (String.concat "\n\n" (List.map (fun (a, b, c) -> arith c b a (fun x -> x)) arith_map)) ^
      "\n\n" ^
        (String.concat "\n\n" (List.map (fun (a, b, c, d) -> comparator a d c b) comp_map));;


  (* The following set of operations contain fewer similarities, to the degree that it doesn't seem that 
     creating more fine-grained templates for them is beneficial. However, since they all make use of
     some of the other templates, it is beneficial to organize them in a structure that enables
     a uniform mapping operation to join them all into the final string.*)
  let misc_ops =
    let misc_parts = [
        (* string ops *)
        "STRING_LENGTH rsi, rsi
         MAKE_RATIONAL(rax, rsi, 1)", make_unary, "string_length";
        
        "STRING_ELEMENTS rsi, rsi
         NUMERATOR rdi, rdi
         add rsi, rdi
         mov sil, byte [rsi]
         MAKE_CHAR(rax, sil)", make_binary, "string_ref";
        
        "STRING_ELEMENTS rsi, rsi
         NUMERATOR rdi, rdi
         add rsi, rdi
         CHAR_VAL rax, rdx
         mov byte [rsi], al
         mov rax, SOB_VOID_ADDRESS", make_tertiary, "string_set";
        
        "NUMERATOR rsi, rsi
         CHAR_VAL rdi, rdi
         and rdi, 255
         MAKE_STRING rax, rsi, dil", make_binary, "make_string";
        
        "SYMBOL_VAL rsi, rsi
	 STRING_LENGTH rcx, rsi
	 STRING_ELEMENTS rdi, rsi
	 push rcx
	 push rdi
	 mov dil, byte [rdi]
	 MAKE_CHAR(rax, dil)
	 push rax
	 MAKE_RATIONAL(rax, rcx, 1)
	 push rax
	 push 2
	 push SOB_NIL_ADDRESS
	 call make_string
	 add rsp, 4*8
	 STRING_ELEMENTS rsi, rax   
	 pop rdi
	 pop rcx
	 cmp rcx, 0
	 je .end
         .loop:
	 lea r8, [rdi+rcx]
	 lea r9, [rsi+rcx]
	 mov bl, byte [r8]
	 mov byte [r9], bl
	 loop .loop
         .end:", make_unary, "symbol_to_string";

        (* the identity predicate (i.e., address equality) *)
        (return_boolean_eq "cmp rsi, rdi"), make_binary, "eq?";

        (* type conversions *)
        "CHAR_VAL rsi, rsi
	 and rsi, 255
	 MAKE_RATIONAL(rax, rsi, 1)", make_unary, "char_to_integer";

        "NUMERATOR rsi, rsi
	 and rsi, 255
	 MAKE_CHAR(rax, sil)", make_unary, "integer_to_char";

        "DENOMINATOR rdi, rsi
	 NUMERATOR rsi, rsi 
	 cvtsi2sd xmm0, rsi
	 cvtsi2sd xmm1, rdi
	 divsd xmm0, xmm1
	 movq rsi, xmm0
	 MAKE_FLOAT(rax, rsi)", make_unary, "exact_to_inexact";

        "NUMERATOR rsi, rsi
	 mov rdi, 1
	 MAKE_RATIONAL(rax, rsi, rdi)", make_unary, "numerator";

        "DENOMINATOR rsi, rsi
	 mov rdi, 1
	 MAKE_RATIONAL(rax, rsi, rdi)", make_unary, "denominator";

        (* GCD *)
        "xor rdx, rdx
	 NUMERATOR rax, rsi
         NUMERATOR rdi, rdi
         " ^ inline_gcd ^ "
	 mov rdx, rax
         cmp rdx, 0
         jge .make_result
         neg rdx
         .make_result:
         MAKE_RATIONAL(rax, rdx, 1)", make_binary, "gcd";
         
         (* car *)
         "CAR rax, rsi", make_unary, "car";

         (* cdr *)
         "CDR rax, rsi", make_unary, "cdr";

         (* set_car *)
         "lea rsi, [rsi+TYPE_SIZE]
         mov [rsi] ,rdi
         mov rax, SOB_VOID_ADDRESS", make_unary, "set_car";

         (* set_cdr *)
         "lea rsi, [rsi+TYPE_SIZE+WORD_SIZE]
         mov [rsi] ,rdi
         mov rax, SOB_VOID_ADDRESS", make_unary, "set_cdr";

         (* cons *)
         "MAKE_PAIR(rax, rsi, rdi)", make_binary, "cons";

         (* apply v1 *)
         "mov rcx, 0
         mov rdx, PARAM_COUNT                             ;; rdx = arg_count
         add rdx, 3                                       ;; to use as index to s
         mov rsi, qword [rbp + rdx*WORD_SIZE]             ;; rsi points to s
         
         push SOB_NIL_ADDRESS                             ;; push magic for new frame
         
         ;; Extract S's arguments
         L_start_extract_s:
         cmp rsi, SOB_NIL_ADDRESS
         je L_end_extract_s
         CAR rdi, rsi
         push rdi
         inc rcx
         CDR rsi, rsi
         jmp L_start_extract_s
         
         L_end_extract_s:
         
         ;; Push S's arguments
         mov rbx, rcx                              ;; rbx = rcx = length of s
         cmp rcx, 0                                ;; loop guard
         je L_copy_x
         
         mov rsi, rsp
         sub rsi, WORD_SIZE                        ;; adjust to use correct value in loop
         
         L_start_push_s:
         add rsi, WORD_SIZE
         push qword [rsi]
         loop L_start_push_s
         
         ;; Shift S's arguments up in stack (below magic for new frame)
         mov rsi, rsp
         mov rcx, rbx                              ;; rcx = rbx = length of s
         shl rcx, 3                                ;; multiple by WORD_SIZE
         add rsi, rcx                              ;; rsi points to rsp + (length of s)
         sub rsi, WORD_SIZE                        ;; adjust to use correct value in loop
         mov rcx, rbx                              ;; rcx = rbx = length of s
         ;; No need for loop guard because length of s is checked above and if zero jumps to L_copy_x
         L_start_shift_s:
         pop rax
         add rsi, WORD_SIZE
         mov qword [rsi], rax
         loop L_start_shift_s
         
         L_copy_x:
         ;; Copy Xs to new frame
         mov rcx, PARAM_COUNT                      ;; rcx = arg_count
         mov rdx, rcx                              ;; rdx = arg_count
         add rdx, 3                                ;; skip frame bottom          
         dec rdx                                   ;; to use as index to point X_n-1
         shl rdx, 3                                ;; multiple by WORD_SIZE
         mov rsi, rbp
         add rsi, rdx                              ;; rsi points to X_n-1
         add rsi, WORD_SIZE                        ;; adjust to use correct value in loop
         
         sub rcx, 2                                ;; rcx = number of Xs (number of Xs is arg_count - 1 (proc) - 1(s))
         cmp rcx, 0                                ;; loop guard
         je L_copy_rest
         
         L_loop_copy_x:
         sub rsi, WORD_SIZE
         push qword [rsi]
         loop L_loop_copy_x
         
         ;; Copy rest for new frame
         L_copy_rest:
         mov rdx, PARAM_COUNT                      ;; rdx = arg_count
         sub rdx, 2                                ;; rdx = number of Xs = arg_count - 2
         add rdx, rbx                              ;; rdx = new arg_count = number of Xs + length of s
         push rdx                                  ;; push new arg_count
         
         sub rsi, WORD_SIZE                        ;; rsi points to proc
         mov rdi, qword [rsi]                      ;; rdi = closure of proc
         CLOSURE_ENV rax, rdi                      ;; rax = env of proc
         push rax                                  ;; push env
         
         mov rsi, qword [rbp + 1*WORD_SIZE]        ;; rsi points to ret_addr
         push qword rsi                            ;; push ret_addr
         
         push qword [rbp]                          ;; push dereference of old_rbp
         
         ;; Shift new frame to override current frame
         add rdx, 5                                ;; set counter to shift frame
         mov rcx, rdx                              ;; counter to shift frame
         
         mov rax, PARAM_COUNT
         add rax, 5
         mov rdx, -1                               ;; used as index in loop
         
         ;; No need for loop guard because rcx is at least 5
         L_loop_shift_frame:
         dec rax
         mov rbx, [rbp + WORD_SIZE * rdx]
         mov qword [rbp + WORD_SIZE * rax], rbx
         dec rdx
         loop L_loop_shift_frame
         
         ;; Move control to the new frame after overrinding the current frame
         ;; Adjust rbp and rsp for a return from tail position
         ;; Last copied value is old_rbp for the new frame which where rbp should be now
         cmp rax, 0
         je l_end_adjust_rbp
         mov rcx, rax
         mov rax, WORD_SIZE
         cmp rcx, 0
         jg l_loop_adjust_rbp
         neg rcx
         mov rax, -WORD_SIZE
         l_loop_adjust_rbp:
         add rbp, rax
         loop l_loop_adjust_rbp
         
         l_end_adjust_rbp:
         
         ;; Imitates 'leave'
         mov rsp, rbp
         add rsp, WORD_SIZE                 ;; same as 'pop rbp' (pop adds WORD_SIZE to rsp)
         mov rbp, [rbp]
         
         CLOSURE_CODE rax, rdi              ;; rax = code of proc
         jmp rax                            ;; call code", make_routine, "apply";

      ] in
    String.concat "\n\n" (List.map (fun (a, b, c) -> (b c a)) misc_parts);;

  (* This is the interface of the module. It constructs a large x86 64-bit string using the routines
     defined above. The main compiler pipline code (in compiler.ml) calls into this module to get the
     string of primitive procedures. *)
  let procs = String.concat "\n\n" [type_queries; numeric_ops; misc_ops];;
end;;
