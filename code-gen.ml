#use "semantic-analyser.ml";;

module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> (constant * (int * string)) list
  val make_fvars_tbl : expr' list -> (string * string) list
  val generate : (constant * (int * string)) list -> (string * string) list -> expr' -> string
  val const_eq : constant -> constant -> bool
end;;

module Code_Gen : CODE_GEN = struct
 
  let const_eq c1 c2 =
    match c1, c2 with
    | Void, Void -> true
    | Sexpr(s1), Sexpr(s2) -> sexpr_eq s1 s2
    | _ -> false;;

  let must_consts =
    [Void; Sexpr(Nil); Sexpr(Bool false); Sexpr(Bool true)];;

  let slice list cut =
    let rec helper i acc = function
      | [] -> List.rev acc, []
      | h :: t as l -> (match i with
                        | 0 -> List.rev acc, l
                        | _ -> helper (i-1) (h::acc) t) in
    helper cut [] list;;
  
  let cut_list_tail ls =
    (* assumes ls.length >=1 *)
    let reversed = List.rev ls in
    let tail = List.hd reversed in
    let rest = List.tl reversed in
    let list = List.rev rest in
    (list, tail);;
  
  let remove_element ls x =
    let has_dups hd tl =
      match const_eq hd x with
      | true -> tl
      | false -> hd :: tl in

    List.fold_right has_dups ls [];;


  let rec remove_dups ls =
    match ls with
    | [] -> []
    | h::t -> [h]@(remove_dups (remove_element t h));;

  let remove_element_fvar ls x =
    let has_dups hd tl =
      match (hd=x) with
      | true -> tl
      | false -> hd :: tl in

    List.fold_right has_dups ls [];;

  let rec remove_dups_fvars ls =
    match ls with
    | [] -> []
    | h::t -> [h]@(remove_dups_fvars (remove_element_fvar t h));;

  let rec consts_from_const c =
    match c with
    | Sexpr(s) ->
       (match s with
        | Symbol(str) ->
           [Sexpr(String(str))] @ [c]
        | Pair(p1, p2) ->
           (consts_from_const (Sexpr p1)) @
             (consts_from_const (Sexpr p2)) @ [c] 
        | Vector(v) ->
           (List.flatten
              (List.map
                 (fun x -> consts_from_const (Sexpr(x))) v)
           ) @ [c]
        | _ -> [c])
    | _ -> [c];;
  
  let expand_list ls =
    let get_consts hd tl =
      let consts = consts_from_const hd in
      match consts with
      | [] -> hd :: tl
      | _ -> (consts @ [hd]) @ tl in
    List.fold_right get_consts ls [];;

  let consts_from_exp' ast =
    let consts = ref [] in
    let rec collect_consts e' =
      match e' with
      | Const'(c) ->
         consts := !consts @ [c]
      | If'(test, dif, dit) ->
         begin
           collect_consts test;
           collect_consts dif;
           collect_consts dit;
         end
      | Seq'(body) ->
         begin
           (match List.map collect_consts body with
            | _ -> ())
         end
      | Set'(var_ref, value) ->
         begin
           collect_consts var_ref;
           collect_consts value;
         end
      | BoxSet'(var_ref, value) ->
         collect_consts value
      | Def'(var_ref, value) ->
         begin
           collect_consts var_ref;
           collect_consts value;
         end
      | Or'(body) ->
         begin
           (match List.map collect_consts body with
            | _ -> ())
         end
      | Applic'(app, body) ->
         begin
           collect_consts app;
           (match List.map collect_consts body with
            | _ -> ())
         end
      | ApplicTP'(app, body) ->
         begin
           collect_consts app;
           (match List.map collect_consts body with
            | _ -> ())
         end
      | LambdaSimple'(params, body) -> 
         collect_consts body
      | LambdaOpt' (params, vs, body) ->
         collect_consts body
      | _ ->  () in
    match collect_consts ast with
    | _ -> !consts;;

  let build_consts_tbl tbl =
    let acc = ref [] in
    let get_size c =
      match c with
      | Void -> 1
      | Sexpr(s)-> (match s with
                    | Nil -> 1
                    | Bool(_) -> 2
                    | Char(_) -> 2
                    | Number(_) -> 9
                    | String(s) -> 9 + String.length s
                    | Symbol(_) -> 9
                    | Vector(ls) -> (8 * (List.length ls)) + 9
                    | Pair(_) -> 17) in
    
    let rec get_details c i =
      let find_index e =
        let (_, (index, _)) = List.find (fun (c', (i', _)) ->
                                  (const_eq c' (Sexpr(e)))) !acc in
        string_of_int index in
      
      let macro = (match c with
                   | Void -> "MAKE_VOID"
                   | Sexpr(s) ->
                      (match s with
                       | Nil ->"MAKE_NIL"
                       | Bool(b) ->
                          (match b with
                           | false -> "MAKE_BOOL(0)"
                           | true -> "MAKE_BOOL(1)")
                       | Char(c') -> "MAKE_LITERAL_CHAR("^(string_of_int(Char.code c'))^")"
                       | Number(n) -> (match n with
                                       | Int(x) ->
                                          "MAKE_LITERAL_INT("^(string_of_int x)^")"
                                       | Float(x) ->
                                          "MAKE_LITERAL_FLOAT("^(string_of_float x)^")")
                       | String(s) ->
                          let explode s =
                            let rec exp i l =
                              if i < 0 then l else exp (i-1) (s.[i]::l) in
                            exp (String.length s - 1) [] in
                          let chars_to_ascii c_list = String.concat ", "
                                          (List.map (fun c -> (string_of_int (Char.code c)))
                                             c_list) in
                          let s = explode s in
                          let s = chars_to_ascii s in
                          "MAKE_LITERAL_STRING "^s
                       | Symbol(s) -> let (_, (index, _)) = List.find
                                                              (fun (c', (i', _)) ->
                                                                (const_eq c' (Sexpr(String(s)))))
                                                              !acc in
                                      "MAKE_LITERAL_SYMBOL(consts+"^(string_of_int index)^")"
                       | Vector(ls) -> let indices = List.map find_index ls in
                                       let indices = List.map (fun s-> "consts+"^s^", ") indices in
                                       let indices = String.concat "" indices in
                                       let indices = (match (String.length indices) with
                                                      | 0 -> ""
                                                      | _ -> String.sub indices 0
                                                               ((String.length indices) - 2)) in
                                       "MAKE_LITERAL_VECTOR "^indices
                       | Pair(car, cdr) -> let i1 = find_index car in
                                           let i2 = find_index cdr in
                                           let m1 = "consts+"^i1 in
                                           let m2 = "consts+"^i2 in
                                           "MAKE_LITERAL_PAIR ("^m1^", "^m2^")"
                  )) in
      (c, (i, macro))
      

    and iterate ls i =
      
      match ls with
      | [] -> []
      | hd::tl ->
         begin
           acc := !acc @ [get_details hd i];
           iterate tl (i + (get_size hd))
         end in
    
    match iterate tbl 0 with
      _ -> !acc;;
  

  
  let make_consts_tbl asts = 
    let tbl = List.flatten (List.map consts_from_exp' asts) in
    let tbl = must_consts @ tbl in
    let tbl = remove_dups tbl in
    let tbl = List.flatten (List.map consts_from_const tbl) in
    let tbl = remove_dups tbl in
    let tbl = build_consts_tbl tbl in
    tbl;;

  let fvars_from_exp' asts =
    let fvars = ref [] in
    let rec collect_fvars e' =
      match e' with
      | Var'(v) -> (match v with
                    | VarFree(x) -> fvars := !fvars @ [x]
                    | _ -> ())
      | If'(test, dif, dit) ->
         begin
           collect_fvars test;
           collect_fvars dif;
           collect_fvars dit;
         end
      | Seq'(body) ->
         begin
           (match List.map collect_fvars body with
            | _ -> ())
         end
      | Set'(var_ref, value) ->
         begin
           collect_fvars var_ref;
           collect_fvars value;
         end
      | BoxSet'(var_ref, value) ->
         collect_fvars value
      | Def'(var_ref, value) ->
         begin
           collect_fvars var_ref;
           collect_fvars value;
         end
      | Or'(body) ->
         begin
           (match List.map collect_fvars body with
            | _ -> ())
         end
      | Applic'(app, body) ->
         begin
           collect_fvars app;
           (match List.map collect_fvars body with
            | _ -> ())
         end
      | ApplicTP'(app, body) ->
         begin
           collect_fvars app;
           (match List.map collect_fvars body with
            | _ -> ())
         end
      | LambdaSimple'(params, body) -> 
         collect_fvars body
      | LambdaOpt' (params, vs, body) ->
         collect_fvars body
      | _ ->  () in

    match collect_fvars asts with
    | _ -> !fvars
  ;;

  let build_fvars_tbl tbl =
    let acc = ref [] in

    let rec iterate ls i =
      match ls with
      | [] -> []
      | hd::tl ->
         begin
           acc := !acc @ [(hd, "v"^(string_of_int i))] ;
           iterate tl (i+1) 
         end
    in
    match iterate tbl 0 with
    | _ -> !acc
  ;;
  let make_fvars_tbl asts =
    let tbl = List.flatten (List.map fvars_from_exp' asts) in
    let prims = ["boolean?"; "float?"; "integer?"; "pair?"; "null?"; "char?"; "vector?";
                 "string?"; "procedure?"; "symbol?"; "string-length"; "string-ref";
                 "string-set!"; "make-string"; "vector-length"; "vector-ref";
                 "vector-set!"; "make-vector"; "symbol->string"; "char->integer";
                 "integer->char"; "eq?"; "+"; "*"; "-"; "/"; "<"; "="
                                                                    (* ADDED PRIMS *)
                ; "car"; "cdr"; "cons"; "set-car!"; "set-cdr!"; "apply"] in
    let tbl = prims @ tbl in
    let tbl = remove_dups_fvars tbl in
    let tbl = build_fvars_tbl tbl in
    tbl
  ;;
  let i = ref 0 ;;
  
  let generate consts fvars e =
    let get_const_address const =
      let row = List.find (fun (c, (i, _)) -> const_eq const c) consts in
      let (_, (i, _)) = row in
      "consts+"^(string_of_int i)
    in
    
    let get_fvar_address fvar =
      let row = List.find (fun (name, _)-> (name = fvar)) fvars in
      let (_, label) = row in
      label
    in
    
    let rec code_snippet d e =
      let snippet_same_lvl = code_snippet d in
      let snippet_next_lvl = code_snippet (d+1) in
      let gen_lambda_code body =
        let i_me = string_of_int !i in
        begin
          i := !i+1 ;
          let extend_size = string_of_int ((d+1) * 8) in
          let create_extend =
            "MALLOC rbx, " ^ extend_size  ^ "\n" ^
              "mov r15, rbx\n" ^ 
                "mov rax, qword[rbp+16]\n" ^
                  "lea rbx, [rbx+8]\n" ^
                    "COPY_ARR rax, rbx, "^(string_of_int d)^"\n" in
          let alloc_args =
            "lea rcx, [rbp+24]\n" ^
              "mov rcx, qword[rcx]\n" ^
                "mov rdx, rcx\n" ^
                  "cmp rcx, 0\n" ^
                    "jne NOT_ZERO" ^ i_me ^ "\n" ^
                      "add rcx, 1\n" ^
                        "NOT_ZERO" ^ i_me ^ ":\n" ^
                          "shl rcx, 3\n" ^ 
                            "MALLOC rbx, rcx\n" ^
                              "mov r14, rbx\n" ^
                                "mov [r15], r14\n" ^
                                  "lea rax, [rbp+32]\n" ^
                                    "COPY_ARR rax, rbx, rdx\n"  in
          
          let code3 = "MAKE_CLOSURE(rax, r15, Lcode"^i_me^")\n" in
          let code3 = code3 ^ "jmp Lcont"^i_me^"\n" in

          let code4 = "Lcode"^i_me^":\n" in
          let code4 = code4^"push rbp\nmov rbp, rsp\n" in
          let body = snippet_next_lvl body in
          let code4 = code4^body^"leave\nret\nLcont"^i_me^":\n" in

          create_extend^alloc_args^code3^code4
        end
      in
      let gen_applic_code proc args =
        let args = List.rev args in
        let num_args = string_of_int (List.length args) in
        let args_text =
          List.fold_right (^) (List.map (fun s -> (snippet_same_lvl s)^"push rax\n") args) "" in
        let args_text = args_text ^ "push "^num_args^"\n" in
        let proc = snippet_same_lvl proc in
        let code = args_text ^ proc in
        num_args, code in
      
      match e with
      | Const'(c) -> "mov rax, "^(get_const_address c)^"\n"
      | Var'(v) ->
         (match v with
          | VarParam(_, minor) ->
             "mov rax, qword[rbp + 8*(4+"^(string_of_int minor)^")]\n"
          | VarFree(x) -> "mov rax, qword["^(get_fvar_address x)^"]\n"
          | VarBound(_, major, minor) ->
             let major,minor = string_of_int major, string_of_int minor in
             "mov rax, qword[rbp+8*2]\n"^
               "mov rax, qword[rax+8*"^major^"]\n"^
                 "mov rax, qword[rax+8*"^minor^"]\n"
         )
        
      | Def'(Var'(VarFree(x)), var_val) ->
         let var_val = snippet_same_lvl var_val in
         let var_ref = "mov qword["^(get_fvar_address x)^"], rax\n"^
                         "mov rax, SOB_VOID_ADDRESS\n"  in
         
         var_val^var_ref
         
         
      | Set'(Var'(var_ref), var_val) ->
         let var_val = snippet_same_lvl var_val in
         let var_ref =
           (match var_ref with
            | VarParam(_, minor) ->
               "mov qword [rbp+8*(4+"^(string_of_int minor)^")], rax\n"^
                 "mov rax, SOB_VOID_ADDRESS\n"
            | VarBound(_, major, minor)->
               let major, minor = string_of_int major, string_of_int minor in
               "mov rbx, qword[rbp+8*2]\n"^
                 "mov rbx, qword[rbx+8*"^major^"]\n"^
                   "mov qword[rbx+8*"^minor^"], rax\n"^
                     "mov rax, SOB_VOID_ADDRESS\n"
            | VarFree(x) ->
               "mov qword["^(get_fvar_address x)^"], rax\n"^
                 "mov rax, SOB_VOID_ADDRESS\n")  in
         var_val^var_ref
      | Box'(v) ->
         let text = snippet_same_lvl (Var'(v)) in
         let text = text ^ "MALLOC rbx, 8\n" in
         let text = text ^ "mov [rbx], rax\n" in
         let text = text ^ "mov rax, rbx\n" in
         text
         
      | Seq'(body) ->
         List.fold_right (^) (List.map snippet_same_lvl body) "" 
      | Or'(body) ->
         let i_me = string_of_int !i in
         begin
           i := !i + 1;
           let body = List.map snippet_same_lvl body in
           let rest, last = cut_list_tail body in
           let rest = List.map (fun s -> s^"cmp rax, SOB_FALSE_ADDRESS\n"^
                                           "jne Lexit"^i_me^"\n") rest in
           let last = last^"Lexit"^i_me^":\n" in
           let body = List.fold_right (^) rest "" in
           let body = body^last in
           body
         end
      | If'(test, dit, dif) ->
         let i_me = string_of_int !i in
         begin
           i := !i + 1;
           let test, dit, dif = snippet_same_lvl test, snippet_same_lvl dit, snippet_same_lvl dif in
           let test_text = "cmp rax, SOB_FALSE_ADDRESS\n"^
                             "je Lelse"^i_me^"\n" in
           let true_text = "jmp Lexit"^i_me^"\nLelse"^i_me^":\n" in
           let false_text = "Lexit"^i_me^":\n" in
           test^test_text^dit^true_text^dif^false_text                 
         end
      | BoxGet'(v) -> (snippet_same_lvl (Var'(v))) ^ "mov rax, qword[rax]\n"
      | BoxSet'(v, body) ->
         let code = snippet_same_lvl body in
         let code = code ^ "push rax\n" in
         let code = code ^ (snippet_same_lvl (Var'(v))) in
         let code = code ^ "pop qword [rax]\nmov rax, SOB_VOID\n" in
         code
      | LambdaSimple'(params, body) -> gen_lambda_code body
      | LambdaOpt'(params, vs, body) ->
         let i_me = string_of_int !i in
         begin
           i := !i+1 ;
           let num_params = string_of_int (List.length params) in
           let extend_size = string_of_int ((d+1) * 8) in
           let create_extend =
             "MALLOC rbx, " ^ extend_size  ^ "\n" ^
               "mov r15, rbx\n" ^ 
                 "mov rax, qword[rbp+16]\n" ^
                   "lea rbx, [rbx+8]\n" ^
                     "COPY_ARR rax, rbx, "^(string_of_int d)^"\n" in
           let alloc_args =
             "lea rcx, [rbp+24]\n" ^
               "mov rcx, qword[rcx]\n" ^
                 "mov rdx, rcx\n" ^
                   "cmp rcx, 0\n" ^
                     "jne NOT_ZERO" ^ i_me ^ "\n" ^
                       "add rcx, 1\n" ^
                         "NOT_ZERO" ^ i_me ^ ":\n" ^
                           "shl rcx, 3\n" ^ 
                             "MALLOC rbx, rcx\n" ^
                               "mov r14, rbx\n" ^
                                 "mov [r15], r14\n" ^
                                   "lea rax, [rbp+32]\n" ^
                                     "COPY_ARR rax, rbx, rdx\n"  in
           let make_closure =
             "MAKE_CLOSURE(rax, r15, Lcode"^i_me^")\n" ^
               "jmp Lcont"^i_me^"\n" in
           let open_frame =
             "Lcode"^i_me^":\n" ^
               "push rbp\n" ^
                 "mov rbp, rsp\n"
           in
 
           let pack_vs =
             "mov rbx, " ^ num_params ^ "\n" ^ (*rbx=#params*)
               "mov r8, rbx\n" ^ (* r8=#params *)
                 "lea rcx, [rbp+24]\n" ^ 
                   "mov rcx, qword[rcx]\n" ^ (*rcx = #args*)
                     "mov rdx, rcx\n" ^  (*rdx=#args*)
                       "mov rsi, rdx\n" ^ (*rsi=#args*)
                         "dec rdx\n" ^ (*rdx = #args-1*)
                           "sub rcx, rbx\n" ^ (*rcx=args-params*)
                             "cmp rcx, 0\n" ^
                               "je insert_nil"^i_me^"\n"^
                                 "mov rdi, rcx\n" ^ (*rdi=args-params*)
                                   "inc r8\n" ^ (* r8 =#params+1 *)
                                     "mov qword[rbp+24], r8\n" ^
                                       "lea rax, [rbp+8*(4+rdx)]\n" ^
                                         "ARRAY_TO_LIST rax, rcx\n"  in
           (* now in the highest place there's a list instead *)
           let shrink =
               "mov r8, " ^ num_params ^ "\n" ^ (* r8 = #params *)
                 "mov r9, r8\n" ^  (* r9 = #params *)
                   "dec r9\n" ^ (* r9=#params-1 *)
                     "mov r10, r9\n" ^ (*r10=#params-1*)
                       "add r10, 4\n" ^ (*r10 #param-1+4*)
                         "lea r14, [rbp+r10*8]\n" ^
                           "dec rdi\n"^(*rdi=args-param-1*)
                             "lea r15, [r14+rdi*8]\n" ^
                               "mov rcx, r8\n" ^ (*rcx = #params *)
                                 "add rcx, 4\n" ^ (*rcx = #params+4 *)
                                   "COPY_ARR_BACK r14, r15, rcx\n" ^
                                     ";pop rbp\n"^
                                       "lea rbp, [rsp+8*rdi]\n"^
                                         "mov rsp, rbp\n" ^
                                           "jmp Lbody"^i_me^"\n"
           in
           let fix_nil =
             "insert_nil"^i_me^":\n"^
               "mov r10, rbp\n"^
                 "lea r11, [rbp-8]\n"^
                   "mov r12, " ^ num_params ^ "\n" ^
                     "mov r13, r12\n"^
                       "add r12, 4\n" ^
                         "COPY_ARR r10, r11, r12\n"^
                           "sub rbp, 8\nsub rsp, 8\n"^
                             "lea rax, [rbp+8*r12]\n"^
                               "mov qword[rax], SOB_NIL_ADDRESS\n"^
                                 "inc r13\n"^
                                   "mov qword[rbp+3*WORD_SIZE], r13\n"^
                                     "Lbody"^i_me^":\n"

           in
           let body = snippet_next_lvl body in
           let close_frame = "close"^i_me^":\n" ^
             "leave\nret\nLcont"^i_me^":\n" in
           
           create_extend ^
             alloc_args ^
               make_closure ^
                 open_frame ^
                   pack_vs ^
                     shrink ^
                       fix_nil ^
                         body ^
                           close_frame
         end
      | Applic'(proc, args) ->
         let num_args, code = (gen_applic_code proc args) in
         let code = code ^
                      "mov sil, byte[rax]\n"^
                        "cmp sil, T_CLOSURE\n"^
                          "jne end1234\n"^
                            "CLOSURE_CODE rbx, rax\n"^
                              "CLOSURE_ENV rax, rax\n"^
                                "push rax\ncall rbx\n\n" in
         let code = code  ^
                      "add rsp, 8\n" ^
                      "pop rbx\nshl rbx, 3\n"^
                        "add rsp, rbx\n" in
         code
      | ApplicTP'(Var'(VarFree("apply")), args) ->
         snippet_same_lvl (Applic'(Var'(VarFree("apply")), args))
      | ApplicTP'(proc, args) ->
         let num_args, code = (gen_applic_code proc args) in
         let num_args = string_of_int((int_of_string num_args) + 4) in
         let code = code ^
                      "mov sil, byte[rax]\n"^
                        "cmp sil, T_CLOSURE\n"^
                          "jne end1234\n"^
                            "CLOSURE_CODE r13, rax\n"^
                              "CLOSURE_ENV rax, rax\n"^
                                "push rax\n"^
                                  "push qword[rbp+8]\n"^
                                    "mov r12, qword[rbp]\n"^
                                      "SHIFT_FRAME "^
                                        num_args^"\n"^
                                          "mov rbp, r12\n"^
                                            "jmp r13\n" in
         code

      | _-> "" in
 
    code_snippet 0 e;;

end;;
