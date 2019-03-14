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
  | Box'(_), Box'(_) -> true
  | BoxGet'(_), BoxGet'(_) -> true
  | BoxSet'(_, v1), BoxSet'(_, v2) -> expr'_eq v1 v2 
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

let rec map f ls p =
    match ls with
    | [] -> []
    | hd :: tl -> [f hd p] @ (map f tl p);;


let rec find_indeces ls x i j=
  let rec find_index ls i =
      match ls with
      | [] -> -1
      | hd :: tl -> (match (hd=x) with
                     | true -> i
                     | _ -> find_index tl (i+1)) in
  match ls with
  | [] -> (-1, -1)
  | hd :: tl -> let j = find_index hd j in
                (match j with
                 | -1 -> find_indeces tl x (i+1) 0
                 | _ -> (i,j));;


let annotate_var x vars =
  let (i,j) = find_indeces vars x 0 0 in
  match j with
  | -1 -> Var'(VarFree(x))
  | _ -> (match i with
          | 0 -> Var'(VarParam(x, j))
          | _ -> Var'(VarBound(x, i-1, j)));;

let annotate_lexical_addresses e =
   let rec annotate e vars =
     match e with
     | Const(c) -> Const'(c)
     | If(test, dif, dit) -> If'(annotate test vars, annotate dif vars, annotate dit vars)
     | Seq(ls) -> Seq'(map annotate ls vars)
     | Set(var_ref, value) -> Set'(annotate var_ref vars, annotate value vars)
     | Def(var_ref, value) -> Def'(annotate var_ref vars, annotate value vars)
     | Or(ls) -> Or'(map annotate ls vars)
     | Applic(app, ls) -> Applic'(annotate app vars, map annotate ls vars)
     | LambdaSimple(params, body) -> LambdaSimple'(params, annotate body ([params] @ vars))
     | LambdaOpt (params, vs, body) -> LambdaOpt'(params, vs, annotate body ([params @ [vs]] @ vars))
     | Var(x) -> annotate_var x vars in
   annotate e [];;

let cut_list_tail ls =
  (* assumes ls.length >=1 *)
  let reversed = List.rev ls in
  let tail = List.hd reversed in
  let rest = List.tl reversed in
  let list = List.rev rest in
  (list, tail);;

let annotate_tail_calls e =
  let rec annotate e tp =
    match e with
    | Set'(var_ref, value) -> Set'(var_ref, annotate value false)
    | Def'(var_ref, value) -> Def'(var_ref, annotate value tp)
    | Seq'(body) -> Seq'(annotate_list body tp)
    | Or'(body) -> Or'(annotate_list body tp)

    | If'(test, dif, dit) ->
       If'(annotate test false, annotate dif tp, annotate dit tp)

    | LambdaSimple'(params, body) ->
       LambdaSimple'(params, annotate body true)
    | LambdaOpt'(params, vs, body) ->
       LambdaOpt'(params, vs, annotate body true)
    | Applic'(app, body) ->
       (match tp with
        | true -> ApplicTP'(annotate app false, map annotate body false)
        | false -> Applic'(annotate app false, map annotate body false))
   
    | _ -> e 
  and annotate_list ls tp  =
    (match tp with
     | false -> map annotate ls tp
     | true ->
        let (body, tail) = cut_list_tail ls in
        let body = map annotate body false in
        let tail = annotate tail true in
        (body @ [tail])) in

  annotate e false;;

(**** box_set *****)
let check_var var param =
  match var with
  | Var'(v) ->
     let v_str = (match v with
                  | VarParam(s, i) -> s
                  | VarBound(s, i, j) -> s
                  | VarFree(s) -> s) in
     (v_str = param)
  | _ -> false;;

let check_params params param =
   let params = List.map (fun x -> (x = param)) params in
   List.fold_right (||) params false;;

let check_rw e param =
  let read = ref 0 in
  let write = ref 0 in
  let rec check e =
    match e with
    | If'(test, dif, dit) ->
       begin
         check test;
         check dif;
         check dit
       end 
   | Seq'(body) ->
      begin
        (match List.map check body with
         | _ -> ())
      end
   | Set'(var_ref, value) ->
      begin
        (match (check_var var_ref param) with
         | true -> write := 1
         | false -> ());
        check value;
      end
   | Def'(var_ref, value) ->
      begin
        check var_ref;
        check value;
      end
   | BoxSet'(v, e') ->
      check e';
      begin
        (match (check_var (Var'(v)) param) with
         | true -> write := 1
         | false -> ());
      end
      (*
   | Box'(v) ->
      begin
        (match (check_var (Var'(v)) param) with
         | true -> read := 1
         | false -> ())
       *)
   | BoxGet'(v) ->
      begin
        (match (check_var (Var'(v)) param) with
         | true -> read := 1
         | false -> ())
      end
       
   | Or'(body) ->
      begin
        (match List.map check body with
         | _ -> ())
      end
   | Applic'(app, body) ->
      begin
        check app;
        (match List.map check body with
         | _ -> ())
      end
   | ApplicTP'(app, body) ->
      begin
        check app;
        (match List.map check body with
         | _ -> ())
      end
   | LambdaSimple'(params, body) ->
      begin
        (match (check_params params param) with
         | true -> ()
         | false -> check body)
      end
   | LambdaOpt'(params, vs, body) ->
      begin
        (match (check_params (params@[vs]) param) with
         | true -> ()
         | false -> check body)
      end
   | v  -> (match (check_var v param) with
            | true -> read := 1
            | false -> ()) in
  let u = check e in
  match u with
  | _ -> (read, write);;

let has_boxes e =
  match e with
  | Seq'(ls) ->
     (match List.hd ls with
      | Set'(_,Box'(_)) -> true
      | _ -> false)
  | _ -> false;;
  
let check_and_replace param set e index =
  let rec rw_conflicts set =
    match set with
    | [] -> false
    | [(_, _)] -> false
    | hd :: tl ->
       (match hd with
        | (0,0) -> rw_conflicts tl
        | (r,w) -> 
           let rest = List.fold_right (fun (r1, w1) (r2, w2) ->
                            (r1 lor r2, w1 lor w2))
                        tl (0,0) in
           let (r_rest, w_rest) = rest in
           (match ((r land w_rest) lor (w land r_rest)) with
            | 0 -> rw_conflicts tl
            | _ -> true)) in

  let rec replace e =
     match e with
     | If'(test, dif, dit) ->
        If'(replace test, replace dif, replace dit)
     | Seq'(body) -> Seq'(List.map replace body)
     | Set'(var_ref, value) ->
        (match var_ref with
         | Var'(v) ->
            (match (check_var var_ref param) with
             | true ->
                BoxSet'(v, replace value)
             | false -> Set'(replace var_ref, replace value))
         | _ -> raise X_syntax_error)
     | BoxSet'(var_ref, value) ->
        BoxSet'(var_ref, replace value)
     | Def'(var_ref, value) ->
        Def'(replace var_ref, replace value)
     | Or'(body) -> Or'(List.map replace body)
     | Applic'(app, body) ->
        Applic'(replace app, List.map replace body)
     | ApplicTP'(app, body) ->
        ApplicTP'(replace app, List.map replace body)
     | LambdaSimple'(params, body) ->
        (match (check_params params param) with
         | true -> e
         | false -> LambdaSimple'(params, replace body))
     | LambdaOpt' (params, vs, body) ->
         (match (check_params (params@[vs]) param) with
         | true -> e
         | false -> LambdaOpt'(params, vs, replace body))
     | v  ->
        (match v with
         | Var'(v') ->
            (match (check_var v param) with
             | true -> BoxGet'(v')
             | false -> e)
         | _ -> e) in
  let set = !set in
  let set = List.map (fun (x,y) -> (!x, !y)) set in 
  match (rw_conflicts set) with
  | true ->
     (match (has_boxes e) with
      | false ->
         Seq'([Set'(Var'(VarParam(param, index)), Box'(VarParam(param, index))); replace e])
      | true ->
         (match e with
          | Seq'(ls) ->
             let boxes, body = cut_list_tail ls in
             Seq'((boxes @ [Set'(Var'(VarParam(param, index)), Box'(VarParam(param, index)))] @ [replace body]))
          | _ -> e))
  |  _ -> e;;

let rec check_curr_rw e param =
  let read = ref 0 in
  let write = ref 0 in
  let rec check e =
    match e with
    | If'(test, dif, dit) ->
       begin
         check test;
         check dif;
         check dit
       end
   | Seq'(body) ->
      begin
        (match List.map check body with
         | _ -> ())
      end
   | Set'(var_ref, value) ->
      begin
        (match (check_var var_ref param) with
         | true -> write := 1
         | false -> ());
        check value;
      end
   | Def'(var_ref, value) ->
      begin
        check var_ref;
        check value;
      end
   | Or'(body) ->
      begin
        (match List.map check body with
         | _ -> ())
      end
   | Applic'(app, body) ->
      begin
        check app;
        (match List.map check body with
         | _ -> ())
      end
   | ApplicTP'(app, body) ->
      begin
        check app;
        (match List.map check body with
         | _ -> ())
      end
   | LambdaSimple'(params, body) ->
      begin
        ()
      end
   | LambdaOpt'(params, vs, body) ->
      begin
        ()
      end
   | BoxSet'(v, e') ->
      begin
        (match (check_var (Var' v) param) with
         | true -> write := 1
         | false -> ());
        check e'
      end
   | Box'(v) ->
      (match (check_var (Var' v) param) with
       | true -> read := 1
       | false -> ())
   | BoxGet'(v) ->
      (match (check_var (Var' v) param) with
       | true -> read := 1
       | false -> ())
   | v  -> (match (check_var v param) with
            | true -> read := 1
            | false -> ()) in
  let u = check e in
  match u with
  | _ -> (read, write)
  ;;

let make_box params e =
  let get_rws param e =
    let rws = ref [check_curr_rw e param] in 
    let rec get_rw e =
      (match e with
       | If'(test, dif, dit) ->
          begin
            get_rw test;
            get_rw dif;
            get_rw dit
          end
       | Seq'(body) ->
          begin
            (match List.map get_rw body with
             | _ -> ())
          end
       | Set'(var_ref, value) ->
          begin
            get_rw var_ref;
            get_rw value;
          end
       | Def'(var_ref, value) ->
          begin
            get_rw var_ref;
            get_rw value;
          end
       | Or'(body) ->
          begin
            (match List.map get_rw body with
             | _ -> ())
          end
       | Applic'(app, body) ->
          begin
            get_rw app;
            (match List.map get_rw body with
             | _ -> ())
          end
       | ApplicTP'(app, body) ->
          begin
            get_rw app;
            (match List.map get_rw body with
             | _ -> ())
          end
       | LambdaSimple'(params, body) ->
          begin
            rws := !rws @ [check_rw e param]
          end
       | LambdaOpt'(params, vs, body) ->
          begin
            rws := !rws @ [check_rw e param]
          end
       | BoxSet'(_, e') ->
          begin
            get_rw e'
          end
       | _ -> ()) in

    let u = get_rw e in
    match u with
      _ -> rws in
  let ref_e = ref e in
  let rec replace_params params rws index =
      (match (params, rws) with
      | ([], []) -> ()
      | (hd1 :: tl1, hd2 :: tl2) ->
         begin 
           ref_e := check_and_replace hd1 hd2 !ref_e index;
           (replace_params tl1 tl2 (index+1))
         end
      | _ -> raise X_syntax_error) in
  let rws = map get_rws params e in
  let e' = replace_params params rws 0 in
  (match e' with
   | _ -> !ref_e)
   ;;

let box_set e =
  let rec lambda_finder e = 
     match e with
     | If'(test, dif, dit) ->
        If'(lambda_finder test, lambda_finder dif, lambda_finder dit)
     | Seq'(body) -> Seq'(List.map lambda_finder body)
     | Set'(var_ref, value) ->
        Set'(lambda_finder var_ref, lambda_finder value)
     | Def'(var_ref, value) ->
        Def'(lambda_finder var_ref, lambda_finder value)
     | Or'(body) -> Or'(List.map lambda_finder body)
     | Applic'(app, body) ->
        Applic'(lambda_finder app, List.map lambda_finder body)
     | ApplicTP'(app, body) ->
        ApplicTP'(lambda_finder app, List.map lambda_finder body)
     | BoxSet'(v, e') -> BoxSet'(v, (lambda_finder e'))
     | LambdaSimple'(params, body) -> 
        LambdaSimple'(params, (make_box params (lambda_finder body)))
     | LambdaOpt' (params, vs, body) ->
        LambdaOpt'(params, vs, (make_box (params@[vs]) (lambda_finder body)))
     | _ -> e in

  lambda_finder e;;



let run_semantics expr =
  (box_set
     (annotate_tail_calls
        (annotate_lexical_addresses expr)));;
   
   end;; (* struct Semantics *)
