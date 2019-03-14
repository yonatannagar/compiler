(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "reader.ml";;

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

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;

(************** Utilities ***************)

let  make_pair a b =
  Pair(a, b);;

let rec list_to_pair l =
  match l with
  | []->Nil
  | head :: tail -> make_pair head (list_to_pair tail);;

let contains ls x = List.exists ((=) x) ls;;

let no_dups ls =
  let unique x =
    let (l1, l2) = List.partition ((=) x) ls in
    (match List.length l1 with
    | 1 -> true
    | _ -> false) in
  List.fold_right (&&) (List.map unique ls) true;;

let strip_symbol symbol =
  match symbol with
  | Symbol(s) -> s
  | _ -> raise X_syntax_error;;

let proper_pairs_to_list_by_f f pairs =
  let rec pair_to_list pair =
    match pair with
    | Pair(e1, e2) -> [e1] @ pair_to_list e2
    | _ -> [] in
  let list = pair_to_list pairs in
  List.map f list;;


let improper_pairs_to_list_by_f f pairs =
  let rec pair_to_list pair =
    match pair with
    | Pair (e1, e2) -> (match e2 with
                        | Pair (f1, f2) -> [e1] @ pair_to_list e2
                        | _ -> [e1] @ [e2])
    | _ -> [] in
  let list = pair_to_list pairs in
  List.map f list;;

let is_not_nil x =
  match x with
  | Nil -> raise X_syntax_error
  | _ -> x;;

let is_list pairs =
  let not_list = -1 in
  let proper_list = 0 in
  let improper_list = 1 in
  let rec is_list_helper pair =
    match pair with
    | Pair(e1, e2) -> (match e2 with
                      | Pair(f1, f2)-> is_list_helper e2
                      | Nil -> proper_list
                      | _ -> improper_list)
    | _ -> not_list in
  let ans = match pairs with
    | Nil -> proper_list
    | _ -> is_list_helper pairs in
  ans;;

let cut_list_tail ls =
  (* assumes ls.length >=1 *)
  let reversed = List.rev ls in
  let tail = List.hd reversed in
  let rest = List.tl reversed in
  let list = List.rev rest in
  (list, tail);;

let prepare_simple_args args =
  let args = proper_pairs_to_list_by_f strip_symbol args in
  match no_dups args with
  | true -> args
  | _ -> raise X_syntax_error;;

let prepare_opt_args args =
  let args = improper_pairs_to_list_by_f strip_symbol args in
  match no_dups args with
  | true -> cut_list_tail args
  | _ -> raise X_syntax_error;;

let prepare_seq body =
  Pair(Symbol("begin"), is_not_nil (body));;


let extract_args args =
  let args = proper_pairs_to_list_by_f (fun x-> x) args in
  let args = List.map (function
                               | Pair(var_ref, Pair(value, Nil)) -> (var_ref, value)
                               | _ -> raise X_syntax_error) args in
  List.split args;;

let expand_let args body =
  let (var_names, values) = extract_args args in
  let var_names = list_to_pair var_names in
  let values = list_to_pair values in
  Pair(Pair((Symbol("lambda")), (Pair (var_names, body))), values);;

let expand_let_star args body =
  let args = proper_pairs_to_list_by_f (fun x -> x) args in
  match List.length args with
  | 0 -> Pair(Symbol("let"), Pair(Nil, body))
  | 1 -> Pair(Symbol("let"), Pair(Pair(List.hd args, Nil), body))
  | _ -> let arg = List.hd args in
         let rest = List.tl args in
         let rest = list_to_pair rest in
         Pair (Symbol("let"), Pair (Pair (arg, Nil),
         Pair (Pair(Symbol("let*"), Pair(rest, body)), Nil)));;

let expand_and body =
  let body = proper_pairs_to_list_by_f (fun x -> x) body in
  match List.length body with
  | 0 -> Bool(true)
  | 1 -> List.hd body
  | _ -> let first = List.hd body in
         let rest = List.tl body in
         let rest = list_to_pair rest in
         Pair(Symbol("if"), Pair(first, Pair (Pair(Symbol("and"), rest), Pair(Bool(false), Nil))));;

let expand_letrec args body =
  let we =  Pair(Symbol"quote", Pair(Symbol "whatever", Nil)) in
  let var_names, values = extract_args args in
  let we_pairs = List.map (fun var -> Pair(var, Pair(we, Nil))) var_names in
  let sets = List.map2 (fun var exp ->
                 Pair(Symbol("set!"), Pair(var, Pair(exp, Nil))))
               var_names values in
  let we_pairs = list_to_pair we_pairs in
  let body = proper_pairs_to_list_by_f (fun x->x) body in
  let sets = sets @ body in
  let sets = list_to_pair sets in

  Pair(Symbol("let"), Pair(we_pairs, sets));;


let expand_mit_def var arg_list expr_list =
  Pair(Symbol("define"),
       Pair(var,Pair(Pair(Symbol("lambda"),
                          Pair(arg_list, expr_list)), Nil)));;


let expand_cond ribs =
  match ribs with
  | Pair(Pair(Symbol "else", x),Nil) -> Pair(Symbol("begin"), x)
  | Pair(Pair(test, Pair(Symbol "=>", Pair(dit, Nil))), rest) ->
     let assign_val = Pair(Symbol "value", Pair(test, Nil)) in
     let assign_f = Pair(Symbol("lambda"), Pair(Nil, Pair(dit, Nil))) in
     let assign_f = Pair(Symbol "f", Pair(assign_f, Nil)) in

     let dit = Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)) in
     let rest = (match rest with
                | Nil -> Nil
                | _-> Pair(Symbol "cond", rest)) in
     let assign_rest = Pair(Symbol "lambda", Pair(Nil,
                                                  Pair(rest, Nil))) in
     let assign_rest = Pair(Symbol "rest", Pair(assign_rest, Nil)) in

     let dif = Pair(Pair(Symbol "rest", Nil), Nil) in
     let assignments = (match rest with
                        | Nil ->
                           Pair(assign_val,
                                Pair(assign_f, Nil))
                        | _ ->
                           Pair(assign_val,
                                Pair(assign_f,
                                     Pair(assign_rest, Nil))) ) in
     let clause = (match rest with
                   | Nil ->
                      Pair(Symbol "if",
                           Pair(Symbol "value",
                                Pair(dit, Nil)))
                   | _ ->
                      Pair(Symbol "if",
                           Pair(Symbol "value",
                                Pair(dit, dif))) ) in
     Pair(Symbol "let", Pair(assignments, Pair(clause, Nil)))

  | Pair(Pair(test, dit), dif) ->
     let dit = (match dit with
                | Nil -> raise X_syntax_error
                | _ -> Pair(Symbol "begin", dit)) in
     (match dif with
      | Nil -> Pair(Symbol "if", Pair(test, Pair(dit, Nil)))
      | _ -> let dif = Pair(Symbol "cond", dif) in
             Pair(Symbol "if", Pair(test, Pair(dit, Pair(dif, Nil))))
     )
  | _ ->raise X_syntax_error;;

let rec expand_qq sexpr =
  match sexpr with
  | Pair(Symbol("unquote"), Pair (sexpr, Nil)) -> sexpr
  | Pair(Symbol("unquote-splicing"), _) -> raise X_syntax_error
  | Symbol(x) -> Pair(Symbol("quote"), Pair(Symbol(x), Nil))
  | Nil -> Pair(Symbol("quote"), Pair(Nil, Nil))
  | Vector(v) -> let v = List.map expand_qq v in
                 let v = list_to_pair v in
                 Pair(Symbol("vector"), v)
  | Pair(a,b) -> (match (a, b) with
      | ((Pair((Symbol("unquote-splicing")), (Pair(a, Nil)))), b) ->
	 (Pair((Symbol("append")), (Pair(a, (Pair(expand_qq b, Nil))))))
      | (a, (Pair((Symbol("unquote-splicing")), (Pair(b, Nil))))) ->
	 (Pair((Symbol("cons")), (Pair(expand_qq a, (Pair(b, Nil))))))
      | _ -> (Pair((Symbol("cons")), (Pair(expand_qq a, (Pair(expand_qq b, Nil)))))))
  | _ -> sexpr;;


(* work on the tag parser starts here *)

let tag_parse_expression sexpr =
  let rec tag_parse sexpr=
    match sexpr with
    | Number(x) -> Const(Sexpr(Number(x)))
    | Bool(x) -> Const(Sexpr(Bool(x)))
    | Char(x) -> Const(Sexpr(Char(x)))
    | String(x) -> Const(Sexpr(String(x)))
    | Pair(Symbol("quote"), Pair(x, Nil)) -> Const(Sexpr(x))
    | Symbol(var) -> (match contains reserved_word_list var with
                      | false -> Var(var)
                      | true -> raise  X_syntax_error)
    | Pair (Symbol("if"), Pair(test, Pair(dit, Nil))) ->
       If(tag_parse(test), tag_parse(dit), Const(Void))
    | Pair (Symbol("if"), Pair(test, Pair(dit, Pair(dif, Nil)))) ->
      If(tag_parse(test), tag_parse(dit), tag_parse(dif))
    | Pair(Symbol("set!"), Pair(var_ref, Pair(value, Nil))) ->
       let (var_ref, value) = tag_parse_pair var_ref value in
       Set(var_ref, value)
    (* MIT define *)
    | Pair(Symbol("define"), Pair(Pair(var, arg_list),
                                  expr_list))->
       tag_parse (expand_mit_def var arg_list expr_list)
    (* regular define *)
    | Pair(Symbol("define"), Pair(var_ref, Pair(value, Nil))) ->
         let (var_ref, value) = tag_parse_pair var_ref value in
         Def(var_ref, value)
    | Pair (Symbol("or"), body) ->
       let expr_list = tag_parse_list body in
       (match List.length expr_list with
        | 0 -> Const(Sexpr(Bool(false)))
        | 1 -> List.hd expr_list
        | _ -> Or(expr_list))
    (* lambdas *)
    | Pair(Symbol("lambda"), Pair(Symbol(vs), body)) ->
       LambdaOpt([], vs, tag_parse (prepare_seq body))
    | Pair(Symbol("lambda"), Pair(args, body)) ->
        let args_type = is_list args in
           (match args_type with
            | 0 -> let str_args = prepare_simple_args args in
                    LambdaSimple(str_args, tag_parse (prepare_seq body))
            | 1 -> let (str_args, vs) = prepare_opt_args args in
                   LambdaOpt(str_args, vs,tag_parse (prepare_seq body))
            | _ -> raise X_syntax_error)
    (* explicit sequence *)
    | Pair(Symbol("begin"), body) ->
       let expr_list =  tag_parse_list body in
        (match List.length expr_list with
         | 0 -> Const(Void)
         | 1 -> List.hd expr_list
         | _ -> Seq(expr_list))
    (* let *)
    | Pair(Symbol("let"), Pair(args, body)) ->
       tag_parse(expand_let args body)
    | Pair(Symbol("let*"), Pair(args, body)) ->
       tag_parse(expand_let_star args body)
    (* and *)
    | Pair(Symbol("and"), body) ->
       tag_parse(expand_and body)
    (* letrec *)
    | Pair(Symbol("letrec"), Pair(args, body)) ->
       tag_parse(expand_letrec args body)
    | Pair(Symbol("cond"), ribs) ->
       tag_parse(expand_cond ribs)
    (* quasiquote *)
    | Pair(Symbol("quasiquote"), Pair(sexpr, Nil)) ->
       tag_parse (expand_qq sexpr)
    (* application *)
    | Pair(app, args) -> Applic(tag_parse app, tag_parse_list args)

    | _ -> raise X_syntax_error

  and tag_parse_list ls =
      (match is_list ls with
       | 0 -> proper_pairs_to_list_by_f tag_parse ls
       | _ -> raise X_syntax_error)

  and tag_parse_pair var_ref value =
    let var_ref = tag_parse var_ref in
    let value =  tag_parse value in
    (match var_ref with
     | Var(x) -> (var_ref, value)
     | _ -> raise X_syntax_error) in

  tag_parse sexpr;;

let tag_parse_expressions sexpr = List.map tag_parse_expression sexpr;;


end;; (* struct Tag_Parser *)
