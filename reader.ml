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
  | Vector(l1), Vector(l2) -> List.length l1 = List.length l2 && List.for_all2 sexpr_eq l1 l2
  | _ -> false;;

module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end

= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

let bool_reader =
  let false_bool = pack (word_ci "#f")  (fun s -> Bool (false)) in
  let true_bool = pack (word_ci "#t") (fun s -> Bool (true)) in
  disj false_bool true_bool;;

 let char_reader =
  let char_prefix = word "#\\" in
  let simple_char = pack (range ' ' '~') (fun s -> Char (s)) in
  let newline_char = pack (word_ci "newline") (fun s -> Char ('\n')) in
  let nul_char = pack (word_ci "nul") (fun s -> Char (Char.chr 0)) in
  let page_char = pack (word_ci "page") (fun s -> Char (Char.chr 12)) in
  let return_char = pack (word_ci "return") (fun s -> Char (Char.chr 13 )) in
  let space_char = pack (word_ci "space") (fun s -> Char (Char.chr 32)) in
  let tab_char = pack (word_ci "tab") (fun s -> Char (Char.chr 9)) in

  let named_char = disj_list [newline_char; nul_char; page_char; return_char; space_char; tab_char] in
  
  let hex_prefix = char_ci 'x' in
  let hex_suffix = pack (plus (disj_list (List.map2 range ['0'; 'a'; 'A'] ['9'; 'f'; 'F'])))
                     (fun s -> Char (Char.chr (int_of_string ("0x" ^ (list_to_string s))))) in
  let hex_char = pack (caten hex_prefix hex_suffix) (fun (s , e)-> e) in
  let char_suffix = disj_list [named_char; hex_char; simple_char] in
  pack (caten char_prefix char_suffix) (fun (s,e) -> e);;

let decimal_number_reader =
  let digit = (range '0' '9') in
  let natural = plus digit in
  let sign = maybe (disj (char '+') (char '-')) in
  let str_integer = pack (caten sign natural)
             (fun (s,e) ->
               (let rest = list_to_string e in
            match s with
              None -> rest
            | Some opt -> (String.make 1 opt) ^ rest)) in
  let str_e = pack (char_ci 'e') (fun s -> String.make 1 s) in
  let str_exp = pack (caten str_e str_integer) (fun (s,e) -> s ^ e) in
  let str_exp = maybe str_exp in
  let str_integer_exp =  pack (caten str_integer str_exp)
                  (fun (s,e) ->
                    match e with
                      None -> s
                    | Some opt -> s ^ opt) in
  let integer = pack (caten str_integer str_exp)
                  (fun (s,e) ->
                    match e with
                      None -> Number (Int (int_of_string s))
                    | Some opt ->
                       Number (Float (float_of_string (s ^ opt)))) in
  let str_dot = pack (char '.') (fun s -> String.make 1 s) in
  let str_float = caten_list [str_integer; str_dot; str_integer_exp] in
  let float = pack str_float (fun s -> Number (Float (float_of_string (String.concat "" s)))) in
  disj float integer;;

let hex_number_reader =
  let hex_prefix = word_ci "#x" in
  let hex_digit = disj_list (List.map2 range ['0'; 'a'; 'A'] ['9'; 'f'; 'F']) in
  let hex_natural = plus hex_digit in
  let sign = maybe (disj (char '+') (char '-')) in
  let str_integer = pack (caten sign hex_natural)
                      (fun (s,e) ->
                        (let rest = list_to_string e in
                         match s with
                           None -> "0x" ^ rest
                         | Some opt -> (String.make 1 opt) ^ "0x" ^ rest)) in
  let str_integer = pack (caten hex_prefix str_integer) (fun (s,e) -> e) in
  let integer = pack str_integer (fun s -> Number (Int (int_of_string s))) in
  let str_dot = pack (char '.') (fun s -> String.make 1 s) in
  let str_natural = pack hex_natural (fun s -> list_to_string s) in
  let str_float = caten_list [str_integer; str_dot; str_natural] in
  let float = pack str_float (fun s -> Number (Float (float_of_string (String.concat "" s)))) in
  disj float integer;;

let symbol_char =
  let r1 = range 'a' 'z' in
  let r2 = range 'A' 'Z' in
  let r3 = range '0' '9' in
  let c1 = char '!' in
  let c2 = char '$' in
  let c3 = char '^' in
  let c4 = char '*' in
  let c5 = char '-' in
  let c6 = char '_' in
  let c7 = char '=' in
  let c8 = char '+' in
  let c9 = char '<' in
  let c10 = char '>' in
  let c11 = char '?' in
  let c12 = char '/' in
  let c13 = char ':' in
  let rs = disj_list [r1; r2; r3] in
  let cs = disj_list [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13] in

  disj rs cs;;

let symbol_reader =
  pack (plus symbol_char) (fun s->Symbol(String.lowercase_ascii(list_to_string s)));;
  
let number_reader =
  not_followed_by (disj hex_number_reader decimal_number_reader) symbol_char;;


let string_lit_char =
  diff nt_any (one_of "\"\\");;


let string_meta_char =
  let backslash = char '\\' in
  let m1 = pack (word "\\n") (fun s->'\n') in
  let m2 = pack (word "\\r") (fun s->'\r') in
  let m3 = pack (word "\\t") (fun s->'\t') in
  let m4 = pack (word "\\f") (fun s->Char.chr 12) in
  let m5 = pack (caten backslash backslash) (fun (e, s)->'\\') in
  let doubleq = char '\"' in
  let m6 = pack (caten backslash doubleq) (fun (e, s)->'\"') in

  disj_list [m1; m2; m3; m4; m5; m6];;

let string_hex_char =
  let backslash = pack (char '\\') (fun s-> [s]) in
  let hex = pack (char_ci 'x') (fun s-> [s]) in
  let r1 = range 'a' 'f' in
  let r2 = range 'A' 'F' in
  let r3 = range '0' '9' in
  let ranges = plus (disj_list [r1; r2; r3]) in
  let term = pack (char ';') (fun s->[s]) in

  pack (caten_list [backslash; hex; ranges; term])
    (fun s-> Char.chr(int_of_string("0x"^list_to_string(List.nth s 2))));;

let string_reader =
  let dq = word "\"" in
  let string_char = disj_list[string_meta_char; string_hex_char; string_lit_char] in
  let p = pack (caten dq (star string_char)) (fun (s, e)-> e) in
  let p2 = pack (caten p dq) (fun (s, e)-> s) in

  pack p2 (fun s->String(list_to_string s));;

let line_comment_reader =
  let semi_colon = char ';' in
  let body = star (guard nt_any (fun s-> s!='\n')) in
  let end_of_line  = pack (char '\n') (fun s -> []) in
  let end_of_input = nt_end_of_input in
  let ending = disj end_of_line end_of_input in
  let comment = caten semi_colon body in
  let comment = caten comment ending in
  pack comment (fun (s,e) -> Nil);;


let  make_pair a b =
  Pair(a, b);;

let rec list_to_pair l =
  match l with
  | []->Nil
  | head :: tail -> make_pair head (list_to_pair tail);;

let rec dotted_to_pair l fin =
  match l with
  | []->fin
  | head :: tail -> make_pair head (dotted_to_pair tail fin);;

let dots = word "...";;

let rec list_reader s =
  let lparen = char '(' in
  let rparen = char ')' in
  let lbrack = char '[' in
  let rbrack = char ']' in
  let body = star reader in
  let b_parse = pack (caten lbrack body) (fun (s, e)-> e) in
  let b_parse = pack (caten b_parse rbrack) (fun (s, e)-> s) in
  let p_parse = pack (caten lparen body) (fun (s, e)-> e) in
  let p_parse = pack (caten p_parse rparen) (fun (s, e)-> s) in
  let list = disj b_parse p_parse in
  let list = pack list (fun s->list_to_pair s) in

  let body2 = star (disj not_closed_reader reader) in
  let b_not_closed = pack (caten lbrack body2) (fun (s, e)-> e) in
  let b_not_closed = pack (caten b_not_closed dots) (fun (s, e)-> s) in
  let p_not_closed = pack (caten lparen body2) (fun (s, e)-> e) in
  let p_not_closed = pack (caten p_not_closed dots) (fun (s, e)-> s) in

  let not_closed = disj b_not_closed p_not_closed in
  let not_closed = pack not_closed (fun s->list_to_pair s) in


  (disj list not_closed) s

and not_closed_list s =
  let lparen = char '(' in
  let rparen = pack (maybe (char ')')) (fun _->Nil) in
  let lbrack = char '[' in
  let rbrack = pack (maybe (char ']')) (fun _->Nil) in
  let body = star not_closed_reader in

  let plist = pack (caten lparen body) (fun (s, e)-> e) in
  let plist = pack (caten plist rparen) (fun (s, e)-> s) in
  let plist = pack plist (fun s->list_to_pair s) in

  let blist = pack (caten lbrack body) (fun (s, e)-> e) in
  let blist = pack (caten blist rbrack) (fun (s, e)-> s) in
  let blist = pack blist (fun s->list_to_pair s) in
  (disj plist blist) s

and dotted_list_reader s =
  let lparen = char '(' in
  let rparen = char ')' in
  let lbrack = char '[' in
  let rbrack = char ']' in
  let sexp1 = plus reader in
  let dot = char '.' in
  let sexp2 = reader in

  let p_left_to_dot = pack (caten lparen sexp1) (fun (s,e) -> e) in
  let p_right_to_dot = pack (caten sexp2 rparen) (fun (s,e) -> s) in
  let b_left_to_dot = pack (caten lbrack sexp1) (fun (s, e) -> e) in
  let b_right_to_dot = pack (caten sexp2 rbrack) (fun (s, e) -> s) in

  let b_lst = pack (caten b_left_to_dot dot) (fun (s, e) -> s) in
  let b_lst = pack (caten b_lst b_right_to_dot) (fun s -> s) in
  let p_lst = pack (caten p_left_to_dot dot) (fun (s,e) ->  s) in
  let p_lst = pack (caten p_lst p_right_to_dot) (fun s -> s) in

  let lst = disj b_lst p_lst in
  let lst = pack lst (fun (s, e) -> dotted_to_pair s e) in

  let sexp1' = plus (disj not_closed_reader reader) in
  let sexp2' = disj not_closed_reader reader in
  let p_not_closed_left = pack (caten lparen sexp1') (fun (s, e)-> e) in
  let p_not_closed_right = pack (caten sexp2' dots) (fun (s, e)-> s) in
  let p_not_closed = pack (caten p_not_closed_left dot) (fun (s, e)-> s) in
  let p_not_closed = pack (caten p_not_closed p_not_closed_right) (fun s -> s) in

  let b_not_closed_left = pack (caten lbrack sexp1') (fun (s, e)-> e) in
  let b_not_closed_right = pack (caten sexp2' dots) (fun (s, e)-> s) in
  let b_not_closed = pack (caten b_not_closed_left dot) (fun (s, e) -> s) in
  let b_not_closed = pack (caten b_not_closed b_not_closed_right) (fun s -> s) in

  let not_closed = disj p_not_closed b_not_closed in
  let not_closed = pack not_closed (fun (s, e) -> dotted_to_pair s e) in

  (disj not_closed lst) s

and not_closed_dotted s =
  let lparen = char '(' in
  let rparen = pack (maybe (char ')')) (fun _->Nil) in
  let lbrack = char '[' in
  let rbrack = pack (maybe (char ']')) (fun _->Nil) in
  let sexp1 = plus not_closed_reader in
  let sexp2 = not_closed_reader in
  let p_right = pack (caten lparen sexp1) (fun (s, e)-> e) in
  let p_left = pack (caten sexp2 rparen) (fun (s, e)-> s) in
  let p_dotted = pack (caten p_right (char '.')) (fun (s, e) -> s) in
  let p_dotted = pack (caten p_dotted p_left) (fun s -> s) in
  let b_right = pack (caten lbrack sexp1) (fun (s, e)-> e) in
  let b_left = pack (caten sexp2 rbrack) (fun (s, e)-> s) in
  let b_dotted = pack (caten b_right (char '.')) (fun (s, e) -> s) in
  let b_dotted = pack (caten b_dotted b_left) (fun s -> s) in

  let dotted = disj p_dotted b_dotted in
  let dotted = pack dotted (fun (s, e) -> dotted_to_pair s e) in

  dotted s

and empty_list_reader s =
  let lparen = char '(' in
  let lbrack = char '[' in
  let rparen = disj dots (word ")") in
  let rbrack = disj dots (word "]") in
  let body = star ignored_reader in

  let p_nil = caten lparen body in
  let p_nil = caten p_nil rparen in

  let b_nil = caten lbrack body in
  let b_nil = caten b_nil rbrack in

  let nil = disj p_nil b_nil in

  (pack nil (fun ((e, s) , f)->Nil)) s


and vector_reader s =
  let hashtag = char '#' in
  let lparen = char '(' in
  let rparen = char ')' in
  let body = star reader in
  let left = caten hashtag lparen in
  let vector = pack (caten left body) (fun (s, e)-> e) in
  let vector = pack (caten vector rparen) (fun (s, e)-> s) in
  let vector = pack vector (fun s -> Vector(s)) in


  let body2 = star (disj not_closed_reader reader) in
  let auto_closer = pack (caten left body2) (fun (s, e)-> e) in
  let auto_closer = pack (caten auto_closer dots) (fun (s, e)-> s) in
  let auto_closer = pack auto_closer (fun s-> Vector(s)) in

  (disj auto_closer vector) s

and not_closed_vector s =
  let start = word "#(" in
  let body = star not_closed_reader in
  let fin = pack (maybe (char ')')) (fun s-> Nil) in
  let vector = pack (caten start body) (fun (s, e) -> e) in
  let vector = pack (caten vector fin) (fun (s, e) -> s) in
  let vector = pack vector (fun s->Vector(s)) in
  let empty_vector = caten start (star ignored_reader) in
  let empty_vector = pack (caten empty_vector fin) (fun _ -> Vector([])) in

  (disj vector empty_vector) s

and empty_vector_reader s =
  let hashtag = char '#' in
  let lparen = char '(' in
  let rparen = disj dots (word ")") in
  let body = (star ignored_reader) in
  let left = caten hashtag lparen in
  let vector = caten left body in
  let vector = caten vector rparen in
  (pack vector (fun _->Vector([]))) s

and quote_reader s =
  let q = char '\'' in
  let packed = pack (caten q reader)
                 (fun (s, e)-> Pair(Symbol("quote"), (make_pair e Nil))) in
  packed s

and quasiquote_reader s =
  let q = char '`' in
  let packed = pack (caten q reader)
                 (fun (s, e)-> Pair(Symbol("quasiquote"), (make_pair e Nil))) in
  packed s

and unquote_reader s =
  let q = char ',' in
  let packed = pack (caten q reader)
                 (fun (s, e)-> Pair(Symbol("unquote"), (make_pair e Nil))) in
  packed s

and unquote_spliced_reader s =
  let q = word ",@" in
  let packed = pack (caten q reader)
                 (fun (s, e)-> Pair(Symbol("unquote-splicing"), (make_pair e Nil))) in
  packed s

and sexpr_comment_reader s =
  let start = word "#;" in
  let ret = pack (caten start reader) (fun _-> Nil) in
  ret s

and ignored_reader s =
  let ws = range (char_of_int 0) (char_of_int 32) in
  let ws = pack ws (fun _->Nil) in
  (disj_list [sexpr_comment_reader; line_comment_reader; ws]) s

and not_closed_reader s =
  let basics = disj_list [bool_reader;
                          char_reader;
                          number_reader;
                          string_reader;
                          symbol_reader] in
  let recs = disj_list [not_closed_vector;
                        not_closed_dotted;
                        not_closed_list;
                        quote_reader;
                        unquote_reader;
                        quasiquote_reader;
                        unquote_spliced_reader] in
  let readers = disj basics recs in

  let ignored_star = star ignored_reader in
  let reader = pack (caten ignored_star readers) (fun (s, e)-> e) in
  let reader = pack (caten reader ignored_star) (fun (s, e)-> s) in
  reader s

and reader s=
  let basics = disj_list [bool_reader;
                          char_reader;
                          number_reader;
                          string_reader;
                          symbol_reader] in
  let recs = disj_list [list_reader;
                        dotted_list_reader;
                        vector_reader;
                        empty_vector_reader;
                        empty_list_reader;
                        quote_reader;
                        unquote_reader;
                        quasiquote_reader;
                        unquote_spliced_reader] in
  let readers = disj basics recs in

  let ignored_star = star ignored_reader in
  let reader = pack (caten ignored_star readers) (fun (s, e)-> e) in
  let reader = pack (caten reader ignored_star) (fun (s, e)-> s) in
  reader s;;

let read_sexpr string =
  let sexpr = string_to_list string in
  let (e, s) = reader sexpr in
  e;;

let read_sexprs string =
  let multi_reader = star reader in
  let to_parse = string_to_list string in
  let (e, s) = multi_reader to_parse in
  e;;

end;; (* struct Reader *)
