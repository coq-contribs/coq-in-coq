open Genlex
open Core

(*> lexer *)
let string_of_token = function
    Kwd k -> k
  | Ident i -> i
  | Int i -> string_of_int i
  | Float f -> string_of_float f
  | String s -> s
  | Char c -> String.make 1 c
;;

let lexer=
  make_lexer
    ["Set"; "Prop"; "Kind";
    "["; "]"; "("; ")"; ":"; "->"; "let"; "in"; "_"; ",";
     ":="; "Quit";"Axiom";"Infer";"Check";"Delete";"List";"."]
;;

(*> parser *)
let rec parse_star p = parser       
    [< x = p; l = (parse_star p) >] -> x::l
  | [< >] -> []
;;

let anon_var = parser
    [< 'Kwd "_" >] -> "_"
  | [< 'Ident x >] -> x
;;

let virg_an_var = parser
    [< 'Kwd "," ; x = anon_var (*, ^ (<ident>|_)*)  >] -> x
;;

let lident = parser
    [< x = anon_var; l = (parse_star virg_an_var) >] -> x::l
;;

let parse_atom = parser
    [< 'Kwd "Prop" >] -> SRT Prop
  | [< 'Kwd "Set" >] -> SRT Set
  | [< 'Kwd "Kind" >] -> SRT Kind
  | [< 'Ident x >] -> REF x
;;

let rec parse_expr = parser
    [< 'Kwd "[";
       l = lident       (*[ ^ <ident>*);
       'Kwd ":"         (*[ <ident>* ^ (,|:)*);
       typ = parse_expr (*[ ... : ^ <expr>*);
       'Kwd "]"         (*[ ... : <expr> ^ ]*);
       trm = parse_expr (*[ ... ] ^ <expr>*)
    >] -> List.fold_right (fun x t->ABS (x,typ,t)) l trm

  | [< 'Kwd "let";
       x = anon_var     (*let ^ <ident>*);
       'Kwd ":"         (*let <ident> ^ :*);
       typ = parse_expr (*let <ident> : ^ <expr>*);
       'Kwd ":="        (*let <ident> : <expr> ^ :=*);
       arg = parse_expr (*let ... := ^ <expr>*);
        'Kwd "in"       (*let ... := <expr> ^ in*);
       trm = parse_expr (*let ... in ^ <expr>*)
    >] -> APP (ABS (x,typ,trm), arg)

  | [< 'Kwd "(" ; r = parse_expr1 (*( ^ (<ident>|<expr>)*) >] -> r

  | [< at = parse_atom; r = (parse_expr2 at) >] -> r 

and parse_expr1 = parser
    [< 'Kwd "_"; r = (parse_end_pi ["_"]) >] -> r

  | [< 'Ident x; r = (parse_expr3 x) >] -> r

  | [< t1 = parse_expr;
       l = (parse_star parse_expr);
       'Kwd ")"                     (*( <expr>* ^ )*);
       r = (parse_expr2 (List.fold_left (fun t a->APP (t,a)) t1 l))
    >] -> r

and parse_expr2 at = parser
    [< 'Kwd "->";
       t = parse_expr (*( <expr> ) -> ^ <expr>*)
    >] -> PROD ("_",at,t)

  | [< >] -> at

and parse_expr3 x = parser
    [< 'Kwd ",";
       y = anon_var (*( <ident> , ^ (<ident>|_)*);
       r = (parse_end_pi [x;y])
    >] -> r

  | [< 'Kwd ":";
       typ = parse_expr (*( <ident> : ^ <expr>*);
       'Kwd ")"         (*( <ident> : <expr> ^ )*);
       trm = parse_expr (*( ... ) ^ <expr>*)
    >] -> PROD(x,typ,trm)

  | [< 'Kwd "->";
       t = parse_expr               (*( <ident> -> ^ <expr>*);
       l = (parse_star parse_expr)  (*( <ident> -> <expr> ^ <expr>*);
       'Kwd ")"                     (*( <expr>* ^ )*);
       str
    >] -> parse_expr2 (List.fold_left (fun t a->APP(t,a))
                         (PROD ("_",(REF x),t)) l) str

  | [< l = (parse_star parse_expr);
       'Kwd ")"  (*( <expr>* ^ )*);
       str
    >] -> parse_expr2 (List.fold_left (fun t a->APP(t,a)) (REF x) l) str

and parse_end_pi lb = parser
    [< l = (parse_star virg_an_var);
       'Kwd ":"         (*( <ident>* ^ :*);
       typ = parse_expr (*( <ident>* : ^ <expr>*);
       'Kwd ")"         (*( <ident>* : <expr> ^ )*);
       trm = parse_expr (*( ... ) ^ <expr>*)
    >] -> List.fold_right (fun x t->PROD(x,typ,t)) (lb@l) trm
;;


let prompt () = print_string "\nCoc < "; flush stdout;;

let parse_ast strm =
  prompt();
  match strm with parser
      [< 'Kwd "Infer";
         e = parse_expr  (*Infer ^ <expr>*)
      >] -> AST_INFER e

    | [< 'Kwd "Axiom";
         'Ident x        (*Axiom ^ <ident>*);
         'Kwd ":"        (*Axiom <ident> ^ :*);
         e = parse_expr  (*Axiom <ident> : ^ <expr>*)
      >] -> AST_AXIOM(x,e)

    | [< 'Kwd "Check";
         e1 = parse_expr (*Check ^ <expr>*);
         'Kwd ":"        (*Check <expr> ^ :*);
         e2 = parse_expr (*Check <expr> : ^ <expr>*)
      >] -> AST_CHECK(e1,e2)  

    | [< 'Kwd "Delete" >] -> AST_DELETE

    | [< 'Kwd "List" >] -> AST_LIST

    | [< 'Kwd "Quit" >] -> AST_QUIT
;;


(*> affichage *)
let string_of_sort = function 
    Kind -> "Kind"
  | Prop -> "Prop"
  | Set -> "Set"
;;

let rec string_of_expr = function
    SRT s -> string_of_sort s
  | REF x -> x
  | ABS (x,tt,t) -> "["^x^":"^(string_of_expr tt)^"]"^(string_of_expr t)
  | APP (u,v) -> "("^(string_of_app u)^" "^(string_of_expr v)^")"
  | PROD (x,tt,u) ->
      (match is_free_var x u with
          true -> "("^x^":"^(string_of_expr tt)^")"^(string_of_expr u)
        | false -> (string_of_arrow tt)^"->"^(string_of_expr u))

and string_of_app = function
    APP (u,v) -> (string_of_app u)^" "^(string_of_expr v)
  | t -> string_of_expr t

and string_of_arrow = function
    ABS (x0,x1,x2) -> "("^(string_of_expr (ABS (x0,x1,x2)))^")"
  | PROD (x0,x1,x2) -> "("^(string_of_expr (PROD (x0,x1,x2)))^")"
  | t -> string_of_expr t
;;

let print_expr e = print_string (string_of_expr e);;


let rec print_names = function
    Nil -> ()
  | Cons (x,l) ->
      print_names l;
      print_string (x^" ")
;;

(*
let rec print_terms = function
    Nil -> ()
  | Cons(t,l) ->
      print_string "x. : ";
      print_term t;
      print_newline();
      print_terms l
;;

let print_local_ctx = function
    Nil -> print_newline()
  | l ->
      print_endline "Dans le contexte:";
      print_terms l
;;
*)

let print_message = function
    Pnew_axiom x ->
      print_endline (x^" admis.")
  | Pinfered_type e ->
      print_string "Type infere: ";
      print_expr e;
      print_newline()
  | Pcorrect ->
      print_endline "Correct."
  | Pcontext_listing l ->
      print_string "Axiomes: ";
      print_names l;
      print_newline()
  | Pdelete_axiom x ->
      print_endline (x^" supprime.")
  | Pexiting ->
      print_endline "\nAu revoir..."; exit 0
;;

let rec print_type_err = function
    Punder (x,e,err) ->
      print_string x;
      print_string " : ";
      print_expr e;
      print_newline();
      print_type_err err
  | Pexpected_type(m,at,et) ->
      print_string "Le terme ";
      print_expr m;
      print_string " a le type ";
      print_expr at;
      print_string " mais est utilise avec le type ";
      print_expr et;
      print_endline "."
  | Pkind_ill_typed ->
      print_endline "Kind est mal type."
  | Pdb_error n ->
      print_string "Variable de de Bruijn #";
      print_int (int_of_nat n);
      print_endline " libre."
  | Plambda_kind t ->
      print_string "Le terme ";
      print_expr t;
      print_endline " est une abstraction sur une kind."
  | Pnot_a_type(m,t) ->
      print_string "Le type de ";
      print_expr m;
      print_string ", qui est ";
      print_expr t;
      print_endline " ne se reduit pas vers une sorte."
  | Pnot_a_fun(m,t) ->
      print_string "Le type de ";
      print_expr m;
      print_string ", qui est ";
      print_expr t;
      print_endline " ne se reduit pas vers un produit."
  | Papply_err(u,tu,v,tv) ->
      print_string "Le terme ";
      print_expr u;
      print_string " de type ";
      print_expr tu;
      print_string " ne peut etre applique a ";
      print_expr v;
      print_string " qui a pour type ";
      print_expr tv;
      print_endline "."
;;

let print_type_error err =
  begin
    match err with
        Punder _ ->
          print_endline "Dans le contexte:";
      | _ -> ()
  end;
  print_type_err err
;;


let print_error = function
    Punbound_vars l ->
      print_string "Variables inconnues: [ ";
      print_names l;
      print_endline "]."
  | Pname_clash x ->
      print_endline ("Nom "^x^" deja utilise.")
  | Ptype_error te ->
      print_type_error te
  | Pcannot_delete ->
      print_endline "Contexte deja vide."
;;



(*> encapsulation de l'etat *)
let update_state = 
  let state = ref empty_state in
    (fun ast -> 
       match (interp_ast !state ast) with
           Inl(Pair(ns,msg)) ->
             print_message msg;
             state := ns
         | Inr err ->
             print_string "Erreur: ";
             print_error err)
;;


(*> boucle toplevel *)


let rec discarder stk strm =
  let head_tok =
    try
      match strm with parser
        | [< 't >] -> Some t
        | [< >] -> None
    with
        Stream.Error s when (* lexer error *)
          (String.sub s 0 17) = "Illegal character"
                                -> Some (Char s.[18])
  in
    match head_tok with
        Some (Kwd ".") -> List.rev ((Kwd ".")::stk)
      | Some tok -> discarder (tok::stk) strm
      | None -> []
;;

let skip_til_dot err_msg strm =
  let toklst = discarder [] strm in
    if toklst <> [] then
      begin
        print_string "\nDiscarding ";
        List.iter
          (fun tok -> print_string ((string_of_token tok)^" ")) toklst
      end;
    print_string "\nErreur de syntaxe: ";
    print_endline err_msg
;;

let rec parse_strm strm =
  try
    match strm with parser
        [< ast = parse_ast; 'Kwd "." (*<command> ^ .*); strm >] ->
          [< 'ast; parse_strm strm >]
      | [< _ = Stream.empty >] -> [< >]
  with 
      Stream.Failure -> 
        skip_til_dot "^ <command>" strm;
        parse_strm strm
    | Stream.Error s ->
        skip_til_dot s strm;
        parse_strm strm
;;

let go () =
  let ast_strm = parse_strm (lexer (Stream.of_channel stdin)) in
    Stream.iter update_state ast_strm;
    print_endline "EOF!";
    flush stdout
;;

go();;
