(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)



Require Import Termes.
Require Import Conv.
Require Import Types.
Require Import Conv_Dec.
Require Import Infer.
Require Import Expr.


  Record state : Set := 
    {glob_ctx : env;
     glob_names : prt_names;
     glob_wf_ctx : wf glob_ctx;
     glob_length : length glob_ctx = length glob_names;
     glob_unique : name_unique glob_names}.

  Hint Resolve glob_wf_ctx glob_unique: coc.


  Definition empty_state : state.
refine (Build_state nil nil _ _ _); auto with coc core arith datatypes.
exact wf_nil.

red in |- *; intros.
inversion H.
Defined.


  Record state_ext (x : name) (t : term) (s0 s1 : state) : Prop := 
    {cons_env : glob_ctx s1 = t :: glob_ctx s0;
     cons_names : glob_names s1 = x :: glob_names s0}.



  (* internal level *)
  Inductive command : Set :=
    | INFER : term -> command
    | CHECK : term -> term -> command
    | AXIOM : name -> term -> command
    | DELETE : command
    | LIST : command
    | QUIT : command.

  Inductive message : Set :=
    | New_axiom : name -> message
    | Infered_type : term -> message
    | Correct : message
    | Delete_axiom : name -> message
    | Context_listing : prt_names -> message
    | Exiting : message.

  Inductive error : Set :=
    | Name_clash : name -> error
    | Type_error : type_error -> error
    | Cannot_delete : error.


  (* external level *)
  Inductive ast : Set :=
    | AST_INFER : expr -> ast
    | AST_CHECK : expr -> expr -> ast
    | AST_AXIOM : name -> expr -> ast
    | AST_DELETE : ast
    | AST_LIST : ast
    | AST_QUIT : ast.

  Inductive expr_of_ast : ast -> expr -> Prop :=
    | ea_inf : forall e : expr, expr_of_ast (AST_INFER e) e
    | ea_chk1 : forall e1 e2 : expr, expr_of_ast (AST_CHECK e1 e2) e1
    | ea_chk2 : forall e1 e2 : expr, expr_of_ast (AST_CHECK e1 e2) e2
    | ea_ax : forall (x : name) (e : expr), expr_of_ast (AST_AXIOM x e) e.

  Hint Resolve ea_inf ea_chk1 ea_chk2 ea_ax: coc.

  (* printable messages *)
  Inductive pmessage : Set :=
    | Pnew_axiom : name -> pmessage
    | Pinfered_type : expr -> pmessage
    | Pcorrect : pmessage
    | Pcontext_listing : prt_names -> pmessage
    | Pdelete_axiom : name -> pmessage
    | Pexiting : pmessage.


  (* printable type errors *)
  Inductive ptype_error : Set :=
    | Punder : name -> expr -> ptype_error -> ptype_error
    | Pexpected_type : expr -> expr -> expr -> ptype_error
    | Pkind_ill_typed : ptype_error
    | Pdb_error : nat -> ptype_error
    | Plambda_kind : expr -> ptype_error
    | Pnot_a_type : expr -> expr -> ptype_error
    | Pnot_a_fun : expr -> expr -> ptype_error
    | Papply_err : expr -> expr -> expr -> expr -> ptype_error.

  (* printable errors *)
  Inductive perror : Set :=
    | Punbound_vars : prt_names -> perror
    | Pname_clash : name -> perror
    | Ptype_error : ptype_error -> perror
    | Pcannot_delete : perror.


  (* command translated to the internal level *)
  Inductive synthesis_trans (s : state) : ast -> command -> Prop :=
    | Sy_infer :
        forall (e : expr) (t : term),
        term_expr_equiv (glob_names s) t e ->
        synthesis_trans s (AST_INFER e) (INFER t)
    | Sy_check :
        forall (e1 e2 : expr) (m t : term),
        term_expr_equiv (glob_names s) m e1 ->
        term_expr_equiv (glob_names s) t e2 ->
        synthesis_trans s (AST_CHECK e1 e2) (CHECK m t)
    | Sy_axiom :
        forall (x : name) (e : expr) (t : term),
        term_expr_equiv (glob_names s) t e ->
        synthesis_trans s (AST_AXIOM x e) (AXIOM x t)
    | Sy_delete : synthesis_trans s AST_DELETE DELETE
    | Sy_list : synthesis_trans s AST_LIST LIST
    | Sy_quit : synthesis_trans s AST_QUIT QUIT.

  Hint Resolve Sy_infer Sy_check Sy_axiom Sy_delete Sy_list Sy_quit: coc.


  (* commands *)
  Inductive transition (s1 : state) : command -> state -> message -> Prop :=
    | Tr_infer :
        forall m t : term,
        typ (glob_ctx s1) m t -> transition s1 (INFER m) s1 (Infered_type t)
    | Tr_check :
        forall m t : term,
        typ (glob_ctx s1) m t -> transition s1 (CHECK m t) s1 Correct
    | Tr_axiom :
        forall (x : name) (t : term) (s2 : state),
        glob_ctx s2 = t :: glob_ctx s1 ->
        glob_names s2 = x :: glob_names s1 ->
        transition s1 (AXIOM x t) s2 (New_axiom x)
    | Tr_delete :
        forall (x : name) (s2 : state),
        x :: glob_names s2 = glob_names s1 ->
        transition s1 DELETE s2 (Delete_axiom x)
    | Tr_list : transition s1 LIST s1 (Context_listing (glob_names s1))
    | Tr_quit : transition s1 QUIT s1 Exiting.

  Hint Resolve Tr_infer Tr_check Tr_axiom Tr_delete Tr_list Tr_quit: coc.



  (* translation of messages *)
  Inductive transl_msg (s : state) : message -> pmessage -> Prop :=
    | Tm_infer :
        forall (t : term) (e : expr),
        term_expr_equiv (glob_names s) t e ->
        transl_msg s (Infered_type t) (Pinfered_type e)
    | Tm_check : transl_msg s Correct Pcorrect
    | Tm_axiom : forall x : name, transl_msg s (New_axiom x) (Pnew_axiom x)
    | Tm_delete :
        forall x : name, transl_msg s (Delete_axiom x) (Pdelete_axiom x)
    | Tm_listing :
        forall l : prt_names,
        transl_msg s (Context_listing l) (Pcontext_listing l)
    | Tm_exit : transl_msg s Exiting Pexiting.

  Hint Resolve Tm_infer Tm_check Tm_axiom Tm_delete Tm_listing Tm_exit: coc.




  (* ERRORS *)

  (* errors occuring during synthesis *)
  Inductive synth_error (s : state) : ast -> perror -> Prop :=
      Syf_db_failed :
        forall (a : ast) (e : expr) (undef : prt_names),
        expr_of_ast a e ->
        undef_vars e (glob_names s) undef ->
        undef <> nil -> synth_error s a (Punbound_vars undef).


  (* errors of internal commands *)
  Inductive com_error (s : state) : command -> error -> Prop :=
    | Ce_inf_error :
        forall (m : term) (err : type_error),
        inf_error m err ->
        expln (glob_ctx s) err -> com_error s (INFER m) (Type_error err)
    | Ce_chk_error :
        forall (m t : term) (err : type_error),
        chk_error m t err ->
        expln (glob_ctx s) err -> com_error s (CHECK m t) (Type_error err)
    | Ce_decl_error :
        forall (x : name) (m : term) (err : type_error),
        decl_error m err ->
        expln (glob_ctx s) err -> com_error s (AXIOM x m) (Type_error err)
    | Ce_axiom :
        forall (x : name) (t : term),
        In _ x (glob_names s) -> com_error s (AXIOM x t) (Name_clash x)
    | Ce_delete : glob_names s = nil -> com_error s DELETE Cannot_delete.

  Hint Resolve Ce_inf_error Ce_chk_error Ce_decl_error Ce_axiom Ce_delete:
    coc.


  (* translation of type_errors *)
  Inductive transl_type_error :
  prt_names -> ptype_error -> type_error -> Prop :=
    | Tpe_under :
        forall (l : prt_names) (x : name) (t : term) (e : expr),
        ~ In name x l ->
        term_expr_equiv l t e ->
        forall (perr : ptype_error) (err : type_error),
        transl_type_error (x :: l) perr err ->
        transl_type_error l (Punder x e perr) (Under t err)
    | Tpe_exp_type :
        forall (l : prt_names) (t0 t1 t2 : term) (e0 e1 e2 : expr),
        term_expr_equiv l t0 e0 ->
        term_expr_equiv l t1 e1 ->
        term_expr_equiv l t2 e2 ->
        transl_type_error l (Pexpected_type e0 e1 e2)
          (Expected_type t0 t1 t2)
    | Tpe_is_kind :
        forall l : prt_names,
        transl_type_error l Pkind_ill_typed Kind_ill_typed
    | Tpe_db_error :
        forall (l : prt_names) (n : nat),
        transl_type_error l (Pdb_error n) (Db_error n)
    | Tpe_lam_kind :
        forall (l : prt_names) (t : term) (e : expr),
        term_expr_equiv l t e ->
        transl_type_error l (Plambda_kind e) (Lambda_kind t)
    | Tpe_not_a_type :
        forall (l : prt_names) (t0 t1 : term) (e0 e1 : expr),
        term_expr_equiv l t0 e0 ->
        term_expr_equiv l t1 e1 ->
        transl_type_error l (Pnot_a_type e0 e1) (Not_a_type t0 t1)
    | Tpe_not_a_fun :
        forall (l : prt_names) (t0 t1 : term) (e0 e1 : expr),
        term_expr_equiv l t0 e0 ->
        term_expr_equiv l t1 e1 ->
        transl_type_error l (Pnot_a_fun e0 e1) (Not_a_fun t0 t1)
    | Tpe_apply_err :
        forall (l : prt_names) (t0 t1 t2 t3 : term) (e0 e1 e2 e3 : expr),
        term_expr_equiv l t0 e0 ->
        term_expr_equiv l t1 e1 ->
        term_expr_equiv l t2 e2 ->
        term_expr_equiv l t3 e3 ->
        transl_type_error l (Papply_err e0 e1 e2 e3) (Apply_err t0 t1 t2 t3).

  Hint Resolve Tpe_exp_type Tpe_is_kind Tpe_db_error Tpe_lam_kind
    Tpe_not_a_type Tpe_not_a_fun Tpe_apply_err: coc.


  (* translation of internal errors to the external level *)
  Inductive transl_err (s : state) : error -> perror -> Prop :=
    | Te_name_clash :
        forall x : name, transl_err s (Name_clash x) (Pname_clash x)
    | Te_type_error :
        forall (e : type_error) (pe : ptype_error),
        transl_type_error (glob_names s) pe e ->
        transl_err s (Type_error e) (Ptype_error pe)
    | Te_cannot_delete : transl_err s Cannot_delete Pcannot_delete.

  Hint Resolve Te_name_clash Te_type_error Te_cannot_delete: coc.




  (* global architecture *)

  Lemma trans_error_no_confusion :
   forall (si sf : state) (c : command) (m : message) (err : error),
   transition si c sf m -> com_error si c err -> False.
simple induction 1; intros.
inversion_clear H1.
elim inf_error_no_type with m0 err0 (glob_ctx si) t;
 auto with coc core arith datatypes.

inversion_clear H1.
elim chk_error_no_type with (glob_ctx si) m0 t err0;
 auto with coc core arith datatypes.

inversion_clear H2.
elim decl_err_not_wf with (glob_ctx si) t err0;
 auto with coc core arith datatypes.
elim H0.
apply glob_wf_ctx.

cut (exists n : nat, item _ x (glob_names si) n); intros.
inversion_clear H2.
absurd (0 = S x0); auto with coc core arith datatypes.
generalize (glob_unique s2).
unfold name_unique in |- *; intros.
apply H2 with x.
rewrite H1; auto with coc core arith datatypes.

rewrite H1; auto with coc core arith datatypes.

elim H3; intros.
split with 0; auto with coc core arith datatypes.

inversion_clear H4.
split with (S x0); auto with coc core arith datatypes.

inversion_clear H1.
rewrite H2 in H0.
discriminate H0.

inversion_clear H0.

inversion_clear H0.
Qed.



  Inductive top_trans (si : state) (a : ast) (sf : state) 
  (m : pmessage) : Prop :=
      Top_int :
        forall (c : command) (im : message),
        synthesis_trans si a c ->
        transition si c sf im
        (* the message should be understandable in initial state! *)
         -> transl_msg si im m -> top_trans si a sf m.


  Inductive top_error (si : state) (a : ast) (e : perror) : Prop :=
    | Te_sy : synth_error si a e -> top_error si a e
    | Te_int :
        forall (c : command) (ie : error),
        synthesis_trans si a c ->
        com_error si c ie -> transl_err si ie e -> top_error si a e.

  Hint Resolve Te_sy: coc.


  Lemma synth_no_confusion :
   forall (si : state) (a : ast) (c : command) (e : perror),
   synthesis_trans si a c -> synth_error si a e -> False.
simple induction 1; intros.
inversion_clear H1.
apply H4.
apply equiv_no_undef with (glob_names si) t e0;
 auto with coc core arith datatypes.
inversion_clear H2; auto with coc core arith datatypes.

inversion_clear H2.
apply H5.
generalize H0 H1.
inversion_clear H3; intros.
apply equiv_no_undef with (glob_names si) m e0;
 auto with coc core arith datatypes.

apply equiv_no_undef with (glob_names si) t e0;
 auto with coc core arith datatypes.

inversion_clear H1.
apply H4.
apply equiv_no_undef with (glob_names si) t e0;
 auto with coc core arith datatypes.
inversion_clear H2; auto with coc core arith datatypes.

inversion_clear H0.
inversion_clear H1.

inversion_clear H0.
inversion_clear H1.

inversion_clear H0.
inversion_clear H1.
Qed.


  Lemma synth_deterministic :
   forall (si : state) (a : ast) (c d : command),
   synthesis_trans si a c -> synthesis_trans si a d -> c = d.
simple induction 1; intros.
inversion_clear H1.
elim equiv_unique with (glob_names si) t e t0;
 auto with coc core arith datatypes.

inversion_clear H2.
elim equiv_unique with (glob_names si) m e1 m0;
 auto with coc core arith datatypes.
elim equiv_unique with (glob_names si) t e2 t0;
 auto with coc core arith datatypes.

inversion_clear H1.
elim equiv_unique with (glob_names si) t e t0;
 auto with coc core arith datatypes.

inversion_clear H0; auto with coc core arith datatypes.

inversion_clear H0; auto with coc core arith datatypes.

inversion_clear H0; auto with coc core arith datatypes.
Qed.



  Lemma top_trans_error_no_confusion :
   forall (si sf : state) (a : ast) (m : pmessage) (perr : perror),
   top_trans si a sf m -> top_error si a perr -> False.
simple induction 1; intros.
inversion_clear H3.
apply synth_no_confusion with si a c perr; auto with coc core arith datatypes.

apply trans_error_no_confusion with si sf c im ie;
 auto with coc core arith datatypes.
elim synth_deterministic with si a c0 c; auto with coc core arith datatypes.
Qed.


  Definition answer (si : state) (a : ast) : Set :=
    ({p : state * pmessage |
     match p with
     | (sf, m) => top_trans si a sf m
     end} + {err : perror | top_error si a err})%type.




  Definition synth_answer (si : state) (a : ast) : Set :=
    ({c : command | synthesis_trans si a c} +
     {err : perror | synth_error si a err})%type.

  Definition synthesis : forall (si : state) (a : ast), synth_answer si a.
(*
Realizer [si:state][a:ast]
  Cases a of
    (AST_INFER e) => Cases (term_of_expr e (glob_names si)) of
            (inl t) => (inl ? perror (INFER t))
          | (inr u) => (inr command ? (Punbound_vars u))
          end
  | (AST_CHECK e1 e2) => Cases (term_of_expr e1 (glob_names si))
                               (term_of_expr e2 (glob_names si)) of
            (inl m) (inl t) => (inl ? perror (CHECK m t))
          | (inr u1) _ => (inr command ? (Punbound_vars u1))
          | _ (inr u2) => (inr command ? (Punbound_vars u2))
          end
  | (AST_AXIOM x e) => Cases (term_of_expr e (glob_names si)) of
            (inl t) => (inl ? perror (AXIOM x t))
          | (inr u) => (inr command ? (Punbound_vars u))
          end
  | AST_DELETE => (inl ? perror DELETE)
  | AST_LIST => (inl ? perror LIST)
  | AST_QUIT => (inl ? perror QUIT)
  end.
*)
simple destruct a; intros.
elim (term_of_expr e (glob_names si)); intros.
left.
inversion_clear a0.
exists (INFER x); auto with coc core arith datatypes.

right.
inversion_clear b.
exists (Punbound_vars x); auto with coc core arith datatypes.
apply Syf_db_failed with e; auto with coc core arith datatypes.

elim (term_of_expr e (glob_names si)); intros.
inversion_clear a0.
elim (term_of_expr e0 (glob_names si)); intros.
left.
inversion_clear a0.
exists (CHECK x x0); auto with coc core arith datatypes.

right.
inversion_clear b.
exists (Punbound_vars x0); auto with coc core arith datatypes.
apply Syf_db_failed with e0; auto with coc core arith datatypes.

right.
inversion_clear b.
exists (Punbound_vars x); auto with coc core arith datatypes.
apply Syf_db_failed with e; auto with coc core arith datatypes.

elim (term_of_expr e (glob_names si)); intros.
left.
inversion_clear a0.
exists (AXIOM n x); auto with coc core arith datatypes.

right.
inversion_clear b.
exists (Punbound_vars x); auto with coc core arith datatypes.
apply Syf_db_failed with e; auto with coc core arith datatypes.

left.
exists DELETE; auto with coc core arith datatypes.

left.
exists LIST; auto with coc core arith datatypes.

left.
exists QUIT; auto with coc core arith datatypes.
Defined.



  Definition com_answer (si : state) (c : command) : Set :=
    ({p : state * message |
     match p with
     | (sf, m) => transition si c sf m
     end} + {e : error | com_error si c e})%type.


  Definition exec_infer : forall (s : state) (m : term), com_answer s (INFER m).
(*
Realizer
  [s:state][m:term]Cases (infer (glob_ctx s) m) of
    (inl t) => (inl ? error (s,(Infered_type t)))
  | (inr err) => (inr state*message ? (Type_error err))
  end.
*)
intros.
elim infer with (glob_ctx s) m; intros; auto with coc core arith datatypes.
elim a.
intros t H.
left.
exists (s, Infered_type t).
apply Tr_infer; auto with coc core arith datatypes.

right.
inversion_clear b.
exists (Type_error x); auto with coc core arith datatypes.
Defined.


  Definition exec_check :
   forall (s : state) (m t : term), com_answer s (CHECK m t).
(*
Realizer
  [s:state][m,t:term]Cases (check_typ (glob_ctx s) m t) of
    (inleft err) => (inr state*message ? (Type_error err))
  | inright => (inl ? error (s,Correct))
  end.
*)
intros.
elim check_typ with (glob_ctx s) m t; intros;
 auto with coc core arith datatypes.
right.
inversion_clear a.
exists (Type_error x); auto with coc core arith datatypes.

left.
exists (s, Correct); auto with coc core arith datatypes.
Defined.


  Definition exec_axiom :
   forall (s : state) (x : name) (t : term), com_answer s (AXIOM x t).
(*
Realizer
  [s:state][x:name][t:term]Cases (add_typ (glob_ctx s) t)
                                 (list_index ? name_dec x (glob_names s)) of
    left inright => (NewState 
                           (Build_state (cons (Ax t) (glob_ctx s))
                                        (cons x (glob_names s)))
                           (Pnew_axiom x))
  | left (inleft _) => (Failed (Pname_clash x))
  | right _ => (Failed (Ptype_error terr))
  end.
*)
intros.
elim (add_typ (glob_ctx s) t); intros; auto with coc core arith datatypes.
right.
inversion_clear a.
exists (Type_error x0); auto with coc core arith datatypes.

elim (list_index _ name_dec x (glob_names s)); intros.
right.
exists (Name_clash x); auto with coc core arith datatypes.
inversion_clear a.
apply Ce_axiom.
elim H; auto with coc core arith datatypes.

left.
(*
Refine (exist state*message
    [p:?]
     Cases p of 
     
       (pair dum_sf dum_m)  => (transition s (AXIOM x t) dum_sf dum_m)
     end
    ((Build_state (cons term t (glob_ctx s))
       (cons x (glob_names s)) ? ? ?),(New_axiom x)) ?).
*)
cut (name_unique (x :: glob_names s)); intros.
cut (length (t :: glob_ctx s) = length (x :: glob_names s)); intros.
exists
 (Build_state (t :: glob_ctx s) (x :: glob_names s) b H0 H, New_axiom x);
 auto with coc core arith datatypes.

simpl in |- *.
elim glob_length with s; auto with coc core arith datatypes.

apply fv_ext; auto with coc core arith datatypes.
Defined.



  Definition exec_delete : forall s : state, com_answer s DELETE.
(*
Realizer [s:state]Cases (glob_ctx s) (glob_names s) of
    (cons _ e) (cons x l) => (NewState (Build_state e l) (Delete_axiom x))
  | _          _          => (Failed Pcannot_delete)
  end.
*)
intros.
generalize (refl_equal (glob_names s)).
pattern (glob_names s) at 1 in |- *.
case (glob_names s); intros.
right.
exists Cannot_delete; auto with coc core arith datatypes.

generalize (refl_equal (glob_ctx s)).
pattern (glob_ctx s) at 1 in |- *.
case (glob_ctx s); intros.
generalize (glob_length s).
elim H.
elim H0; simpl in |- *; intros.
discriminate H1.

cut (length l0 = length l); intros.
cut (name_unique l); intros.
cut (wf l0); intros.
left.
exists (Build_state l0 l H3 H1 H2, Delete_axiom n);
 auto with coc core arith datatypes.

generalize (glob_wf_ctx s).
elim H0; intros.
inversion_clear H3.
apply typ_wf with t (Srt s0); auto with coc core arith datatypes.

generalize (glob_unique s).
elim H.
unfold name_unique in |- *; intros.
cut (S m = S n0); intros.
injection H5; auto with coc core arith datatypes.

apply H2 with x; auto with coc core arith datatypes.

generalize (glob_length s).
elim H.
elim H0; simpl in |- *; intros.
injection H1; auto with coc core arith datatypes.
Defined.



  Definition interp_command : forall (si : state) (c : command), com_answer si c.
simple induction c.
exact (exec_infer si).
exact (exec_check si).
exact (exec_axiom si).
exact (exec_delete si).
left; exists (si, Context_listing (glob_names si)); auto with coc.
left; exists (si, Exiting); auto with coc.

(*
Realizer [si:state][c:command]
  Cases c of
    (INFER t) => (exec_infer si t)
  | (CHECK m t) => (exec_check si m t)
  | (AXIOM x t) => (exec_axiom si x t)
  | DELETE => (exec_delete si)
  | LIST => (inl ? error (si,(Context_listing (glob_names si))))
  | QUIT => (inl ? error (si,Exiting))
  end.
Program_all. 
*)
Defined.


  Definition transl_message :
   forall (s : state) (im : message),
   (exists c : command, (exists sf : state, transition s c sf im)) ->
   {m : pmessage | transl_msg s im m}.
simple induction im.
intro x; exists (Pnew_axiom x); auto with coc.
intros t H; elim (expr_of_term t (glob_names s)); auto with coc.
intros; exists (Pinfered_type x); auto with coc.
inversion_clear H.
inversion_clear H0.
inversion_clear H.
elim glob_length.
apply type_free_db with m; auto.
exists Pcorrect; auto with coc.
intro x; exists (Pdelete_axiom x); auto with coc.
intro l; exists (Pcontext_listing l); auto with coc.
exists Pexiting; auto with coc.
Defined.



  Definition transl_ty_error :
   forall (err : type_error) (s : state),
   expln (glob_ctx s) err ->
   {perr : ptype_error | transl_type_error (glob_names s) perr err}.
simple induction err; intros.
elim find_free_var with (glob_names s); intros.
elim expr_of_term with t (glob_names s); intros;
 auto with coc core arith datatypes.
elimtype {si : state | state_ext x t s si}; intros.
elim H with x1; intros.
exists (Punder x x0 x2).
apply Tpe_under; auto with coc core arith datatypes.
elim cons_names with x t s x1; auto with coc core arith datatypes.

inversion_clear H0.
rewrite (cons_env x t s x1); auto with coc core arith datatypes.

cut (wf (t :: glob_ctx s)); intros.
cut (S (length (glob_ctx s)) = S (length (glob_names s))); intros.
cut (name_unique (x :: glob_names s)); intros.
exists (Build_state (t :: glob_ctx s) (x :: glob_names s) H1 H2 H3).
split; auto with coc core arith datatypes.

apply fv_ext; auto with coc core arith datatypes.

elim glob_length with s; auto with coc core arith datatypes.

inversion_clear H0; auto with coc core arith datatypes.
apply expln_wf with t0; auto with coc core arith datatypes.

inversion_clear H0.
elim glob_length with s; auto with coc core arith datatypes.
cut (wf (t :: glob_ctx s)); intros.
inversion_clear H0.
apply typ_free_db with (Srt s0); auto with coc core arith datatypes.

apply expln_wf with t0; auto with coc core arith datatypes.

elim expr_of_term with t (glob_names s); intros;
 auto with coc core arith datatypes.
elim expr_of_term with t0 (glob_names s); intros;
 auto with coc core arith datatypes.
elim expr_of_term with t1 (glob_names s); intros;
 auto with coc core arith datatypes.
exists (Pexpected_type x x0 x1); auto with coc core arith datatypes.

inversion_clear H.
elim glob_length with s.
auto with coc core arith datatypes.

inversion_clear H.
elim glob_length with s.
apply type_free_db with t; auto with coc core arith datatypes.

inversion_clear H.
elim glob_length with s.
apply typ_free_db with t0; auto with coc core arith datatypes.

exists Pkind_ill_typed; auto with coc core arith datatypes.

exists (Pdb_error n); auto with coc core arith datatypes.

elim expr_of_term with t (glob_names s); intros;
 auto with coc core arith datatypes.
exists (Plambda_kind x); auto with coc core arith datatypes.

inversion_clear H.
elim glob_length with s.
apply db_abs.
cut (wf (t0 :: glob_ctx s)); intros.
inversion_clear H.
apply typ_free_db with (Srt s0); auto with coc core arith datatypes.

apply typ_wf with m (Srt kind); auto with coc core arith datatypes.

change (free_db (length (t0 :: glob_ctx s)) m) in |- *.
apply typ_free_db with (Srt kind); auto with coc core arith datatypes.

elim expr_of_term with t (glob_names s); intros;
 auto with coc core arith datatypes.
elim expr_of_term with t0 (glob_names s); intros;
 auto with coc core arith datatypes.
exists (Pnot_a_type x x0); auto with coc core arith datatypes.

inversion_clear H.
elim glob_length with s.
apply type_free_db with t; auto with coc core arith datatypes.

inversion_clear H.
elim glob_length with s.
apply typ_free_db with t0; auto with coc core arith datatypes.

elim expr_of_term with t (glob_names s); intros;
 auto with coc core arith datatypes.
elim expr_of_term with t0 (glob_names s); intros;
 auto with coc core arith datatypes.
exists (Pnot_a_fun x x0); auto with coc core arith datatypes.

inversion_clear H.
elim glob_length with s.
apply type_free_db with t; auto with coc core arith datatypes.

inversion_clear H.
elim glob_length with s.
apply typ_free_db with t0; auto with coc core arith datatypes.

elim expr_of_term with t (glob_names s); intros;
 auto with coc core arith datatypes.
elim expr_of_term with t0 (glob_names s); intros;
 auto with coc core arith datatypes.
elim expr_of_term with t1 (glob_names s); intros;
 auto with coc core arith datatypes.
elim expr_of_term with t2 (glob_names s); intros;
 auto with coc core arith datatypes.
exists (Papply_err x x0 x1 x2); auto with coc core arith datatypes.

inversion_clear H.
elim glob_length with s.
apply type_free_db with t1; auto with coc core arith datatypes.

inversion_clear H.
elim glob_length with s.
apply typ_free_db with t2; auto with coc core arith datatypes.

inversion_clear H.
elim glob_length with s.
apply type_free_db with t; auto with coc core arith datatypes.

inversion_clear H.
elim glob_length with s.
apply typ_free_db with (Prod a b); auto with coc core arith datatypes.
Defined.


  Definition transl_error :
   forall (s : state) (err : error),
   (forall terr : type_error,
    err = Type_error terr -> expln (glob_ctx s) terr) ->
   {perr : perror | transl_err s err perr}.
Proof.
simple induction err.
intro x; exists (Pname_clash x); auto with coc.
intros er H; elim (transl_ty_error er s); auto with coc.
intros terr H0; exists (Ptype_error terr); auto with coc.
exists Pcannot_delete; auto with coc.

(* 
Realizer [s:state][err:error]
  Cases err of
    (Name_clash x) => (Pname_clash x)
  | (Type_error er) => (Ptype_error (transl_ty_error er s)) 
  | Cannot_delete => Pcannot_delete
  end.
Program_all.
*)
Defined.


  Definition interp_ast : forall (si : state) (a : ast), answer si a.
(*
Realizer [si:state][a:ast]
  Cases (synthesis si a) of
    (inl c) => Cases (interp_command si c) of
                 (inl (sf,im)) => (inl ? perror (sf, (transl_message si im))) 
               | (inr ie) => (inr state*pmessage ? (transl_error si ie))
               end
  | (inr err) => (inr state*pmessage ? err)
  end.
*)
intros.
elim synthesis with si a; intros.
elim a0; intros c H.
elim interp_command with si c; intros.
elim a1; simple destruct x; intros.
elim transl_message with si m; intros.
left.
exists (s, x0); auto with coc core arith datatypes.
apply Top_int with c m; auto with coc core arith datatypes.

exists c; exists s; auto with coc core arith datatypes.

right.
inversion_clear b.
elim transl_error with si x; intros.
exists x0.
apply Te_int with c x; auto with coc core arith datatypes.

rewrite H1 in H0.
inversion_clear H0; auto with coc core arith datatypes.

right.
inversion_clear b.
exists x; auto with coc core arith datatypes.
Defined.
