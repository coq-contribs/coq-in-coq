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



Require Import MyList.
Require Import Termes.
Require Export Names.

  (* external level *)

  Inductive expr : Set :=
    | SRT : sort -> expr
    | REF : name -> expr
    | ABS : name -> expr -> expr -> expr
    | APP : expr -> expr -> expr
    | PROD : name -> expr -> expr -> expr.


  Inductive expr_vars (x : name) : expr -> Prop :=
    | ev_ref : expr_vars x (REF x)
    | ev_abs_l :
        forall (y : name) (T M : expr),
        expr_vars x T -> expr_vars x (ABS y T M)
    | ev_abs_r :
        forall (y : name) (T M : expr),
        x <> y -> expr_vars x M -> expr_vars x (ABS y T M)
    | ev_app_l : forall u v : expr, expr_vars x u -> expr_vars x (APP u v)
    | ev_app_r : forall u v : expr, expr_vars x v -> expr_vars x (APP u v)
    | ev_prod_l :
        forall (y : name) (T U : expr),
        expr_vars x T -> expr_vars x (PROD y T U)
    | ev_prod_r :
        forall (y : name) (T U : expr),
        x <> y -> expr_vars x U -> expr_vars x (PROD y T U).

  Hint Resolve ev_ref ev_abs_l ev_abs_r ev_app_l ev_app_r ev_prod_l
    ev_prod_r: coc.


  Lemma is_free_var :
   forall (x : name) (e : expr), {expr_vars x e} + {~ expr_vars x e}.

simple induction e.
right; red in |- *; intros; inversion H.

intro y; case (name_dec x y); intros; [ left | right ].
rewrite e0; auto with coc.
red in |- *; intros A; inversion A; auto.
                    
intros y t H u H1.
elim H; intros;
 [ idtac | elim (name_dec x y); intros; [ idtac | elim H1; intros ] ];
 auto with coc; right; red in |- *; intros A; inversion A; 
 auto.

intros u H v H1.
elim H; intros; [ idtac | elim H1; intros ]; auto with coc; right;
 red in |- *; intros A; inversion A; auto.

intros y t H u H1.
elim H; intros;
 [ idtac | elim (name_dec x y); intros; [ idtac | elim H1; intros ] ];
 auto with coc; right; red in |- *; intros A; inversion A; 
 auto.

Qed.





  Inductive transl_name : list name -> name -> list name -> name -> Prop :=
    | tr_nil : forall x : name, transl_name nil x nil x
    | tr_hd :
        forall (x y : name) (l1 l2 : list name),
        transl_name (x :: l1) x (y :: l2) y
    | tr_tl :
        forall (x x0 y y0 : name) (l1 l2 : list name),
        x <> x0 ->
        y <> y0 ->
        transl_name l1 x l2 y -> transl_name (x0 :: l1) x (y0 :: l2) y.


  Inductive alpha : list name -> expr -> list name -> expr -> Prop :=
    | alp_srt :
        forall (l1 l2 : list name) (s : sort), alpha l1 (SRT s) l2 (SRT s)
    | alp_ref :
        forall (l1 l2 : list name) (x y : name),
        transl_name l1 x l2 y -> alpha l1 (REF x) l2 (REF y)
    | alp_abs :
        forall (l1 l2 : list name) (x y : name) (A A' M M' : expr),
        alpha l1 A l2 A' ->
        alpha (x :: l1) M (y :: l2) M' ->
        alpha l1 (ABS x A M) l2 (ABS y A' M')
    | alp_app :
        forall (l1 l2 : list name) (A A' M M' : expr),
        alpha l1 A l2 A' ->
        alpha l1 M l2 M' -> alpha l1 (APP A M) l2 (APP A' M')
    | alp_prod :
        forall (l1 l2 : list name) (x y : name) (A A' M M' : expr),
        alpha l1 A l2 A' ->
        alpha (x :: l1) M (y :: l2) M' ->
        alpha l1 (PROD x A M) l2 (PROD y A' M').


  (* conversion *)
  Inductive term_expr_equiv : prt_names -> term -> expr -> Prop :=
    | eqv_srt :
        forall (l : prt_names) (s : sort), term_expr_equiv l (Srt s) (SRT s)
    | eqv_ref :
        forall (l : prt_names) (x : name) (n : nat),
        first_item _ x l n -> term_expr_equiv l (Ref n) (REF x)
    | eqv_abs :
        forall (l : prt_names) (A M : term) (B N : expr) (x : name),
        term_expr_equiv l A B ->
        term_expr_equiv (x :: l) M N ->
        term_expr_equiv l (Abs A M) (ABS x B N)
    | eqv_app :
        forall (l : prt_names) (u v : term) (a b : expr),
        term_expr_equiv l u a ->
        term_expr_equiv l v b -> term_expr_equiv l (App u v) (APP a b)
    | eqv_prod :
        forall (l : prt_names) (A M : term) (B N : expr) (x : name),
        term_expr_equiv l A B ->
        term_expr_equiv (x :: l) M N ->
        term_expr_equiv l (Prod A M) (PROD x B N).



  Lemma equiv_free_db :
   forall (l : prt_names) (t : term) (e : expr),
   term_expr_equiv l t e -> free_db (length l) t.
simple induction 1; simpl in |- *; intros; auto with coc core arith datatypes.
apply db_ref.
elim H0; simpl in |- *; auto with coc core arith datatypes.
Qed.


  Lemma equiv_unique :
   forall (l : prt_names) (t : term) (e : expr),
   term_expr_equiv l t e -> forall u : term, term_expr_equiv l u e -> t = u.
simple induction 1; intros.
inversion_clear H0; auto with coc core arith datatypes.

inversion_clear H1.
elim first_item_unique with name x l0 n n0;
 auto with coc core arith datatypes.

inversion_clear H4.
elim H1 with A0; auto with coc core arith datatypes.
elim H3 with M0; auto with coc core arith datatypes.

inversion_clear H4.
elim H1 with u1; auto with coc core arith datatypes.
elim H3 with v0; auto with coc core arith datatypes.

inversion_clear H4.
elim H1 with A0; auto with coc core arith datatypes.
elim H3 with M0; auto with coc core arith datatypes.
Qed.



  Lemma unique_alpha :
   forall (l1 : prt_names) (t : term) (e : expr),
   term_expr_equiv l1 t e ->
   forall (l2 : prt_names) (f : expr),
   term_expr_equiv l2 t f -> alpha l1 e l2 f.
simple induction 1; intros.
inversion_clear H0.
apply alp_srt.

inversion_clear H1.
apply alp_ref.
generalize l2 H2.
elim H0; intros.
inversion_clear H1.
apply tr_hd.

inversion_clear H5.
apply tr_tl; auto with coc core arith datatypes.

inversion_clear H4.
apply alp_abs; auto with coc core arith datatypes.

inversion_clear H4.
apply alp_app; auto with coc core arith datatypes.

inversion_clear H4.
apply alp_prod; auto with coc core arith datatypes.
Qed.



  Theorem expr_of_term :
   forall (t : term) (l : prt_names),
   name_unique l ->
   free_db (length l) t -> {e : expr | term_expr_equiv l t e}.
simple induction t; intros.
exists (SRT s).
apply eqv_srt.

elim (list_item _ l n); intros.
inversion_clear a.
exists (REF x).
apply eqv_ref.
apply name_unique_first; auto with coc core arith datatypes.

elimtype False.
inversion_clear H0.
generalize n b H1.
elim l; simpl in |- *.
intros.
inversion_clear H0.

simple destruct n0; intros.
elim b0 with a; auto with coc core arith datatypes.

apply H0 with n1; auto with coc core arith datatypes.
red in |- *; intros.
elim b0 with t0; auto with coc core arith datatypes.

elim H with l; intros; auto with coc core arith datatypes.
elim find_free_var with l; intros.
elim H0 with (x0 :: l); intros.
exists (ABS x0 x x1).
apply eqv_abs; auto with coc core arith datatypes.

apply fv_ext; auto with coc core arith datatypes.

inversion_clear H2; auto with coc core arith datatypes.

inversion_clear H2; auto with coc core arith datatypes.

elim H with l; intros; auto with coc core arith datatypes.
elim H0 with l; intros; auto with coc core arith datatypes.
exists (APP x x0).
apply eqv_app; auto with coc core arith datatypes.

inversion_clear H2; auto with coc core arith datatypes.

inversion_clear H2; auto with coc core arith datatypes.

elim H with l; intros; auto with coc core arith datatypes.
elim find_free_var with l; intros.
elim H0 with (x0 :: l); intros.
exists (PROD x0 x x1).
apply eqv_prod; auto with coc core arith datatypes.

apply fv_ext; auto with coc core arith datatypes.

inversion_clear H2; auto with coc core arith datatypes.

inversion_clear H2; auto with coc core arith datatypes.
Qed.



  Definition undef_vars (e : expr) (def undef : prt_names) : Prop :=
    list_disjoint _ def undef /\
    (forall x : name, In _ x undef -> expr_vars x e).

  Lemma undef_vars_incl :
   forall (e : expr) (l u1 u2 : prt_names),
   incl _ u1 u2 -> undef_vars e l u2 -> undef_vars e l u1.
unfold undef_vars in |- *; split.
inversion_clear H0.
red in |- *; simpl in |- *; intros.
apply H1 with x; auto with coc core arith datatypes.

inversion_clear H0; auto with coc core arith datatypes.
Qed.



  Lemma undef_vars_abs :
   forall (x : name) (e1 e2 : expr) (l u1 u2 : prt_names),
   undef_vars e1 l u1 ->
   undef_vars e2 (x :: l) u2 -> undef_vars (ABS x e1 e2) l (u1 ++ u2).
split; intros.
inversion_clear H.
inversion_clear H0.
red in |- *; simpl in |- *; intros.
elim In_app with name x0 u1 u2; intros; auto with coc core arith datatypes.
apply H1 with x0; auto with coc core arith datatypes.

apply H with x0; auto with coc core arith datatypes.

inversion_clear H.
inversion_clear H0.
elim In_app with name x0 u1 u2; intros; auto with coc core arith datatypes.
apply ev_abs_r; auto with coc core arith datatypes.
red in |- *; intros.
apply H with x0; auto with coc core arith datatypes.
rewrite H5; auto with coc core arith datatypes.
Qed.


  Lemma undef_vars_app :
   forall (e1 e2 : expr) (l u1 u2 : prt_names),
   undef_vars e1 l u1 ->
   undef_vars e2 l u2 -> undef_vars (APP e1 e2) l (u1 ++ u2).
split; intros.
inversion_clear H.
inversion_clear H0.
red in |- *; simpl in |- *; intros.
elim In_app with name x u1 u2; intros; auto with coc core arith datatypes.
apply H1 with x; auto with coc core arith datatypes.

apply H with x; auto with coc core arith datatypes.

inversion_clear H.
inversion_clear H0.
elim In_app with name x u1 u2; intros; auto with coc core arith datatypes.
Qed.

  Lemma undef_vars_prod :
   forall (x : name) (e1 e2 : expr) (l u1 u2 : prt_names),
   undef_vars e1 l u1 ->
   undef_vars e2 (x :: l) u2 -> undef_vars (PROD x e1 e2) l (u1 ++ u2).
split; intros.
inversion_clear H.
inversion_clear H0.
red in |- *; simpl in |- *; intros.
elim In_app with name x0 u1 u2; intros; auto with coc core arith datatypes.
apply H1 with x0; auto with coc core arith datatypes.

apply H with x0; auto with coc core arith datatypes.

inversion_clear H.
inversion_clear H0.
elim In_app with name x0 u1 u2; intros; auto with coc core arith datatypes.
apply ev_prod_r; auto with coc core arith datatypes.
red in |- *; intros.
apply H with x0; auto with coc core arith datatypes.
rewrite H5; auto with coc core arith datatypes.
Qed.



  Lemma equiv_no_undef :
   forall (l : prt_names) (t : term) (e : expr),
   term_expr_equiv l t e ->
   forall undef : prt_names, undef_vars e l undef -> undef = nil.
simple induction 1; simple destruct undef; intros;
 auto with coc core arith datatypes.
inversion_clear H0.
cut (expr_vars n (SRT s)); intros; auto with coc core arith datatypes.
inversion_clear H0.

inversion_clear H1.
elim H2 with n0; auto with coc core arith datatypes.
cut (expr_vars n0 (REF x)); intros; auto with coc core arith datatypes.
inversion_clear H1.
elim H0; auto with coc core arith datatypes.

inversion_clear H4.
cut (expr_vars n (ABS x B N)); intros; auto with coc core arith datatypes.
cut (n :: nil = nil); intros.
discriminate H7.

inversion_clear H4.
apply H1.
split; intros.
red in |- *; simpl in |- *; intros.
elim H5 with n; auto with coc core arith datatypes.
generalize H4.
inversion_clear H8; auto with coc core arith datatypes.
inversion H9.

generalize H7.
inversion_clear H4; auto with coc core arith datatypes.
inversion H8.

apply H3.
split; intros.
red in |- *; simpl in |- *; intros.
inversion H4.
apply H7.
elim H11.
inversion_clear H9; auto with coc core arith datatypes.
inversion H10.

elim H5 with x0; auto with coc core arith datatypes.
inversion_clear H9; auto with coc core arith datatypes.
inversion H13.

generalize H8.
inversion_clear H4; auto with coc core arith datatypes.
inversion H9.

inversion_clear H4.
cut (expr_vars n (APP a b)); intros; auto with coc core arith datatypes.
cut (n :: nil = nil); intros.
discriminate H7.

inversion_clear H4.
apply H1.
split; intros.
red in |- *; simpl in |- *; intros.
elim H5 with n; auto with coc core arith datatypes.
generalize H4.
inversion_clear H8; auto with coc core arith datatypes.
inversion H9.

generalize H7.
inversion_clear H4; auto with coc core arith datatypes.
inversion H8.

apply H3.
split; intros.
red in |- *; simpl in |- *; intros.
elim H5 with n; auto with coc core arith datatypes.
generalize H4.
inversion_clear H8; auto with coc core arith datatypes.
inversion H9.

generalize H7.
inversion_clear H4; auto with coc core arith datatypes.
inversion H8.

inversion_clear H4.
cut (expr_vars n (PROD x B N)); intros; auto with coc core arith datatypes.
cut (n :: nil = nil); intros.
discriminate H7.

inversion_clear H4.
apply H1.
split; intros.
red in |- *; simpl in |- *; intros.
elim H5 with n; auto with coc core arith datatypes.
generalize H4.
inversion_clear H8; auto with coc core arith datatypes.
inversion H9.

generalize H7.
inversion_clear H4; auto with coc core arith datatypes.
inversion H8.

apply H3.
split; intros.
red in |- *; simpl in |- *; intros.
inversion H4.
apply H7.
elim H11.
inversion_clear H9; auto with coc core arith datatypes.
inversion H10.

elim H5 with x0; auto with coc core arith datatypes.
inversion_clear H9; auto with coc core arith datatypes.
inversion H13.

generalize H8.
inversion_clear H4; auto with coc core arith datatypes.
inversion H9.
Qed.


  Theorem term_of_expr :
   forall (e : expr) (l : prt_names),
   {t : term | term_expr_equiv l t e} +
   {undef : prt_names | undef_vars e l undef &  undef <> nil}.
(*Realizer Fix term_of_expr
  {term_of_expr/1: expr->prt_names->(sum term prt_names) :=
    [e:expr][l:prt_names]Cases e of
      (SRT s) => (inl term prt_names (Srt s))
    | (REF x) => Cases (list_index name name_dec x l) of
             (inleft n) => (inl term prt_names (Ref n))
           | inright => (inr term prt_names (cons x (nil name)))
           end
    | (ABS x e1 e2) =>
           Cases (term_of_expr e1 l) (term_of_expr e2 (cons x l)) of
             (inl a) (inl m) => (inl term prt_names (Abs a m))
           | (inr u1) (inr u2) => (inr term prt_names u1^u2)
           | (inr u) _ => (inr term prt_names u)
           | _ (inr u) => (inr term prt_names u)
           end
    | (APP e1 e2) =>
           Cases (term_of_expr e1 l) (term_of_expr e2 l) of
             (inl u) (inl v) => (inl term prt_names (App u v))
           | (inr u1) (inr u2) => (inr term prt_names u1^u2)
           | (inr u) _ => (inr term prt_names u)
           | _ (inr u) => (inr term prt_names u)
           end
    | (PROD x e1 e2) =>
           Cases (term_of_expr e1 l) (term_of_expr e2 (cons x l)) of
             (inl a) (inl b) => (inl term prt_names (Prod a b))
           | (inr u1) (inr u2) => (inr term prt_names u1^u2)
           | (inr u) _ => (inr term prt_names u)
           | _ (inr u) => (inr term prt_names u)
           end
    end}.
*)
simple induction e; intros.
left.
exists (Srt s).
apply eqv_srt.

elim (list_index _ name_dec n l); intros.
left.
inversion_clear a.
exists (Ref x).
apply eqv_ref; auto with coc core arith datatypes.

right.
exists (n :: nil).
split.
red in |- *; simpl in |- *; intros.
generalize H.
inversion_clear H0.
intros.
elim H0; intros; auto with coc core arith datatypes.

inversion_clear H1.

intros.
inversion_clear H.
apply ev_ref.

inversion_clear H0.

discriminate.

elim H with l; intros.
elim H0 with (n :: l); intros.
left.
inversion_clear a.
inversion_clear a0.
exists (Abs x x0).
apply eqv_abs; auto with coc core arith datatypes.

inversion_clear b.
right.
exists x.
replace x with (nil ++ x); auto with coc core arith datatypes.
apply undef_vars_abs; auto with coc core arith datatypes.
split; intros.
red in |- *; simpl in |- *; intros.
inversion_clear H4.

inversion_clear H3.

auto with coc core arith datatypes.

inversion_clear b.
elim H0 with (n :: l); intros.
right.
exists x; auto with coc core arith datatypes.
apply undef_vars_incl with (x ++ nil).
red in |- *; simpl in |- *; intros.
elim H3; simpl in |- *; auto with coc core arith datatypes.

apply undef_vars_abs; auto with coc core arith datatypes.
split; intros.
red in |- *; simpl in |- *; intros.
inversion_clear H4.

inversion_clear H3.

inversion_clear b.
right.
exists (x ++ x0); intros.
apply undef_vars_abs; auto with coc core arith datatypes.

generalize H2.
case x; simpl in |- *; intros.
elim H5; auto with coc core arith datatypes.

discriminate.

elim H with l; intros.
elim H0 with l; intros.
left.
inversion_clear a.
inversion_clear a0.
exists (App x x0).
apply eqv_app; auto with coc core arith datatypes.

inversion_clear b.
right.
exists x.
replace x with (nil ++ x); auto with coc core arith datatypes.
apply undef_vars_app; auto with coc core arith datatypes.
split; intros.
red in |- *; simpl in |- *; intros.
inversion H4.

inversion H3.

auto with coc core arith datatypes.

inversion_clear b.
elim H0 with l; intros.
right.
exists x; auto with coc core arith datatypes.
apply undef_vars_incl with (x ++ nil).
red in |- *; simpl in |- *; intros.
elim H3; simpl in |- *; auto with coc core arith datatypes.

apply undef_vars_app; auto with coc core arith datatypes.
split; intros.
red in |- *; simpl in |- *; intros.
inversion_clear H4.

inversion_clear H3.

inversion_clear b.
right.
exists (x ++ x0); intros.
apply undef_vars_app; auto with coc core arith datatypes.

generalize H2.
case x; simpl in |- *; intros.
elim H5; auto with coc core arith datatypes.

discriminate.

elim H with l; intros.
elim H0 with (n :: l); intros.
left.
inversion_clear a.
inversion_clear a0.
exists (Prod x x0).
apply eqv_prod; auto with coc core arith datatypes.

inversion_clear b.
right.
exists x.
replace x with (nil ++ x); auto with coc core arith datatypes.
apply undef_vars_prod; auto with coc core arith datatypes.
split; intros.
red in |- *; simpl in |- *; intros.
inversion H4.

inversion H3.

auto with coc core arith datatypes.

inversion_clear b.
elim H0 with (n :: l); intros.
right.
exists x; auto with coc core arith datatypes.
apply undef_vars_incl with (x ++ nil).
red in |- *; simpl in |- *; intros.
elim H3; simpl in |- *; auto with coc core arith datatypes.

apply undef_vars_prod; auto with coc core arith datatypes.
split; intros.
red in |- *; simpl in |- *; intros.
inversion H4.

inversion H3.

inversion_clear b.
right.
exists (x ++ x0); intros.
apply undef_vars_prod; auto with coc core arith datatypes.

generalize H2.
case x; simpl in |- *; intros.
elim H5; auto with coc core arith datatypes.

discriminate.
Qed.
