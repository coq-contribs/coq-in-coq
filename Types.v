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
Require Export MyList.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

  Definition env := list term.

  Implicit Types e f g : env.

  Definition item_lift t e n :=
    ex2 (fun u => t = lift (S n) u) (fun u => item term u (e:list term) n).



Section Typage.

  Inductive wf : env -> Prop :=
    | wf_nil : wf nil
    | wf_var : forall e T s, typ e T (Srt s) -> wf (T :: e)
with typ : env -> term -> term -> Prop :=
  | type_prop : forall e, wf e -> typ e (Srt prop) (Srt kind)
  | type_set : forall e, wf e -> typ e (Srt set) (Srt kind)
  | type_var :
      forall e,
      wf e -> forall (v : nat) t, item_lift t e v -> typ e (Ref v) t
  | type_abs :
      forall e T s1,
      typ e T (Srt s1) ->
      forall M (U : term) s2,
      typ (T :: e) U (Srt s2) ->
      typ (T :: e) M U -> typ e (Abs T M) (Prod T U)
  | type_app :
      forall e v (V : term),
      typ e v V ->
      forall u (Ur : term),
      typ e u (Prod V Ur) -> typ e (App u v) (subst v Ur)
  | type_prod :
      forall e T s1,
      typ e T (Srt s1) ->
      forall (U : term) s2,
      typ (T :: e) U (Srt s2) -> typ e (Prod T U) (Srt s2)
  | type_conv :
      forall e t (U V : term),
      typ e t U -> conv U V -> forall s, typ e V (Srt s) -> typ e t V.

  Hint Resolve wf_nil type_prop type_set type_var: coc.


  Lemma type_prop_set :
   forall s, is_prop s -> forall e, wf e -> typ e (Srt s) (Srt kind).
simple destruct 1; intros; rewrite H0.
apply type_prop; trivial.
apply type_set; trivial.
Qed.

  Lemma typ_free_db : forall e t T, typ e t T -> free_db (length e) t.
simple induction 1; intros; auto with coc core arith datatypes.
inversion_clear H1.
apply db_ref.
elim H3; simpl in |- *; intros; auto with coc core arith datatypes.
Qed.


  Lemma typ_wf : forall e t T, typ e t T -> wf e.
simple induction 1; auto with coc core arith datatypes.
Qed.


  Lemma wf_sort :
   forall n e f,
   trunc _ (S n) e f ->
   wf e -> forall t, item _ t e n -> exists s : sort, typ f t (Srt s).
simple induction n.
do 3 intro.
inversion_clear H.
inversion_clear H0.
intros.
inversion_clear H0.
inversion_clear H.
exists s; auto with coc core arith datatypes.

do 5 intro.
inversion_clear H0.
intros.
inversion_clear H2.
inversion_clear H0.
elim H with e0 f t; intros; auto with coc core arith datatypes.
exists x0; auto with coc core arith datatypes.

apply typ_wf with x (Srt s); auto with coc core arith datatypes.
Qed.



  Definition inv_type (P : Prop) e t T : Prop :=
    match t with
    | Srt prop => conv T (Srt kind) -> P
    | Srt set => conv T (Srt kind) -> P
    | Srt kind => True
    | Ref n => forall x : term, item _ x e n -> conv T (lift (S n) x) -> P
    | Abs A M =>
        forall s1 s2 (U : term),
        typ e A (Srt s1) ->
        typ (A :: e) M U -> typ (A :: e) U (Srt s2) -> conv T (Prod A U) -> P
    | App u v =>
        forall Ur V : term,
        typ e v V -> typ e u (Prod V Ur) -> conv T (subst v Ur) -> P
    | Prod A B =>
        forall s1 s2,
        typ e A (Srt s1) -> typ (A :: e) B (Srt s2) -> conv T (Srt s2) -> P
    end.

  Lemma inv_type_conv :
   forall (P : Prop) e t (U V : term),
   conv U V -> inv_type P e t U -> inv_type P e t V.
do 6 intro.
cut (forall x : term, conv V x -> conv U x).
intro.
case t; simpl in |- *; intros.
generalize H1.
elim s; auto with coc core arith datatypes; intros.

apply H1 with x; auto with coc core arith datatypes.

apply H1 with s1 s2 U0; auto with coc core arith datatypes.

apply H1 with Ur V0; auto with coc core arith datatypes.

apply H1 with s1 s2; auto with coc core arith datatypes.

intros.
apply trans_conv_conv with V; auto with coc core arith datatypes.
Qed.


  Theorem typ_inversion :
   forall (P : Prop) e t T, typ e t T -> inv_type P e t T -> P.
simple induction 1; simpl in |- *; intros.
auto with coc core arith datatypes.

auto with coc core arith datatypes.

elim H1; intros.
apply H2 with x; auto with coc core arith datatypes.
rewrite H3; auto with coc core arith datatypes.

apply H6 with s1 s2 U; auto with coc core arith datatypes.

apply H4 with Ur V; auto with coc core arith datatypes.

apply H4 with s1 s2; auto with coc core arith datatypes.

apply H1.
apply inv_type_conv with V; auto with coc core arith datatypes.
Qed.




  Lemma inv_typ_kind : forall e t, ~ typ e (Srt kind) t.
red in |- *; intros.
apply typ_inversion with e (Srt kind) t; simpl in |- *;
 auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_prop : forall e T, typ e (Srt prop) T -> conv T (Srt kind).
intros.
apply typ_inversion with e (Srt prop) T; simpl in |- *;
 auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_set : forall e T, typ e (Srt set) T -> conv T (Srt kind).
intros.
apply typ_inversion with e (Srt set) T; simpl in |- *;
 auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_ref :
   forall (P : Prop) e T n,
   typ e (Ref n) T ->
   (forall U : term, item _ U e n -> conv T (lift (S n) U) -> P) -> P.
intros.
apply typ_inversion with e (Ref n) T; simpl in |- *; intros;
 auto with coc core arith datatypes.
apply H0 with x; auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_abs :
   forall (P : Prop) e A M (U : term),
   typ e (Abs A M) U ->
   (forall s1 s2 T,
    typ e A (Srt s1) ->
    typ (A :: e) M T -> typ (A :: e) T (Srt s2) -> conv (Prod A T) U -> P) ->
   P.
intros.
apply typ_inversion with e (Abs A M) U; simpl in |- *;
 auto with coc core arith datatypes; intros.
apply H0 with s1 s2 U0; auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_app :
   forall (P : Prop) e u v T,
   typ e (App u v) T ->
   (forall V Ur : term,
    typ e u (Prod V Ur) -> typ e v V -> conv T (subst v Ur) -> P) -> P.
intros.
apply typ_inversion with e (App u v) T; simpl in |- *;
 auto with coc core arith datatypes; intros.
apply H0 with V Ur; auto with coc core arith datatypes.
Qed.

  Lemma inv_typ_prod :
   forall (P : Prop) e T (U s : term),
   typ e (Prod T U) s ->
   (forall s1 s2,
    typ e T (Srt s1) -> typ (T :: e) U (Srt s2) -> conv (Srt s2) s -> P) -> P.
intros.
apply typ_inversion with e (Prod T U) s; simpl in |- *;
 auto with coc core arith datatypes; intros.
apply H0 with s1 s2; auto with coc core arith datatypes.
Qed.




  Lemma typ_mem_kind : forall e t T, mem_sort kind t -> ~ typ e t T.
red in |- *; intros.
apply typ_inversion with e t T; auto with coc core arith datatypes.
generalize e T.
clear H0.
elim H; simpl in |- *; auto with coc core arith datatypes; intros.
apply typ_inversion with e0 u (Srt s1); auto with coc core arith datatypes.

apply typ_inversion with (u :: e0) v (Srt s2);
 auto with coc core arith datatypes.

apply typ_inversion with e0 u (Srt s1); auto with coc core arith datatypes.

apply typ_inversion with (u :: e0) v U; auto with coc core arith datatypes.

apply typ_inversion with e0 u (Prod V Ur); auto with coc core arith datatypes.

apply typ_inversion with e0 v V; auto with coc core arith datatypes.
Qed.


  Lemma inv_typ_conv_kind : forall e t T, conv t (Srt kind) -> ~ typ e t T.
intros.
apply typ_mem_kind.
apply red_sort_mem.
elim church_rosser with t (Srt kind); intros;
 auto with coc core arith datatypes.
rewrite (red_normal (Srt kind) x); auto with coc core arith datatypes.
red in |- *; red in |- *; intros.
inversion_clear H2.
Qed.



  Inductive ins_in_env A : nat -> env -> env -> Prop :=
    | ins_O : forall e, ins_in_env A 0 e (A :: e)
    | ins_S :
        forall n e f t,
        ins_in_env A n e f ->
        ins_in_env A (S n) (t :: e) (lift_rec 1 t n :: f).

  Hint Resolve ins_O ins_S: coc.

  Lemma ins_item_ge :
   forall A n e f,
   ins_in_env A n e f ->
   forall v : nat, n <= v -> forall t, item _ t e v -> item _ t f (S v).
simple induction 1; auto with coc core arith datatypes.
simple destruct v; intros.
inversion_clear H2.

inversion_clear H3; auto with coc core arith datatypes.
Qed.

  Lemma ins_item_lt :
   forall A n e f,
   ins_in_env A n e f ->
   forall v : nat,
   n > v -> forall t, item_lift t e v -> item_lift (lift_rec 1 t n) f v.
simple induction 1.
intros.
inversion_clear H0.

simple destruct v; intros.
elim H3; intros.
rewrite H4.
exists (lift_rec 1 t n0); auto with coc core arith datatypes.
inversion_clear H5.
elim permute_lift with t n0; auto with coc core arith datatypes.

elim H3; intros.
rewrite H4.
inversion_clear H5.
elim H1 with n1 (lift (S n1) x); intros; auto with coc core arith datatypes.
exists x0; auto with coc core arith datatypes.
pattern (lift (S (S n1)) x0) at 1 in |- *.
rewrite simpl_lift; auto with coc core arith datatypes.
elim H5.
change
  (lift_rec 1 (lift (S (S n1)) x) (S n0) =
   lift 1 (lift_rec 1 (lift (S n1) x) n0)) in |- *.
rewrite (permute_lift (lift (S n1) x) n0).
unfold lift at 2 in |- *.
pattern (lift (S (S n1)) x) in |- *.
rewrite simpl_lift; auto with coc core arith datatypes.

exists x; auto with coc core arith datatypes.
Qed.


  Lemma typ_weak_weak :
   forall A e t T,
   typ e t T ->
   forall n f,
   ins_in_env A n e f -> wf f -> typ f (lift_rec 1 t n) (lift_rec 1 T n).
simple induction 1; simpl in |- *; intros; auto with coc core arith datatypes.
elim (le_gt_dec n v); intros; apply type_var;
 auto with coc core arith datatypes.
elim H1; intros.
exists x.
rewrite H4.
unfold lift in |- *.
rewrite simpl_lift_rec; simpl in |- *; auto with coc core arith datatypes.

apply ins_item_ge with A n e0; auto with coc core arith datatypes.

apply ins_item_lt with A e0; auto with coc core arith datatypes.

cut (wf (lift_rec 1 T0 n :: f)).
intro.
apply type_abs with s1 s2; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

rewrite distr_lift_subst.
apply type_app with (lift_rec 1 V n); auto with coc core arith datatypes.

cut (wf (lift_rec 1 T0 n :: f)).
intro.
apply type_prod with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

apply type_conv with (lift_rec 1 U n) s; auto with coc core arith datatypes.
Qed.


  Theorem thinning :
   forall e t T,
   typ e t T -> forall A, wf (A :: e) -> typ (A :: e) (lift 1 t) (lift 1 T).
unfold lift in |- *.
intros.
inversion_clear H0.
apply typ_weak_weak with A e; auto with coc core arith datatypes.
apply wf_var with s; auto with coc core arith datatypes.
Qed.


  Lemma thinning_n :
   forall n e f,
   trunc _ n e f ->
   forall t T, typ f t T -> wf e -> typ e (lift n t) (lift n T).
simple induction n.
intros.
rewrite lift0.
rewrite lift0.
replace e with f; auto with coc core arith datatypes.
inversion_clear H; auto with coc core arith datatypes.

do 8 intro.
inversion_clear H0.
intro.
rewrite simpl_lift; auto with coc core arith datatypes.
pattern (lift (S n0) T) in |- *.
rewrite simpl_lift; auto with coc core arith datatypes.
inversion_clear H0.
change (typ (x :: e0) (lift 1 (lift n0 t)) (lift 1 (lift n0 T))) in |- *.
apply thinning; auto with coc core arith datatypes.
apply H with f; auto with coc core arith datatypes.
apply typ_wf with x (Srt s); auto with coc core arith datatypes.

apply wf_var with s; auto with coc core arith datatypes.
Qed.


  Lemma wf_sort_lift :
   forall n e t, wf e -> item_lift t e n -> exists s : sort, typ e t (Srt s).
simple induction n.
simple destruct e; intros.
elim H0; intros.
inversion_clear H2.

elim H0; intros.
rewrite H1.
inversion_clear H2.
inversion_clear H.
exists s.
replace (Srt s) with (lift 1 (Srt s)); auto with coc core arith datatypes.
apply thinning; auto with coc core arith datatypes.
apply wf_var with s; auto with coc core arith datatypes.

intros.
elim H1; intros.
rewrite H2.
generalize H0.
inversion_clear H3; intros.
rewrite simpl_lift; auto with coc core arith datatypes.
cut (wf l); intros.
elim H with l (lift (S n0) x); intros; auto with coc core arith datatypes.
inversion_clear H3.
exists x0.
change (typ (y :: l) (lift 1 (lift (S n0) x)) (lift 1 (Srt x0))) in |- *.
apply thinning; auto with coc core arith datatypes.
apply wf_var with s; auto with coc core arith datatypes.

exists x; auto with coc core arith datatypes.

inversion_clear H3.
apply typ_wf with y (Srt s); auto with coc core arith datatypes.
Qed.



  Inductive sub_in_env t T : nat -> env -> env -> Prop :=
    | sub_O : forall e, sub_in_env t T 0 (T :: e) e
    | sub_S :
        forall e f n u,
        sub_in_env t T n e f ->
        sub_in_env t T (S n) (u :: e) (subst_rec t u n :: f).

  Hint Resolve sub_O sub_S: coc.

  Lemma nth_sub_sup :
   forall t T n e f,
   sub_in_env t T n e f ->
   forall v : nat, n <= v -> forall u, item _ u e (S v) -> item _ u f v.
simple induction 1.
intros.
inversion_clear H1; auto with coc core arith datatypes.

simple destruct v; intros.
inversion_clear H2.

inversion_clear H3; auto with coc core arith datatypes.
Qed.


  Lemma nth_sub_eq : forall t T n e f, sub_in_env t T n e f -> item _ T e n.
simple induction 1; auto with coc core arith datatypes.
Qed.


  Lemma nth_sub_inf :
   forall t T n e f,
   sub_in_env t T n e f ->
   forall v : nat,
   n > v -> forall u, item_lift u e v -> item_lift (subst_rec t u n) f v.
simple induction 1.
intros.
inversion_clear H0.

simple destruct v; intros.
elim H3; intros.
rewrite H4.
inversion_clear H5.
exists (subst_rec t u n0); auto with coc core arith datatypes.
apply commut_lift_subst; auto with coc core arith datatypes.

elim H3; intros.
rewrite H4.
inversion_clear H5.
elim H1 with n1 (lift (S n1) x); intros; auto with coc core arith datatypes.
exists x0; auto with coc core arith datatypes.
rewrite simpl_lift; auto with coc core arith datatypes.
pattern (lift (S (S n1)) x0) in |- *.
rewrite simpl_lift; auto with coc core arith datatypes.
elim H5.
change
  (subst_rec t (lift 1 (lift (S n1) x)) (S n0) =
   lift 1 (subst_rec t (lift (S n1) x) n0)) in |- *.
apply commut_lift_subst; auto with coc core arith datatypes.

exists x; auto with coc core arith datatypes.
Qed.


  Lemma typ_sub_weak :
   forall g (d : term) t,
   typ g d t ->
   forall e u (U : term),
   typ e u U ->
   forall f n,
   sub_in_env d t n e f ->
   wf f -> trunc _ n f g -> typ f (subst_rec d u n) (subst_rec d U n).
simple induction 2; simpl in |- *; intros; auto with coc core arith datatypes.
elim (lt_eq_lt_dec n v); [ intro Hlt_eq | intro Hlt ].
elim H2.
elim Hlt_eq; clear Hlt_eq.
case v; [ intro Hlt | intros n0 Hlt ]; intros.
inversion_clear Hlt.

simpl in |- *.
rewrite H6.
rewrite simpl_subst; auto with coc core arith datatypes.
apply type_var; auto with coc core arith datatypes.
exists x; auto with coc core arith datatypes.
apply nth_sub_sup with d t n e0; auto with coc core arith datatypes.

intro Heq; intros.
rewrite H6.
elim Heq.
rewrite simpl_subst; auto with coc core arith datatypes.
replace x with t.
apply thinning_n with g; auto with coc core arith datatypes.

apply fun_item with e0 v; auto with coc core arith datatypes.
apply nth_sub_eq with d f; auto with coc core arith datatypes.
elim Heq; auto with coc core arith datatypes.

apply type_var; auto with coc core arith datatypes.
apply nth_sub_inf with t e0; auto with coc core arith datatypes.

cut (wf (subst_rec d T n :: f)); intros.
apply type_abs with s1 s2; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

rewrite distr_subst.
apply type_app with (subst_rec d V n); auto with coc core arith datatypes.

cut (wf (subst_rec d T n :: f)); intros.
apply type_prod with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

apply type_conv with (subst_rec d U0 n) s; auto with coc core arith datatypes.
Qed.


  Theorem substitution :
   forall e t u (U : term),
   typ (t :: e) u U ->
   forall d : term, typ e d t -> typ e (subst d u) (subst d U).
intros.
unfold subst in |- *.
apply typ_sub_weak with e t (t :: e); auto with coc core arith datatypes.
apply typ_wf with d t; auto with coc core arith datatypes.
Qed.





  Theorem typ_unique :
   forall e t T, typ e t T -> forall U : term, typ e t U -> conv T U.
simple induction 1; intros.
apply sym_conv.
apply inv_typ_prop with e0; auto with coc core arith datatypes.

apply sym_conv.
apply inv_typ_set with e0; auto with coc core arith datatypes.

apply inv_typ_ref with e0 U v; auto with coc core arith datatypes; intros.
elim H1; intros.
rewrite H5.
elim fun_item with term U0 x e0 v; auto with coc core arith datatypes.

apply inv_typ_abs with e0 T0 M U0; auto with coc core arith datatypes; intros.
apply trans_conv_conv with (Prod T0 T1); auto with coc core arith datatypes.

apply inv_typ_app with e0 u v U; auto with coc core arith datatypes; intros.
apply trans_conv_conv with (subst v Ur0); auto with coc core arith datatypes.
unfold subst in |- *; apply conv_conv_subst;
 auto with coc core arith datatypes.
apply inv_conv_prod_r with V V0; auto with coc core arith datatypes.

apply inv_typ_prod with e0 T0 U U0; auto with coc core arith datatypes;
 intros.
apply trans_conv_conv with (Srt s3); auto with coc core arith datatypes.

apply trans_conv_conv with U; auto with coc core arith datatypes.
Qed.



  Theorem type_case :
   forall e t T,
   typ e t T -> (exists s : sort, typ e T (Srt s)) \/ T = Srt kind.
simple induction 1; intros; auto with coc core arith datatypes.
left.
elim wf_sort_lift with v e0 t0; auto with coc core arith datatypes; intros.
exists x; auto with coc core arith datatypes.

left.
exists s2.
apply type_prod with s1; auto with coc core arith datatypes.

left.
elim H3; intros.
elim H4; intros.
apply inv_typ_prod with e0 V Ur (Srt x); auto with coc core arith datatypes;
 intros.
exists s2.
replace (Srt s2) with (subst v (Srt s2)); auto with coc core arith datatypes.
apply substitution with V; auto with coc core arith datatypes.

discriminate H4.

case s2; auto with coc core arith datatypes.
left.
exists kind.
apply type_prop.
apply typ_wf with T0 (Srt s1); auto with coc core arith datatypes.

left.
exists kind.
apply type_set.
apply typ_wf with T0 (Srt s1); auto with coc core arith datatypes.

left.
exists s; auto with coc core arith datatypes.
Qed.


  Lemma type_kind_not_conv :
   forall e t T, typ e t T -> typ e t (Srt kind) -> T = Srt kind.
intros.
elim type_case with e t T; intros; auto with coc core arith datatypes.
elim H1; intros.
elim inv_typ_conv_kind with e T (Srt x); auto with coc core arith datatypes.
apply typ_unique with e t; auto with coc core arith datatypes.
Qed.


  Lemma type_free_db : forall e t T, typ e t T -> free_db (length e) T.
intros.
elim type_case with e t T; intros; auto with coc core arith datatypes.
inversion_clear H0.
apply typ_free_db with (Srt x); auto with coc core arith datatypes.

rewrite H0; auto with coc core arith datatypes.
Qed.



  Inductive red1_in_env : env -> env -> Prop :=
    | red1_env_hd : forall e t u, red1 t u -> red1_in_env (t :: e) (u :: e)
    | red1_env_tl :
        forall e f t, red1_in_env e f -> red1_in_env (t :: e) (t :: f).

  Hint Resolve red1_env_hd red1_env_tl: coc.

  Lemma red_item :
   forall n t e,
   item_lift t e n ->
   forall f,
   red1_in_env e f ->
   item_lift t f n \/
   (forall g, trunc _ (S n) e g -> trunc _ (S n) f g) /\
   ex2 (fun u => red1 t u) (fun u => item_lift u f n).
simple induction n.
do 3 intro.
elim H.
do 4 intro.
rewrite H0.
inversion_clear H1.
intros.
inversion_clear H1.
right.
split; intros.
inversion_clear H1; auto with coc core arith datatypes.

exists (lift 1 u).
unfold lift in |- *; auto with coc core arith datatypes.

exists u; auto with coc core arith datatypes.

left.
exists x; auto with coc core arith datatypes.

do 5 intro.
elim H0.
do 4 intro.
rewrite H1.
inversion_clear H2.
intros.
inversion_clear H2.
left.
exists x; auto with coc core arith datatypes.

elim H with (lift (S n0) x) l f0; auto with coc core arith datatypes; intros.
left.
elim H2; intros.
exists x0; auto with coc core arith datatypes.
rewrite simpl_lift.
pattern (lift (S (S n0)) x0) in |- *.
rewrite simpl_lift.
elim H5; auto with coc core arith datatypes.

right.
elim H2.
simple induction 2; intros.
split; intros.
inversion_clear H9; auto with coc core arith datatypes.

elim H8; intros.
exists (lift (S (S n0)) x1).
rewrite simpl_lift.
pattern (lift (S (S n0)) x1) in |- *.
rewrite simpl_lift.
elim H9; unfold lift at 1 3 in |- *; auto with coc core arith datatypes.

exists x1; auto with coc core arith datatypes.

exists x; auto with coc core arith datatypes.
Qed.



  Lemma typ_red_env :
   forall e t T, typ e t T -> forall f, red1_in_env e f -> wf f -> typ f t T.
simple induction 1; intros.
auto with coc core arith datatypes.

auto with coc core arith datatypes.

elim red_item with v t0 e0 f; auto with coc core arith datatypes; intros.
inversion_clear H4.
inversion_clear H6.
elim H1; intros.
elim item_trunc with term v e0 x0; intros; auto with coc core arith datatypes.
elim wf_sort with v e0 x1 x0; auto with coc core arith datatypes.
intros.
apply type_conv with x x2; auto with coc core arith datatypes.
rewrite H6.
replace (Srt x2) with (lift (S v) (Srt x2));
 auto with coc core arith datatypes.
apply thinning_n with x1; auto with coc core arith datatypes.

cut (wf (T0 :: f)); intros.
apply type_abs with s1 s2; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

apply type_app with V; auto with coc core arith datatypes.

cut (wf (T0 :: f)); intros.
apply type_prod with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

apply type_conv with U s; auto with coc core arith datatypes.
Qed.


  Lemma subj_red : forall e t T, typ e t T -> forall u, red1 t u -> typ e u T.
simple induction 1; intros.
inversion_clear H1.

inversion_clear H1.

inversion_clear H2.

inversion_clear H6.
cut (wf (M' :: e0)); intros.
apply type_conv with (Prod M' U) s2; auto with coc core arith datatypes.
apply type_abs with s1 s2; auto with coc core arith datatypes.
apply typ_red_env with (T0 :: e0); auto with coc core arith datatypes.

apply typ_red_env with (T0 :: e0); auto with coc core arith datatypes.

apply type_prod with s1; auto with coc core arith datatypes.

apply wf_var with s1; auto with coc core arith datatypes.

apply type_abs with s1 s2; auto with coc core arith datatypes.

elim type_case with e0 u (Prod V Ur); intros;
 auto with coc core arith datatypes.
inversion_clear H5.
apply inv_typ_prod with e0 V Ur (Srt x); intros;
 auto with coc core arith datatypes.
generalize H2 H3.
clear H2 H3.
inversion_clear H4; intros.
apply inv_typ_abs with e0 T0 M (Prod V Ur); intros;
 auto with coc core arith datatypes.
apply type_conv with (subst v T1) s2; auto with coc core arith datatypes.
apply substitution with T0; auto with coc core arith datatypes.
apply type_conv with V s0; auto with coc core arith datatypes.
apply inv_conv_prod_l with Ur T1; auto with coc core arith datatypes.

unfold subst in |- *.
apply conv_conv_subst; auto with coc core arith datatypes.
apply inv_conv_prod_r with T0 V; auto with coc core arith datatypes.

replace (Srt s2) with (subst v (Srt s2)); auto with coc core arith datatypes.
apply substitution with V; auto with coc core arith datatypes.

apply type_app with V; auto with coc core arith datatypes.

apply type_conv with (subst N2 Ur) s2; auto with coc core arith datatypes.
apply type_app with V; auto with coc core arith datatypes.

unfold subst in |- *.
apply conv_conv_subst; auto with coc core arith datatypes.

replace (Srt s2) with (subst v (Srt s2)); auto with coc core arith datatypes.
apply substitution with V; auto with coc core arith datatypes.

discriminate H5.

inversion_clear H4.
apply type_prod with s1; auto with coc core arith datatypes.
apply typ_red_env with (T0 :: e0); auto with coc core arith datatypes.
apply wf_var with s1; auto with coc core arith datatypes.

apply type_prod with s1; auto with coc core arith datatypes.

apply type_conv with U s; auto with coc core arith datatypes.
Qed.


  Theorem subject_reduction :
   forall e t u, red t u -> forall T, typ e t T -> typ e u T.
simple induction 1; intros; auto with coc core arith datatypes.
apply subj_red with P; intros; auto with coc core arith datatypes.
Qed.


  Lemma type_reduction :
   forall e t T (U : term), red T U -> typ e t T -> typ e t U.
intros.
elim type_case with e t T; intros; auto with coc core arith datatypes.
inversion_clear H1.
apply type_conv with T x; auto with coc core arith datatypes.
apply subject_reduction with T; auto with coc core arith datatypes.

elim red_normal with T U; auto with coc core arith datatypes.
rewrite H1.
red in |- *; red in |- *; intros.
inversion_clear H2.
Qed.



  Lemma typ_conv_conv :
   forall e u (U : term) v (V : term),
   typ e u U -> typ e v V -> conv u v -> conv U V.
intros.
elim church_rosser with u v; auto with coc core arith datatypes; intros.
apply typ_unique with e x.
apply subject_reduction with u; auto with coc core arith datatypes.

apply subject_reduction with v; auto with coc core arith datatypes.
Qed.

End Typage.

  Hint Resolve ins_O ins_S: coc.
  Hint Resolve sub_O sub_S: coc.
  Hint Resolve red1_env_hd red1_env_tl: coc.
