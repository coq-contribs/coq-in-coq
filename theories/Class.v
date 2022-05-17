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
Require Export ListType.

  (* Kind skeletons *)

  Inductive skel : Type :=
    | PROP : skel
    | PROD : skel -> skel -> skel.

  Lemma EQ_skel : forall a b : skel, {a = b} + {a <> b}.
induction a as [| s H s0 H0]; simple destruct b; intros.
left; auto with core.

right; red in |- *; intros neq; discriminate neq.

right; red in |- *; intros neq; discriminate neq.

elim H with s1; [ intro Heq1 | intro Hneq1 ].
elim Heq1.
elim H0 with s2; [ intro Heq2 | intro Hneq2 ].
elim Heq2.
left; auto with core.

right; red in |- *; intros; apply Hneq2.
injection H1; trivial.

right; red in |- *; intros; apply Hneq1.
injection H1; trivial.
Qed.



  (* Classes *)

  Inductive class : Type :=
    | Trm : class
    | Typ : skel -> class
    | Knd : skel -> class.

  Definition cls := TList class.


  Definition cv_skel (c : class) : skel :=
    match c with
    | Knd s => s
    | _ => PROP
    end.

  Definition typ_skel (c : class) : skel :=
    match c with
    | Typ s => s
    | _ => PROP
    end.


  Lemma commut_case :
   forall (A B : Type) (f : A -> B) (c : class) (bt : A) (bT bK : skel -> A),
   f match c with
     | Trm => bt
     | Typ s => bT s
     | Knd s => bK s
     end =
   match c with
   | Trm => f bt
   | Typ _ => f (bT (typ_skel c))
   | Knd _ => f (bK (cv_skel c))
   end. 
simple destruct c; auto with coc core arith datatypes.
Qed.



  Fixpoint cl_term (t : term) : cls -> class :=
    fun i : cls =>
    match t with
    | Srt _ => Knd PROP
    | Ref n => match Tnth_def _ Trm i n with
               | Knd s => Typ s
               | _ => Trm
               end
    | Abs A B =>
        let j := TCs _ (cl_term A i) i in
        match cl_term B j, cl_term A i with
        | Typ s2, Knd s1 => Typ (PROD s1 s2)
        | Typ s, _ => Typ s
        | Knd _, _ => Knd PROP
        | Trm, _ => Trm
        end
    | App u v =>
        match cl_term u i, cl_term v i with
        | Typ (PROD s1 s2), Typ s => Typ s2
        | Typ s, _ => Typ s
        | Knd _, _ => Knd PROP
        | Trm, _ => Trm
        end
    | Prod T U =>
        let j := TCs _ (cl_term T i) i in
        match cl_term U j, cl_term T i with
        | Knd s2, Knd s1 => Knd (PROD s1 s2)
        | Knd s, _ => Knd s
        | Typ s, _ => Typ s
        | c1, _ => c1
        end
    end.


  Fixpoint class_env (e : env) : cls :=
    match e with
    | nil => TNl _
    | t :: f => TCs _ (cl_term t (class_env f)) (class_env f)
    end.



  Lemma nth_class_env :
   forall (t : term) (e f : env) (n : nat),
   item _ t e n ->
   trunc _ (S n) e f ->
   cl_term t (class_env f) = Tnth_def _ Trm (class_env e) n.
simple induction 1; simpl in |- *; intros.
inversion_clear H0.
inversion_clear H1; auto with coc core arith datatypes.

apply H1.
inversion_clear H2; auto with coc core arith datatypes.
Qed.


  Lemma cl_term_lift :
   forall (x : class) (t : term) (k : nat) (f g : cls),
   TIns _ x k f g -> cl_term t f = cl_term (lift_rec 1 t k) g.
simple induction t; intros.
simpl in |- *; auto with coc core arith datatypes.

simpl in |- *.
elim (le_gt_dec k n); simpl in |- *; intros.
elim Tins_le with class k f g Trm x n; auto with coc core arith datatypes.

elim Tins_gt with class k f g Trm x n; auto with coc core arith datatypes.

simpl in |- *.
elim H with k f g; auto with coc core arith datatypes.
elim H0 with (S k) (TCs class (cl_term t0 f) f) (TCs class (cl_term t0 f) g);
 auto with coc core arith datatypes.

simpl in |- *; auto with coc core arith datatypes.
elim H with k f g; auto with coc core arith datatypes.
elim H0 with k f g; auto with coc core arith datatypes.

simpl in |- *.
elim H with k f g; auto with coc core arith datatypes.
elim H0 with (S k) (TCs class (cl_term t0 f) f) (TCs class (cl_term t0 f) g);
 auto with coc core arith datatypes.
Qed.



  Lemma class_env_trunc :
   forall (k : nat) (e f : env),
   trunc _ k e f -> TTrunc _ k (class_env e) (class_env f).
simple induction 1; simpl in |- *; auto with coc core arith datatypes.
Qed.

  Hint Resolve class_env_trunc: coc.


  Lemma cl_trunc :
   forall (n : nat) (e f : cls),
   TTrunc _ n e f -> forall t : term, cl_term (lift n t) e = cl_term t f.
simple induction 1; intros.
rewrite lift0; auto with coc core arith datatypes.

elim H1.
rewrite simpl_lift.
unfold lift at 1 in |- *.
simpl in |- *.
elim cl_term_lift with x (lift k t) 0 e0 (TCs _ x e0);
 auto with coc core arith datatypes.
Qed.





  (* Loose stability results *)

  Inductive loose_eqc : class -> class -> Prop :=
    | leqc_trm : loose_eqc Trm Trm
    | leqc_typ : forall s1 s2 : skel, loose_eqc (Typ s1) (Typ s2)
    | leqc_ord : forall s : skel, loose_eqc (Knd s) (Knd s).

  Hint Resolve leqc_trm leqc_typ leqc_ord: coc. 

  Lemma refl_loose_eqc : forall c : class, loose_eqc c c.
simple induction c; auto with coc core arith datatypes.
Qed.

  Hint Resolve refl_loose_eqc: coc.

  Lemma refl_loose_eqc_cls : forall c : cls, Tfor_all2 _ _ loose_eqc c c.
simple induction c; auto with coc core arith datatypes.
Qed.

  Hint Resolve refl_loose_eqc_cls: coc.


  Lemma loose_eqc_trans :
   forall c1 c2 : class,
   loose_eqc c1 c2 -> forall c3 : class, loose_eqc c2 c3 -> loose_eqc c1 c3.
simple induction 1; intros; inversion_clear H0;
 auto with coc core arith datatypes.
Qed.


  Inductive adj_cls : class -> class -> Prop :=
    | adj_t : forall s : skel, adj_cls Trm (Typ s)
    | adj_T : forall s1 s2 : skel, adj_cls (Typ s1) (Knd s2).

  Hint Resolve adj_t adj_T: coc.


  Lemma loose_eqc_stable :
   forall (t : term) (cl1 cl2 : cls),
   Tfor_all2 _ _ loose_eqc cl1 cl2 ->
   loose_eqc (cl_term t cl1) (cl_term t cl2).
simple induction t; simpl in |- *; intros; auto with coc core arith datatypes.
generalize n.
elim H; simpl in |- *; intros; auto with coc core arith datatypes.
case n0; auto with coc core arith datatypes.
inversion_clear H0; auto with coc core arith datatypes.

elim
 H0 with (TCs class (cl_term t0 cl1) cl1) (TCs class (cl_term t0 cl2) cl2);
 auto with coc core arith datatypes.
elim H with cl1 cl2; auto with coc core arith datatypes.

elim H with cl1 cl2; auto with coc core arith datatypes; intros.
elim s1; elim s2; elim H0 with cl1 cl2; auto with coc core arith datatypes.

elim
 H0 with (TCs class (cl_term t0 cl1) cl1) (TCs class (cl_term t0 cl2) cl2);
 auto with coc core arith datatypes.
elim H with cl1 cl2; auto with coc core arith datatypes.
Qed.

  Hint Resolve loose_eqc_stable: coc.



  Lemma cl_term_subst :
   forall (a : class) (G : cls) (x : term),
   adj_cls (cl_term x G) a ->
   forall (t : term) (k : nat) (E F : cls),
   TIns _ a k E F ->
   TTrunc _ k E G -> loose_eqc (cl_term t F) (cl_term (subst_rec x t k) E).
simple induction t; simpl in |- *; intros; auto with coc core arith datatypes.
elim (lt_eq_lt_dec k n); simpl in |- *; [ intro Hlt_eq | intro lt ].
elim Hlt_eq; clear Hlt_eq.
case n; simpl in |- *; [ intro Hlt | intros n0 Heq ].
inversion_clear Hlt.

elim Tins_le with class k E F Trm a n0; auto with coc core arith datatypes.

simple induction 1.
rewrite (Tins_eq class k E F Trm a); auto with coc core arith datatypes.
apply loose_eqc_trans with (cl_term x G).
inversion_clear H; auto with coc core arith datatypes.

elim cl_trunc with k E G x; auto with coc core arith datatypes.

elim Tins_gt with class k E F Trm a n; auto with coc core arith datatypes.

cut (loose_eqc (cl_term t0 F) (cl_term (subst_rec x t0 k) E)); intros;
 auto with coc core arith datatypes.
cut
 (loose_eqc (cl_term t1 (TCs class (cl_term t0 F) F))
    (cl_term (subst_rec x t1 (S k))
       (TCs class (cl_term (subst_rec x t0 k) E) E))); 
 intros.
elim H5; auto with coc core arith datatypes; intros.
elim H4; auto with coc core arith datatypes.

apply
 loose_eqc_trans with (cl_term t1 (TCs _ (cl_term (subst_rec x t0 k) E) F));
 auto with coc core arith datatypes.

elim H0 with k E F; auto with coc core arith datatypes; intros.
elim s1; elim s2; elim H1 with k E F; auto with coc core arith datatypes.

cut (loose_eqc (cl_term t0 F) (cl_term (subst_rec x t0 k) E)); intros;
 auto with coc core arith datatypes.
cut
 (loose_eqc (cl_term t1 (TCs class (cl_term t0 F) F))
    (cl_term (subst_rec x t1 (S k))
       (TCs class (cl_term (subst_rec x t0 k) E) E))); 
 intros.
elim H5; auto with coc core arith datatypes; intros.
elim H4; auto with coc core arith datatypes.

apply
 loose_eqc_trans with (cl_term t1 (TCs _ (cl_term (subst_rec x t0 k) E) F));
 auto with coc core arith datatypes.
Qed.



  Lemma class_knd :
   forall (e : env) (t T : term),
   typ e t T ->
   T = Srt kind ->
   cl_term t (class_env e) = Knd (cv_skel (cl_term t (class_env e))).
simple induction 1; intros.
simpl in |- *; auto with coc core arith datatypes.

simpl in |- *; auto with coc core arith datatypes.

elim H1; intros.
elim item_trunc with term v e0 x; auto with coc core arith datatypes; intros.
elim wf_sort with v e0 x0 x; auto with coc core arith datatypes; intros.
elim inv_typ_kind with e0 (Srt x1).
elim H2.
rewrite H3.
replace (Srt x1) with (lift (S v) (Srt x1));
 auto with coc core arith datatypes.
apply thinning_n with x0; auto with coc core arith datatypes.

discriminate H6.

elim type_case with e0 u (Prod V Ur); auto with coc core arith datatypes;
 intros.
inversion_clear H5.
apply inv_typ_prod with e0 V Ur (Srt x); auto with coc core arith datatypes.
intros.
elim inv_typ_kind with e0 (Srt s2); auto with coc core arith datatypes.
elim H4.
replace (Srt s2) with (subst v (Srt s2)); auto with coc core arith datatypes.
apply substitution with V; auto with coc core arith datatypes.

discriminate H5.

simpl in H3.
simpl in |- *.
rewrite H3; auto with coc core arith datatypes.
elim (cl_term T0 (class_env e0)); auto with coc core arith datatypes.

elim inv_typ_kind with e0 (Srt s); auto with coc core arith datatypes.
elim H5; auto with coc core arith datatypes.
Qed.



  Lemma class_typ :
   forall (e : env) (t T : term),
   typ e t T ->
   typ e T (Srt kind) ->
   cl_term t (class_env e) = Typ (typ_skel (cl_term t (class_env e))).
simple induction 1; intros.
elim inv_typ_kind with e0 (Srt kind); auto with coc core arith datatypes.

elim inv_typ_kind with e0 (Srt kind); auto with coc core arith datatypes.

elim H1; intros.
simpl in |- *.
elim item_trunc with term v e0 x; auto with coc core arith datatypes; intros.
elim nth_class_env with x e0 x0 v; auto with coc core arith datatypes.
elim cl_trunc with (S v) (class_env e0) (class_env x0) x;
 auto with coc core arith datatypes.
elim H3.
rewrite (class_knd e0 t0 (Srt kind)); auto with coc core arith datatypes.

simpl in |- *.
simpl in H5.
rewrite H5.
elim (cl_term T0 (class_env e0)); intros; auto with coc core arith datatypes.

apply inv_typ_prod with e0 T0 U (Srt kind); intros;
 auto with coc core arith datatypes.
elim conv_sort with s3 kind; auto with coc core arith datatypes.

simpl in |- *.
elim type_case with e0 u (Prod V Ur); auto with coc core arith datatypes;
 intros.
inversion_clear H5.
rewrite H3.
case (typ_skel (cl_term u (class_env e0)));
 auto with coc core arith datatypes.

elim (cl_term v (class_env e0)); auto with coc core arith datatypes.

apply inv_typ_prod with e0 V Ur (Srt x); intros;
 auto with coc core arith datatypes.
apply type_prod with s1; auto with coc core arith datatypes.
elim conv_sort with s2 kind; auto with coc core arith datatypes.
apply typ_unique with e0 (subst v Ur); auto with coc core arith datatypes.
replace (Srt s2) with (subst v (Srt s2)); auto with coc core arith datatypes.
apply substitution with V; auto with coc core arith datatypes.

discriminate H5.

simpl in |- *.
simpl in H3.
rewrite H3; auto with coc core arith datatypes.
replace (Srt s2) with (lift 1 (Srt s2)); auto with coc core arith datatypes.
replace (Srt kind) with (lift 1 (Srt kind));
 auto with coc core arith datatypes.
apply thinning; auto with coc core arith datatypes.
apply wf_var with s1; auto with coc core arith datatypes.

apply H1.
elim type_case with e0 t0 U; auto with coc core arith datatypes; intros.
inversion_clear H6.
elim conv_sort with x kind; auto with coc core arith datatypes.
apply typ_conv_conv with e0 U V; auto with coc core arith datatypes.

elim inv_typ_conv_kind with e0 V (Srt kind);
 auto with coc core arith datatypes.
elim H6; auto with coc core arith datatypes.
Qed.


  Lemma class_typ_ord :
   forall (e : env) (T : term) (s : sort),
   typ e T (Srt s) ->
   forall P : class -> Prop,
   P (Typ (typ_skel (cl_term T (class_env e)))) ->
   P (Knd (cv_skel (cl_term T (class_env e)))) -> P (cl_term T (class_env e)).
simple destruct s; intros.
rewrite (class_knd e T (Srt kind)); auto with coc core arith datatypes.

rewrite (class_typ e T (Srt prop)); auto with coc core arith datatypes.
apply type_prop.
apply typ_wf with T (Srt prop); auto with coc core arith datatypes.

rewrite (class_typ e T (Srt set)); auto with coc core arith datatypes.
apply type_set.
apply typ_wf with T (Srt set); auto with coc core arith datatypes.
Qed.


  Lemma class_trm :
   forall (e : env) (t T : term) (s : sort),
   is_prop s -> typ e t T -> typ e T (Srt s) -> cl_term t (class_env e) = Trm.
intros e t T s is_p.
simple induction 1; intros.
elim inv_typ_kind with e0 (Srt s); auto with coc core arith datatypes.

elim inv_typ_kind with e0 (Srt s); auto with coc core arith datatypes.

elim H1; intros.
simpl in |- *.
elim item_trunc with term v e0 x; auto with coc core arith datatypes; intros.
elim nth_class_env with x e0 x0 v; auto with coc core arith datatypes.
elim cl_trunc with (S v) (class_env e0) (class_env x0) x;
 auto with coc core arith datatypes.
elim H3.
rewrite (class_typ e0 t0 (Srt s)); auto with coc core arith datatypes.
apply type_prop_set; auto with coc core arith datatypes.

simpl in |- *.
simpl in H5.
rewrite H5; auto with coc core arith datatypes.
apply inv_typ_prod with e0 T0 U (Srt s); intros;
 auto with coc core arith datatypes.
elim conv_sort with s3 s; auto with coc core arith datatypes.

simpl in |- *.
elim type_case with e0 u (Prod V Ur); auto with coc core arith datatypes;
 intros.
inversion_clear H5.
rewrite H3; auto with coc core arith datatypes.
apply inv_typ_prod with e0 V Ur (Srt x); intros;
 auto with coc core arith datatypes.
apply type_prod with s1; auto with coc core arith datatypes.
elim conv_sort with s2 s; auto with coc core arith datatypes.
apply typ_unique with e0 (subst v Ur); auto with coc core arith datatypes.
replace (Srt s2) with (subst v (Srt s2)); auto with coc core arith datatypes.
apply substitution with V; auto with coc core arith datatypes.

discriminate H5.

simpl in |- *.
simpl in H3.
rewrite H3; auto with coc core arith datatypes.
replace (Srt s2) with (lift 1 (Srt s2)); auto with coc core arith datatypes.
replace (Srt s) with (lift 1 (Srt s)); auto with coc core arith datatypes.
apply thinning; auto with coc core arith datatypes.
apply wf_var with s1; auto with coc core arith datatypes.

apply H1.
elim type_case with e0 t0 U; auto with coc core arith datatypes; intros.
inversion_clear H6.
elim conv_sort with x s; auto with coc core arith datatypes.
apply typ_conv_conv with e0 U V; auto with coc core arith datatypes.

elim inv_typ_conv_kind with e0 V (Srt s); auto with coc core arith datatypes.
elim H6; auto with coc core arith datatypes.
Qed.


  Lemma cl_term_sound :
   forall (e : env) (t T : term),
   typ e t T ->
   forall K : term,
   typ e T K -> adj_cls (cl_term t (class_env e)) (cl_term T (class_env e)).
intros.
elim type_case with e t T; intros; auto with coc core arith datatypes.
elim H1.
intro x; elim x using sort_level_ind; intros.
rewrite (class_knd e T (Srt kind)); auto with coc core arith datatypes.
rewrite (class_typ e t T); auto with coc core arith datatypes.

rewrite (class_typ e T (Srt s)); auto with coc core arith datatypes.
rewrite (class_trm e t T s); auto with coc core arith datatypes.

apply type_prop_set; trivial.
apply typ_wf with t T; auto with coc core arith datatypes.

elim inv_typ_kind with e K; auto with coc core arith datatypes.
elim H1; auto with coc core arith datatypes.
Qed.




  Lemma cl_term_red1 :
   forall (e : env) (A T : term),
   typ e A T ->
   forall B : term,
   red1 A B -> loose_eqc (cl_term A (class_env e)) (cl_term B (class_env e)).
simple induction 1; intros; auto with coc core arith datatypes.
inversion_clear H1.

inversion_clear H1.

inversion_clear H2.

inversion_clear H6.
simpl in |- *.
elim
 loose_eqc_stable
  with
    M
    (TCs class (cl_term T0 (class_env e0)) (class_env e0))
    (TCs class (cl_term M' (class_env e0)) (class_env e0));
 auto with coc core arith datatypes.
elim H1 with M'; auto with coc core arith datatypes.

simpl in |- *.
replace (TCs class (cl_term T0 (class_env e0)) (class_env e0)) with
 (class_env (T0 :: e0)); trivial.
elim H5 with M'; auto with coc core arith datatypes.
elim (cl_term T0 (class_env e0)); auto with coc core arith datatypes.

generalize H2 H3; clear H2 H3.
inversion_clear H4; intros.
elim type_case with e0 (Abs T0 M) (Prod V Ur); intros;
 auto with coc core arith datatypes.
inversion_clear H4.
apply inv_typ_prod with e0 V Ur (Srt x); intros;
 auto with coc core arith datatypes.
apply inv_typ_abs with e0 T0 M (Prod V Ur); intros;
 auto with coc core arith datatypes.
simpl in |- *.
apply loose_eqc_trans with (cl_term M (class_env (T0 :: e0))).
replace (TCs class (cl_term T0 (class_env e0)) (class_env e0)) with
 (class_env (T0 :: e0)); auto with coc core arith datatypes.
elim cl_term_sound with (T0 :: e0) M T1 (Srt s3); intros;
 auto with coc core arith datatypes.
elim (cl_term T0 (class_env e0)); intros.
elim s4; elim (cl_term v (class_env e0)); auto with coc core arith datatypes.

elim s4; elim (cl_term v (class_env e0)); auto with coc core arith datatypes.

elim (cl_term v (class_env e0)); auto with coc core arith datatypes.

unfold subst in |- *.
apply cl_term_subst with (cl_term T0 (class_env e0)) (class_env e0);
 auto with coc core arith datatypes.
apply cl_term_sound with (Srt s0); auto with coc core arith datatypes.
apply type_conv with V s0; auto with coc core arith datatypes.
apply inv_conv_prod_l with Ur T1; auto with coc core arith datatypes.

simpl in |- *; auto with coc core arith datatypes.

discriminate H4.

simpl in |- *.
elim H4 with N1; intros; auto with coc core arith datatypes.
case s1; case s2; elim (cl_term v (class_env e0));
 auto with coc core arith datatypes.

simpl in |- *.
elim (cl_term u (class_env e0)); intros; auto with coc core arith datatypes.
case s; elim H1 with N2; auto with coc core arith datatypes.

inversion_clear H4.
simpl in |- *.
elim
 loose_eqc_stable
  with
    U
    (TCs class (cl_term T0 (class_env e0)) (class_env e0))
    (TCs class (cl_term N1 (class_env e0)) (class_env e0));
 auto with coc core arith datatypes.
elim H1 with N1; auto with coc core arith datatypes.

simpl in |- *.
replace (TCs class (cl_term T0 (class_env e0)) (class_env e0)) with
 (class_env (T0 :: e0)); auto with coc core arith datatypes.
elim H3 with N2; auto with coc core arith datatypes.
Qed.



  Lemma cl_term_red :
   forall T U : term,
   red T U ->
   forall (e : env) (K : term),
   typ e T K -> loose_eqc (cl_term T (class_env e)) (cl_term U (class_env e)).
simple induction 1; intros; auto with coc core arith datatypes.
apply loose_eqc_trans with (cl_term P (class_env e));
 auto with coc core arith datatypes.
apply H1 with K; auto with coc core arith datatypes.

apply cl_term_red1 with K; auto with coc core arith datatypes.
apply subject_reduction with T; auto with coc core arith datatypes.
Qed.

  Lemma cl_term_conv :
   forall (e : env) (T U K1 K2 : term),
   typ e T K1 ->
   typ e U K2 ->
   conv T U -> loose_eqc (cl_term T (class_env e)) (cl_term U (class_env e)).
intros.
elim church_rosser with T U; intros; auto with coc core arith datatypes.
apply loose_eqc_trans with (cl_term x (class_env e)).
apply cl_term_red with K1; auto with coc core arith datatypes.

elim cl_term_red with U x e K2; auto with coc core arith datatypes.
Qed.



  Lemma skel_sound :
   forall (e : env) (t T : term),
   typ e t T ->
   cv_skel (cl_term T (class_env e)) = typ_skel (cl_term t (class_env e)).
simple induction 1; intros; auto with coc core arith datatypes.
inversion_clear H1.
rewrite H2.
simpl in |- *.
clear H2 t0.
elim H3; simpl in |- *; intros.
unfold lift in |- *.
elim
 cl_term_lift
  with
    (cl_term x (class_env l))
    x
    0
    (class_env l)
    (TCs class (cl_term x (class_env l)) (class_env l));
 auto with coc core arith datatypes.
elim (cl_term x (class_env l)); auto with coc core arith datatypes.

rewrite simpl_lift.
unfold lift at 1 in |- *.
elim
 cl_term_lift
  with
    (cl_term y (class_env l))
    (lift (S n) x)
    0
    (class_env l)
    (TCs class (cl_term y (class_env l)) (class_env l));
 auto with coc core arith datatypes.

simpl in |- *.
replace (TCs class (cl_term T0 (class_env e0)) (class_env e0)) with
 (class_env (T0 :: e0)); auto with coc core arith datatypes.
rewrite
 (commut_case _ _ cv_skel)
                           with
                           (bK := 
                             fun s =>
                             match cl_term T0 (class_env e0) with
                             | Trm => Knd s
                             | Typ _ => Knd s
                             | Knd s0 => Knd (PROD s0 s)
                             end).
rewrite
 (commut_case _ _ typ_skel)
                            with
                            (bT := 
                              fun s =>
                              match cl_term T0 (class_env e0) with
                              | Trm => Typ s
                              | Typ _ => Typ s
                              | Knd s0 => Typ (PROD s0 s)
                              end)
                           (bK := fun s : skel => Knd PROP).
simpl in |- *.
replace (TCs class (cl_term T0 (class_env e0)) (class_env e0)) with
 (class_env (T0 :: e0)); auto with coc core arith datatypes.
pattern (cl_term M (class_env (T0 :: e0))) at 1,
 (cl_term U (class_env (T0 :: e0))) at 1 in |- *.
elim cl_term_sound with (T0 :: e0) M U (Srt s2); intros;
 auto with coc core arith datatypes.
rewrite
 (commut_case _ _ cv_skel)
                           with
                           (bT := 
                             fun s : skel =>
                             Knd (cv_skel (cl_term U (class_env (T0 :: e0)))))
                          (bK := 
                            fun s =>
                            Knd
                              (PROD s
                                 (cv_skel (cl_term U (class_env (T0 :: e0)))))).
rewrite
 (commut_case _ _ typ_skel)
                            with
                            (bT := 
                              fun s : skel =>
                              Typ
                                (typ_skel (cl_term M (class_env (T0 :: e0)))))
                           (bK := 
                             fun s =>
                             Typ
                               (PROD s
                                  (typ_skel
                                     (cl_term M (class_env (T0 :: e0)))))).
elim (cl_term T0 (class_env e0)); auto with coc core arith datatypes.
elim H5; auto with coc core arith datatypes.

elim type_case with e0 u (Prod V Ur); intros;
 auto with coc core arith datatypes.
inversion_clear H4.
apply inv_typ_prod with e0 V Ur (Srt x); intros;
 auto with coc core arith datatypes.
unfold subst in |- *.
generalize H3.
cut (adj_cls (cl_term u (class_env e0)) (cl_term (Prod V Ur) (class_env e0))).
simpl in |- *.
elim
 cl_term_subst
  with
    (cl_term V (class_env e0))
    (class_env e0)
    v
    Ur
    0
    (class_env e0)
    (TCs class (cl_term V (class_env e0)) (class_env e0)); 
 simpl in |- *; auto with coc core arith datatypes.
intros.
inversion_clear H8.

intros.
inversion_clear H8.
auto with coc core arith datatypes.

elim cl_term_sound with e0 v V (Srt s1); simpl in |- *; intros;
 auto with coc core arith datatypes.
rewrite H9.
inversion_clear H8; auto with coc core arith datatypes.
elim s3; auto with coc core arith datatypes.

generalize H9.
inversion_clear H8; intros; auto with coc core arith datatypes.
simpl in H8.
elim H8; auto with coc core arith datatypes.

apply cl_term_sound with (Srt s1); auto with coc core arith datatypes.

apply cl_term_sound with (Srt x); auto with coc core arith datatypes.

discriminate H4.

simpl in |- *.
simpl in H3.
simpl in H1.
rewrite
 (commut_case _ _ typ_skel)
                            with
                            (bK := 
                              fun s =>
                              match cl_term T0 (class_env e0) with
                              | Trm => Knd s
                              | Typ _ => Knd s
                              | Knd s0 => Knd (PROD s0 s)
                              end).
simpl in |- *.
elim H3.
elim (cl_term U (TCs class (cl_term T0 (class_env e0)) (class_env e0)));
 auto with coc core arith datatypes.
elim (cl_term T0 (class_env e0)); auto with coc core arith datatypes.

elim H1.
elim cl_term_conv with e0 U V (Srt s) (Srt s);
 auto with coc core arith datatypes.
elim type_case with e0 t0 U; auto with coc core arith datatypes; intros.
inversion_clear H5.
elim conv_sort with x s; auto with coc core arith datatypes.
apply typ_conv_conv with e0 U V; auto with coc core arith datatypes.

elim inv_typ_conv_kind with e0 V (Srt s); auto with coc core arith datatypes.
elim H5; auto with coc core arith datatypes.
Qed.



  (* Strict stability results *)

  Inductive typ_cls : class -> class -> Prop :=
    | tc_t : typ_cls Trm (Typ PROP)
    | tc_T : forall s : skel, typ_cls (Typ s) (Knd s).

  Hint Resolve tc_t tc_T: coc.


  Lemma class_subst :
   forall (a : class) (G : cls) (x : term),
   typ_cls (cl_term x G) a ->
   forall (t : term) (k : nat) (E F : cls),
   TIns _ a k E F ->
   TTrunc _ k E G -> cl_term t F = cl_term (subst_rec x t k) E.
simple induction t; simpl in |- *; intros; auto with coc core arith datatypes.
elim (lt_eq_lt_dec k n); simpl in |- *; [ intro Hlt_eq | intro Hlt ].
elim Hlt_eq; clear Hlt_eq.
case n; simpl in |- *; [ intro Hlt | intro; intro Heq ].
inversion_clear Hlt.

elim Tins_le with class k E F Trm a n0; auto with coc core arith datatypes.

simple induction 1.
rewrite (Tins_eq class k E F Trm a); auto with coc core arith datatypes.
replace (cl_term (lift k x) E) with (cl_term x G).
inversion_clear H; auto with coc core arith datatypes.

symmetry  in |- *.
apply cl_trunc; auto with coc core arith datatypes.

elim Tins_gt with class k E F Trm a n; auto with coc core arith datatypes.

elim H0 with k E F; auto with coc core arith datatypes.
elim H1 with (S k) (TCs class (cl_term t0 F) E) (TCs class (cl_term t0 F) F);
 auto with coc core arith datatypes.

elim H0 with k E F; auto with coc core arith datatypes.
elim H1 with k E F; auto with coc core arith datatypes.

elim H0 with k E F; auto with coc core arith datatypes.
elim H1 with (S k) (TCs class (cl_term t0 F) E) (TCs class (cl_term t0 F) F);
 auto with coc core arith datatypes.
Qed.


  Lemma class_sound :
   forall (e : env) (t T : term),
   typ e t T ->
   forall K : term,
   typ e T K -> typ_cls (cl_term t (class_env e)) (cl_term T (class_env e)).
intros.
elim type_case with (1 := H); intros.
elim H1.
intro x; elim x using sort_level_ind; intros.
rewrite (class_knd e T (Srt kind)); trivial.
rewrite (class_typ e t T); trivial.
elim skel_sound with (1 := H); auto with coc.

rewrite (class_typ e T (Srt s)); trivial.
rewrite (class_trm e t T s); trivial.
elim skel_sound with (1 := H3); simpl in |- *; auto with coc.

apply type_prop_set; trivial.
apply typ_wf with t T; auto with coc.

elim inv_typ_kind with e K.
elim H1; auto with coc core arith datatypes.
Qed.




  Lemma class_red :
   forall (e : env) (T U K : term),
   typ e T K -> red T U -> cl_term T (class_env e) = cl_term U (class_env e).
intros.
cut (typ_skel (cl_term T (class_env e)) = typ_skel (cl_term U (class_env e))).
elim cl_term_red with (1 := H0) (2 := H); simpl in |- *; intros; trivial.
elim H1; trivial.

elim skel_sound with (1 := H); trivial.
apply skel_sound.
apply subject_reduction with (1 := H0) (2 := H).
Qed.
