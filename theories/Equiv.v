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
Require Import Ered.
Require Import Types.
Require Import ETypes.
Require Import Conv_Dec.
Require Import Strong_Norm.

Definition is_lam (t : term) :=
  exists T : term, (exists M : term, t = Abs T M).

Lemma normal_normal_abs :
 forall T M : term, normal T -> normal M -> normal (Abs T M).
intros; unfold normal, not in |- *; intros.
inversion_clear H1.
elim H with M'; auto with coc.
elim H0 with M'; auto with coc.
Qed.

Lemma normal_normal_app :
 forall M N : term, normal M -> normal N -> ~ is_lam M -> normal (App M N).
intros; unfold normal, not in |- *; intros.
generalize H H1; clear H H1; inversion_clear H2.
intros.
apply H1.
unfold is_lam in |- *; split with T; split with M0; trivial.
intros H1; elim H1 with N1; auto with coc.
elim H0 with N2; auto with coc.
Qed.


Lemma normal_normal_prod :
 forall T U : term, normal T -> normal U -> normal (Prod T U).
intros; unfold normal, not in |- *; intros.
inversion_clear H1.
elim H with N1; auto with coc.
elim H0 with N2; auto with coc.
Qed.

Hint Resolve normal_normal_abs normal_normal_app normal_normal_prod: ecoc.

Lemma normal_abs_inv :
 forall T M : term, normal (Abs T M) -> normal T /\ normal M.
unfold normal in |- *; intuition.
apply H with (Abs u M); auto with coc.
apply H with (Abs T u); auto with coc.
Qed.

Lemma normal_app_inv :
 forall M N : term, normal (App M N) -> normal M /\ normal N /\ ~ is_lam M.
unfold normal in |- *; intuition.
apply H with (App u N); auto with coc.
apply H with (App M u); auto with coc.
generalize H0; clear H0; unfold is_lam in |- *; intros (T, (x0, H0)).
rewrite H0 in H; apply H with (subst N x0); auto with coc.
Qed.

Lemma normal_prod_inv :
 forall T U : term, normal (Prod T U) -> normal T /\ normal U.
unfold normal in |- *; intuition.
apply H with (Prod u U); auto with coc.
apply H with (Prod T u); auto with coc.
Qed.


Inductive NF_Econv : term -> term -> Prop :=
  | nf_var : forall n : nat, NF_Econv (Ref n) (Ref n)
  | nf_app :
      forall M M' N N' : term,
      NF_Econv M M' ->
      ~ is_lam M -> NF_Econv N N' -> NF_Econv (App M N) (App M' N')
  | nf_lam :
      forall T T' M M' : term,
      NF_Econv M M' ->
      normal T -> normal T' -> NF_Econv (Abs T M) (Abs T' M')
  | nf_sort : forall s : sort, NF_Econv (Srt s) (Srt s)
  | nf_prod :
      forall T T' U U' : term,
      NF_Econv T T' -> NF_Econv U U' -> NF_Econv (Prod T U) (Prod T' U').

Hint Resolve nf_var nf_app nf_lam nf_sort nf_prod: ecoc.

Lemma normal_prop : normal (Srt prop).
unfold normal, not in |- *; intros.
inversion H.
Qed.
Hint Resolve normal_prop: ecoc.


Lemma not_is_lam_Ered1 :
 forall M N : term, Ered1 M N -> normal M -> ~ is_lam M -> ~ is_lam N.
simple induction 1; intros.
elim H0 with (subst N0 M0); auto with coc.
elim H1; unfold is_lam in |- *; split with T; split with M0; trivial.
elim H3; unfold is_lam in |- *; split with M0; split with N0; trivial.
elim H3; unfold is_lam in |- *; split with N0; split with M0; trivial.
unfold not in |- *; unfold is_lam in |- *; intros (x, (x0, H4)); discriminate.
unfold not in |- *; unfold is_lam in |- *; intros (x, (x0, H4)); discriminate.
unfold not in |- *; unfold is_lam in |- *; intros (x, (x0, H4)); discriminate.
unfold not in |- *; unfold is_lam in |- *; intros (x, (x0, H4)); discriminate.
Qed.

Hint Resolve not_is_lam_Ered1: ecoc.

Lemma Ered1_normal_normal :
 forall M N : term, Ered1 M N -> normal M -> normal N.
simple induction 1; intros.
elim H0 with (subst N0 M0); auto with coc.
elim (normal_abs_inv T M0 H0); auto with ecoc.
elim (normal_abs_inv M0 N0 H2); auto with ecoc.
elim (normal_abs_inv N0 M0 H2); auto with ecoc.
elim (normal_app_inv M1 M2 H2); intros.
elim H4; eauto with ecoc.
elim (normal_app_inv M1 M2 H2); intros.
elim H4; eauto with ecoc.
elim (normal_prod_inv M1 M2 H2); auto with ecoc.
elim (normal_prod_inv M1 M2 H2); auto with ecoc.
Qed.

Hint Resolve Ered1_normal_normal: ecoc.

Lemma refl_NF_Econv : forall t : term, normal t -> NF_Econv t t.
simple induction t; auto with ecoc; intros.
elim (normal_abs_inv t0 t1 H1); auto with ecoc.
elim (normal_app_inv t0 t1 H1); intros.
elim H3; auto with ecoc.
elim (normal_prod_inv t0 t1 H1); auto with ecoc.
Qed.

Hint Resolve refl_NF_Econv: ecoc.

Lemma NF_Econv_not_is_lam :
 forall M N : term, NF_Econv M N -> ~ is_lam M -> ~ is_lam N.
intros M N H; inversion_clear H; auto; intros.
unfold is_lam, not in |- *; intros (x, (x0, H3)); discriminate.
elim H; unfold is_lam in |- *; split with T; split with M0; trivial.
unfold is_lam, not in |- *; intros (x, (x0, H3)); discriminate.
Qed.

Hint Resolve NF_Econv_not_is_lam: ecoc.

Lemma sym_NF_Econv : forall M N : term, NF_Econv M N -> NF_Econv N M.
simple induction 1; eauto with ecoc; eauto with ecoc.
Qed.

Hint Resolve sym_NF_Econv: ecoc.

Lemma trans_NF_Econv_NF_Econv :
 forall M N : term,
 NF_Econv M N -> forall P : term, NF_Econv N P -> NF_Econv M P.
simple induction 1; auto with ecoc; intros.
inversion H5; auto with ecoc.
inversion H4; auto with ecoc.
inversion H4; auto with ecoc.
Qed.

Lemma Ered1_normal_NF_Econv :
 forall T T' : term, Ered1 T T' -> normal T -> NF_Econv T T'.
simple induction 1; intros.
elim H0 with (subst N M); auto with coc.
elim (normal_abs_inv T0 M H0); intros.
apply trans_NF_Econv_NF_Econv with (Abs (Srt prop) M); auto with ecoc.
elim (normal_abs_inv M N H2); eauto with ecoc.
elim (normal_abs_inv N M H2); eauto with ecoc.
elim (normal_app_inv M1 M2 H2); intros.
elim H4; eauto with ecoc.
elim (normal_app_inv M1 M2 H2); intros.
elim H4; eauto with ecoc.
elim (normal_prod_inv M1 M2 H2); auto with ecoc.
elim (normal_prod_inv M1 M2 H2); auto with ecoc.
Qed.

Hint Resolve Ered1_normal_NF_Econv: ecoc.

Lemma Ered_normal_NF_Econv :
 forall T T' : term, Ered T T' -> normal T -> NF_Econv T T'.
intros T T' H.
pattern T in |- *.
apply Ered1_Ered_ind with T'; auto with ecoc sets.
intros.
apply trans_NF_Econv_NF_Econv with R; eauto with ecoc.
Qed.

Hint Resolve Ered_normal_NF_Econv: ecoc.

Lemma normal_Econv_NF_conv :
 forall T T' : term, Econv T T' -> normal T -> normal T' -> NF_Econv T T'.
intros T T' H.
elim Econv_church_rosser with T T'; auto with ecoc; intros.
apply trans_NF_Econv_NF_Econv with x; eauto with ecoc.
Qed.

Hint Resolve normal_Econv_NF_conv: ecoc.


Lemma NF_Econv_Econv : forall M N : term, NF_Econv M N -> Econv M N.
simple induction 1; auto with ecoc.
Qed.
Hint Resolve NF_Econv_Econv: ecoc.

Inductive equiv_env (P : term -> term -> Prop) : env -> env -> Prop :=
  | EE_n : equiv_env P nil nil
  | EE_c :
      forall (t t' : term) (e e' : env),
      P t t' -> equiv_env P e e' -> equiv_env P (t :: e) (t' :: e').
 
Lemma equiv_env_item :
 forall (P : term -> term -> Prop) (n : nat) (e e' : env) (A B : term),
 item _ A e n -> item _ B e' n -> equiv_env P e e' -> P A B. 
intro P; simple induction n.
intros e e' A B H; inversion_clear H.
intros H; inversion_clear H; intros H; inversion H; trivial.

intros n0 H e e' A B H0; inversion_clear H0.
intros H0; inversion_clear H0; intros H0; inversion_clear H0; eauto.
Qed.


Lemma Etyp_NF_Econv_Econv :
 forall M M' : term,
 NF_Econv M M' ->
 ~ is_lam M ->
 forall (e e' : env) (A B : term),
 equiv_env Econv e e' -> Etyp e M A -> Etyp e' M' B -> Econv A B.

simple induction 1; intros.
apply inv_Etyp_ref with e A n; trivial; intros.
apply inv_Etyp_ref with e' B n; trivial; intros.
apply trans_Econv_Econv with (lift (S n) U); trivial.
apply trans_Econv_Econv with (lift (S n) U0); auto with ecoc.
unfold lift in |- *; apply Econv_Econv_lift.
apply equiv_env_item with n e e'; trivial.

apply inv_Etyp_app with e M0 N A; trivial.
intros.
apply inv_Etyp_app with e' M'0 N' B; trivial.
intros.
apply trans_Econv_Econv with (subst N Ur); trivial.
apply sym_Econv; apply trans_Econv_Econv with (subst N' Ur0); trivial.
unfold subst in |- *; apply Econv_Econv_subst.
apply sym_Econv; apply NF_Econv_Econv; trivial.

cut (Econv (Prod V Ur) (Prod V0 Ur0)).
intros.
apply sym_Econv.
eapply inv_Econv_prod_r; eauto.

apply H1 with e e'; trivial.

elim H4; unfold is_lam in |- *; split with T; split with M0; trivial.

generalize H2 H3; clear H2 H3; case s; intros.
elim (inv_Etyp_kind e A H2).

apply trans_Econv_Econv with (Srt kind).
eapply inv_Etyp_prop; eauto.

apply sym_Econv; eapply inv_Etyp_prop; eauto.

apply trans_Econv_Econv with (Srt kind).
eapply inv_Etyp_set; eauto.

apply sym_Econv; eapply inv_Etyp_set; eauto.

apply inv_Etyp_prod with e T U A; trivial; intros.
apply inv_Etyp_prod with e' T' U' B; trivial; intros.
apply trans_Econv_Econv with (Srt s2); auto with ecoc.
apply trans_Econv_Econv with (Srt s3); auto with ecoc.
apply H3 with (T :: e) (T' :: e'); trivial.
unfold not, is_lam in |- *; intros (x, (x0, H14)).
rewrite H14 in H9.
apply inv_Etyp_abs with (T :: e) x x0 (Srt s2); trivial.
intros.
elim (Econv_sort_prod s2 x T0); auto with ecoc.

constructor; auto with ecoc.
Qed.

Lemma refl_equiv_env : forall e : env, equiv_env Econv e e.
simple induction e; constructor; auto with ecoc.
Qed.
Hint Resolve refl_equiv_env: ecoc.

Lemma Econv_eq :
 forall (e : env) (a Ta : term),
 Etyp e a Ta ->
 forall b Tb : term, Etyp e b Tb -> NF_Econv a b -> Econv Ta Tb -> a = b.

simple induction 1; intros.
(* sort et var *)
inversion H2; trivial.
inversion H2; trivial.
inversion H3; trivial.

(* Abs *)
inversion H7.
rewrite <- H13 in H6.
apply inv_Etyp_abs with e0 T' M' Tb; trivial.
intros; cut (T = T'); intros.
rewrite H19; cut (M = M'); intros.
rewrite H20; trivial.
apply H5 with T1; trivial.
rewrite H19; trivial.
apply inv_Econv_prod_r with T T'.
apply trans_Econv_Econv with Tb; auto with ecoc.
apply H1 with (Srt s0); trivial.
apply normal_Econv_NF_conv; trivial.
apply inv_Econv_prod_l with U T1.
apply trans_Econv_Econv with Tb; auto with ecoc.
cut (Econv T T').
intros; apply Etyp_NF_Econv_Econv with T T' e0 e0; auto with ecoc.
unfold not, is_lam in |- *; intros (x, (x0, H20)).
rewrite H20 in H0.
apply inv_Etyp_abs with e0 x x0 (Srt s1); trivial.
intros.
elim (Econv_sort_prod s1 x T2); auto with ecoc.
apply inv_Econv_prod_l with U T1.
apply trans_Econv_Econv with Tb; auto with ecoc.

(* App *)
inversion H5.
rewrite <- H11 in H4.
apply inv_Etyp_app with e0 M' N' Tb; trivial.

intros; cut (u = M').
intros; cut (v = N').
intros; rewrite H16; rewrite H17; trivial.

apply H1 with V0; trivial.
apply inv_Econv_prod_l with Ur Ur0.
apply Etyp_NF_Econv_Econv with u M' e0 e0; auto with ecoc.

apply H3 with (Prod V0 Ur0); trivial.
apply Etyp_NF_Econv_Econv with u M' e0 e0; auto with ecoc.

(* Prod *)
inversion H5.
rewrite <- H10 in H4.
apply inv_Etyp_prod with e0 T' U' Tb; trivial.
intros; cut (T = T').
intros; cut (U = U').
intros; rewrite H15; rewrite H16; trivial.

apply H3 with (Srt s3); auto.
rewrite H15; trivial.

apply trans_Econv_Econv with Tb; auto with ecoc.

apply H1 with (Srt s0); auto.
apply Etyp_NF_Econv_Econv with T T' e0 e0; auto with ecoc.
unfold not, is_lam in |- *; intros (x, (x0, H15)).
rewrite H15 in H0.
apply inv_Etyp_abs with e0 x x0 (Srt s1); trivial.
intros.
elim (Econv_sort_prod s1 x T1); auto with ecoc.

(* Conv *)
apply H1 with Tb; trivial.
apply trans_Econv_Econv with V; auto with ecoc.
Qed.


Lemma typ_is_nf :
 forall (e : env) (a Ta : term),
 typ e a Ta -> exists a' : term, red a a' /\ normal a' /\ typ e a' Ta.
intros.
elim (compute_nf a).
intros; split with x; intuition; trivial.
apply subject_reduction with a; trivial.
apply str_norm with e Ta; trivial.
Qed.


Lemma EConv_Conv :
 forall (e : env) (a b Ta Tb : term),
 typ e a Ta -> typ e b Tb -> Econv a b -> Econv Ta Tb -> conv a b.
intros.
generalize (typ_is_nf e a Ta H).
generalize (typ_is_nf e b Tb H0).
intros (x, H3) (x0, H4); intuition.
cut (x = x0).
intros.
rewrite <- H7 in H3.
apply trans_conv_conv with x; auto with coc.
apply sym_conv; auto with coc.
apply Econv_eq with e Tb Ta; auto with coc ecoc.
apply typ_Etyp; trivial.
apply typ_Etyp; trivial.
apply normal_Econv_NF_conv; trivial.
apply trans_Econv_Econv with b.
apply sym_Econv; apply Ered_Econv; auto with ecoc.
apply trans_Econv_Econv with a; auto with ecoc.
apply Ered_Econv; auto with ecoc.
Qed.

Lemma typ_sort_Econv_Econv :
 forall (e : env) (V U : term) (r s : sort),
 typ e V (Srt s) -> typ e U (Srt r) -> Econv U V -> Econv (Srt s) (Srt r).
intros.
generalize (typ_is_nf e V (Srt s) H).
generalize (typ_is_nf e U (Srt r) H0).
intros (x, H2) (x0, H3); intuition.
apply Etyp_NF_Econv_Econv with x0 x e e; eauto with ecoc.
apply normal_Econv_NF_conv; auto with ecoc.
apply trans_Econv_Econv with U; auto with ecoc.
apply sym_Econv.
apply trans_Econv_Econv with V; trivial.
apply Ered_Econv; auto with ecoc.

apply Ered_Econv; auto with ecoc.

unfold not in |- *; unfold is_lam in |- *; intros (x1, (x2, H6)).
rewrite H6 in H8.
apply inv_Etyp_abs with e x1 x2 (Srt s); trivial.
apply typ_Etyp; trivial.

intros.
elim (Econv_sort_prod s x1 T); auto with ecoc.

apply typ_Etyp; trivial.

apply typ_Etyp; trivial.
Qed.


Lemma Etyp_typ : forall (e : env) (M t : term), Etyp e M t -> typ e M t.
fix Etyp_typ 4.
intros.
case H.
intros; apply type_prop.
case H0.
apply wf_nil.
intros; apply wf_var with s.
apply Etyp_typ; trivial.
intros; apply type_set.
case H0.
apply wf_nil.
intros; apply wf_var with s.
apply Etyp_typ; trivial.
intros; apply type_var.
case H0.
apply wf_nil.
intros; apply wf_var with s.
apply Etyp_typ; trivial.
trivial.
intros.
apply type_abs with s1 s2.
apply Etyp_typ; trivial.
apply Etyp_typ; trivial.
apply Etyp_typ; trivial.
intros; apply type_app with V.
apply Etyp_typ; trivial.
apply Etyp_typ; trivial.
intros.
apply type_prod with s1.
apply Etyp_typ; trivial.
apply Etyp_typ; trivial.
intros.
generalize (Etyp_typ e0 t0 U H0); intros.
generalize (Etyp_typ e0 V (Srt s) H2); intros.
generalize (type_case e0 t0 U H3).
intros [(x, H5)| H6].
apply type_conv with U s; trivial.
apply EConv_Conv with e0 (Srt x) (Srt s); trivial.
apply typ_sort_Econv_Econv with e0 U V; auto with ecoc.
rewrite H6 in H1.
elim (inv_Etyp_Econv_kind e0 V (Srt s)); auto with ecoc.
Qed.
