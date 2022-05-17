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

Inductive Ered1 : term -> term -> Prop :=
  | Ebeta : forall M N T : term, Ered1 (App (Abs T M) N) (subst N M)
  | Eabs : forall M T : term, Ered1 (Abs T M) (Abs (Srt prop) M)
  | Eabs_red_l :
      forall M M' : term,
      Ered1 M M' -> forall N : term, Ered1 (Abs M N) (Abs M' N)
  | Eabs_red_r :
      forall M M' : term,
      Ered1 M M' -> forall N : term, Ered1 (Abs N M) (Abs N M')
  | Eapp_red_l :
      forall M1 N1 : term,
      Ered1 M1 N1 -> forall M2 : term, Ered1 (App M1 M2) (App N1 M2)
  | Eapp_red_r :
      forall M2 N2 : term,
      Ered1 M2 N2 -> forall M1 : term, Ered1 (App M1 M2) (App M1 N2)
  | Eprod_red_l :
      forall M1 N1 : term,
      Ered1 M1 N1 -> forall M2 : term, Ered1 (Prod M1 M2) (Prod N1 M2)
  | Eprod_red_r :
      forall M2 N2 : term,
      Ered1 M2 N2 -> forall M1 : term, Ered1 (Prod M1 M2) (Prod M1 N2).

Inductive Ered (M : term) : term -> Prop :=
  | Erefl : Ered M M
  | Etrans_red : forall P N : term, Ered M P -> Ered1 P N -> Ered M N.

Inductive Econv (M : term) : term -> Prop :=
  | Erefl_conv : Econv M M
  | Etrans_conv_red : forall P N : term, Econv M P -> Ered1 P N -> Econv M N
  | Etrans_conv_exp : forall P N : term, Econv M P -> Ered1 N P -> Econv M N.

Inductive Epar_red1 : term -> term -> Prop :=
  | Epar_beta :
      forall M M' : term,
      Epar_red1 M M' ->
      forall N N' : term,
      Epar_red1 N N' ->
      forall T : term, Epar_red1 (App (Abs T M) N) (subst N' M')
  | Epar_abs :
      forall M M' : term,
      Epar_red1 M M' ->
      forall T : term, Epar_red1 (Abs T M) (Abs (Srt prop) M')
  | Esort_par_red : forall s : sort, Epar_red1 (Srt s) (Srt s)
  | Eref_par_red : forall n : nat, Epar_red1 (Ref n) (Ref n)
  | Eabs_par_red :
      forall M M' : term,
      Epar_red1 M M' ->
      forall T T' : term, Epar_red1 T T' -> Epar_red1 (Abs T M) (Abs T' M')
  | Eapp_par_red :
      forall M M' : term,
      Epar_red1 M M' ->
      forall N N' : term, Epar_red1 N N' -> Epar_red1 (App M N) (App M' N')
  | Eprod_par_red :
      forall M M' : term,
      Epar_red1 M M' ->
      forall N N' : term, Epar_red1 N N' -> Epar_red1 (Prod M N) (Prod M' N').

  Definition Epar_red := clos_trans term Epar_red1.

  Definition Enormal (t : term) : Prop := forall u : term, ~ Ered1 t u.

Hint Resolve Erefl Ebeta Eabs Eabs_red_l Eabs_red_r Eapp_red_l Eapp_red_r
  Eprod_red_l Eprod_red_r: ecoc.

Hint Resolve Etrans_red: ecoc.
Hint Resolve Erefl_conv Etrans_conv_red Etrans_conv_exp: ecoc.
Hint Resolve Epar_beta Epar_abs Esort_par_red Eref_par_red Eabs_par_red
  Eapp_par_red Eprod_par_red: ecoc.

(* normal -> E *)
Lemma red1_Ered1 : forall M N : term, red1 M N -> Ered1 M N.
simple induction 1; auto with ecoc.
Qed.

Hint Resolve red1_Ered1: ecoc.

Lemma red_Ered : forall M N : term, red M N -> Ered M N.
simple induction 1; eauto with ecoc.
Qed.

Hint Resolve red_Ered: ecoc.

Lemma conv_Econv : forall M N : term, conv M N -> Econv M N.
simple induction 1; eauto with ecoc.
Qed.

Hint Resolve conv_Econv: ecoc.

(* Ered *)

Lemma trans_Ered_Ered : forall M N P : term, Ered M N -> Ered N P -> Ered M P.
intros.
generalize H0 M H.
simple induction 1; auto with ecoc coc core arith sets.
intros; apply Etrans_red with P0; auto with ecoc coc core arith sets.
Qed.
 
(* Epar_red1 *)
Lemma refl_Epar_red1 : forall M : term, Epar_red1 M M.
simple induction M; auto with coc ecoc core arith sets.
Qed.

Hint Resolve refl_Epar_red1: ecoc.

Lemma Epar_red1_Epar_red : forall M N : term, Epar_red1 M N -> Epar_red M N.
intros; unfold Epar_red in |- *; apply t_trans with M; auto with ecoc sets.
Qed.

Hint Resolve Epar_red1_Epar_red: ecoc.

Lemma Epar_red1_lift :
 forall (n : nat) (a b : term),
 Epar_red1 a b -> forall k : nat, Epar_red1 (lift_rec n a k) (lift_rec n b k).
simple induction 1; simpl in |- *; eauto with coc ecoc core arith sets.
intros.
rewrite distr_lift_subst; auto with coc ecoc core arith sets.
Qed.

Hint Resolve Epar_red1_lift: ecoc.

Lemma Epar_red1_subst :
 forall c d : term,
 Epar_red1 c d ->
 forall a b : term,
 Epar_red1 a b ->
 forall k : nat, Epar_red1 (subst_rec a c k) (subst_rec b d k).
simple induction 1; simpl in |- *; eauto with coc ecoc core arith sets;
 intros.
rewrite distr_subst; auto with coc ecoc core arith sets.

elim (lt_eq_lt_dec k n); auto with coc ecoc core arith sets; intro a0.
elim a0; intros; auto with coc ecoc core arith sets.
unfold lift in |- *; auto with ecoc.
Qed.

Hint Resolve Epar_red1_subst: ecoc.

Lemma inv_Epar_red_abs :
 forall (P : Prop) (T U x : term),
 Epar_red1 (Abs T U) x ->
 (forall T' U' : term, x = Abs T' U' -> Epar_red1 U U' -> P) -> P.
do 5 intro.
inversion_clear H; intros.
apply H with (Srt prop) M'; auto with ecoc.
apply H with T' M'; auto with ecoc.
Qed.
  
Lemma Ered1_Epar_red1 : forall M N : term, Ered1 M N -> Epar_red1 M N.
simple induction 1; eauto with ecoc coc core arith sets; intros.
Qed.

Hint Resolve Ered1_Epar_red1: ecoc.

Lemma Ered_Epar_red : forall M N : term, Ered M N -> Epar_red M N.
red in |- *; simple induction 1; intros; auto with ecoc coc core arith sets.
apply t_trans with P; auto with ecoc coc core arith sets.
Qed.

Lemma Ered_Ered_app :
 forall u u0 v v0 : term,
 Ered u u0 -> Ered v v0 -> Ered (App u v) (App u0 v0).
simple induction 1.
simple induction 1; intros; auto with ecoc coc core arith sets.
apply Etrans_red with (App u P); auto with ecoc coc core arith sets.

intros; apply Etrans_red with (App P v0); auto with ecoc coc core arith sets.
Qed.


Lemma Ered_Ered_abs :
 forall u u0 v v0 : term,
 Ered u u0 -> Ered v v0 -> Ered (Abs u v) (Abs u0 v0).
simple induction 1.
simple induction 1; intros; auto with ecoc coc core arith sets.
apply Etrans_red with (Abs u P); auto with ecoc coc core arith sets.

intros; apply Etrans_red with (Abs P v0); auto with ecoc coc core arith sets.
Qed.


Lemma Ered_Ered_prod :
 forall u u0 v v0 : term,
 Ered u u0 -> Ered v v0 -> Ered (Prod u v) (Prod u0 v0).
simple induction 1.
simple induction 1; intros; auto with ecoc coc core arith sets.
apply Etrans_red with (Prod u P); auto with ecoc coc core arith sets.

intros; apply Etrans_red with (Prod P v0); auto with ecoc coc core arith sets.
Qed.

Hint Resolve Ered_Ered_app Ered_Ered_abs Ered_Ered_prod: ecoc.

Lemma Epar_red_Ered : forall M N : term, Epar_red M N -> Ered M N.
simple induction 1.
simple induction 1; intros; eauto with ecoc coc core arith sets.

intros; apply trans_Ered_Ered with y; auto with ecoc coc core arith sets.
Qed.

Hint Resolve Ered_Epar_red Epar_red_Ered: ecoc.

(* Ered1 *)
Lemma Ered1_lift :
 forall u v : term,
 Ered1 u v -> forall n k : nat, Ered1 (lift_rec n u k) (lift_rec n v k).
simple induction 1; simpl in |- *; intros; auto with ecoc coc core arith sets.
rewrite distr_lift_subst; auto with ecoc coc core arith sets.
Qed.

Hint Resolve Ered1_lift: ecoc.


Lemma Ered1_subst_r :
 forall t u : term,
 Ered1 t u ->
 forall (a : term) (k : nat), Ered1 (subst_rec a t k) (subst_rec a u k).
simple induction 1; simpl in |- *; intros; auto with ecoc coc core arith sets.
rewrite distr_subst; auto with ecoc coc core arith sets.
Qed.


Lemma Ered1_subst_l :
 forall (a t u : term) (k : nat),
 Ered1 t u -> Ered (subst_rec t a k) (subst_rec u a k).
simple induction a; simpl in |- *; auto with ecoc coc core arith sets.
intros.
elim (lt_eq_lt_dec k n);
 [ intro a0 | intro b; auto with ecoc coc core arith sets ].
elim a0; auto with ecoc coc core arith sets.
unfold lift in |- *; auto with ecoc coc core arith sets.
Qed.

Hint Resolve Ered1_subst_l Ered1_subst_r: ecoc.

Lemma subst_rec_Ered1_r :
 forall N M M' : term,
 Ered1 M M' -> forall k : nat, Ered1 (subst_rec N M k) (subst_rec N M' k).
simple induction 1; simpl in |- *; intros; auto with ecoc.
rewrite distr_subst.
auto with ecoc.
Qed.

Lemma subst_Ered1_r :
 forall N M M' : term, Ered1 M M' -> Ered1 (subst N M) (subst N M').
unfold subst in |- *; intros; apply subst_rec_Ered1_r; trivial.
Qed.





(* church_rosser *)
Lemma str_confluence_Epar_red1 : str_confluent Epar_red1.
red in |- *; red in |- *.
simple induction 1; intros.
inversion_clear H4.
elim H1 with M'0; auto with ecoc coc core arith sets; intros.
elim H3 with N'0; auto with ecoc coc core arith sets; intros.
split with (subst x1 x0); unfold subst in |- *;
 auto with coc ecoc core arith sets.

inversion_clear H5.
elim H1 with M'1; auto with ecoc coc core arith sets; intros.
elim H3 with N'0; auto with ecoc coc core arith sets; intros.
split with (subst x1 x0); auto with ecoc coc core arith sets.
unfold subst in |- *; auto with ecoc coc core arith sets.

elim H1 with M'1; auto with ecoc coc core arith sets; intros.
elim H3 with N'0; auto with ecoc coc core arith sets; intros.
split with (subst x1 x0); auto with ecoc coc core arith sets.
unfold subst in |- *; auto with ecoc coc core arith sets.

inversion_clear H2.
elim H1 with M'0; auto with ecoc coc core arith sets; intros.
split with (Abs (Srt prop) x0); eauto with ecoc coc core arith sets; intros.

elim H1 with M'0; auto with ecoc coc core arith sets; intros.
split with (Abs (Srt prop) x0); eauto with ecoc coc core arith sets.

inversion_clear H0.
split with (Srt s); auto with ecoc coc core arith sets.

inversion_clear H0.
split with (Ref n); auto with ecoc coc core arith sets.

inversion_clear H4.
elim H1 with M'0; auto with ecoc coc core arith sets; intros.
split with (Abs (Srt prop) x0); eauto with ecoc coc core arith sets.

elim H1 with M'0; auto with ecoc coc core arith sets; intros.
elim H3 with T'0; auto with ecoc coc core arith sets; intros.
split with (Abs x1 x0); auto with ecoc coc core arith sets.

generalize H0 H1.
clear H0 H1.
inversion_clear H4.
intro.
inversion_clear H4.
intros.
elim H4 with (Abs (Srt prop) M'0); auto with coc core arith sets; intros.
elim H3 with N'0; auto with coc core arith sets; intros.
apply inv_Epar_red_abs with (Srt prop) M'1 x0; intros;
 auto with coc core arith sets.
rewrite H10 in H7; inversion_clear H7.
split with (subst x1 U'); auto with ecoc sets.
unfold subst in |- *; auto with ecoc coc core arith sets.

split with (subst x1 U'); auto with ecoc sets.
unfold subst in |- *; auto with ecoc coc core arith sets.

auto with ecoc sets.

intros.
elim H3 with N'0; auto with ecoc sets; intros.
elim H4 with (Abs T' M'0); auto with ecoc sets; intros.
apply inv_Epar_red_abs with T' M'0 x1; intros; auto with coc core arith sets.
rewrite H11 in H9; inversion_clear H9.
split with (subst x0 U'); auto with ecoc sets.
unfold subst in |- *; auto with ecoc coc core arith sets.

split with (subst x0 U'); auto with ecoc sets.
unfold subst in |- *; auto with ecoc coc core arith sets.

intros.
elim H5 with M'0; auto with ecoc sets; intros.
elim H3 with N'0; auto with ecoc sets; intros.
split with (App x0 x1); auto with ecoc sets.

inversion_clear H4.
elim H1 with M'0; auto with coc ecoc sets; intros.
elim H3 with N'0; auto with coc ecoc sets; intros.
split with (Prod x0 x1); auto with ecoc sets.
Qed.

Lemma strip_lemma_Epar_red1 : commut _ Epar_red (transp _ Epar_red1).
unfold commut, Epar_red in |- *; simple induction 1; intros.
elim str_confluence_Epar_red1 with z x0 y0;
 auto with ecoc coc core arith sets; intros.
split with x1; auto with ecoc coc core arith sets.

elim H1 with z0; auto with ecoc coc core arith sets; intros.
elim H3 with x1; intros; auto with ecoc coc core arith sets.
split with x2; auto with ecoc coc core arith sets.
apply t_trans with x1; auto with ecoc coc core arith sets.
Qed.

Lemma confluence_Epar_red : str_confluent Epar_red.
red in |- *; red in |- *.
simple induction 1; intros.
elim strip_lemma_Epar_red1 with z x0 y0; intros;
 auto with ecoc coc core arith sets.
split with x1; auto with ecoc coc core arith sets.

elim H1 with z0; intros; auto with ecoc coc core arith sets.
elim H3 with x1; intros; auto with ecoc coc core arith sets.
split with x2; auto with ecoc coc core arith sets.
red in |- *; apply t_trans with x1; auto with ecoc coc core arith sets.
Qed.

Lemma confluence_Ered : str_confluent Ered.
red in |- *; red in |- *.
intros.
elim confluence_Epar_red with x y z; auto with ecoc coc core arith sets;
 intros.
exists x0; auto with ecoc coc core arith sets.
Qed.

Theorem Econv_church_rosser :
 forall u v : term,
 Econv u v -> ex2 (fun t : term => Ered u t) (fun t : term => Ered v t).
simple induction 1; intros.
exists u; auto with ecoc coc core arith sets.

elim H1; intros.
elim confluence_Ered with x P N; auto with ecoc coc core arith sets; intros.
exists x0; auto with ecoc coc core arith sets.
apply trans_Ered_Ered with x; auto with ecoc coc core arith sets.

elim H1; intros.
exists x; auto with ecoc coc core arith sets.
apply trans_Ered_Ered with P; auto with ecoc coc core arith sets.
Qed.

(* Econv *)

Lemma one_step_Econv_exp : forall M N : term, Ered1 M N -> Econv N M.
intros.
apply Etrans_conv_exp with N; auto with ecoc coc core arith sets.
Qed.


Lemma Ered_Econv : forall M N : term, Ered M N -> Econv M N.
simple induction 1; auto with ecoc coc core arith sets.
intros; apply Etrans_conv_red with P; auto with ecoc coc core arith sets.
Qed.

Hint Resolve one_step_Econv_exp Ered_Econv: coc.

Lemma sym_Econv : forall M N : term, Econv M N -> Econv N M.
simple induction 1; auto with ecoc coc core arith sets.
simple induction 2; intros; auto with ecoc coc core arith sets.
apply Etrans_conv_red with P0; auto with ecoc coc core arith sets.

apply Etrans_conv_exp with P0; auto with ecoc coc core arith sets.

simple induction 2; intros; auto with ecoc coc core arith sets.
apply Etrans_conv_red with P0; auto with ecoc coc core arith sets.

apply Etrans_conv_exp with P0; auto with ecoc coc core arith sets.
Qed.

Hint Immediate sym_Econv: coc.

Lemma trans_Econv_Econv :
 forall M N P : term, Econv M N -> Econv N P -> Econv M P.
intros.
generalize M H; elim H0; intros; auto with ecoc coc core arith sets.
apply Etrans_conv_red with P0; auto with ecoc coc core arith sets.
apply Etrans_conv_exp with P0; auto with ecoc coc core arith sets.
Qed.

Lemma Econv_Econv_prod :
 forall a b c d : term, Econv a b -> Econv c d -> Econv (Prod a c) (Prod b d).
intros.
apply trans_Econv_Econv with (Prod a d).
elim H0; intros; auto with ecoc coc core arith sets.
apply Etrans_conv_red with (Prod a P); auto with ecoc coc core arith sets.

apply Etrans_conv_exp with (Prod a P); auto with ecoc coc core arith sets.

elim H; intros; auto with ecoc coc core arith sets.
apply Etrans_conv_red with (Prod P d); auto with ecoc coc core arith sets.

apply Etrans_conv_exp with (Prod P d); auto with ecoc coc core arith sets.
Qed.

Lemma Econv_Econv_app :
 forall a b c d : term, Econv a b -> Econv c d -> Econv (App a c) (App b d).
intros.
apply trans_Econv_Econv with (App a d).
elim H0; intros; auto with ecoc coc core arith sets.
apply Etrans_conv_red with (App a P); auto with ecoc coc core arith sets.

apply Etrans_conv_exp with (App a P); auto with ecoc coc core arith sets.

elim H; intros; auto with ecoc coc core arith sets.
apply Etrans_conv_red with (App P d); auto with ecoc coc core arith sets.

apply Etrans_conv_exp with (App P d); auto with ecoc coc core arith sets.
Qed.

Hint Resolve Econv_Econv_prod Econv_Econv_app: ecoc.

Lemma Ered_Enormal : forall u v : term, Ered u v -> Enormal u -> u = v.
simple induction 1; auto with ecoc coc core arith sets; intros.
absurd (Ered1 u N); auto with ecoc coc core arith sets.
absurd (Ered1 P N); auto with ecoc coc core arith sets.
elim (H1 H3).
unfold not in |- *; intro; apply (H3 N); auto with ecoc coc core arith sets.
Qed.

Lemma Ered_prod_prod :
 forall u v t : term,
 Ered (Prod u v) t ->
 forall P : Prop,
 (forall a b : term, t = Prod a b -> Ered u a -> Ered v b -> P) -> P.
simple induction 1; intros.
apply H0 with u v; auto with ecoc coc core arith sets.

apply H1; intros.
inversion_clear H4 in H2.
inversion H2.
apply H3 with N1 b; auto with ecoc coc core arith sets.
apply Etrans_red with a; auto with ecoc coc core arith sets.

apply H3 with a N2; auto with ecoc coc core arith sets.
apply Etrans_red with b; auto with ecoc coc core arith sets.
Qed.

Lemma Econv_sort_prod :
 forall (s : sort) (t u : term), ~ Econv (Srt s) (Prod t u).
red in |- *; intros.
elim Econv_church_rosser with (Srt s) (Prod t u);
 auto with ecoc coc core arith sets.
do 2 intro.
elim Ered_Enormal with (Srt s) x; auto with ecoc coc core arith sets.
intro.
apply Ered_prod_prod with t u (Srt s); auto with ecoc coc core arith sets;
 intros.
discriminate H2.

red in |- *; red in |- *; intros.
inversion_clear H1.
Qed.

Lemma Econv_abs : forall a b T : term, Econv a b -> Econv (Abs T a) (Abs T b).
intros.
elim H; intros; auto with ecoc coc core arith sets.
apply Etrans_conv_red with (Abs T P); auto with ecoc coc core arith sets.
apply Etrans_conv_exp with (Abs T P); auto with ecoc coc core arith sets.
Qed.

Hint Resolve Econv_abs: ecoc.

Lemma Econv_Type_abs :
 forall a b T T' : term, Econv a b -> Econv (Abs T a) (Abs T' b).
intros.
apply trans_Econv_Econv with (Abs (Srt prop) a); eauto with ecoc.
Qed.

Hint Resolve Econv_Type_abs: ecoc.

Lemma Econv_Econv_lift :
 forall (a b : term) (n k : nat),
 Econv a b -> Econv (lift_rec n a k) (lift_rec n b k).
intros.
elim H; intros; auto with ecoc coc core arith sets.
apply Etrans_conv_red with (lift_rec n P k);
 auto with ecoc coc core arith sets.

apply Etrans_conv_exp with (lift_rec n P k);
 auto with ecoc coc core arith sets.
Qed.
 
Lemma Econv_Econv_subst :
 forall (a b c d : term) (k : nat),
 Econv a b -> Econv c d -> Econv (subst_rec a c k) (subst_rec b d k).
intros.
apply trans_Econv_Econv with (subst_rec a d k).
elim H0; intros; auto with ecoc coc core arith sets.
apply Etrans_conv_red with (subst_rec a P k);
 auto with ecoc coc core arith sets.

apply Etrans_conv_exp with (subst_rec a P k);
 auto with ecoc coc core arith sets.

elim H; intros; auto with ecoc coc core arith sets.
apply trans_Econv_Econv with (subst_rec P d k);
 auto with ecoc coc core arith sets.

apply trans_Econv_Econv with (subst_rec P d k);
 auto with ecoc coc core arith sets.
apply sym_Econv; auto with ecoc coc core arith sets.
Qed.

Lemma inv_Econv_prod_l :
 forall a b c d : term, Econv (Prod a c) (Prod b d) -> Econv a b.
intros.
elim Econv_church_rosser with (Prod a c) (Prod b d); intros;
 auto with ecoc coc core arith sets.
apply Ered_prod_prod with a c x; intros; auto with ecoc coc core arith sets.
apply Ered_prod_prod with b d x; intros; auto with ecoc coc core arith sets.
apply trans_Econv_Econv with a0; auto with ecoc coc core arith sets.
apply sym_Econv.
generalize H2.
rewrite H5; intro.
injection H8.
simple induction 2; auto with ecoc coc core arith sets.
Qed.

Lemma inv_Econv_prod_r :
 forall a b c d : term, Econv (Prod a c) (Prod b d) -> Econv c d.
intros.
elim Econv_church_rosser with (Prod a c) (Prod b d); intros;
 auto with ecoc coc core arith sets.
apply Ered_prod_prod with a c x; intros; auto with ecoc coc core arith sets.
apply Ered_prod_prod with b d x; intros; auto with ecoc coc core arith sets.
apply trans_Econv_Econv with b0; auto with ecoc coc core arith sets.
apply sym_Econv.
generalize H2.
rewrite H5; intro.
injection H8.
simple induction 1; auto with ecoc coc core arith sets.
Qed.

Hint Resolve sym_Econv trans_Econv_Econv Econv_Econv_prod Econv_Econv_lift
  Econv_Econv_subst: ecoc.

Lemma Ered1_Ered_ind :
 forall (N : term) (P : term -> Prop),
 P N ->
 (forall M R : term, Ered1 M R -> Ered R N -> P R -> P M) ->
 forall M : term, Ered M N -> P M.
cut
 (forall M N : term,
  Ered M N ->
  forall P : term -> Prop,
  P N -> (forall M R : term, Ered1 M R -> Ered R N -> P R -> P M) -> P M).
intros.
apply (H M N); auto with ecoc coc core arith sets.

simple induction 1; intros; auto with ecoc coc core arith sets.
apply H1; auto with ecoc coc core arith sets.
apply H4 with N0; auto with ecoc coc core arith sets.

intros.
apply H4 with R; auto with ecoc coc core arith sets.
apply Etrans_red with P; auto with ecoc coc core arith sets.
Qed.


Lemma inv_Ered_Abs :
 forall T U x : term,
 Ered (Abs T U) x -> exists T' : term, (exists U' : term, x = Abs T' U').
simple induction 1.
split with T; split with U; trivial.
intros P N H0 (T', (U', H1)) H2.
rewrite H1 in H2.
inversion H2.
split with (Srt prop); split with U'; trivial.
split with M'; split with U'; trivial.
split with T'; split with M'; trivial.
Qed.

Lemma not_Ered_Abs_sort :
 forall (T M : term) (s : sort), ~ Ered (Abs T M) (Srt s).
unfold not in |- *; intros.
inversion H.
generalize (inv_Ered_Abs T M P H0).
intros (T', (U', H3)).
rewrite H3 in H1; inversion H1.
Qed.


Lemma Ered1_sort_mem :
 forall (t : term) (s : sort), Ered1 t (Srt s) -> mem_sort s t.
intros.
inversion H.
elim mem_sort_subst with M N 0 s; intros; auto with coc core arith sets.
unfold subst in H2; rewrite H2.
auto with coc.
Qed.

Inductive mem_sort2 (s : sort) : term -> Prop :=
  | mem_eq2 : mem_sort2 s (Srt s)
  | mem_prod_l2 : forall u v : term, mem_sort2 s u -> mem_sort2 s (Prod u v)
  | mem_prod_r2 : forall u v : term, mem_sort2 s v -> mem_sort2 s (Prod u v)
  | mem_abs_r2 : forall u v : term, mem_sort2 s v -> mem_sort2 s (Abs u v)
  | mem_app_l2 : forall u v : term, mem_sort2 s u -> mem_sort2 s (App u v)
  | mem_app_r2 : forall u v : term, mem_sort2 s v -> mem_sort2 s (App u v).

Hint Resolve mem_eq2 mem_prod_l2 mem_prod_r2 mem_abs_r2 mem_app_l2
  mem_app_r2: ecoc.

Lemma mem_sort2_lift :
 forall (t : term) (n k : nat) (s : sort),
 mem_sort2 s (lift_rec n t k) -> mem_sort2 s t.
simple induction t; simpl in |- *; intros; auto with ecoc coc core arith sets.
generalize H; elim (le_gt_dec k n); intros;
 auto with ecoc coc core arith sets.
inversion_clear H0.

inversion_clear H1.
apply mem_abs_r2; apply H0 with n (S k); auto with ecoc coc core arith sets.

inversion_clear H1.
apply mem_app_l2; apply H with n k; auto with ecoc coc core arith sets.

apply mem_app_r2; apply H0 with n k; auto with ecoc coc core arith sets.

inversion_clear H1.
apply mem_prod_l2; apply H with n k; auto with ecoc coc core arith sets.

apply mem_prod_r2; apply H0 with n (S k); auto with ecoc coc core arith sets.
Qed.


Lemma mem_sort2_subst :
 forall (b a : term) (n : nat) (s : sort),
 mem_sort2 s (subst_rec a b n) -> mem_sort2 s a \/ mem_sort2 s b.
simple induction b; simpl in |- *; intros; auto with ecoc coc core arith sets.
generalize H; elim (lt_eq_lt_dec n0 n); [ intro a0 | intro b0 ].
elim a0; intros.
inversion_clear H0.

left.
apply mem_sort2_lift with n0 0; auto with ecoc coc core arith sets.

intros.
inversion_clear H0.

inversion_clear H1.
elim H0 with a (S n) s; auto with ecoc coc core arith sets.

inversion_clear H1.
elim H with a n s; auto with ecoc coc core arith sets.

elim H0 with a n s; auto with ecoc coc core arith sets.

inversion_clear H1.
elim H with a n s; auto with ecoc coc core arith sets.

elim H0 with a (S n) s; intros; auto with ecoc coc core arith sets.
Qed.

Lemma Ered_sort_mem2 :
 forall (t : term) (s : sort), Ered t (Srt s) -> mem_sort2 s t.
intros.
pattern t in |- *.
apply Ered1_Ered_ind with (Srt s); auto with ecoc coc core arith sets.
do 4 intro.
elim H0; intros.
elim mem_sort2_subst with M0 N 0 s; intros;
 auto with ecoc coc core arith sets.

inversion H2; auto with ecoc.

inversion H4; auto with ecoc.

inversion H4; auto with ecoc.

inversion H4; auto with ecoc.

inversion H4; auto with ecoc.

inversion H4; auto with ecoc.

inversion H4; auto with ecoc.
Qed.

Lemma mem_sort2_mem_sort :
 forall (t : term) (s : sort), mem_sort2 s t -> mem_sort s t.
simple induction 1; auto with coc.
Qed.

Lemma Ered_sort_mem :
 forall (t : term) (s : sort), Ered t (Srt s) -> mem_sort s t.
intros; apply mem_sort2_mem_sort; apply Ered_sort_mem2; trivial.
Qed.

 