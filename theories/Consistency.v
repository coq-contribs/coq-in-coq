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
Require Import Types.
Require Import Conv.
Require Import Conv_Dec.
Require Import Strong_Norm.

Require Import Lia.

Fixpoint applist (l : list term) : term -> term :=
  fun t =>
  match l with
  | nil => t
  | arg :: args => App (applist args t) arg
  end.

Lemma applist_assoc :
 forall t e e', applist (e ++ e') t = applist e (applist e' t).
simple induction e; simpl in |- *; intros; auto.
rewrite H; trivial.
Qed.

Lemma inv_typ_applist_head :
 forall e t l T, typ e (applist l t) T -> exists U : _, typ e t U.
Proof.
simple induction l; simpl in |- *; intros.
split with T; trivial.

apply inv_typ_app with (1 := H0); intros.
eauto.
Qed.



Definition is_atom (e : env) t :=
  exists2 n : _, n < length e & (exists l : _, t = applist l (Ref n)).

Lemma sort_not_atom : forall e s, ~ is_atom e (Srt s).
intros e s (n, lt_n, ([| t l], eq_atom)); discriminate eq_atom.
Qed.

Lemma prod_not_atom : forall e T M, ~ is_atom e (Prod T M).
intros e T M (n, lt_n, ([| t l], eq_atom)); discriminate eq_atom.
Qed.

Lemma is_atom_app : forall e a b, is_atom e a -> is_atom e (App a b).
intros e a b (n, lt_n, (l, eq_atom)).
rewrite eq_atom.
split with n; trivial.
split with (b :: l); trivial.
Qed.

Lemma atom_reduction : forall e t u, red t u -> is_atom e t -> is_atom e u.
simple induction 1; intros; trivial.
generalize (H1 H3); clear H1 H3.
intros (n, lt_n, (l, eq_atom)).
rewrite eq_atom in H2.
split with n; trivial.
generalize N H2; clear N H2 eq_atom H0.
elim l; simpl in |- *; intros.
inversion H2.

inversion H2.
apply False_ind.
generalize H3.
case l0; simpl in |- *; try intros tt ll; discriminate.

elim H0 with (1 := H5); intros.
rewrite H6.
split with (a :: x); reflexivity.

split with (N2 :: l0); reflexivity.
Qed.


Lemma conv_sort_atom : forall (s : sort) e u, is_atom e u -> ~ conv (Srt s) u.
Proof.
red in |- *; intros.
elim church_rosser with (1 := H0); intros.
rewrite <- red_normal with (1 := H1) in H2.
specialize atom_reduction with (1 := H2) (2 := H).
apply sort_not_atom.

red in |- *; red in |- *; intros.
inversion H3.
Qed.

  Lemma conv_prod_atom : forall a b e u, is_atom e u -> ~ conv (Prod a b) u.
red in |- *; intros.
elim church_rosser with (1 := H0); intros.
apply red_prod_prod with (1 := H1); intros.
rewrite H3 in H2.
specialize atom_reduction with (1 := H2) (2 := H).
apply prod_not_atom.
Qed.


(* Normal proofs of products are either atomic proofs or an abstraction *)
Lemma prod_inhabitants :
 forall e t u,
 typ e t u ->
 forall a b,
 conv u (Prod a b) ->
 normal t -> is_atom e t \/ (exists a' : _, (exists m : _, t = Abs a' m)).
Proof.
simple induction 1; intros; eauto.
elim conv_sort_prod with (1 := H1).

elim conv_sort_prod with (1 := H1).

left.
exists v.
inversion_clear H1.
elim H5; intros; simpl in |- *; auto with arith.

exists (nil (A:=term)); simpl in |- *; auto.

left.
apply is_atom_app.
elim H3 with V Ur; intros; auto with coc.
inversion_clear H6.
inversion_clear H7.
rewrite H6 in H5.
elim H5 with (subst v x0); auto with coc.

red in |- *; red in |- *; intros.
elim H5 with (App u1 v); auto with coc.

elim conv_sort_prod with (1 := H4).

apply H1 with a b; auto.
apply trans_conv_conv with V; auto.
Qed.

Definition hnf_proofs (e : env) (t : term) : Prop :=
  match t with
  | App _ _ => is_atom e t
  | _ => True
  end.

(* The head of an application of a well-typed term in normal form must
   be a variable *)
Lemma hnf_proofs_sound :
 forall e t T, typ e t T -> normal t -> hnf_proofs e t.
simple induction 1; simpl in |- *; intros; auto.
apply is_atom_app.
elim prod_inhabitants with (1 := H2) (a := V) (b := Ur); intros;
 auto with coc.
inversion_clear H5.
inversion_clear H6.
rewrite H5 in H4.
elim H4 with (subst v x0); auto with coc.

red in |- *; red in |- *; intros.
elim H4 with (App u0 v); auto with coc.
Qed.

(* Normal proofs of atomic types are atomic terms *)
Lemma atom_inhabitants :
 forall e t u u',
 typ e t u -> conv u u' -> is_atom e u' -> hnf_proofs e t -> is_atom e t.
simple induction 1; simpl in |- *; intros; auto.
elim conv_sort_atom with (1 := H2) (2 := H1).

elim conv_sort_atom with (1 := H2) (2 := H1).

split with v.
inversion_clear H1.
elim H6; simpl in |- *; auto with arith.

split with (nil (A:=term)); auto.

elim conv_prod_atom with (1 := H7) (2 := H6).

elim conv_sort_atom with (1 := H5) (2 := H4).

apply H1; auto.
apply trans_conv_conv with V; auto with coc.
Qed.

(* The absurd proposition: False := (P:Prop)P *)
Definition absurd_prop := Prod (Srt prop) (Ref 0).

(* False has no proof in normal form *)
Lemma coc_consistency_nf : forall t, normal t -> ~ typ nil t absurd_prop.
Proof.
unfold absurd_prop in |- *.
red in |- *; intros.
elim prod_inhabitants with (1 := H0) (a := Srt prop) (b := Ref 0) (3 := H);
 auto with coc.
(* Case 1: t atomic impossible because context is empty *)
intros.
inversion_clear H1.
inversion H2.

(* Case 2: t is an abstraction (Abs ty M) *)
intros (ty, (M, eq_abs)).
rewrite eq_abs in H0.
apply inv_typ_abs with (1 := H0); intros.
specialize inv_conv_prod_l with (1 := H4); intro conv_ty.
specialize inv_conv_prod_r with (1 := H4); intro conv_P.
clear H0 H4 H3 H1.
(* Then M is an atomic proof *)
cut (is_atom (ty :: nil) M).
intros (n, lt_n, (l, eq_atom)).
simpl in lt_n.
generalize eq_atom.
clear eq_atom.
replace n with 0; try lia.
rewrite <- (rev_involutive l).
case (rev l); simpl in |- *; intros; rewrite eq_atom in H2.
(* Case 2.1: the head var of M is not applied *) 
apply inv_typ_ref with (1 := H2).
intros U itm_U.
inversion_clear itm_U.
intro conv_T.
(* Impossible because var has type prop instead of (Ref O) *)
cut (Ref 0 = Srt prop); try discriminate.
apply nf_uniqueness.
apply trans_conv_conv with T; auto with coc.
apply trans_conv_conv with (lift 1 ty); auto with coc.
change (conv (lift_rec 1 ty 0) (lift_rec 1 (Srt prop) 0)) in |- *.
apply conv_conv_lift; auto with coc.

red in |- *; red in |- *; intros r red_n; inversion red_n.

red in |- *; red in |- *; intros r red_n; inversion red_n.

(* Case 2.2: the head var of M is applied *)
rewrite applist_assoc in H2.
simpl in H2.
elim inv_typ_applist_head with (1 := H2); intros.
clear H2 eq_atom.
apply inv_typ_app with (1 := H0); intros.
apply inv_typ_ref with (1 := H1); intros.
(* Impossible because head var has type prop and cannot be applied *)
apply conv_sort_prod with prop V Ur.
apply trans_conv_conv with (lift 1 U); auto with coc.
apply sym_conv.
change (conv (lift_rec 1 U 0) (lift_rec 1 (Srt prop) 0)) in |- *.
inversion_clear H4.
apply conv_conv_lift; auto with coc.

(* Proof of M atomic *)
apply atom_inhabitants with (1 := H2) (2 := conv_P).
split with 0; simpl in |- *; auto with arith; split with (nil (A:=term));
 trivial.

apply hnf_proofs_sound with (1 := H2).
rewrite eq_abs in H.
red in |- *; red in |- *; intros.
elim H with (Abs ty u); auto with coc.
Qed.



(* The absurd proposition has no proof in the empty context *)
Theorem coc_consistency : forall t, ~ typ nil t absurd_prop.
Proof.
red in |- *; intros.
elim compute_nf with t; intros.
specialize subject_reduction with (1 := p) (2 := H).
apply coc_consistency_nf; trivial.

apply str_norm with (1 := H).
Qed.
