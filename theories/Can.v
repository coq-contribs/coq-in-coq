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
Require Import Class.

  (* schemes of reducibility: functions on sets of terms *)  

  Fixpoint Can (K : skel) : Type :=
    match K with
    | PROP => term -> Prop
    | PROD s1 s2 => Can s1 -> Can s2
    end.


  (* equality on schemes *)

  Definition eq_cand (X Y : term -> Prop) : Prop :=
    forall t : term, X t <-> Y t.


  Hint Unfold eq_cand: coc.

  Fixpoint eq_can (s : skel) : Can s -> Can s -> Prop :=
    match s as s0 return (Can s0 -> Can s0 -> Prop) with
    | PROP => eq_cand
    | PROD s1 s2 =>
        fun C1 C2 : Can (PROD s1 s2) =>
        forall X1 X2 : Can s1,
        eq_can s1 X1 X2 ->
        eq_can s1 X1 X1 -> eq_can s1 X2 X2 -> eq_can s2 (C1 X1) (C2 X2)
    end.

  Hint Unfold iff: coc.



  Lemma eq_can_sym :
   forall (s : skel) (X Y : Can s), eq_can s X Y -> eq_can s Y X.
simple induction s; simpl in |- *; intros; auto with coc core arith datatypes.
unfold eq_cand in |- *; intros.
elim H with t; auto with coc core arith datatypes.
Qed.

  Lemma eq_can_trans :
   forall (s : skel) (a b c : Can s),
   eq_can s a b -> eq_can s b b -> eq_can s b c -> eq_can s a c.
simple induction s; simpl in |- *; intros.
unfold eq_cand in |- *; intros.
elim H with t; elim H1 with t; auto with coc core arith datatypes.

apply H0 with (b X1); auto with coc core arith datatypes.
Qed.


  Lemma eq_cand_incl :
   forall (t : term) (X Y : Can PROP), eq_can PROP X Y -> X t -> Y t.
intros.
elim H with t; auto with coc core arith datatypes.
Qed.



  (* Higher order candidates of reducibility *)

  Definition neutral (t : term) : Prop := forall u v : term, t <> Abs u v.

  Record is_cand (X : term -> Prop) : Prop := 
    {incl_sn : forall t : term, X t -> sn t;
     clos_red : forall t : term, X t -> forall u : term, red1 t u -> X u;
     clos_exp :
      forall t : term, neutral t -> (forall u : term, red1 t u -> X u) -> X t}. 



  Lemma var_in_cand :
   forall (n : nat) (X : term -> Prop), is_cand X -> X (Ref n).
intros.
apply (clos_exp X); auto with coc core arith datatypes.
unfold neutral in |- *; intros; discriminate.

intros.
inversion H0.
Qed.


  Lemma clos_red_star :
   forall R : term -> Prop,
   is_cand R -> forall a b : term, R a -> red a b -> R b.
simple induction 3; intros; auto with coc core arith datatypes.
apply (clos_red R) with P; auto with coc core arith datatypes.
Qed.


  Lemma cand_sat :
   forall X : term -> Prop,
   is_cand X ->
   forall T : term,
   sn T ->
   forall u : term,
   sn u -> forall m : term, X (subst u m) -> X (App (Abs T m) u).
unfold sn in |- *.
simple induction 2.
simple induction 3.
intros.
generalize H6.
cut (sn m); [intros H'; elim H' | ]; intros.
apply (clos_exp X); intros; auto with coc core arith datatypes.
red in |- *; intros; discriminate.

inversion_clear H10; auto with coc core arith datatypes.
inversion_clear H11.
apply H2; auto with coc core arith datatypes.
apply Acc_intro; auto with coc core arith datatypes.

apply H8; auto with coc core arith datatypes.
apply (clos_red X) with (subst x0 x1); auto with coc core arith datatypes.
unfold subst in |- *; auto with coc core arith datatypes.

apply H5; auto with coc core arith datatypes.
apply clos_red_star with (subst x0 x1); auto with coc core arith datatypes.
unfold subst in |- *; auto with coc core arith datatypes.

apply sn_subst with x0.
apply (incl_sn X); auto with coc core arith datatypes.
Qed.



  Fixpoint is_can (s : skel) : Can s -> Prop :=
    match s as s0 return (Can s0 -> Prop) with
    | PROP => fun X : term -> Prop => is_cand X
    | PROD s1 s2 =>
        fun C : Can s1 -> Can s2 =>
        forall X : Can s1, is_can s1 X -> eq_can s1 X X -> is_can s2 (C X)
    end.


  Lemma is_can_prop : forall X : term -> Prop, is_can PROP X -> is_cand X.
auto with coc core arith datatypes.
Qed.

  Hint Resolve is_can_prop: coc.




  (* Default Candidates *)

  Fixpoint default_can (s : skel) : Can s :=
    match s as ss return (Can ss) with
    | PROP => sn
    | PROD s1 s2 => fun _ : Can s1 => default_can s2
    end.


  Lemma cand_sn : is_cand sn.
apply Build_is_cand; intros; auto with coc core arith datatypes.

apply sn_red_sn with t; auto with coc core arith datatypes.

red in |- *; apply Acc_intro; auto with coc core arith datatypes.
Qed.

  Hint Resolve cand_sn: coc.


  Lemma def_can_cr : forall s : skel, is_can s (default_can s).
simple induction s; simpl in |- *; intros; auto with coc core arith datatypes.
Qed.


  Lemma def_inv : forall s : skel, eq_can s (default_can s) (default_can s).
simple induction s; simpl in |- *; intros; auto with coc core arith datatypes.
Qed.


  Hint Resolve def_inv def_can_cr: coc.



  Definition Pi (s : skel) (X : term -> Prop) (F : Can (PROD s PROP))
    (t : term) : Prop :=
    forall u : term,
    X u -> forall C : Can s, is_can s C -> eq_can s C C -> F C (App t u).


  Lemma eq_can_Pi :
   forall (s : skel) (X Y : term -> Prop) (F1 F2 : Can (PROD s PROP)),
   eq_can PROP X Y ->
   eq_can (PROD s PROP) F1 F2 -> eq_can PROP (Pi s X F1) (Pi s Y F2).
simpl in |- *; intros; unfold iff, Pi in |- *.
split; intros.
elim H0 with C C (App t u); elim H with u; auto with coc core arith datatypes.

elim H0 with C C (App t u); elim H with u; auto with coc core arith datatypes.
Qed.



  Lemma is_can_Pi :
   forall (s : skel) (X : term -> Prop),
   is_cand X ->
   forall F : Can (PROD s PROP), is_can (PROD s PROP) F -> is_cand (Pi s X F).
simpl in |- *; unfold Pi in |- *; intros.
apply Build_is_cand; intros.
apply subterm_sn with (App t (Ref 0)); auto with coc core arith datatypes.
apply (incl_sn (F (default_can s))); auto with coc core arith datatypes.
apply H1; auto with coc core arith datatypes.
apply (var_in_cand 0 X); auto with coc core arith datatypes.

apply (clos_red (F C)) with (App t u0); auto with coc core arith datatypes.

apply (clos_exp (F C)); auto with coc core arith datatypes.
red in |- *; intros; discriminate.

generalize H3.
cut (sn u).
simple induction 1; intros.
generalize H1.
inversion_clear H10; intros; auto with coc core arith datatypes.
elim H10 with T M; auto with coc core arith datatypes.

apply (clos_exp (F C)); intros; auto with coc core arith datatypes.
red in |- *; intros; discriminate.

apply H8 with N2; auto with coc core arith datatypes.
apply (clos_red X) with x; auto with coc core arith datatypes.

apply (incl_sn X); auto with coc core arith datatypes.
Qed.



  Lemma Abs_sound :
   forall (A : term -> Prop) (s : skel) (F : Can s -> term -> Prop)
     (T m : term),
   is_can PROP A ->
   is_can (PROD s PROP) F ->
   (forall n : term,
    A n -> forall C : Can s, is_can s C -> eq_can s C C -> F C (subst n m)) ->
   sn T -> Pi s A F (Abs T m).
unfold Pi in |- *; simpl in |- *; intros.
cut (is_cand (F C)); intros; auto with coc core arith datatypes.
apply (clos_exp (F C)); intros; auto with coc core arith datatypes.
red in |- *; intros; discriminate.

apply clos_red with (App (Abs T m) u); auto with coc core arith datatypes.
apply (cand_sat (F C)); auto with coc core arith datatypes.
apply (incl_sn A); auto with coc core arith datatypes.
Qed.



