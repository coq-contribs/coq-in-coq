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


Require Import Le.
Require Import Gt.
Require Export List.

Global Set Asymmetric Patterns.

Section Listes.

  Variable A : Set.

  Let List := list A.


  Inductive In (x : A) : List -> Prop :=
    | In_hd : forall l : List, In x (x :: l)
    | In_tl : forall (y : A) (l : List), In x l -> In x (y :: l).

  Hint Resolve In_hd In_tl: coc. 


  Lemma In_app :
   forall (x : A) (l1 l2 : List), In x (l1 ++ l2) -> In x l1 \/ In x l2.
simple induction l1; simpl in |- *; intros;
 auto with coc core arith datatypes.

inversion_clear H0; auto with coc core arith datatypes.
elim H with l2; auto with coc core arith datatypes.
Qed.


  Definition incl (l1 l2 : List) : Prop := forall x : A, In x l1 -> In x l2.

  Hint Unfold incl: coc.


  Lemma incl_app_sym : forall l1 l2 : List, incl (l1 ++ l2) (l2 ++ l1).
red in |- *; intros.
elim In_app with x l1 l2; intros; auto with coc core arith datatypes.
elim l2; simpl in |- *; auto with coc core arith datatypes.

elim H0; simpl in |- *; auto with coc core arith datatypes.
Qed.


  Inductive item (x : A) : List -> nat -> Prop :=
    | item_hd : forall l : List, item x (x :: l) 0
    | item_tl :
        forall (l : List) (n : nat) (y : A),
        item x l n -> item x (y :: l) (S n).

  Lemma fun_item :
   forall (u v : A) (e : List) (n : nat), item u e n -> item v e n -> u = v.
simple induction 1; intros.
inversion_clear H0; auto with coc core arith datatypes.

inversion_clear H2; auto with coc core arith datatypes.
Qed.


  Fixpoint nth_def (d : A) (l : List) {struct l} : 
   nat -> A :=
    fun n : nat =>
    match l, n with
    | nil, _ => d
    | x :: _, O => x
    | _ :: tl, S k => nth_def d tl k
    end.

  Lemma nth_sound :
   forall (x : A) (l : List) (n : nat),
   item x l n -> forall d : A, nth_def d l n = x.
simple induction 1; simpl in |- *; auto with coc core arith datatypes.
Qed.

  Lemma inv_nth_nl : forall (x : A) (n : nat), ~ item x nil n.
unfold not in |- *; intros.
inversion_clear H.
Qed.

  Lemma inv_nth_cs :
   forall (x y : A) (l : List) (n : nat), item x (y :: l) (S n) -> item x l n.
intros.
inversion_clear H; auto with coc core arith datatypes.
Qed.

  Inductive insert (x : A) : nat -> List -> List -> Prop :=
    | insert_hd : forall l : List, insert x 0 l (x :: l)
    | insert_tl :
        forall (n : nat) (l il : List) (y : A),
        insert x n l il -> insert x (S n) (y :: l) (y :: il).


  Inductive trunc : nat -> List -> List -> Prop :=
    | trunc_O : forall e : List, trunc 0 e e
    | trunc_S :
        forall (k : nat) (e f : List) (x : A),
        trunc k e f -> trunc (S k) (x :: e) f.

  Hint Resolve trunc_O trunc_S: coc.


  Lemma item_trunc :
   forall (n : nat) (e : List) (t : A),
   item t e n -> exists f : List, trunc (S n) e f.
simple induction n; intros.
inversion_clear H.
exists l; auto with coc core arith datatypes.

inversion_clear H0.
elim H with l t; intros; auto with coc core arith datatypes.
exists x; auto with coc core arith datatypes.
Qed.


  Lemma ins_le :
   forall (k : nat) (f g : List) (d x : A),
   insert x k f g ->
   forall n : nat, k <= n -> nth_def d f n = nth_def d g (S n).
simple induction 1; auto with coc core arith datatypes.
simple destruct n0; intros.
inversion_clear H2.

simpl in |- *.
auto with coc core arith datatypes.
Qed.

  Lemma ins_gt :
   forall (k : nat) (f g : List) (d x : A),
   insert x k f g -> forall n : nat, k > n -> nth_def d f n = nth_def d g n.
simple induction 1; auto with coc core arith datatypes.
intros.
inversion_clear H0.

simple destruct n0; intros.
auto with coc core arith datatypes.

simpl in |- *; auto with coc core arith datatypes.
Qed.

  Lemma ins_eq :
   forall (k : nat) (f g : List) (d x : A),
   insert x k f g -> nth_def d g k = x.
simple induction 1; simpl in |- *; auto with coc core arith datatypes.
Qed.




Definition list_item :
 forall (e : List) (n : nat),
 {t : A | item t e n} + {(forall t : A, ~ item t e n)}.

simple induction e.
right.
red in |- *; intros t H; inversion_clear H.
intros h f itemf n.
case n.
left; exists h; constructor.
intro k; case (itemf k).
simple destruct 1; intro u; left; exists u; constructor; trivial.
intros; right.
red in |- *; intros.
inversion_clear H.
apply (n0 t); auto.
Defined.




  Definition list_disjoint (l1 l2 : List) : Prop :=
    forall x : A, In x l1 -> In x l2 -> False.




  Inductive first_item (x : A) : List -> nat -> Prop :=
    | fit_hd : forall l : List, first_item x (x :: l) 0
    | fit_tl :
        forall (l : List) (y : A) (n : nat),
        first_item x l n -> x <> y -> first_item x (y :: l) (S n).

  Hint Resolve fit_hd fit_tl: coc.

  Lemma first_item_is_item :
   forall (x : A) (l : List) (n : nat), first_item x l n -> item x l n.
simple induction 1; intros.
apply item_hd.

apply item_tl; trivial with coc core arith datatypes.
Qed.

  Lemma first_item_unique :
   forall (x : A) (l : List) (n : nat),
   first_item x l n -> forall m : nat, first_item x l m -> m = n.
simple induction 1; intros; auto with coc core arith datatypes.
inversion_clear H0; auto with coc core arith datatypes.

elim H2; auto with coc core arith datatypes.

generalize H2.
inversion_clear H3; intros.
elim H3; auto with coc core arith datatypes.

elim H1 with n1; auto with coc core arith datatypes.
Qed.


 
  Hypothesis eq_dec : forall x y : A, {x = y} + {x <> y}.

  Definition list_index :
   forall (x : A) (l : List), {n : nat | first_item x l n} + {~ In x l}.

refine
 (fix list_index (x : A) (l : List) {struct l} :
    {n : nat | first_item x l n} + {~ In x l} :=
    match l return ({n : nat | first_item x l n} + {~ In x l}) with
    | nil => inright _ _
    | y :: l1 =>
        match eq_dec x y with
        | left found => inleft _ (exist _ 0 _)
        | right notfound =>
            match list_index x l1 with
            | inleft (exist k in_tail) => inleft _ (exist _ (S k) _)
            | inright not_tail => inright _ _
            end
        end
    end); auto with coc.

red in |- *; intros.
inversion H.

elim found; auto with coc.

red in |- *; intros; apply not_tail.
inversion H; auto with coc.
elim notfound; trivial.
Defined.

End Listes.

  Hint Resolve item_hd item_tl insert_hd insert_tl trunc_O trunc_S: coc.
  Hint Resolve In_hd In_tl fit_hd fit_tl trunc_O trunc_S: coc.
  Hint Unfold incl: coc.


