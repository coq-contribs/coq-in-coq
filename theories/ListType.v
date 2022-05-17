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



Require Import Arith.
Require Import MyList.

Section TListes.

  Variable A : Type.

  Inductive TList : Type :=
    | TNl : TList
    | TCs : A -> TList -> TList.


  Fixpoint Tnth_def (d : A) (l : TList) {struct l} : 
   nat -> A :=
    fun n : nat =>
    match l, n with
    | TNl, _ => d
    | TCs x _, O => x
    | TCs _ tl, S k => Tnth_def d tl k
    end.


  Inductive TIns (x : A) : nat -> TList -> TList -> Prop :=
    | TIns_hd : forall l : TList, TIns x 0 l (TCs x l)
    | TIns_tl :
        forall (n : nat) (l il : TList) (y : A),
        TIns x n l il -> TIns x (S n) (TCs y l) (TCs y il).

  Hint Resolve TIns_hd TIns_tl: coc.

  Lemma Tins_le :
   forall (k : nat) (f g : TList) (d x : A),
   TIns x k f g ->
   forall n : nat, k <= n -> Tnth_def d f n = Tnth_def d g (S n).
simple induction 1; auto with coc core arith datatypes.
simple destruct n0; intros.
inversion H2.

simpl in |- *; auto with coc core arith datatypes.
Qed.

  Lemma Tins_gt :
   forall (k : nat) (f g : TList) (d x : A),
   TIns x k f g -> forall n : nat, k > n -> Tnth_def d f n = Tnth_def d g n.
simple induction 1; auto with coc core arith datatypes.
intros.
inversion_clear H0.

simple destruct n0; intros.
auto with coc core arith datatypes.

simpl in |- *; auto with coc core arith datatypes.
Qed.

  Lemma Tins_eq :
   forall (k : nat) (f g : TList) (d x : A),
   TIns x k f g -> Tnth_def d g k = x.
simple induction 1; simpl in |- *; auto with coc core arith datatypes.
Qed.


  Inductive TTrunc : nat -> TList -> TList -> Prop :=
    | Ttr_O : forall e : TList, TTrunc 0 e e
    | Ttr_S :
        forall (k : nat) (e f : TList) (x : A),
        TTrunc k e f -> TTrunc (S k) (TCs x e) f.

  Hint Resolve Ttr_O Ttr_S: coc.

  Fixpoint TList_iter (B : Type) (f : A -> B -> B) 
   (l : TList) {struct l} : B -> B :=
    fun x : B =>
    match l with
    | TNl => x
    | TCs hd tl => f hd (TList_iter _ f tl x)
    end.

  Inductive Tfor_all (P : A -> Prop) : TList -> Prop :=
    | Tfa_nil : Tfor_all P TNl
    | Tfa_cs :
        forall (h : A) (t : TList),
        P h -> Tfor_all P t -> Tfor_all P (TCs h t).

  Inductive Tfor_all_fold (P : A -> TList -> Prop) : TList -> Prop :=
    | Tfaf_nil : Tfor_all_fold P TNl
    | Tfaf_cs :
        forall (h : A) (t : TList),
        P h t -> Tfor_all_fold P t -> Tfor_all_fold P (TCs h t).

End TListes.

  Hint Resolve TIns_hd TIns_tl Ttr_O Ttr_S: coc.
  Hint Resolve Tfa_nil Tfa_cs Tfaf_nil Tfaf_cs: coc.

  Fixpoint Tmap (A B : Type) (f : A -> B) (l : TList A) {struct l} :
   TList B :=
    match l with
    | TNl => TNl B
    | TCs t tl => TCs _ (f t) (Tmap A B f tl)
    end.

  Fixpoint TSmap (A : Type) (B : Set) (f : A -> B) 
   (l : TList A) {struct l} : list B :=
    match l with
    | TNl => nil (A:=B)
    | TCs t tl => f t :: TSmap A B f tl
    end.


  Inductive Tfor_all2 (A B : Type) (P : A -> B -> Prop) :
  TList A -> TList B -> Prop :=
    | Tfa2_nil : Tfor_all2 _ _ P (TNl _) (TNl _)
    | Tfa2_cs :
        forall (h1 : A) (h2 : B) (t1 : TList A) (t2 : TList B),
        P h1 h2 ->
        Tfor_all2 _ _ P t1 t2 -> Tfor_all2 _ _ P (TCs _ h1 t1) (TCs _ h2 t2).

  Hint Resolve Tfa2_nil Tfa2_cs: coc.