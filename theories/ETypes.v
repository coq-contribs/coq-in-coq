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
Require Export MyList.
Require Import Types.

 
Section Typage.

  Inductive Ewf : env -> Prop :=
    | Ewf_nil : Ewf nil
    | Ewf_var :
        forall (e : env) (T : term) (s : sort),
        Etyp e T (Srt s) -> Ewf (T :: e)
with Etyp : env -> term -> term -> Prop :=
  | Etype_prop : forall e : env, Ewf e -> Etyp e (Srt prop) (Srt kind)
  | Etype_set : forall e : env, Ewf e -> Etyp e (Srt set) (Srt kind)
  | Etype_var :
      forall e : env,
      Ewf e ->
      forall (v : nat) (t : term), item_lift t e v -> Etyp e (Ref v) t
  | Etype_abs :
      forall (e : env) (T : term) (s1 : sort),
      Etyp e T (Srt s1) ->
      forall (M U : term) (s2 : sort),
      Etyp (T :: e) U (Srt s2) ->
      Etyp (T :: e) M U -> Etyp e (Abs T M) (Prod T U)
  | Etype_app :
      forall (e : env) (v V : term),
      Etyp e v V ->
      forall u Ur : term,
      Etyp e u (Prod V Ur) -> Etyp e (App u v) (subst v Ur)
  | Etype_prod :
      forall (e : env) (T : term) (s1 : sort),
      Etyp e T (Srt s1) ->
      forall (U : term) (s2 : sort),
      Etyp (T :: e) U (Srt s2) -> Etyp e (Prod T U) (Srt s2)
  | Etype_Econv :
      forall (e : env) (t U V : term),
      Etyp e t U ->
      Econv U V -> forall s : sort, Etyp e V (Srt s) -> Etyp e t V.

  Hint Resolve Ewf_nil Etype_prop Etype_set Etype_var: ecoc.


Lemma typ_Etyp : forall (e : env) (a Ta : term), typ e a Ta -> Etyp e a Ta. 
fix typ_Etyp 4.
intros.
case H; intros.
apply Etype_prop.
case H0.
apply Ewf_nil.

intros; apply Ewf_var with s.
apply typ_Etyp; trivial.

apply Etype_set.
case H0.
apply Ewf_nil.

intros; apply Ewf_var with s; auto.

apply Etype_var.
case H0.
apply Ewf_nil.

intros; apply Ewf_var with s.
apply typ_Etyp; trivial.

trivial.

apply Etype_abs with s1 s2; auto.

apply Etype_app with V; auto.

apply Etype_prod with s1; auto.

apply Etype_Econv with U s; auto.
apply conv_Econv; trivial.
Qed.

  Lemma Etype_prop_set :
   forall s : sort,
   is_prop s -> forall e : env, Ewf e -> Etyp e (Srt s) (Srt kind).
simple destruct 1; intros; rewrite H0.
apply Etype_prop; trivial.
apply Etype_set; trivial.
Qed.

  Lemma Etyp_free_db :
   forall (e : env) (t T : term), Etyp e t T -> free_db (length e) t.
simple induction 1; intros; auto with coc ecoc core arith datatypes.
inversion_clear H1.
apply db_ref.
elim H3; simpl in |- *; intros; auto with coc ecoc core arith datatypes.
Qed.


  Lemma Etyp_Ewf : forall (e : env) (t T : term), Etyp e t T -> Ewf e.
simple induction 1; auto with coc core arith datatypes.
Qed.


  Lemma Ewf_sort :
   forall (n : nat) (e f : env),
   trunc _ (S n) e f ->
   Ewf e ->
   forall t : term, item _ t e n -> exists s : sort, Etyp f t (Srt s).
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

apply Etyp_Ewf with x (Srt s); auto with coc core arith datatypes.
Qed.



  Definition inv_Etype (P : Prop) (e : env) (t T : term) : Prop :=
    match t with
    | Srt prop => Econv T (Srt kind) -> P
    | Srt set => Econv T (Srt kind) -> P
    | Srt kind => True
    | Ref n => forall x : term, item _ x e n -> Econv T (lift (S n) x) -> P
    | Abs A M =>
        forall (s1 s2 : sort) (U : term),
        Etyp e A (Srt s1) ->
        Etyp (A :: e) M U ->
        Etyp (A :: e) U (Srt s2) -> Econv T (Prod A U) -> P
    | App u v =>
        forall Ur V : term,
        Etyp e v V -> Etyp e u (Prod V Ur) -> Econv T (subst v Ur) -> P
    | Prod A B =>
        forall s1 s2 : sort,
        Etyp e A (Srt s1) ->
        Etyp (A :: e) B (Srt s2) -> Econv T (Srt s2) -> P
    end.

  Lemma inv_Etype_Econv :
   forall (P : Prop) (e : env) (t U V : term),
   Econv U V -> inv_Etype P e t U -> inv_Etype P e t V.
do 6 intro.
cut (forall x : term, Econv V x -> Econv U x).
intro.
case t; simpl in |- *; intros.
generalize H1.
elim s; auto with coc ecoc core arith datatypes; intros.

apply H1 with x; auto with coc core arith datatypes.

apply H1 with s1 s2 U0; auto with coc core arith datatypes.

apply H1 with Ur V0; auto with coc core arith datatypes.

apply H1 with s1 s2; auto with coc core arith datatypes.

intros; apply trans_Econv_Econv with V; auto with coc core arith datatypes.
Qed.


  Theorem Etyp_inversion :
   forall (P : Prop) (e : env) (t T : term),
   Etyp e t T -> inv_Etype P e t T -> P.
simple induction 1; simpl in |- *; intros.
auto with coc ecoc core arith datatypes.

auto with coc ecoc core arith datatypes.

elim H1; intros.
apply H2 with x; auto with coc ecoc core arith datatypes.
rewrite H3; auto with coc ecoc core arith datatypes.

apply H6 with s1 s2 U; auto with coc ecoc core arith datatypes.

apply H4 with Ur V; auto with coc ecoc core arith datatypes.

apply H4 with s1 s2; auto with coc ecoc core arith datatypes.

apply H1.
apply inv_Etype_Econv with V; auto with coc ecoc core arith datatypes.
Qed.




  Lemma inv_Etyp_kind : forall (e : env) (t : term), ~ Etyp e (Srt kind) t.
red in |- *; intros.
apply Etyp_inversion with e (Srt kind) t; simpl in |- *;
 auto with coc ecoc core arith datatypes.
Qed.

  Lemma inv_Etyp_prop :
   forall (e : env) (T : term), Etyp e (Srt prop) T -> Econv T (Srt kind).
intros.
apply Etyp_inversion with e (Srt prop) T; simpl in |- *;
 auto with ecoc coc core arith datatypes.
Qed.

  Lemma inv_Etyp_set :
   forall (e : env) (T : term), Etyp e (Srt set) T -> Econv T (Srt kind).
intros.
apply Etyp_inversion with e (Srt set) T; simpl in |- *;
 auto with coc ecoc core arith datatypes.
Qed.

  Lemma inv_Etyp_ref :
   forall (P : Prop) (e : env) (T : term) (n : nat),
   Etyp e (Ref n) T ->
   (forall U : term, item _ U e n -> Econv T (lift (S n) U) -> P) -> P.
intros.
apply Etyp_inversion with e (Ref n) T; simpl in |- *; intros;
 auto with coc ecoc core arith datatypes.
apply H0 with x; auto with coc ecoc core arith datatypes.
Qed.

  Lemma inv_Etyp_abs :
   forall (P : Prop) (e : env) (A M U : term),
   Etyp e (Abs A M) U ->
   (forall (s1 s2 : sort) (T : term),
    Etyp e A (Srt s1) ->
    Etyp (A :: e) M T -> Etyp (A :: e) T (Srt s2) -> Econv (Prod A T) U -> P) ->
   P.
intros.
apply Etyp_inversion with e (Abs A M) U; simpl in |- *;
 auto with coc ecoc core arith datatypes; intros.
apply H0 with s1 s2 U0; auto with coc ecoc core arith datatypes.
Qed.

  Lemma inv_Etyp_app :
   forall (P : Prop) (e : env) (u v T : term),
   Etyp e (App u v) T ->
   (forall V Ur : term,
    Etyp e u (Prod V Ur) -> Etyp e v V -> Econv T (subst v Ur) -> P) -> P.
intros.
apply Etyp_inversion with e (App u v) T; simpl in |- *;
 auto with coc ecoc core arith datatypes; intros.
apply H0 with V Ur; auto with coc ecoc core arith datatypes.
Qed.

  Lemma inv_Etyp_prod :
   forall (P : Prop) (e : env) (T U s : term),
   Etyp e (Prod T U) s ->
   (forall s1 s2 : sort,
    Etyp e T (Srt s1) -> Etyp (T :: e) U (Srt s2) -> Econv (Srt s2) s -> P) ->
   P.
intros.
apply Etyp_inversion with e (Prod T U) s; simpl in |- *;
 auto with coc ecoc core arith datatypes; intros.
apply H0 with s1 s2; auto with coc ecoc core arith datatypes.
Qed.




  Lemma Etyp_mem_kind :
   forall (e : env) (t T : term), mem_sort kind t -> ~ Etyp e t T.
red in |- *; intros.
apply Etyp_inversion with e t T; auto with coc core arith datatypes.
generalize e T.
clear H0.
elim H; simpl in |- *; auto with coc core arith datatypes; intros.
apply Etyp_inversion with e0 u (Srt s1); auto with coc core arith datatypes.

apply Etyp_inversion with (u :: e0) v (Srt s2);
 auto with coc core arith datatypes.

apply Etyp_inversion with e0 u (Srt s1); auto with coc core arith datatypes.

apply Etyp_inversion with (u :: e0) v U; auto with coc core arith datatypes.

apply Etyp_inversion with e0 u (Prod V Ur);
 auto with coc core arith datatypes.

apply Etyp_inversion with e0 v V; auto with coc core arith datatypes.
Qed.
  

Lemma inv_Etyp_Econv_kind :
 forall (e : env) (t T : term), Econv t (Srt kind) -> ~ Etyp e t T.
intros.
apply Etyp_mem_kind.
apply Ered_sort_mem.
elim Econv_church_rosser with t (Srt kind); intros;
 auto with ecoc coc core arith datatypes.
rewrite (Ered_Enormal (Srt kind) x); auto with ecoc coc core arith datatypes.
red in |- *; red in |- *; intros.
inversion_clear H2.
Qed.

End Typage.

