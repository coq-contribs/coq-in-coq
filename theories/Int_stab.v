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
Require Import Can.
Require Import Int_typ.

  Lemma int_equiv_int_typ :
   forall (T : term) (i i' : intP),
   int_eq_can i i' ->
   forall s : skel, eq_can s (int_typ T i s) (int_typ T i' s).
simple induction T; simpl in |- *; intros; auto with coc core arith datatypes.
generalize n.
elim H; auto with coc core arith datatypes.
unfold Tnth_def in |- *.
intros.
apply eq_can_extr.
simpl in |- *; auto with coc core arith datatypes.

simple destruct n0; intros; auto with coc core arith datatypes.
unfold Tnth_def in |- *.
inversion_clear H0; apply eq_can_extr || simpl in |- *;
 auto with coc core arith datatypes.

simpl in |- *; auto with coc core arith datatypes.

unfold def_cons, int_cons, ext_ik in |- *.
elim int_eq_can_cls with i i'; auto with coc core arith datatypes.
elim (cl_term t (cls_of_int i)); simpl in |- *;
 auto with coc core arith datatypes.
case s; simpl in |- *; auto with coc core arith datatypes.

unfold skel_int in |- *.
elim int_eq_can_cls with i i'; auto with coc core arith datatypes.
elim (cl_term t0 (cls_of_int i)); auto with coc core arith datatypes.
intros.
generalize (H i i' H1 (PROD s0 s)).
unfold skel_int in |- *.
simpl in |- *; intros.
apply H2; auto with coc core arith datatypes.
apply H0; auto with coc core arith datatypes.
elim H1; intros; auto with coc core arith datatypes.
inversion_clear H3; auto with coc core arith datatypes.

apply H0; auto with coc core arith datatypes.
elim H1; intros; auto with coc core arith datatypes.
inversion_clear H3; auto with coc core arith datatypes.

case s; simpl in |- *; auto with coc core arith datatypes.
unfold int_cons, ext_ik in |- *.
elim int_eq_can_cls with i i'; auto with coc core arith datatypes.
apply eq_can_Pi; auto with coc core arith datatypes.
simpl in |- *; intros.
replace eq_cand with (eq_can PROP); auto with coc core arith datatypes.
apply H0.
pattern (cl_term t (cls_of_int i)) at 1 3 in |- *.
elim (cl_term t (cls_of_int i)); auto with coc core arith datatypes.
Qed.

  Hint Resolve int_equiv_int_typ: coc.


  Inductive can_interp : Int_K -> Prop :=
    | ca_K :
        forall (s : skel) (C : Can s),
        is_can s C -> eq_can s C C -> can_interp (iK s C)
    | ca_T : can_interp iT.

  Hint Resolve ca_K ca_T: coc.

  Definition can_adapt : intP -> Prop := Tfor_all _ can_interp.

  Hint Unfold can_adapt: coc.


  Lemma adapt_int_inv : forall ip : intP, can_adapt ip -> int_inv ip.
simple induction 1; simpl in |- *; auto with coc core arith datatypes.
simple induction 1; auto with coc core arith datatypes.
Qed.

  Hint Resolve adapt_int_inv: coc.


  Lemma int_typ_cr :
   forall (t : term) (ip : intP),
   can_adapt ip -> forall s : skel, is_can s (int_typ t ip _).
simple induction t; simpl in |- *; intros; auto with coc core arith datatypes.
generalize n.
elim H; unfold Tnth_def in |- *; fold (Tnth_def Int_K) in |- *; intros.
apply is_can_coerce; apply cand_sn.

case n0; simpl in |- *; auto with coc core arith datatypes.
inversion_clear H0; auto with coc; simpl in |- *; auto with coc.

unfold def_cons, int_cons, ext_ik in |- *.
elim (cl_term t0 (cls_of_int ip)); auto with coc core arith datatypes.
case s; simpl in |- *; auto with coc core arith datatypes.

elim (cl_term t1 (cls_of_int ip)); auto with coc core arith datatypes.
intros.
generalize (H ip H1 (PROD s0 s)); simpl in |- *;
 auto with coc core arith datatypes.

case s; simpl in |- *; auto with coc core arith datatypes.
apply is_can_Pi; simpl in |- *; intros; auto with coc core arith datatypes.
unfold def_cons, int_cons, ext_ik in |- *.
generalize X H2 H3.
elim (cl_term t0 (cls_of_int ip)); auto with coc core arith datatypes.
simpl in |- *.
intros.
change (is_can PROP (int_typ t1 (TCs Int_K (iK s0 X0) ip) PROP)) in |- *;
 auto with coc core arith datatypes.
Qed.
(*
  Hints Resolve int_typ_cr : coc.
*)


  Lemma nth_lift_int :
   forall (y : Int_K) (s0 : skel) (ipe ipf : intP) (n k : nat),
   TIns _ y k ipe ipf ->
   int_typ (lift_rec 1 (Ref n) k) ipf s0 = int_typ (Ref n) ipe s0.
simpl in |- *; intros.
elim (le_gt_dec k n).
generalize n.
elim H; simpl in |- *; auto with coc core arith datatypes.
simple destruct n1; intro Hle; auto with coc core arith datatypes.
inversion_clear Hle.

generalize n.
elim H; simpl in |- *; auto with coc core arith datatypes.
intros l n0 Hgt.
inversion_clear Hgt.

simple destruct n1; intros; auto with coc core arith datatypes.
Qed.



  Lemma lift_int_typ :
   forall (y : Int_K) (T : term) (k : nat) (ipe ipf : intP),
   TIns _ y k ipe ipf ->
   int_inv ipf ->
   forall s : skel,
   eq_can s (int_typ T ipe s) (int_typ (lift_rec 1 T k) ipf s).
simple induction T.
simpl in |- *; auto with coc core arith datatypes.

intros.
elim nth_lift_int with y s ipe ipf n k; intros;
 auto with coc core arith datatypes.

simpl in |- *; intros.
unfold def_cons, int_cons, ext_ik in |- *.
elim cl_term_lift with (class_of_ik y) t k (cls_of_int ipe) (cls_of_int ipf);
 auto with coc core arith datatypes.
elim (cl_term t (cls_of_int ipe)); auto with coc core arith datatypes.
case s; simpl in |- *; intros; auto with coc core arith datatypes.
apply
 eq_can_trans with (int_typ (lift_rec 1 t0 (S k)) (TCs _ (iK s0 X1) ipf) s1);
 auto 10 with coc core arith datatypes.

apply ins_in_cls with y; auto with coc core arith datatypes.

simpl in |- *; intros.
elim cl_term_lift with (class_of_ik y) t k (cls_of_int ipe) (cls_of_int ipf);
 auto with coc core arith datatypes.
elim cl_term_lift with (class_of_ik y) t0 k (cls_of_int ipe) (cls_of_int ipf);
 auto with coc core arith datatypes.
elim (cl_term t0 (cls_of_int ipe)); auto with coc core arith datatypes.
intros.
generalize (H k ipe ipf H1 H2 (PROD s0 s)).
simpl in |- *; intros.
apply H3; auto with coc core arith datatypes.
apply int_equiv_int_typ.
apply int_inv_int_eq_can.
apply ins_int_inv with ipf k y; auto with coc core arith datatypes.

apply ins_in_cls with y; auto with coc core arith datatypes.

apply ins_in_cls with y; auto with coc core arith datatypes.

simpl in |- *; intros.
case s; simpl in |- *; intros; auto with coc core arith datatypes.
unfold def_cons, int_cons, ext_ik in |- *.
elim cl_term_lift with (class_of_ik y) t k (cls_of_int ipe) (cls_of_int ipf);
 auto with coc core arith datatypes.
apply eq_can_Pi; auto with coc core arith datatypes.
simpl in |- *; intros.
replace eq_cand with (eq_can PROP); auto with coc core arith datatypes.
pattern (cl_term t (cls_of_int ipe)) at 1 3 in |- *.
elim (cl_term t (cls_of_int ipe)); auto with coc core arith datatypes; intros.
apply
 eq_can_trans with (int_typ (lift_rec 1 t0 (S k)) (TCs _ (iK _ X1) ipf) PROP);
 auto 10 with coc core arith datatypes.

apply ins_in_cls with y; auto with coc core arith datatypes.
Qed.






  Inductive int_var_sound (t : term) (ip : intP) : Int_K -> Prop :=
    | ivs_K :
        forall s : skel,
        cl_term t (cls_of_int ip) = Typ s ->
        int_var_sound t ip (iK _ (int_typ t ip s))
    | ivs_T : cl_term t (cls_of_int ip) = Trm -> int_var_sound t ip iT.


  Lemma int_var_sound_lift :
   forall (t : term) (ip : intP) (i : Int_K),
   int_var_sound t ip i ->
   typ_cls (cl_term t (cls_of_int ip)) (class_of_ik i).
intros.
elim H; simpl in |- *; intros; rewrite H0; auto with coc core arith datatypes.
Qed.

  Hint Resolve ivs_K ivs_T int_var_sound_lift: coc.



  Lemma subst_int_typ :
   forall (v : term) (ipg : intP) (i : Int_K),
   int_var_sound v ipg i ->
   forall (e : env) (T K : term),
   typ e T K ->
   forall (k : nat) (ipe ipf : intP),
   TIns _ i k ipf ipe ->
   TTrunc _ k ipf ipg ->
   cls_of_int ipe = class_env e ->
   int_inv ipe ->
   cl_term T (cls_of_int ipe) <> Trm ->
   eq_can (skel_int T ipe) (int_typ T ipe _)
     (int_typ (subst_rec v T k) ipf _).
simple induction 2; intros.
simpl in |- *; auto with coc core arith datatypes.

simpl in |- *; auto with coc core arith datatypes.

unfold subst_rec in |- *.
elim (lt_eq_lt_dec k v0); [ intro Hlt_eq | intro Hlt ].
elim Hlt_eq; clear Hlt_eq; [ idtac | intro Heq ].
case v0; [ intro Hlt | intros n Hlt ].
inversion_clear Hlt.

unfold pred in |- *.
elim nth_lift_int with i (skel_int (Ref (S n)) ipe) ipf ipe n k;
 auto with coc core arith datatypes.
rewrite lift_ref_ge; auto with coc core arith datatypes.

generalize H4 H6 H7.
elim Heq.
clear H4 H6 H7 Heq.
elim H3; simpl in |- *; intros.
rewrite lift0.
unfold skel_int in |- *.
simpl in |- *.
generalize H7.
inversion_clear H; intros; simpl in H9.
unfold class_of_ik, typ_skel in |- *.
apply extr_eq with (P := fun s c => eq_can s c (int_typ v l s)).
generalize H6.
inversion_clear H4; intros.
inversion_clear H4; auto with coc core arith datatypes.

elim H9; auto with coc core arith datatypes.

replace (skel_int (Ref (S n)) (TCs Int_K y il)) with (skel_int (Ref n) il);
 auto with coc core arith datatypes.
rewrite simpl_lift.
apply eq_can_trans with (int_typ (lift n v) l (skel_int (Ref n) il)).
apply H6; auto with coc core arith datatypes.
inversion_clear H7; auto with coc core arith datatypes.

inversion_clear H8; auto with coc core arith datatypes.

inversion_clear H8.
apply int_equiv_int_typ.
apply int_inv_int_eq_can.
apply ins_int_inv with il n i; auto with coc core arith datatypes.

unfold lift at 2 in |- *.
apply lift_int_typ with y; auto with coc core arith datatypes.
apply ins_int_inv with (TCs _ y il) (S n) i;
 auto with coc core arith datatypes.

elim nth_lift_int with i (skel_int (Ref v0) ipe) ipf ipe v0 k;
 auto with coc core arith datatypes.
rewrite lift_ref_lt; auto with coc core arith datatypes.

unfold skel_int in |- *.
simpl in |- *.
replace
 (cl_term M (TCs class (cl_term T0 (cls_of_int ipe)) (cls_of_int ipe))) with
 (Typ (typ_skel (cl_term M (class_env (T0 :: e0))))).
unfold def_cons, int_cons, ext_ik in |- *.
elim
 class_subst
  with
    (class_of_ik i)
    (cls_of_int ipg)
    v
    T0
    k
    (cls_of_int ipf)
    (cls_of_int ipe); auto with coc core arith datatypes.
generalize H11.
simpl in |- *.
generalize (refl_equal (cl_term T0 (class_env e0))).
rewrite H9.
pattern (cl_term T0 (class_env e0)) at 1 in |- *.
apply class_typ_ord with s1; auto with coc core arith datatypes;
 simple induction 1; auto with coc core arith datatypes.
simpl in |- *.
rewrite H12.
replace
 (typ_skel (cl_term M (TCs class (cl_term T0 (class_env e0)) (class_env e0))))
 with (skel_int M (TCs Int_K iT ipe)).
intros.
apply H6; auto with coc core arith datatypes.
simpl in |- *.
elim H12.
elim skel_sound with e0 T0 (Srt s1); auto with coc core arith datatypes.
unfold cls_of_int in |- *; simpl in |- *; elim H9;
 auto with coc core arith datatypes.

unfold cls_of_int in |- *.
simpl in |- *.
red in |- *; intros; apply H13.
elim H12.
elim skel_sound with e0 T0 (Srt s1); simpl in |- *;
 auto with coc core arith datatypes.
elim H9.
unfold cls_of_int in |- *.
rewrite H14.
auto with coc core arith datatypes.

elim H12.
elim skel_sound with e0 T0 (Srt s1); simpl in |- *;
 auto with coc core arith datatypes.
unfold skel_int, cls_of_int in |- *; simpl in |- *;
 auto with coc core arith datatypes; elim H9;
 auto with coc core arith datatypes.

simpl in |- *.
intros.
replace
 (typ_skel
    (cl_term M
       (TCs class (Knd (cv_skel (cl_term T0 (class_env e0)))) (class_env e0))))
 with (skel_int M (TCs _ (iK _ X2) ipe)).
apply
 eq_can_trans
  with (int_typ M (TCs _ (iK _ X2) ipe) (skel_int M (TCs _ (iK _ X2) ipe)));
 auto with coc core arith datatypes.
apply H6; auto with coc core arith datatypes.
unfold cls_of_int in |- *.
simpl in |- *.
elim H12.
elim H9; auto with coc core arith datatypes.

unfold cls_of_int in |- *.
simpl in |- *.
elim H9.
unfold cls_of_int in |- *.
red in |- *; intros; apply H13.
elim H9.
unfold cls_of_int in |- *.
rewrite H17; auto with coc core arith datatypes.

unfold skel_int in |- *.
unfold cls_of_int in |- *.
simpl in |- *.
elim H9; auto with coc core arith datatypes.

apply ins_in_cls with i; auto with coc core arith datatypes.

unfold cls_of_int in |- *.
elim H8; simpl in |- *; auto with coc core arith datatypes.

generalize H11.
simpl in |- *.
rewrite H9.
replace (TCs class (cl_term T0 (class_env e0)) (class_env e0)) with
 (class_env (T0 :: e0)); auto with coc core arith datatypes.
elim class_sound with (T0 :: e0) M U (Srt s2);
 auto with coc core arith datatypes; intros.
elim H12; auto with coc core arith datatypes.

elim type_case with e0 u (Prod V Ur); intros;
 auto with coc core arith datatypes.
inversion_clear H10.
apply inv_typ_prod with e0 V Ur (Srt x); auto with coc core arith datatypes;
 intros.
unfold skel_int in |- *.
simpl in |- *.
elim
 class_subst
  with
    (class_of_ik i)
    (cls_of_int ipg)
    v
    u
    k
    (cls_of_int ipf)
    (cls_of_int ipe); auto with coc core arith datatypes.
cut
 (cl_term u (cls_of_int ipe) = Typ (typ_skel (cl_term u (cls_of_int ipe)))).
intro.
rewrite H14.
elim
 class_subst
  with
    (class_of_ik i)
    (cls_of_int ipg)
    v
    v0
    k
    (cls_of_int ipf)
    (cls_of_int ipe); auto with coc core arith datatypes.
rewrite H7.
generalize (refl_equal (cl_term v0 (class_env e0))).
pattern (cl_term v0 (class_env e0)) at 1, (cl_term V (class_env e0)) in |- *.
elim class_sound with e0 v0 V (Srt s1); auto with coc core arith datatypes;
 intros.
elim H15.
replace
 (typ_skel
    match typ_skel (cl_term u (class_env e0)) with
    | PROP => Typ (typ_skel (cl_term u (class_env e0)))
    | PROD _ _ => Typ (typ_skel (cl_term u (class_env e0)))
    end) with (skel_int u ipe).
apply H4; auto with coc core arith datatypes.
rewrite H14.
discriminate.

unfold skel_int in |- *.
elim H7.
case (typ_skel (cl_term u (cls_of_int ipe)));
 auto with coc core arith datatypes.

elim H15.
elim skel_sound with e0 u (Prod V Ur); auto with coc core arith datatypes.
cut (cl_term V (class_env e0) = Knd s); intros.
cut
 (cl_term Ur (TCs class (cl_term V (class_env e0)) (class_env e0)) =
  Knd (cv_skel (cl_term Ur (class_env (V :: e0))))); 
 intros.
simpl in |- *.
rewrite H17.
rewrite H16.
simpl in |- *.
generalize (H4 k ipe ipf H5 H6 H7 H8).
replace (skel_int u ipe) with
 (PROD s
    (cv_skel
       (cl_term Ur (TCs class (cl_term V (class_env e0)) (class_env e0))))).
simpl in |- *; intros.
apply H18; auto with coc core arith datatypes.
rewrite H14.
discriminate.

replace s with (skel_int v0 ipe).
apply H2; auto with coc core arith datatypes.
rewrite H7.
elim H15.
discriminate.

unfold skel_int in |- *.
rewrite H7.
elim H15; simpl in |- *; auto with coc core arith datatypes.

apply int_equiv_int_typ.
apply int_inv_int_eq_can.
apply ins_int_inv with ipe k i; auto with coc core arith datatypes.

unfold skel_int in |- *.
rewrite H7.
elim skel_sound with e0 u (Prod V Ur); auto with coc core arith datatypes.
simpl in |- *.
rewrite H17.
rewrite H16.
simpl in |- *; auto with coc core arith datatypes.

generalize (class_sound e0 u (Prod V Ur) H3 (Srt x) H11).
simpl in |- *.
rewrite H16.
elim H7.
rewrite H14.
elim (cl_term Ur (TCs class (Knd s) (cls_of_int ipe))); simpl in |- *; intros;
 auto with coc core arith datatypes.
inversion_clear H17.

inversion_clear H17.

replace s with (cv_skel (cl_term V (class_env e0))).
generalize H15.
elim class_sound with e0 v0 V (Srt s1); simpl in |- *;
 auto with coc core arith datatypes; intros.
inversion_clear H16.

generalize H15.
rewrite (skel_sound e0 v0 V); auto with coc core arith datatypes.
elim (cl_term v0 (class_env e0)); simpl in |- *; intros.
discriminate H16.

injection H16; auto with coc core arith datatypes.

discriminate H16.

unfold cls_of_int in |- *.
elim H5; simpl in |- *; auto with coc core arith datatypes.

unfold cls_of_int in |- *.
elim H6; simpl in |- *; auto with coc core arith datatypes.

generalize H9.
rewrite H7.
simpl in |- *.
elim class_sound with e0 u (Prod V Ur) (Srt x); simpl in |- *;
 auto with coc core arith datatypes; intros.
elim H14; auto with coc core arith datatypes.

unfold cls_of_int in |- *.
elim H5; simpl in |- *; auto with coc core arith datatypes.

unfold cls_of_int in |- *.
elim H6; simpl in |- *; auto with coc core arith datatypes.

discriminate H10.

replace (skel_int (Prod T0 U) ipe) with PROP.
simpl; fold Can.
elim class_subst
  with (class_of_ik i) (cls_of_int ipg) v T0 k
     (cls_of_int ipf) (cls_of_int ipe); auto with coc core arith datatypes.
apply eq_can_Pi; simpl in |- *; intros; auto with coc core arith datatypes.
replace eq_cand with (eq_can PROP); auto with coc core arith datatypes.
replace PROP with (skel_int T0 ipe).
apply H2; auto with coc core arith datatypes.
rewrite H7.
apply class_typ_ord with s1; auto with coc core arith datatypes.
discriminate.

discriminate.

unfold skel_int in |- *.
rewrite H7.
elim skel_sound with e0 T0 (Srt s1); simpl in |- *;
 auto with coc core arith datatypes.

replace eq_cand with (eq_can PROP); auto with coc core arith datatypes.
apply
 eq_can_trans
  with
    (int_typ U (int_cons T0 ipe (cv_skel (cl_term T0 (cls_of_int ipe))) X2)
       PROP); auto with coc core arith datatypes.
apply int_equiv_int_typ.
unfold int_cons, ext_ik in |- *.
pattern (cl_term T0 (cls_of_int ipe)) at 1 3 in |- *.
elim (cl_term T0 (cls_of_int ipe)); auto with coc core arith datatypes.

apply int_equiv_int_typ.
unfold int_cons, ext_ik in |- *.
pattern (cl_term T0 (cls_of_int ipe)) at 1 3 in |- *.
elim (cl_term T0 (cls_of_int ipe)); auto with coc core arith datatypes.

replace PROP with
 (skel_int U (int_cons T0 ipe (cv_skel (cl_term T0 (cls_of_int ipe))) X2)).
apply H4; auto with coc core arith datatypes.
unfold int_cons, ext_ik in |- *.
elim
 class_subst
  with
    (class_of_ik i)
    (cls_of_int ipg)
    v
    T0
    k
    (cls_of_int ipf)
    (cls_of_int ipe); auto with coc core arith datatypes.
unfold cls_of_int in |- *.
elim H5; simpl in |- *; auto with coc core arith datatypes.

unfold cls_of_int in |- *.
elim H6; simpl in |- *; auto with coc core arith datatypes.

unfold int_cons in |- *; auto with coc core arith datatypes.

unfold int_cons, ext_ik in |- *.
unfold cls_of_int at 1 in |- *.
simpl in |- *.
cut (typ_skel (cl_term T0 (class_env e0)) = PROP).
generalize X2.
rewrite H7.
pattern (cl_term T0 (class_env e0)) in |- *.
apply class_typ_ord with s1; simpl in |- *;
 auto with coc core arith datatypes.
intros.
rewrite H13.
elim H7; auto with coc core arith datatypes.

intros.
elim H7; auto with coc core arith datatypes.

elim skel_sound with e0 T0 (Srt s1); simpl in |- *;
 auto with coc core arith datatypes.

unfold int_cons, ext_ik in |- *.
pattern (cl_term T0 (cls_of_int ipe)) at 1 in |- *.
elim (cl_term T0 (cls_of_int ipe)); auto with coc core arith datatypes.

replace
 (cls_of_int (int_cons T0 ipe (cv_skel (cl_term T0 (cls_of_int ipe))) X2))
 with (class_env (T0 :: e0)).
apply class_typ_ord with s2; auto with coc core arith datatypes.
discriminate.

discriminate.

unfold cls_of_int, int_cons, ext_ik in |- *.
unfold int_cons, ext_ik in |- *.
simpl in |- *.
rewrite H7.
cut (typ_skel (cl_term T0 (class_env e0)) = PROP).
generalize X2.
unfold cls_of_int in |- *.
replace (Tmap Int_K class class_of_ik ipe) with (cls_of_int ipe);
 auto with coc core arith datatypes.
rewrite H7.
pattern (cl_term T0 (class_env e0)) in |- *.
apply class_typ_ord with s1; simpl in |- *;
 auto with coc core arith datatypes.
intros.
rewrite H13; auto with coc core arith datatypes.

elim skel_sound with e0 T0 (Srt s1); simpl in |- *;
 auto with coc core arith datatypes.

unfold skel_int in |- *.
replace
 (cls_of_int (int_cons T0 ipe (cv_skel (cl_term T0 (cls_of_int ipe))) X2))
 with (class_env (T0 :: e0)).
elim skel_sound with (T0 :: e0) U (Srt s2); simpl in |- *;
 auto with coc core arith datatypes.

unfold int_cons, ext_ik in |- *.
unfold cls_of_int at 1 in |- *.
simpl in |- *.
cut (typ_skel (cl_term T0 (class_env e0)) = PROP).
generalize X2.
rewrite H7.
pattern (cl_term T0 (class_env e0)) in |- *.
apply class_typ_ord with s1; simpl in |- *;
 auto with coc core arith datatypes.
intros.
rewrite H13.
elim H7; auto with coc core arith datatypes.

intros.
elim H7; auto with coc core arith datatypes.

elim skel_sound with e0 T0 (Srt s1); simpl in |- *;
 auto with coc core arith datatypes.

unfold cls_of_int in |- *.
elim H5; simpl in |- *; auto with coc core arith datatypes.

unfold cls_of_int in |- *.
elim H6; simpl in |- *; auto with coc core arith datatypes.

unfold skel_int.
generalize (skel_sound (T0 :: e0) U (Srt s2) H3).
simpl in |- *.
rewrite H7.
elim (cl_term U (TCs class (cl_term T0 (class_env e0)) (class_env e0)));
 simpl in |- *; auto with coc core arith datatypes.
elim (cl_term T0 (class_env e0)); simpl in |- *;
 auto with coc core arith datatypes.

apply H2; auto with coc core arith datatypes.
Qed.


  Lemma int_cons_equal :
   forall (ip : intP) (e : env),
   cls_of_int ip = class_env e ->
   forall (N : term) (s1 : sort),
   typ e N (Srt s1) ->
   forall C : Can (cv_skel (cl_term N (class_env e))),
   cls_of_int (int_cons N ip _ C) = class_env (N :: e).
intros.
unfold int_cons, ext_ik in |- *.
rewrite H.
simpl in |- *.
generalize C.
pattern (cl_term N (class_env e)) in |- *.
apply class_typ_ord with s1; auto with coc core arith datatypes.
simpl in |- *; intros.
elim skel_sound with e N (Srt s1); simpl in |- *; intros;
 auto with coc core arith datatypes.
unfold cls_of_int in |- *; simpl in |- *; elim H;
 auto with coc core arith datatypes.

unfold cls_of_int in |- *; simpl in |- *; elim H;
 auto with coc core arith datatypes.
Qed.



  Lemma int_typ_red1 :
   forall U V : term,
   red1 U V ->
   forall (e : env) (K : term),
   typ e U K ->
   forall ip : intP,
   cls_of_int ip = class_env e ->
   int_inv ip ->
   cl_term U (cls_of_int ip) <> Trm ->
   eq_can (skel_int U ip) (int_typ U ip _) (int_typ V ip _).
simple induction 1; intros.
unfold skel_int in |- *.
apply inv_typ_app with e (Abs T M) N K; intros;
 auto with coc core arith datatypes.
elim type_case with e (Abs T M) (Prod V0 Ur); intros;
 auto with coc core arith datatypes.
inversion_clear H7.
apply inv_typ_prod with e V0 Ur (Srt x); intros;
 auto with coc core arith datatypes.
apply inv_typ_abs with e T M (Prod V0 Ur); intros;
 auto with coc core arith datatypes.
cut (typ e N T); intros.
cut
 (cl_term M (TCs _ (cl_term T (cls_of_int ip)) (cls_of_int ip)) =
  Typ (typ_skel (cl_term M (class_env (T :: e))))).
cut (int_var_sound N ip (ext_ik T ip _ (int_typ N ip (skel_int N ip)))).
simpl in |- *; unfold def_cons, int_cons, ext_ik in |- *; simpl in |- *;
 rewrite H1.
cut (cl_term T (cls_of_int ip) = cl_term T (class_env e)).
elim class_sound with e N T (Srt s0); intros;
 auto with coc core arith datatypes; rewrite H18.
simpl in |- *.
replace
 (typ_skel
    match typ_skel (cl_term M (TCs class (Typ PROP) (class_env e))) with
    | PROP => Typ (typ_skel (cl_term M (TCs _ (Typ PROP) (class_env e))))
    | _ => Typ (typ_skel (cl_term M (TCs _ (Typ PROP) (class_env e))))
    end) with (skel_int M (TCs Int_K iT ip)).
unfold subst in |- *.
apply subst_int_typ with ip iT (T :: e) T0;
 auto with coc core arith datatypes.
unfold cls_of_int in |- *.
simpl in |- *.
elim H16.
elim H1; auto with coc core arith datatypes.

red in |- *; intro; apply H3.
simpl in |- *.
replace (TCs class (cl_term T (cls_of_int ip)) (cls_of_int ip)) with
 (cls_of_int (TCs Int_K iT ip)).
rewrite H19; auto with coc core arith datatypes.

unfold cls_of_int at 1 in |- *.
simpl in |- *.
elim H16; auto with coc core arith datatypes.

unfold skel_int in |- *.
unfold cls_of_int in |- *.
simpl in |- *.
elim H1.
unfold cls_of_int in |- *.
elim
 (typ_skel
    (cl_term M (TCs class (Typ PROP) (Tmap Int_K class class_of_ik ip))));
 auto with coc core arith datatypes.

elim H18.
unfold subst in |- *.
replace (typ_skel (cl_term M (TCs class (Knd s) (class_env e)))) with
 (skel_int M (TCs Int_K (iK s (int_typ N ip s)) ip)).
apply subst_int_typ with ip (iK s (int_typ N ip s)) (T :: e) T0;
 auto with coc core arith datatypes.
apply ivs_K.
generalize H16.
rewrite H1.
elim class_sound with e N T (Srt s0); auto with coc core arith datatypes;
 intros.
discriminate H19.

inversion_clear H19; auto with coc core arith datatypes.

unfold cls_of_int in |- *.
simpl in |- *.
elim H1.
rewrite H16; auto with coc core arith datatypes.

auto 10 with coc core arith datatypes.

unfold cls_of_int in |- *.
simpl in |- *.
red in |- *; intro; apply H3.
simpl in |- *.
rewrite H16.
unfold cls_of_int in |- *.
rewrite H19; auto with coc core arith datatypes.

unfold skel_int in |- *.
unfold cls_of_int in |- *.
simpl in |- *.
elim H1; auto with coc core arith datatypes.

elim H1; auto with coc core arith datatypes.

unfold ext_ik in |- *.
unfold skel_int in |- *.
generalize (ivs_T N ip) (ivs_K N ip).
rewrite H1.
elim class_sound with e N T (Srt s0); auto with coc core arith datatypes;
 intros.

generalize H3.
simpl in |- *.
rewrite H1.
replace (TCs class (cl_term T (class_env e)) (class_env e)) with
 (class_env (T :: e)); auto with coc core arith datatypes.
elim class_sound with (T :: e) M T0 (Srt s3);
 auto with coc core arith datatypes.
simple induction 1; auto with coc core arith datatypes.

apply type_conv with V0 s0; auto with coc core arith datatypes.
apply inv_conv_prod_l with Ur T0; auto with coc core arith datatypes.

discriminate H7.

apply inv_typ_abs with e M N K; intros; auto with coc core arith datatypes.
unfold skel_int in |- *.
rewrite H3.
simpl in |- *.
unfold def_cons in |- *.
replace (TCs _ (cl_term M (class_env e)) (class_env e)) with
 (class_env (M :: e)); auto with coc core arith datatypes.
elim class_sound with (M :: e) N T (Srt s2);
 auto with coc core arith datatypes.
simpl in |- *.
unfold int_cons in |- *.
unfold ext_ik in |- *.
rewrite H3.
elim class_red with e M M' (Srt s1); auto with coc core arith datatypes.

unfold int_cons, ext_ik in |- *.
rewrite H3.
elim class_red with e M M' (Srt s1); auto with coc core arith datatypes.
cut (cl_term M (cls_of_int ip) = cl_term M (class_env e)).
elim (cl_term M (class_env e)); simpl in |- *; intros;
 auto with coc core arith datatypes.

elim H3; auto with coc core arith datatypes.

apply inv_typ_abs with e N M K; intros; auto with coc core arith datatypes.
unfold skel_int in |- *.
simpl in |- *.
rewrite H3.
replace (TCs _ (cl_term M (class_env e)) (class_env e)) with
 (class_env (M :: e)); auto with coc core arith datatypes.
replace (cl_term M (TCs class (cl_term N (class_env e)) (class_env e))) with
 (Typ (typ_skel (cl_term M (class_env (N :: e))))).
cut (cl_term N (cls_of_int ip) = cl_term N (class_env e)).
pattern (cl_term N (class_env e)) in |- *.
apply class_typ_ord with s1; intros; auto with coc core arith datatypes.
simpl in |- *.
replace
 (typ_skel (cl_term M (TCs class (cl_term N (class_env e)) (class_env e))))
 with (skel_int M (def_cons N ip)).
apply H1 with (N :: e) T; auto with coc core arith datatypes.
unfold def_cons, int_cons, ext_ik in |- *.
simpl in |- *.
rewrite H3.
unfold cls_of_int in |- *.
simpl in |- *.
pattern (cl_term N (class_env e)) in |- *.
apply class_typ_ord with s1; intros; auto with coc core arith datatypes.
simpl in |- *.
elim skel_sound with e N (Srt s1); simpl in |- *;
 auto with coc core arith datatypes.
elim H3; auto with coc core arith datatypes.

simpl in |- *.
elim H3; auto with coc core arith datatypes.

unfold def_cons, int_cons, ext_ik in |- *.
rewrite H3.
pattern (cl_term N (class_env e)) in |- *.
apply class_typ_ord with s1; auto with coc core arith datatypes.

unfold def_cons in |- *.
red in |- *; intro; apply H5.
simpl in |- *.
replace (TCs class (cl_term N (cls_of_int ip)) (cls_of_int ip)) with
 (cls_of_int
    (int_cons N ip (cv_skel (cl_term N (cls_of_int ip)))
       (default_can (cv_skel (cl_term N (cls_of_int ip)))))).
rewrite H11; auto with coc core arith datatypes.

replace (TCs class (cl_term N (cls_of_int ip)) (cls_of_int ip)) with
 (class_env (N :: e)); auto with coc core arith datatypes.
rewrite H3.
apply int_cons_equal with s1; auto with coc core arith datatypes.

rewrite H3; auto with coc core arith datatypes.

unfold skel_int in |- *.
replace (cls_of_int (def_cons N ip)) with
 (TCs class (cl_term N (class_env e)) (class_env e)).
auto with coc core arith datatypes.

symmetry  in |- *.
unfold def_cons in |- *.
replace (TCs class (cl_term N (class_env e)) (class_env e)) with
 (class_env (N :: e)); auto with coc core arith datatypes.
rewrite H3.
apply int_cons_equal with s1; auto with coc core arith datatypes.

simpl in |- *.
intros.
replace
 (typ_skel (cl_term M (TCs class (cl_term N (class_env e)) (class_env e))))
 with (skel_int M (TCs Int_K (iK (cv_skel (cl_term N (class_env e))) X2) ip)).
apply
 eq_can_trans
  with (int_typ M (TCs _ (iK _ X2) ip) (skel_int M (TCs _ (iK _ X2) ip)));
 auto with coc core arith datatypes.
apply H1 with (N :: e) T; auto with coc core arith datatypes.
elim int_cons_equal with ip e N s1 X2; auto with coc core arith datatypes.
unfold cls_of_int in |- *.
simpl in |- *.
unfold ext_ik in |- *.
rewrite H10; simpl in |- *; auto with coc core arith datatypes.

unfold cls_of_int in |- *.
simpl in |- *.
red in |- *; intros; apply H5.
simpl in |- *.
rewrite H10.
simpl in |- *.
unfold cls_of_int in |- *.
rewrite H14; auto with coc core arith datatypes.

unfold skel_int in |- *.
unfold cls_of_int in |- *.
simpl in |- *.
elim H3.
rewrite H10; auto with coc core arith datatypes.

elim H3; auto with coc core arith datatypes.

generalize H5.
simpl in |- *.
rewrite H3.
replace (TCs class (cl_term N (class_env e)) (class_env e)) with
 (class_env (N :: e)); auto with coc core arith datatypes.
elim class_sound with (N :: e) M T (Srt s2); simpl in |- *; intros;
 auto with coc core arith datatypes.
elim H10; auto with coc core arith datatypes.

apply inv_typ_app with e M1 M2 K; intros; auto with coc core arith datatypes.
elim type_case with e M1 (Prod V0 Ur); intros;
 auto with coc core arith datatypes.
inversion_clear H9.
apply inv_typ_prod with e V0 Ur (Srt x); intros;
 auto with coc core arith datatypes.
unfold skel_int in |- *.
simpl in |- *.
rewrite H3.
elim class_red with e M1 N1 (Prod V0 Ur); auto with coc core arith datatypes.
cut (cl_term M1 (class_env e) = Typ (typ_skel (cl_term M1 (class_env e)))).
intro.
rewrite H13.
cut (cl_term M2 (cls_of_int ip) = cl_term M2 (class_env e)).
elim class_sound with e M2 V0 (Srt s1); auto with coc core arith datatypes;
 intros.
replace
 (typ_skel
    match typ_skel (cl_term M1 (class_env e)) return class with
    | PROP => Typ (typ_skel (cl_term M1 (class_env e)))
    | PROD _ _ => Typ (typ_skel (cl_term M1 (class_env e)))
    end) with (skel_int M1 ip).
apply H1 with e (Prod V0 Ur); auto with coc core arith datatypes.
red in |- *; intro; apply H5.
simpl in |- *.
rewrite H15; auto with coc core arith datatypes.

unfold skel_int in |- *.
elim H3.
elim (typ_skel (cl_term M1 (cls_of_int ip)));
 auto with coc core arith datatypes.

generalize (H1 e (Prod V0 Ur) H6 ip H3 H4).
replace (skel_int M1 ip) with
 (PROD s
    (typ_skel
       match typ_skel (cl_term M1 (class_env e)) with
       | PROP => Typ (typ_skel (cl_term M1 (class_env e)))
       | PROD _ s2 => Typ s2
       end)).
simpl in |- *; intros.
apply H15; auto with coc core arith datatypes.
red in |- *; intro; apply H5.
simpl in |- *.
rewrite H16; auto with coc core arith datatypes.

unfold skel_int in |- *.
rewrite H3.
elim skel_sound with e M1 (Prod V0 Ur); auto with coc core arith datatypes.
simpl in |- *.
cut (cl_term V0 (class_env e) = Knd s); intros.
cut
 (cl_term Ur (TCs class (cl_term V0 (class_env e)) (class_env e)) =
  Knd (cv_skel (cl_term Ur (class_env (V0 :: e))))); 
 intros.
rewrite H16.
rewrite H15; simpl in |- *; auto with coc core arith datatypes.

generalize (class_sound e M1 (Prod V0 Ur) H6 (Srt x) H10).
simpl in |- *.
rewrite H15.
rewrite H13.
elim (cl_term Ur (TCs class (Knd s) (class_env e))); intros;
 auto with coc core arith datatypes.
inversion_clear H16.

inversion_clear H16.

generalize H14.
rewrite H3.
elim class_sound with e M2 V0 (Srt s1); intros;
 auto with coc core arith datatypes.
discriminate H15.

inversion_clear H15; auto with coc core arith datatypes.

elim H3; auto with coc core arith datatypes.

generalize H5.
simpl in |- *.
rewrite H3.
elim class_sound with e M1 (Prod V0 Ur) (Srt x); intros;
 auto with coc core arith datatypes.
elim H13; auto with coc core arith datatypes.

discriminate H9.

cut (cl_term M1 (cls_of_int ip) <> Trm); intros.
apply inv_typ_app with e M1 M2 K; intros; auto with coc core arith datatypes.
elim type_case with e M1 (Prod V0 Ur); intros;
 auto with coc core arith datatypes.
inversion_clear H10.
apply inv_typ_prod with e V0 Ur (Srt x); intros;
 auto with coc core arith datatypes.
unfold skel_int in |- *.
simpl in |- *.
rewrite H3.
elim class_red with e M2 N2 V0; auto with coc core arith datatypes.
cut (cl_term M1 (class_env e) = Typ (typ_skel (cl_term M1 (class_env e)))).
intro.
rewrite H14.
cut (cl_term M2 (cls_of_int ip) = cl_term M2 (class_env e)).
elim class_sound with e M2 V0 (Srt s1); auto with coc core arith datatypes;
 intros.
cut
 (eq_can _
    (int_typ M1 ip
       (PROD s
          (typ_skel
             match typ_skel (cl_term M1 (class_env e)) with
             | PROP => Typ (typ_skel (cl_term M1 (class_env e)))
             | PROD _ s2 => Typ s2
             end)))
    (int_typ M1 ip
       (PROD s
          (typ_skel
             match typ_skel (cl_term M1 (class_env e)) with
             | PROP => Typ (typ_skel (cl_term M1 (class_env e)))
             | PROD _ s2 => Typ s2
             end)))).
simpl in |- *; intros.
apply H16; auto with coc core arith datatypes.
replace s with (skel_int M2 ip).
apply H1 with e V0; auto with coc core arith datatypes.
rewrite H15.
discriminate.

unfold skel_int in |- *.
generalize H15.
rewrite H3.
elim class_sound with e M2 V0 (Srt s1); intros;
 auto with coc core arith datatypes.
discriminate H17.

inversion_clear H17; auto with coc core arith datatypes.

auto with coc core arith datatypes.

elim H3; auto with coc core arith datatypes.

generalize H6.
rewrite H3.
elim class_sound with e M1 (Prod V0 Ur) (Srt x);
 auto with coc core arith datatypes; intros.
elim H14; auto with coc core arith datatypes.

discriminate H10.

red in |- *; intros; apply H5.
simpl in |- *.
rewrite H6; auto with coc core arith datatypes.

apply inv_typ_prod with e M1 M2 K; intros; auto with coc core arith datatypes.
unfold skel_int in |- *.
simpl in |- *.
rewrite H3.
elim class_red with e M1 N1 (Srt s1); auto with coc core arith datatypes.
replace (TCs class (cl_term M1 (class_env e)) (class_env e)) with
 (class_env (M1 :: e)); auto with coc core arith datatypes.
cut (skel_int M1 ip = PROP); intros.
pattern (cl_term M2 (class_env (M1 :: e))) in |- *.
apply class_typ_ord with s2; auto with coc core arith datatypes.
elim skel_sound with (M1 :: e) M2 (Srt s2); simpl in |- *;
 auto with coc core arith datatypes.
apply eq_can_Pi; auto with coc core arith datatypes.
elim H9.
apply H1 with e (Srt s1); auto with coc core arith datatypes.
rewrite H3.
apply class_typ_ord with s1; auto with coc core arith datatypes.
discriminate.

discriminate.

simpl in |- *; intros.
unfold int_cons, ext_ik in |- *.
rewrite H3.
elim class_red with e M1 N1 (Srt s1); auto with coc core arith datatypes.
pattern (cl_term M1 (class_env e)) at 1 3 in |- *.
elim (cl_term M1 (class_env e)); auto with coc core arith datatypes.
intros.
replace eq_cand with (eq_can PROP); auto with coc core arith datatypes.

pattern (cl_term M1 (class_env e)) in |- *.
apply class_typ_ord with s1; auto with coc core arith datatypes.
simpl in |- *.
apply eq_can_Pi; auto with coc core arith datatypes.
elim H9.
apply H1 with e (Srt s1); auto with coc core arith datatypes.
rewrite H3.
apply class_typ_ord with s1; auto with coc core arith datatypes.
discriminate.

discriminate.

simpl in |- *; intros.
replace eq_cand with (eq_can PROP); auto with coc core arith datatypes.
apply int_equiv_int_typ.
unfold int_cons, ext_ik in |- *.
rewrite H3.
elim class_red with e M1 N1 (Srt s1); auto with coc core arith datatypes.
elim (cl_term M1 (class_env e)); auto with coc core arith datatypes.

simpl in |- *.
apply eq_can_Pi; auto with coc core arith datatypes.
elim H9.
apply H1 with e (Srt s1); auto with coc core arith datatypes.
rewrite H3.
apply class_typ_ord with s1; auto with coc core arith datatypes.
discriminate.

discriminate.

simpl in |- *; intros.
change
  (eq_can PROP
     (int_typ M2 (int_cons M1 ip (cv_skel (cl_term M1 (class_env e))) X1)
        PROP)
     (int_typ M2 (int_cons N1 ip (cv_skel (cl_term M1 (class_env e))) X2)
        PROP)) in |- *.
unfold int_cons, ext_ik in |- *.
rewrite H3.
elim class_red with e M1 N1 (Srt s1); auto with coc core arith datatypes.
pattern (cl_term M1 (class_env e)) at 1 3 in |- *.
elim (cl_term M1 (class_env e)); auto with coc core arith datatypes.

unfold skel_int in |- *.
rewrite H3.
elim skel_sound with e M1 (Srt s1); simpl in |- *;
 auto with coc core arith datatypes.

apply inv_typ_prod with e M1 M2 K; intros; auto with coc core arith datatypes.
unfold skel_int in |- *.
simpl in |- *.
rewrite H3.
elim class_red with (M1 :: e) M2 N2 (Srt s2);
 auto with coc core arith datatypes.
replace (TCs class (cl_term M1 (class_env e)) (class_env e)) with
 (class_env (M1 :: e)); auto with coc core arith datatypes.
pattern (cl_term M2 (class_env (M1 :: e))) in |- *.
apply class_typ_ord with s2; auto with coc core arith datatypes.
elim skel_sound with (M1 :: e) M2 (Srt s2); simpl in |- *;
 auto with coc core arith datatypes.
apply eq_can_Pi; auto with coc core arith datatypes.
simpl in |- *; intros.
replace eq_cand with (eq_can PROP); auto with coc core arith datatypes.
apply
 eq_can_trans
  with
    (int_typ M2 (int_cons M1 ip (cv_skel (cl_term M1 (class_env e))) X2) PROP);
 auto with coc core arith datatypes.
unfold int_cons, ext_ik in |- *.
elim (cl_term M1 (cls_of_int ip)); auto with coc core arith datatypes.

unfold int_cons, ext_ik in |- *.
elim (cl_term M1 (cls_of_int ip)); auto with coc core arith datatypes.

replace PROP with
 (skel_int M2 (int_cons M1 ip (cv_skel (cl_term M1 (class_env e))) X2)).
apply H1 with (M1 :: e) (Srt s2); auto with coc core arith datatypes.
apply int_cons_equal with s1; auto with coc core arith datatypes.

unfold int_cons, ext_ik in |- *.
elim (cl_term M1 (cls_of_int ip)); auto with coc core arith datatypes.

red in |- *; intros.
apply H5.
simpl in |- *.
replace (TCs class (cl_term M1 (cls_of_int ip)) (cls_of_int ip)) with
 (cls_of_int (int_cons M1 ip (cv_skel (cl_term M1 (class_env e))) X2)).
rewrite H12; auto with coc core arith datatypes.

rewrite H3.
replace (TCs class (cl_term M1 (class_env e)) (class_env e)) with
 (class_env (M1 :: e)); auto with coc core arith datatypes.
apply int_cons_equal with s1; auto with coc core arith datatypes.

unfold skel_int in |- *.
replace (cls_of_int (int_cons M1 ip (cv_skel (cl_term M1 (class_env e))) X2))
 with (class_env (M1 :: e)).
elim skel_sound with (M1 :: e) M2 (Srt s2);
 auto with coc core arith datatypes.

replace (TCs class (cl_term M1 (class_env e)) (class_env e)) with
 (class_env (M1 :: e)); auto with coc core arith datatypes.
symmetry  in |- *.
apply int_cons_equal with s1; auto with coc core arith datatypes.

cut (cl_term M1 (cls_of_int ip) = cl_term M1 (class_env e)).
pattern (cl_term M1 (class_env e)) in |- *.
apply class_typ_ord with s1; auto with coc core arith datatypes.
simpl in |- *; intros.
apply eq_can_Pi; auto with coc core arith datatypes.
simpl in |- *; intros.
replace eq_cand with (eq_can PROP); auto with coc core arith datatypes.
apply eq_can_trans with (int_typ M2 (int_cons M1 ip PROP X2) PROP);
 auto with coc core arith datatypes.
unfold int_cons, ext_ik in |- *.
elim (cl_term M1 (cls_of_int ip)); auto with coc core arith datatypes.

unfold int_cons, ext_ik in |- *.
elim (cl_term M1 (cls_of_int ip)); auto with coc core arith datatypes.

pattern PROP at 1 3 5 in |- *.
replace PROP with (skel_int M2 (int_cons M1 ip PROP X2)).
cut (cv_skel (cl_term M1 (class_env e)) = PROP); intros.
apply H1 with (M1 :: e) (Srt s2); auto with coc core arith datatypes.
generalize X2 H12.
change
  (forall X2 : Can PROP,
   eq_can PROP X2 X2 ->
   cls_of_int (int_cons M1 ip PROP X2) = class_env (M1 :: e)) 
 in |- *.
elim H13.
intros.
apply int_cons_equal with s1; auto with coc core arith datatypes.

unfold int_cons, ext_ik in |- *.
elim (cl_term M1 (cls_of_int ip)); auto with coc core arith datatypes.

replace (cls_of_int (int_cons M1 ip PROP X2)) with (class_env (M1 :: e)).
red in |- *; intros; apply H5.
simpl in |- *.
rewrite H3.
replace (TCs class (cl_term M1 (class_env e)) (class_env e)) with
 (class_env (M1 :: e)); auto with coc core arith datatypes.
rewrite H14; auto with coc core arith datatypes.

generalize X2 H12.
change
  (forall X2 : Can PROP,
   eq_can PROP X2 X2 ->
   class_env (M1 :: e) = cls_of_int (int_cons M1 ip PROP X2)) 
 in |- *.
elim H13.
intros.
symmetry  in |- *.
apply int_cons_equal with s1; auto with coc core arith datatypes.

elim H3.
rewrite H9; simpl in |- *; auto with coc core arith datatypes.

unfold skel_int in |- *.
replace (cls_of_int (int_cons M1 ip PROP X2)) with (class_env (M1 :: e)).
elim skel_sound with (M1 :: e) M2 (Srt s2);
 auto with coc core arith datatypes.

generalize X2 H12.
change
  (forall X2 : Can PROP,
   eq_can PROP X2 X2 ->
   class_env (M1 :: e) = cls_of_int (int_cons M1 ip PROP X2)) 
 in |- *.
replace PROP with (cv_skel (cl_term M1 (class_env e))).
intros.
symmetry  in |- *.
apply int_cons_equal with s1; auto with coc core arith datatypes.

elim H3.
rewrite H9; auto with coc core arith datatypes.

intros.
simpl in |- *.
apply eq_can_Pi; auto with coc core arith datatypes.
simpl in |- *; intros.
replace eq_cand with (eq_can PROP); auto with coc core arith datatypes.
apply
 eq_can_trans
  with
    (int_typ M2 (int_cons M1 ip (cv_skel (cl_term M1 (class_env e))) X2) PROP);
 auto with coc core arith datatypes.
unfold int_cons, ext_ik in |- *.
elim (cl_term M1 (cls_of_int ip)); auto with coc core arith datatypes.

unfold int_cons, ext_ik in |- *.
elim (cl_term M1 (cls_of_int ip)); auto with coc core arith datatypes.

replace PROP with
 (skel_int M2 (int_cons M1 ip (cv_skel (cl_term M1 (class_env e))) X2)).
apply H1 with (M1 :: e) (Srt s2); auto with coc core arith datatypes.
apply int_cons_equal with s1; auto with coc core arith datatypes.

unfold int_cons, ext_ik in |- *.
elim (cl_term M1 (cls_of_int ip)); auto with coc core arith datatypes.

red in |- *; intros.
apply H5.
simpl in |- *.
replace (TCs class (cl_term M1 (cls_of_int ip)) (cls_of_int ip)) with
 (cls_of_int (int_cons M1 ip (cv_skel (cl_term M1 (class_env e))) X2)).
rewrite H13; auto with coc core arith datatypes.

rewrite H3.
replace (TCs class (cl_term M1 (class_env e)) (class_env e)) with
 (class_env (M1 :: e)); auto with coc core arith datatypes.
apply int_cons_equal with s1; auto with coc core arith datatypes.

unfold skel_int in |- *.
replace (cls_of_int (int_cons M1 ip (cv_skel (cl_term M1 (class_env e))) X2))
 with (class_env (M1 :: e)).
elim skel_sound with (M1 :: e) M2 (Srt s2);
 auto with coc core arith datatypes.

replace (TCs class (cl_term M1 (class_env e)) (class_env e)) with
 (class_env (M1 :: e)); auto with coc core arith datatypes.
symmetry  in |- *.
apply int_cons_equal with s1; auto with coc core arith datatypes.

elim H3; auto with coc core arith datatypes.
Qed.



  Lemma red_int_typ :
   forall (e : env) (U K : term),
   typ e U K ->
   forall ip : intP,
   cls_of_int ip = class_env e ->
   int_inv ip ->
   cl_term U (class_env e) <> Trm ->
   forall V : term,
   red U V -> eq_can (skel_int U ip) (int_typ U ip _) (int_typ V ip _).
simple induction 5; auto with coc core arith datatypes; intros.
apply eq_can_trans with (int_typ P ip (skel_int U ip));
 auto with coc core arith datatypes.
replace (skel_int U ip) with (skel_int P ip).
apply int_typ_red1 with e K; auto with coc core arith datatypes.
apply subject_reduction with U; auto with coc core arith datatypes.

rewrite H0.
elim class_red with e U P K; auto with coc core arith datatypes.

unfold skel_int in |- *.
rewrite H0.
elim skel_sound with e U K; auto with coc core arith datatypes.
elim skel_sound with e P K; auto with coc core arith datatypes.
apply subject_reduction with U; auto with coc core arith datatypes.
Qed.


  Lemma conv_int_typ :
   forall (e : env) (U V K : term),
   conv U V ->
   typ e U K ->
   typ e V K ->
   forall ip : intP,
   cls_of_int ip = class_env e ->
   int_inv ip ->
   cl_term U (class_env e) <> Trm ->
   eq_can (skel_int U ip) (int_typ U ip _) (int_typ V ip _).
intros.
elim church_rosser with U V; intros; auto with coc core arith datatypes.
apply eq_can_trans with (int_typ x ip (skel_int U ip));
 auto with coc core arith datatypes.
apply red_int_typ with e K; auto with coc core arith datatypes.

apply eq_can_sym.
replace (skel_int U ip) with (skel_int V ip).
apply red_int_typ with e K; auto with coc core arith datatypes.
rewrite (class_red e V x K); auto with coc core arith datatypes.
elim class_red with e U x K; auto with coc core arith datatypes.

unfold skel_int in |- *.
rewrite H2.
elim skel_sound with e U K; auto with coc core arith datatypes.
elim skel_sound with e V K; auto with coc core arith datatypes.
Qed.

