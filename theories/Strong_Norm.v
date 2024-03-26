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
Require Import Int_term.
Require Import Int_typ.
Require Import Int_stab.
Require Import PeanoNat.

Load "ImpVar".

Inductive trm_in_int : env -> intP -> intt -> Prop :=
  | int_nil : forall itt : intt, trm_in_int nil (TNl _) itt
  | int_cs :
      forall e (ip : intP) (itt : intt),
      trm_in_int e ip itt ->
      forall (y : Int_K) t T,
      int_typ T ip PROP t ->
      trm_in_int (T :: e) (TCs _ y ip) (shift_intt itt t).

  Hint Resolve int_nil int_cs: coc.


  Record int_adapt e (ip : intP) (itt : intt) : Prop := 
    {adapt_trm_in_int : trm_in_int e ip itt;
     int_can_adapt : can_adapt ip;
     adapt_class_equal : cls_of_int ip = class_env e}.



  Lemma int_sound :
   forall e t T,
   typ e t T ->
   forall (ip : intP) (it : intt),
   int_adapt e ip it -> int_typ T ip PROP (int_term t it 0).
simple induction 1; simpl in |- *; intros.
red in |- *; apply Acc_intro; intros.
inversion_clear H2.

red in |- *; apply Acc_intro; intros.
inversion_clear H2.

elim (le_gt_dec 0 v); [ intro Hle | intro Hgt ].
rewrite lift0.
rewrite Nat.sub_0_r.
elim H1; intros.
rewrite H3.
generalize ip it H2.
clear H3 Hle H2 it ip H1 t0.
elim H4.
intros l ip it (in_interp, p, q); revert p q;
  (* Do not intro other fields *)
 inversion_clear in_interp; simpl in |- *; intros ip_can_adapted same_classes.
apply eq_cand_incl with (int_typ x ip0 PROP);
 auto with coc core arith datatypes.
unfold lift in |- *.
apply lift_int_typ with y; auto with coc core arith datatypes.

intros l n y H1 H2 ip it (in_interp, p, q); revert p q; inversion_clear in_interp;
 simpl in |- *; intros ip_can_adapted same_classes.
simpl in |- *.
rewrite simpl_lift.
apply eq_cand_incl with (int_typ (lift (S n) x) ip0 PROP).
unfold lift at 2 in |- *.
apply lift_int_typ with y0; auto with coc core arith datatypes.

apply H2.
apply Build_int_adapt; auto with coc core arith datatypes.
inversion_clear ip_can_adapted; auto with coc core arith datatypes.

injection same_classes; auto with coc core arith datatypes.

inversion_clear Hgt.

elim H6; intros in_interp ip_can_adapted same_classes.
apply Abs_sound; intros; auto with coc core arith datatypes.
apply int_typ_cr; auto with coc core arith datatypes.

simpl in |- *; intros.
change
  (is_can PROP
     (int_typ U (int_cons T0 ip (cv_skel (cl_term T0 (cls_of_int ip))) X)
        PROP)) in |- *.
apply int_typ_cr.
unfold int_cons, ext_ik in |- *.
generalize X H7 H8.
elim (cl_term T0 (cls_of_int ip)); auto with coc core arith datatypes.

unfold subst in |- *.
rewrite int_term_subst; auto with coc core arith datatypes.
apply H5.
unfold int_cons, ext_ik in |- *.
apply Build_int_adapt; auto with coc core arith datatypes.
generalize C H8 H9.
elim (cl_term T0 (cls_of_int ip)); auto with coc core arith datatypes.

simpl in |- *.
pattern (cls_of_int ip) at 1 in |- *.
rewrite same_classes.
unfold cls_of_int in |- *.
pattern (cl_term T0 (class_env e0)) in |- *.
apply class_typ_ord with s1; elim same_classes; simpl in |- *;
 auto with coc core arith datatypes.
rewrite same_classes.
elim skel_sound with e0 T0 (Srt s1); simpl in |- *;
 auto with coc core arith datatypes.
elim same_classes; auto with coc core arith datatypes.

apply H1 with ip; auto with coc core arith datatypes.

elim H4; intros in_interp ip_can_adapted same_classes.
elim type_case with e0 u (Prod V Ur); intros;
 auto with coc core arith datatypes.
inversion_clear H5.
apply inv_typ_prod with e0 V Ur (Srt x); auto with coc core arith datatypes;
 intros.
apply
 eq_cand_incl
  with
    (int_typ Ur
       (int_cons V ip (cv_skel (cl_term V (cls_of_int ip))) (int_typ v ip _))
       PROP).
replace PROP with
 (skel_int Ur
    (int_cons V ip (cv_skel (cl_term V (cls_of_int ip)))
       (int_typ v ip (cv_skel (cl_term V (cls_of_int ip)))))).
unfold subst, int_cons in |- *.
apply
 subst_int_typ
  with
    ip
    (ext_ik V ip (cv_skel (cl_term V (cls_of_int ip)))
       (int_typ v ip (cv_skel (cl_term V (cls_of_int ip)))))
    (V :: e0)
    (Srt s2); auto with coc core arith datatypes.
unfold ext_ik in |- *.
rewrite same_classes.
cut (cl_term v (cls_of_int ip) = cl_term v (class_env e0)).
elim class_sound with e0 v V (Srt s1); intros;
 auto with coc core arith datatypes.

elim same_classes; auto with coc core arith datatypes.

simpl in |- *.
unfold ext_ik in |- *.
rewrite same_classes.
unfold cls_of_int in |- *.
apply class_typ_ord with s1; elim same_classes; simpl in |- *;
 auto with coc core arith datatypes.
rewrite same_classes.
elim skel_sound with e0 V (Srt s1); simpl in |- *;
 auto with coc core arith datatypes.
elim same_classes; auto with coc core arith datatypes.

unfold ext_ik in |- *.
red in |- *; red in |- *; auto with coc core arith datatypes.
apply Tfa2_cs; auto with coc core arith datatypes.
elim (cl_term V (cls_of_int ip)); auto with coc core arith datatypes.

change (int_inv ip) in |- *.
apply adapt_int_inv; auto with coc core arith datatypes.

replace
 (cls_of_int
    (TCs Int_K
       (ext_ik V ip (cv_skel (cl_term V (cls_of_int ip)))
          (int_typ v ip (cv_skel (cl_term V (cls_of_int ip))))) ip)) with
 (class_env (V :: e0)).
apply class_typ_ord with s2; auto with coc core arith datatypes.
discriminate.

discriminate.

simpl in |- *.
unfold cls_of_int at 1, ext_ik in |- *.
rewrite same_classes.
pattern (cl_term V (class_env e0)) in |- *.
apply class_typ_ord with s1; elim same_classes; simpl in |- *;
 auto with coc core arith datatypes.
rewrite same_classes.
elim skel_sound with e0 V (Srt s1); simpl in |- *;
 auto with coc core arith datatypes.
elim same_classes; auto with coc core arith datatypes.

unfold int_cons, skel_int in |- *.
replace
 (cls_of_int
    (TCs Int_K
       (ext_ik V ip _ (int_typ v ip (cv_skel (cl_term V (cls_of_int ip)))))
       ip)) with (class_env (V :: e0)).
elim skel_sound with (V :: e0) Ur (Srt s2); simpl in |- *;
 auto with coc core arith datatypes.

simpl in |- *.
unfold ext_ik in |- *.
rewrite same_classes.
unfold cls_of_int in |- *.
elim class_sound with e0 v V (Srt s1); auto with coc core arith datatypes.
simpl in |- *.
elim same_classes; auto with coc core arith datatypes.

simpl in |- *.
elim same_classes; auto with coc core arith datatypes.

unfold Pi in H3.
apply H3; auto with coc core arith datatypes.
apply int_typ_cr; auto with coc core arith datatypes.

discriminate H5.

apply sn_prod.
apply H1 with ip; auto with coc core arith datatypes.

apply sn_subst with (Ref 0).
unfold subst in |- *.
rewrite int_term_subst.
elim H4; intros in_interp ip_can_adapted same_classes.
apply H3 with (def_cons T0 ip).
unfold def_cons, int_cons in |- *.
apply Build_int_adapt.
apply int_cs; auto with coc core arith datatypes.
apply (var_in_cand 0 (int_typ T0 ip PROP));
 auto with coc core arith datatypes.
exact (int_typ_cr T0 ip ip_can_adapted PROP).

red in |- *.
apply Tfa_cs; auto with coc core arith datatypes.
unfold ext_ik in |- *.
elim (cl_term T0 (cls_of_int ip)); auto with coc core arith datatypes.

unfold ext_ik in |- *.
rewrite same_classes.
unfold cls_of_int in |- *.
simpl in |- *.
pattern (cl_term T0 (class_env e0)) in |- *.
apply class_typ_ord with s1; simpl in |- *; elim same_classes;
 auto with coc core arith datatypes.
rewrite same_classes.
elim skel_sound with e0 T0 (Srt s1); simpl in |- *;
 auto with coc core arith datatypes.
elim same_classes; auto with coc core arith datatypes.

cut (typ e0 U (Srt s)); auto with coc core arith datatypes.
intros.
apply eq_cand_incl with (int_typ U ip PROP);
 auto with coc core arith datatypes.
replace PROP with (skel_int U ip).
elim H5; intros in_interp ip_can_adapted same_classes.
apply conv_int_typ with e0 (Srt s); auto with coc core arith datatypes.
apply class_typ_ord with s; auto with coc core arith datatypes.
discriminate.

discriminate.

unfold skel_int in |- *.
elim H5; intros in_interp ip_can_adapted same_classes.
rewrite same_classes.
elim skel_sound with e0 U (Srt s); simpl in |- *;
 auto with coc core arith datatypes.

elim type_case with e0 t0 U; intros; auto with coc core arith datatypes.
inversion_clear H6.
elim conv_sort with x s; auto with coc core arith datatypes.
apply typ_conv_conv with e0 U V; auto with coc core arith datatypes.

elim inv_typ_conv_kind with e0 V (Srt s); auto with coc core arith datatypes.
elim H6; auto with coc core arith datatypes.
Qed.




  Fixpoint def_intp e : intP :=
    match e with
    | nil => TNl _
    | t :: f => def_cons t (def_intp f)
    end.



  Fixpoint def_intt e : nat -> intt :=
    fun k =>
    match e with
    | nil => fun p => Ref (k + p)
    | _ :: f => shift_intt (def_intt f (S k)) (Ref k)
    end.


  Lemma def_intp_can : forall e, can_adapt (def_intp e).
simple induction e; simpl in |- *; auto with coc core arith datatypes; intros.
unfold def_cons, int_cons, ext_ik in |- *.
elim (cl_term a (cls_of_int (def_intp l)));
 auto with coc core arith datatypes.
Qed.


  Lemma def_adapt :
   forall e, wf e -> forall k, int_adapt e (def_intp e) (def_intt e k).
simple induction e; simpl in |- *; intros.
apply Build_int_adapt; auto with coc core arith datatypes.

inversion_clear H0.
cut (wf l); intros.
elim H with (S k); trivial; intros in_interp ip_can_adapted same_classes.
unfold def_cons, int_cons in |- *.
apply Build_int_adapt; auto with coc core arith datatypes.
apply int_cs; auto with coc core arith datatypes.
apply (var_in_cand k (int_typ a (def_intp l) PROP));
 auto with coc core arith datatypes.
change (is_can PROP (int_typ a (def_intp l) PROP)) in |- *.
apply int_typ_cr; auto with coc core arith datatypes.

unfold ext_ik in |- *.
rewrite same_classes.
pattern (cl_term a (class_env l)) in |- *.
apply class_typ_ord with s; auto with coc core arith datatypes.

simpl in |- *.
unfold ext_ik in |- *.
rewrite same_classes.
pattern (cl_term a (class_env l)) in |- *.
apply class_typ_ord with s; unfold cls_of_int in |- *; elim same_classes;
 auto with coc core arith datatypes.
simpl in |- *.
rewrite same_classes.
elim skel_sound with l a (Srt s); auto with coc core arith datatypes.
simpl in |- *; auto with coc core arith datatypes.
elim same_classes; auto with coc core arith datatypes.

apply typ_wf with a (Srt s); auto with coc core arith datatypes.
Qed.

  Hint Resolve def_intp_can def_adapt: coc.


  Lemma def_intt_id : forall n e k, def_intt e k n = Ref (k + n).
simple induction n; simple destruct e; simpl in |- *;
 auto with coc core arith datatypes; intros.
replace (k + 0) with k; auto with coc core arith datatypes.

rewrite H.
replace (k + S n0) with (S (k + n0)); auto with coc core arith datatypes.
Qed.


  Lemma id_int_term : forall e t k, int_term t (def_intt e 0) k = t.
simple induction t; simpl in |- *; intros; auto with coc core arith datatypes.
elim (le_gt_dec k n); intros; auto with coc core arith datatypes.
rewrite def_intt_id.
simpl in |- *; unfold lift in |- *.
rewrite lift_ref_ge; auto with coc core arith datatypes.


rewrite H; rewrite H0; auto with coc core arith datatypes.

rewrite H; rewrite H0; auto with coc core arith datatypes.

rewrite H; rewrite H0; auto with coc core arith datatypes.
Qed.




  Theorem str_norm : forall e t T, typ e t T -> sn t.
intros.
cut (is_can PROP (int_typ T (def_intp e) PROP));
 auto with coc core arith datatypes.
simpl in |- *; intros.
cut (int_typ T (def_intp e) PROP t).
elim H0; auto with coc core arith datatypes.

elim id_int_term with e t 0.
apply int_sound with e; auto with coc core arith datatypes.
apply def_adapt.
apply typ_wf with t T; auto with coc core arith datatypes.

apply int_typ_cr; auto with coc core arith datatypes.
Qed.



  Lemma type_sn : forall e t T, typ e t T -> sn T.
intros.
elim type_case with e t T; intros; auto with coc core arith datatypes.
elim H0; intros.
apply str_norm with e (Srt x); auto with coc core arith datatypes.

rewrite H0.
red in |- *; apply Acc_intro; intros.
inversion_clear H1.
Qed.
