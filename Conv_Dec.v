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



Require Import Peano_dec.
Require Import Transitive_Closure.
Require Import Union.
Require Import Termes.
Require Import Conv.

  Definition ord_norm1 := union _ subterm (transp _ red1).
  Definition ord_norm := clos_trans _ ord_norm1.

  Hint Unfold ord_norm1 ord_norm: coc.


  Lemma subterm_ord_norm : forall a b : term, subterm a b -> ord_norm a b.
auto 10 with coc v62.
Qed.

  Hint Resolve subterm_ord_norm: coc.


  Lemma red_red1_ord_norm :
   forall a b : term, red a b -> forall c : term, red1 b c -> ord_norm c a.
red in |- *.
simple induction 1; intros; auto with coc v62.
apply t_trans with N; auto with coc v62.
Qed.



  Lemma wf_subterm : well_founded subterm.
red in |- *.
simple induction a; intros; apply Acc_intro; intros.
inversion_clear H; inversion_clear H0.

inversion_clear H; inversion_clear H0.

inversion_clear H1; inversion_clear H2; auto with coc v62.

inversion_clear H1; inversion_clear H2; auto with coc v62.

inversion_clear H1; inversion_clear H2; auto with coc v62.
Qed.


  Lemma wf_ord_norm1 : forall t : term, sn t -> Acc ord_norm1 t.
unfold ord_norm1 in |- *.
intros.
apply Acc_union; auto with coc v62.
exact commut_red1_subterm.

intros.
apply wf_subterm.
Qed.


  Theorem wf_ord_norm : forall t : term, sn t -> Acc ord_norm t.
unfold ord_norm in |- *.
intros.
apply Acc_clos_trans.
apply wf_ord_norm1; auto with coc v62.
Qed.




  Definition norm_body (a : term) (norm : term -> term) :=
    match a with
    | Srt s => Srt s
    | Ref n => Ref n
    | Abs T t => Abs (norm T) (norm t)
    | App u v =>
        match norm u return term with
        | Abs _ b => norm (subst (norm v) b)
        | t => App t (norm v)
        end
    | Prod T U => Prod (norm T) (norm U)
    end.

  Theorem compute_nf :
   forall t : term, sn t -> {u : term | red t u &  normal u}.
intros.
elimtype (Acc ord_norm t).
clear H t.
intros [s| n| T t| u v| T U] _ norm_rec.
exists (Srt s); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.

exists (Ref n); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.

elim norm_rec with T; auto with coc; intros T' redT nT.
elim norm_rec with t; auto with coc; intros t' redt nt.
exists (Abs T' t'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nT with M'; trivial.
elim nt with M'; trivial.

elim norm_rec with v; auto with coc; intros v' redv nv.
elim norm_rec with u; auto with coc.
intros [s| n| T t| a b| T U] redu nu. 
exists (App (Srt s) v'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
inversion_clear H0.
elim nv with N2; trivial.

exists (App (Ref n) v'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
inversion_clear H0.
elim nv with N2; trivial.

elim norm_rec with (subst v' t).
intros t' redt nt.
exists t'; trivial.
apply trans_red_red with (subst v' t); auto with coc.
apply trans_red with (App (Abs T t) v'); auto with coc.

apply red_red1_ord_norm with (App (Abs T t) v'); auto with coc.

exists (App (App a b) v'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nu with N1; trivial.
elim nv with N2; trivial.

exists (App (Prod T U) v'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nu with N1; trivial.
elim nv with N2; trivial.

elim norm_rec with T; auto with coc; intros T' redT nT.
elim norm_rec with U; auto with coc; intros U' redU nU.
exists (Prod T' U'); auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H.
elim nT with N1; trivial.
elim nU with N2; trivial.

apply wf_ord_norm; auto with coc.
Qed.

  Lemma eqterm : forall u v : term, {u = v} + {u <> v}.
Proof.
decide equality.
decide equality.
apply eq_nat_dec.
Qed.



  Theorem is_conv :
   forall u v : term, sn u -> sn v -> {conv u v} + {~ conv u v}.
Proof.
intros u v snu snv.
elim compute_nf with (1 := snu); intros u' redu nu.
elim compute_nf with (1 := snv); intros v' redv nv.
elim eqterm with u' v'; [ intros same_nf | intros diff_nf ].
left.
apply trans_conv_conv with u'; auto with coc.
rewrite same_nf; apply sym_conv; auto with coc.

right; red in |- *; intro; apply diff_nf.
elim church_rosser with u' v'; auto with coc; intros.
rewrite (red_normal u' x); auto with coc.
rewrite (red_normal v' x); auto with coc.

apply trans_conv_conv with v; auto with coc.
apply trans_conv_conv with u; auto with coc.
apply sym_conv; auto with coc.
Qed.