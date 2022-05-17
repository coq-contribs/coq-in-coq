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

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

Section Church_Rosser.

  Definition str_confluent (R : term -> term -> Prop) :=
    commut _ R (transp _ R).

  Lemma str_confluence_par_red1 : str_confluent par_red1.
red in |- *; red in |- *.
simple induction 1; intros.
inversion_clear H4.
elim H1 with M'0; auto with coc core arith sets; intros.
elim H3 with N'0; auto with coc core arith sets; intros.
exists (subst x1 x0); unfold subst in |- *; auto with coc core arith sets.

inversion_clear H5.
elim H1 with M'1; auto with coc core arith sets; intros.
elim H3 with N'0; auto with coc core arith sets; intros.
exists (subst x1 x0); auto with coc core arith sets; unfold subst in |- *;
 auto with coc core arith sets.

inversion_clear H0.
exists (Srt s); auto with coc core arith sets.

inversion_clear H0.
exists (Ref n); auto with coc core arith sets.

inversion_clear H4.
elim H1 with M'0; auto with coc core arith sets; intros.
elim H3 with T'0; auto with coc core arith sets; intros.
exists (Abs x1 x0); auto with coc core arith sets.

generalize H0 H1.
clear H0 H1.
inversion_clear H4.
intro.
inversion_clear H4.
intros.
elim H4 with (Abs T M'0); auto with coc core arith sets; intros.
elim H3 with N'0; auto with coc core arith sets; intros.
apply inv_par_red_abs with T' M'1 x0; intros; auto with coc core arith sets.
generalize H7 H8.
rewrite H11.
clear H7 H8; intros.
inversion_clear H7.
inversion_clear H8.
exists (subst x1 U'); auto with coc core arith sets.
unfold subst in |- *; auto with coc core arith sets.

intros.
elim H5 with M'0; auto with coc core arith sets; intros.
elim H3 with N'0; auto with coc core arith sets; intros.
exists (App x0 x1); auto with coc core arith sets.

intros.
inversion_clear H4.
elim H1 with M'0; auto with coc core arith sets; intros.
elim H3 with N'0; auto with coc core arith sets; intros.
exists (Prod x0 x1); auto with coc core arith sets.
Qed.


  Lemma strip_lemma : commut _ par_red (transp _ par_red1).
unfold commut, par_red in |- *; simple induction 1; intros.
elim str_confluence_par_red1 with z x0 y0; auto with coc core arith sets;
 intros.
exists x1; auto with coc core arith sets.

elim H1 with z0; auto with coc core arith sets; intros.
elim H3 with x1; intros; auto with coc core arith sets.
exists x2; auto with coc core arith sets.
apply t_trans with x1; auto with coc core arith sets.
Qed.


  Lemma confluence_par_red : str_confluent par_red.
red in |- *; red in |- *.
simple induction 1; intros.
elim strip_lemma with z x0 y0; intros; auto with coc core arith sets.
exists x1; auto with coc core arith sets.

elim H1 with z0; intros; auto with coc core arith sets.
elim H3 with x1; intros; auto with coc core arith sets.
exists x2; auto with coc core arith sets.
red in |- *.
apply t_trans with x1; auto with coc core arith sets.
Qed.


  Lemma confluence_red : str_confluent red.
red in |- *; red in |- *.
intros.
elim confluence_par_red with x y z; auto with coc core arith sets; intros.
exists x0; auto with coc core arith sets.
Qed.


  Theorem church_rosser :
   forall u v, conv u v -> ex2 (fun t => red u t) (fun t => red v t).
simple induction 1; intros.
exists u; auto with coc core arith sets.

elim H1; intros.
elim confluence_red with x P N; auto with coc core arith sets; intros.
exists x0; auto with coc core arith sets.
apply trans_red_red with x; auto with coc core arith sets.

elim H1; intros.
exists x; auto with coc core arith sets.
apply trans_red_red with P; auto with coc core arith sets.
Qed.



  Lemma inv_conv_prod_l :
   forall a b c d : term, conv (Prod a c) (Prod b d) -> conv a b.
intros.
elim church_rosser with (Prod a c) (Prod b d); intros;
 auto with coc core arith sets.
apply red_prod_prod with a c x; intros; auto with coc core arith sets.
apply red_prod_prod with b d x; intros; auto with coc core arith sets.
apply trans_conv_conv with a0; auto with coc core arith sets.
apply sym_conv.
generalize H2.
rewrite H5; intro.
injection H8.
simple induction 2; auto with coc core arith sets.
Qed.

  Lemma inv_conv_prod_r :
   forall a b c d : term, conv (Prod a c) (Prod b d) -> conv c d.
intros.
elim church_rosser with (Prod a c) (Prod b d); intros;
 auto with coc core arith sets.
apply red_prod_prod with a c x; intros; auto with coc core arith sets.
apply red_prod_prod with b d x; intros; auto with coc core arith sets.
apply trans_conv_conv with b0; auto with coc core arith sets.
apply sym_conv.
generalize H2.
rewrite H5; intro.
injection H8.
simple induction 1; auto with coc core arith sets.
Qed.


  Lemma nf_uniqueness : forall u v, conv u v -> normal u -> normal v -> u = v. 
intros.
elim church_rosser with u v; intros; auto with coc core arith sets.
rewrite (red_normal u x); auto with coc core arith sets.
elim red_normal with v x; auto with coc core arith sets.
Qed.


  Lemma conv_sort : forall s1 s2, conv (Srt s1) (Srt s2) -> s1 = s2.
intros.
cut (Srt s1 = Srt s2); intros.
injection H0; auto with coc core arith sets.

apply nf_uniqueness; auto with coc core arith sets.
red in |- *; red in |- *; intros.
inversion_clear H0.

red in |- *; red in |- *; intros.
inversion_clear H0.
Qed.


  Lemma conv_kind_prop : ~ conv (Srt kind) (Srt prop).
red in |- *; intro.
absurd (kind = prop).
discriminate.

apply conv_sort; auto with coc core arith sets.
Qed.


  Lemma conv_sort_prod : forall s t u, ~ conv (Srt s) (Prod t u).
red in |- *; intros.
elim church_rosser with (Srt s) (Prod t u); auto with coc core arith sets.
do 2 intro.
elim red_normal with (Srt s) x; auto with coc core arith sets.
intro.
apply red_prod_prod with t u (Srt s); auto with coc core arith sets; intros.
discriminate H2.

red in |- *; red in |- *; intros.
inversion_clear H1.
Qed.


End Church_Rosser.