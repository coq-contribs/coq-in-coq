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

  Definition intt := nat -> term.

  Definition shift_intt (i : intt) (t : term) : intt :=
    fun n : nat => match n with
                   | O => t
                   | S k => i k
                   end.


  Fixpoint int_term (t : term) : intt -> nat -> term :=
    fun (I : intt) (k : nat) =>
    match t with
    | Srt s => Srt s
    | Ref n =>
        match le_gt_dec k n with
        | left _ => lift k (I (n - k))
        | right _ => Ref n
        end
    | Abs A t => Abs (int_term A I k) (int_term t I (S k))
    | App u v => App (int_term u I k) (int_term v I k)
    | Prod A B => Prod (int_term A I k) (int_term B I (S k))
    end.

  Opaque le_gt_dec.

  Lemma int_term_subst :
   forall (t : term) (it : intt) (k : nat) (x : term),
   subst_rec x (int_term t it (S k)) k = int_term t (shift_intt it x) k.
simple induction t; simpl in |- *; intros; auto with coc core arith sets.
elim (le_gt_dec (S k) n); intros.
elim (le_gt_dec k n); intros.
rewrite simpl_subst; auto with coc core arith sets.
replace (n - k) with (S (n - S k)); auto with coc core arith sets.
rewrite minus_Sn_m; auto with coc core arith sets.

elim le_not_gt with k n; auto with coc core arith sets.

simpl in |- *.
elim (lt_eq_lt_dec k n); [ intro Hlt_eq | intro Hlt ].
elim Hlt_eq; clear Hlt_eq; [ intro Hlt | intro Heq ].
absurd (n <= k); auto with coc core arith sets.

elim (le_gt_dec k n); [ intro Hle | intro Hgt ];
 auto with coc core arith sets.
elim Heq.
replace (k - k) with 0; auto with coc core arith sets.

inversion_clear Heq in Hgt.
elim gt_irrefl with n; auto with coc core arith sets.

elim (le_gt_dec k n); intros; auto with coc core arith sets.
absurd (k <= n); auto with coc core arith sets.

rewrite H; rewrite H0; auto with coc core arith sets.

rewrite H; rewrite H0; auto with coc core arith sets.

rewrite H; rewrite H0; auto with coc core arith sets.
Qed.
