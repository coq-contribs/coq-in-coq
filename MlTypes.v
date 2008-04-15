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



(* Formalisation of several Objective Caml basic types *)

(* integers *)

  Parameter ml_int : Set.
  Parameter ml_eq_int : forall m n : ml_int, {m = n} + {m <> n}.
  Parameter ml_zero : ml_int.
  Parameter ml_succ : ml_int -> ml_int.

  Parameter ml_int_pred : forall m n : ml_int, ml_succ m = ml_succ n -> m = n.
(* This axiom is wrong in practice: (ml_succ -1)=ml_zero *)
  Axiom dangerous_discr : forall n : ml_int, ml_zero <> ml_succ n.

  Parameter
    ml_int_case :
      forall n : ml_int, {m : ml_int | n = ml_succ m} + {n = ml_zero}.

  Fixpoint int_of_nat (n : nat) : ml_int :=
    match n with
    | O => ml_zero
    | S k => ml_succ (int_of_nat k)
    end.

  Lemma dangerous_int_injection :
   forall i j : nat, int_of_nat i = int_of_nat j -> i = j.
simple induction i; simple destruct j; simpl in |- *; intros; auto with v62.
elim dangerous_discr with (int_of_nat n); auto with v62.

elim dangerous_discr with (int_of_nat n); auto with v62.

elim H with n0; auto with v62.
apply ml_int_pred; auto with v62.
Qed.


(* strings *)
  Parameter ml_string : Set.
  Parameter ml_eq_string : forall s1 s2 : ml_string, {s1 = s2} + {s1 <> s2}.

(* will be realized by (fun n -> "x"^int_of_string n) *)
  Parameter ml_x_int : ml_int -> ml_string.
  Parameter
    ml_x_int_inj : forall m n : ml_int, ml_x_int m = ml_x_int n -> m = n.

