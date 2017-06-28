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
Require Import Conv_Dec.
Require Import Infer.
Require Import Names.
Require Import Expr.
Require Import Machine.
Require Extraction.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive sumor => "option" [ "Some" "None" ].

(* integers *)

Extract Inlined Constant ml_int => "int".
Extract Constant ml_eq_int => "(=)".
Extract Constant ml_zero => "0".
Extract Constant ml_int_case => "function 0 -> None | n -> Some (pred n)".
Extract Inlined Constant ml_succ => "succ".

(* strings *)

Extract Inlined Constant ml_string => "string".
Extract Constant ml_eq_string => "(=)".
Extract Constant ml_x_int => "fun n -> ""x"" ^ (string_of_int n)".

Extraction
 NoInline list_index is_free_var check_typ red_to_sort red_to_prod exec_axiom
         glob_ctx glob_names empty_state name_dec find_free_var synthesis
         interp_command transl_message transl_error interp_ast.

Extraction "core.ml" is_free_var empty_state interp_ast.
