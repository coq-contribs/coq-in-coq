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
Require Import Strong_Norm.
Require Import Conv_Dec.

Load "ImpVar".

  Lemma red_to_sort :
   forall t,
   sn t -> {s : sort | red t (Srt s)} + {(forall s, ~ conv t (Srt s))}.
intros t snt.
elim compute_nf with (1 := snt); intros [s| n| T b| u v| T U] redt nt.
left.
exists s; trivial.

right; red in |- *; intros.
elim church_rosser with (Srt s) (Ref n); intros.
generalize H0.
elim (red_normal (Ref n) x); auto with coc; intros.
apply red_sort_sort with s (Ref n); auto with coc.
discriminate.

apply trans_conv_conv with t; auto with coc.

right; red in |- *; intros.
elim church_rosser with (Srt s) (Abs T b); intros.
generalize H0.
elim (red_normal (Abs T b) x); auto with coc; intros.
apply red_sort_sort with s (Abs T b); auto with coc.
discriminate.

apply trans_conv_conv with t; auto with coc.

right; red in |- *; intros.
elim church_rosser with (Srt s) (App u v); intros.
generalize H0.
elim (red_normal (App u v) x); auto with coc; intros.
apply red_sort_sort with s (App u v); auto with coc.
discriminate.

apply trans_conv_conv with t; auto with coc.

right; red in |- *; intros.
elim church_rosser with (Srt s) (Prod T U); intros.
generalize H0.
elim (red_normal (Prod T U) x); auto with coc; intros.
apply red_sort_sort with s (Prod T U); auto with coc.
discriminate.

apply trans_conv_conv with t; auto with coc.
Qed.


  Lemma red_to_prod :
   forall t,
   sn t ->
   {p : term * term | match p with
                      | (u, v) => red t (Prod u v)
                      end} + {(forall u v, ~ conv t (Prod u v))}.
intros t snt.
elim compute_nf with (1 := snt); intros [s| n| T b| u v| T U] redt nt.
right; red in |- *; intros.
elim church_rosser with (Prod u v) (Srt s); intros.
generalize H0.
elim (red_normal (Srt s) x); auto with coc; intros.
apply red_prod_prod with u v (Srt s); auto with coc; intros.
discriminate H3.

apply trans_conv_conv with t; auto with coc.

right; red in |- *; intros.
elim church_rosser with (Prod u v) (Ref n); intros.
generalize H0.
elim (red_normal (Ref n) x); auto with coc; intros.
apply red_prod_prod with u v (Ref n); auto with coc; intros.
discriminate H3.

apply trans_conv_conv with t; auto with coc.

right; red in |- *; intros.
elim church_rosser with (Prod u v) (Abs T b); intros.
generalize H0.
elim (red_normal (Abs T b) x); auto with coc; intros.
apply red_prod_prod with u v (Abs T b); auto with coc; intros.
discriminate H3.

apply trans_conv_conv with t; auto with coc.

right; red in |- *; intros.
elim church_rosser with (Prod u0 v0) (App u v); intros.
generalize H0.
elim (red_normal (App u v) x); auto with coc; intros.
apply red_prod_prod with u0 v0 (App u v); auto with coc; intros.
discriminate H3.

apply trans_conv_conv with t; auto with coc.

left; exists (T, U); trivial.
Qed.

Section TypeChecker.


  Inductive type_error : Set :=
    | Under : term -> type_error -> type_error
    | Expected_type : term -> term -> term -> type_error
    | Kind_ill_typed : type_error
    | Db_error : nat -> type_error
    | Lambda_kind : term -> type_error
    | Not_a_type : term -> term -> type_error
    | Not_a_fun : term -> term -> type_error
    | Apply_err : term -> term -> term -> term -> type_error.


(* meaning of errors *)
  Inductive expln : env -> type_error -> Prop :=
    | Exp_under :
        forall e t (err : type_error),
        expln (t :: e) err -> expln e (Under t err)
    | Exp_exp_type :
        forall e (m at_ et : term),
        typ e m at_ ->
        ~ typ e m et ->
        free_db (length e) et -> expln e (Expected_type m at_ et)
    | Exp_kind :
        forall e,
        wf e -> (forall t, ~ typ e (Srt kind) t) -> expln e Kind_ill_typed
    | Exp_db : forall e n, wf e -> length e <= n -> expln e (Db_error n)
    | Exp_lam_kind :
        forall e (m : term) t,
        typ (t :: e) m (Srt kind) -> expln e (Lambda_kind (Abs t m))
    | Exp_type :
        forall e (m : term) t,
        typ e m t ->
        (forall s, ~ typ e m (Srt s)) -> expln e (Not_a_type m t)
    | Exp_fun :
        forall e (m : term) t,
        typ e m t ->
        (forall a b : term, ~ typ e m (Prod a b)) -> expln e (Not_a_fun m t)
    | Exp_appl_err :
        forall e u v (a b tv : term),
        typ e u (Prod a b) ->
        typ e v tv -> ~ typ e v a -> expln e (Apply_err u (Prod a b) v tv).

  Hint Resolve Exp_under Exp_exp_type Exp_kind Exp_db Exp_lam_kind Exp_type
    Exp_fun Exp_appl_err: coc.

  Lemma expln_wf : forall e (err : type_error), expln e err -> wf e.
simple induction 1; intros; auto with coc v62.
inversion_clear H1.
apply typ_wf with t (Srt s); auto with coc v62.

apply typ_wf with m at_; auto with coc v62.

cut (wf (t :: e0)); intros.
inversion_clear H1.
apply typ_wf with t (Srt s); auto with coc v62.

apply typ_wf with m (Srt kind); auto with coc v62.

apply typ_wf with m t; auto with coc v62.

apply typ_wf with m t; auto with coc v62.

apply typ_wf with v tv; auto with coc v62.
Qed.

  Inductive inf_error : term -> type_error -> Prop :=
    | Infe_subt :
        forall (m n : term) (err : type_error),
        subt_nobind m n -> inf_error m err -> inf_error n err
    | Infe_under :
        forall (m n : term) T (err : type_error),
        subt_bind T m n -> inf_error m err -> inf_error n (Under T err)
    | Infe_kind : inf_error (Srt kind) Kind_ill_typed
    | Infe_db : forall n, inf_error (Ref n) (Db_error n)
    | Infe_lam_kind : forall M T, inf_error (Abs T M) (Lambda_kind (Abs T M))
    | Infe_type_abs :
        forall (m n : term) t, inf_error (Abs m n) (Not_a_type m t)
    | Infe_fun : forall (m n : term) t, inf_error (App m n) (Not_a_fun m t)
    | Infe_appl_err :
        forall m n tf ta : term, inf_error (App m n) (Apply_err m tf n ta)
    | Infe_type_prod_l :
        forall (m n : term) t, inf_error (Prod m n) (Not_a_type m t)
    | Infe_type_prod_r :
        forall (m n : term) t,
        inf_error (Prod m n) (Under m (Not_a_type n t)).

  Hint Resolve Infe_kind Infe_db Infe_lam_kind Infe_type_abs Infe_fun
    Infe_appl_err Infe_type_prod_l Infe_type_prod_r: coc.


  Lemma inf_error_no_type :
   forall (m : term) (err : type_error),
   inf_error m err -> forall e, expln e err -> forall t, ~ typ e m t.
simple induction 1; intros.
inversion_clear H0; red in |- *; intros.
apply inv_typ_abs with e m0 n0 t; intros; auto with coc v62.
elim H2 with e (Srt s1); auto with coc v62.

apply inv_typ_app with e m0 v t; intros; auto with coc v62.
elim H2 with e (Prod V Ur); auto with coc v62.

apply inv_typ_app with e u m0 t; intros; auto with coc v62.
elim H2 with e V; auto with coc v62.

apply inv_typ_prod with e m0 n0 t; intros; auto with coc v62.
elim H2 with e (Srt s1); auto with coc v62.

inversion_clear H3.
inversion_clear H0; red in |- *; intros.
apply inv_typ_abs with e T m0 t; intros; auto with coc v62.
elim H2 with (T :: e) T0; auto with coc v62.

apply inv_typ_prod with e T m0 t; intros; auto with coc v62.
elim H2 with (T :: e) (Srt s2); auto with coc v62.

inversion_clear H0; auto with coc v62.

red in |- *; intros.
apply inv_typ_ref with e t n; intros; auto with coc v62.
inversion_clear H0.
generalize H5.
elim H2; simpl in |- *; intros; auto with coc v62.
inversion_clear H0.

inversion_clear H0.
red in |- *; intros.
apply inv_typ_abs with e T M t; intros; auto with coc v62.
elim inv_typ_conv_kind with (T :: e) T0 (Srt s2); auto with coc v62.
apply typ_unique with (T :: e) M; auto with coc v62.

inversion_clear H0.
red in |- *; intros.
apply inv_typ_abs with e m0 n t0; intros; auto with coc v62.
elim H2 with s1; auto with coc v62.

inversion_clear H0.
red in |- *; intros.
apply inv_typ_app with e m0 n t0; intros; auto with coc v62.
elim H2 with V Ur; auto with coc v62.

inversion_clear H0.
red in |- *; intros.
apply inv_typ_app with e m0 n t; intros; auto with coc v62.
elim type_case with e m0 (Prod a b); intros; auto with coc v62.
inversion_clear H7.
apply inv_typ_prod with e a b (Srt x); intros; auto with coc v62.
apply H3.
apply type_conv with V s1; auto with coc v62.
apply inv_conv_prod_l with Ur b.
apply typ_unique with e m0; auto with coc v62.

discriminate H7.

inversion_clear H0.
red in |- *; intros.
apply inv_typ_prod with e m0 n t0; intros; auto with coc v62.
elim H2 with s1; auto with coc v62.

inversion_clear H0.
inversion_clear H1.
red in |- *; intros.
apply inv_typ_prod with e m0 n t0; intros; auto with coc v62.
elim H2 with s2; auto with coc v62.
Qed.


  Theorem infer :
   forall e t,
   wf e ->
   {T : term | typ e t T} +
   {err : type_error | expln e err &  inf_error t err}.
(*Realizer [e:env][m:term]
  (Fix inf_rec {inf_rec/1: term->env->(sum term ty_err) :=
     [m:term][e:env]Cases m of
       (Srt kind) => (fail (Ill_typed (Srt kind)))
     | (Srt prop) => (ok (Srt kind))
     | (Ref n) => Cases (list_item term e n) of
                    (inleft T) => (ok (lift (S n) T))
                  | _          => (fail (Ill_typed (Ref n)))
                  end
     | (Abs t b) => Cases (inf_rec t e) of
              (inl T) => Cases (red_to_sort T)
                                  (inf_rec b (cons t e)) of
                  (inleft _) (inl B) => if (eqterm (Srt kind) B)
                                           then (fail (Topsorted b))
                                           else (ok (Prod t B))
                | inright     _          => (fail (Not_a_type t))
                | (inleft _)  (inr err) => (bind t err)
                end
            | (inr err) =>(inr term ? err)
            end
     | (App t b) => Cases (inf_rec t e) of
              (inl T) => Cases (red_to_prod T) of
                    (inleft (V,Ur)) => Cases (inf_rec b e) of
                              (inl B) => if (is_conv V B)
                                            then (ok (subst b Ur))
                                            else (fail (Expected_type b B V))
                            | (inr err) => (inr term ? err)
                            end
                  | _ => (fail (Not_a_fun t T))
                  end
            | (inr err) => (inr term ? err)
            end
     | (Prod t b) => Cases (inf_rec t e) of
              (inl T) => Cases (red_to_sort T)
                                  (inf_rec b (cons t e)) of
                  (inleft _) (inl B) => Cases (red_to_sort B) of
                        (inleft s) => (ok (Srt s))
                      | _          =>(fail (Not_a_type b))
                      end
                | inright    _  => (fail (Not_a_type t))
                | (inleft _) (inr err) => (bind t err)
                end
            | (inr err) => (inr term ? err)
            end
     end} m e).
*)
do 2 intro.
generalize t e.
clear e t.
fix 1.
intros t e wfe.
case t.
simple destruct s.
right.
exists Kind_ill_typed; auto with coc v62.
apply Exp_kind; intros; auto with coc v62.
apply inv_typ_kind.

left.
exists (Srt kind).
apply type_prop; auto with coc v62.

left.
exists (Srt kind).
apply type_set; auto with coc v62.

intros.
generalize (list_item term e n); intros [(T, H0)| b].
left.
exists (lift (S n) T).
apply type_var; auto with coc v62.
exists T; auto with coc v62.

right.
exists (Db_error n); auto with coc v62.
apply Exp_db; auto with coc v62.
generalize n b.
elim e; simpl in |- *; auto with coc v62.
simple destruct n0; intros.
elim b0 with a; auto with coc v62.

cut (length l <= n1); auto with coc v62.
apply H.
red in |- *; intros.
elim b0 with t0; auto with coc v62.

intros a b.
elim (infer a e); trivial with coc v62.
intros (T, ty_a).
elim (red_to_sort T); trivial with coc v62.
intros (s, srt_T).
cut (wf (a :: e)); intros.
elim (infer b (a :: e)); trivial with coc v62.
intros (B, ty_b).
elim (eqterm (Srt kind) B).
intro eq_kind.
right.
exists (Lambda_kind (Abs a b)); auto with coc v62.
apply Exp_lam_kind; auto with coc v62.
rewrite eq_kind; auto with coc v62.

intro not_kind.
left.
exists (Prod a B).
elim type_case with (1 := ty_b).
intros (s2, knd_b).
apply type_abs with s s2; auto with coc v62.
apply type_reduction with T; auto with coc v62.

intros; elim not_kind; auto.

intros (err, expl_err, inf_err).
right.
exists (Under a err); auto with coc v62.
apply Infe_under with b; auto with coc v62.

apply wf_var with s.
apply type_reduction with T; auto with coc v62.

intro not_type.
right.
exists (Not_a_type a T); auto with coc v62.
apply Exp_type; auto with coc v62.
red in |- *; intros.
elim not_type with s.
apply typ_unique with e a; auto with coc v62.

apply type_sn with e a; auto with coc v62.

intros (err, expl_err, inf_err).
right.
exists err; auto with coc v62.
apply Infe_subt with a; auto with coc v62.

intros u v.
elim infer with u e; trivial with coc v62.
intros (T, ty_u).
elim red_to_prod with T.
intros ((V, Ur), red_prod).
cut (typ e u (Prod V Ur)); intros.
elim infer with v e; trivial with coc v62.
intros (B, ty_v).
elim is_conv with V B.
intros domain_conv.
left.
exists (subst v Ur).
apply type_app with V; auto with coc v62.
elim type_case with e u (Prod V Ur); auto with coc v62.
intros (s, ty_prod).
apply inv_typ_prod with (1 := ty_prod); auto with coc v62; intros.
apply type_conv with B s1; auto with coc v62.

intro not_prod; discriminate not_prod.

intro dom_not_conv.
right.
exists (Apply_err u (Prod V Ur) v B); auto with coc v62.
apply Exp_appl_err; auto with coc v62.
red in |- *; intros.
apply dom_not_conv.
apply typ_unique with e v; auto with coc v62.

apply subterm_sn with (Prod V Ur); auto with coc v62.
apply sn_red_sn with T; auto with coc v62.
apply type_sn with e u; auto with coc v62.

apply type_sn with e v; auto with coc v62.

intros (err, expl_err, inf_err).
right.
exists err; auto with coc v62.
apply Infe_subt with v; auto with coc v62.

apply type_reduction with T; auto with coc v62.

intros not_prod.
right.
exists (Not_a_fun u T); auto with coc v62.
apply Exp_fun; auto with coc v62.
red in |- *; intros.
elim not_prod with a b.
apply typ_unique with e u; auto with coc v62.

apply type_sn with e u; auto with coc v62.

intros (err, expl_err, inf_err).
right.
exists err; auto with coc v62.
apply Infe_subt with u; auto with coc v62.

intros a b.
elim infer with a e; trivial with coc v62.
intros (T, ty_a).
elim red_to_sort with T.
intros (s, red_sort).
cut (wf (a :: e)); intros.
elim infer with b (a :: e); trivial with coc v62.
intros (B, ty_b).
elim red_to_sort with B.
intros (s2, red_s2).
left.
exists (Srt s2).
apply type_prod with s; auto with coc v62.
apply type_reduction with T; auto with coc v62.

apply type_reduction with B; auto with coc v62.

intros b_not_type.
right.
exists (Under a (Not_a_type b B)); auto with coc v62.
apply Exp_under; auto with coc v62.
apply Exp_type; auto with coc v62.
red in |- *; intros.
elim b_not_type with s0.
apply typ_unique with (a :: e) b; auto with coc v62.

apply type_sn with (a :: e) b; auto with coc v62.

intros (err, expl_err, inf_err).
right.
exists (Under a err); auto with coc v62.
apply Infe_under with b; auto with coc v62.

apply wf_var with s.
apply type_reduction with T; auto with coc v62.

intros a_not_type.
right.
exists (Not_a_type a T); auto with coc v62.
apply Exp_type; auto with coc v62.
red in |- *; intros.
elim a_not_type with s.
apply typ_unique with e a; auto with coc v62.

apply type_sn with e a; auto with coc v62.

intros (err, expl_err, inf_err).
right.
exists err; auto with coc v62.
apply Infe_subt with a; auto with coc v62.
Qed.



  Inductive chk_error (m : term) t : type_error -> Prop :=
    | Chke_subj :
        forall err : type_error, inf_error m err -> chk_error m t err
    | Chke_type :
        forall err : type_error,
        inf_error t err -> t <> Srt kind -> chk_error m t err
    | Chke_exp : forall at_ : term, chk_error m t (Expected_type m at_ t).

  Hint Resolve Chke_subj Chke_type Chke_exp: coc.


  Lemma chk_error_no_type :
   forall e (m : term) t (err : type_error),
   chk_error m t err -> expln e err -> ~ typ e m t.
simple destruct 1; intros.
apply inf_error_no_type with err0; auto with coc v62.

red in |- *; intros.
elim type_case with e m t; intros; auto with coc v62.
inversion_clear H4.
elim inf_error_no_type with t err0 e (Srt x); auto with coc v62.

inversion_clear H0; auto with coc v62.
Qed.


  Lemma check_typ :
   forall e t (tp : term),
   wf e ->
   {err : type_error | expln e err &  chk_error t tp err} + {typ e t tp}.
(*
Realizer [e:env][t,tp:term]
  Cases (infer e t) (eqterm (Srt kind) tp) of
    (inl tp') inleft => if (eqterm (Srt kind) tp')
                        then (inright type_error)
                        else (inleft ? (fail t (nil ?)
                                     (Expected_type t tp' (Srt kind))))
  | (inl tp') inright => Cases (infer e tp) of
                           (inl k) => if (is_conv tp tp')
                                      then (inright type_error)
                                      else (inleft ? (fail t (nil ?)
                                              (Expected_type t tp' tp)))
                         | (inr err) => (inleft type_error err)
                         end
  | (inr err) _ => (inleft type_error err)
  end.
*)
intros.
elim infer with e t; auto with coc v62.
intros (tp', typ_t).
elim eqterm with (Srt kind) tp.
intros cast_kind.
elim eqterm with (Srt kind) tp'.
intros inf_kind.
right.
elim cast_kind; rewrite inf_kind; trivial.

intros inf_not_kind.
left.
exists (Expected_type t tp' tp); auto with coc.
apply Exp_exp_type; auto with coc v62.
red in |- *; intros; apply inf_not_kind.
symmetry  in |- *.
apply type_kind_not_conv with e t; auto with coc v62.
rewrite cast_kind; trivial.

elim cast_kind; auto with coc.

intros cast_not_kind.
elim infer with e tp; auto with coc.
intros (k, ty_tp).
elim is_conv with tp tp'.
intros cast_ok.
right.
elim red_to_sort with k; auto with coc.
intros (s, red_sort).
apply type_conv with tp' s; auto with coc.
apply type_reduction with k; auto with coc.

intros not_sort.
elim type_case with (1 := typ_t).
intros (s, kind_inf).
elim not_sort with s.
apply typ_conv_conv with e tp tp'; auto with coc v62.

intros is_kind.
elim inv_typ_conv_kind with e tp k; auto with coc v62.
elim is_kind; auto with coc v62.

apply type_sn with e tp; auto with coc v62.

intros cast_err.
left.
exists (Expected_type t tp' tp); auto with coc v62.
apply Exp_exp_type; auto with coc v62.
red in |- *; intros; apply cast_err; apply typ_unique with e t;
 auto with coc v62.

apply typ_free_db with k; auto with coc v62.

apply str_norm with e k; auto with coc v62.

apply type_sn with e t; auto with coc v62.

intros (err, expl_err, inf_err).
left.
exists err; auto with coc v62.

intros (err, expl_err, inf_err).
left.
exists err; auto with coc v62.
Qed.



  Inductive decl_error (m : term) : type_error -> Prop :=
    | Decax_ill :
        forall err : type_error, inf_error m err -> decl_error m err
    | Decax_type : forall t, decl_error m (Not_a_type m t).

  Hint Resolve Decax_ill Decax_type: coc.


  Lemma decl_err_not_wf :
   forall e t (err : type_error),
   decl_error t err -> expln e err -> ~ wf (t :: e).
red in |- *.
simple destruct 1; intros.
inversion_clear H2.
elim inf_error_no_type with t err0 e (Srt s); auto with coc v62.

inversion_clear H0.
inversion_clear H1.
elim H3 with s; auto with coc v62.
Qed.


  Lemma add_typ :
   forall e t,
   wf e ->
   {err : type_error | expln e err &  decl_error t err} + {wf (t :: e)}.
intros.
elim infer with e t; auto with coc.
intros (T, typ_t).
elim red_to_sort with T.
intros (s, red_sort).
right.
apply wf_var with s.
apply type_reduction with T; auto with coc.

intros not_sort.
left.
exists (Not_a_type t T); auto with coc.
apply Exp_type; auto with coc.
red in |- *; intros.
elim not_sort with s.
apply typ_unique with e t; auto with coc.

apply type_sn with e t; auto with coc.

intros (err, expl_err, inf_err).
left.
exists err; auto with coc v62.
Qed.


End TypeChecker.

Section Decidabilite_typage.

  Lemma decide_wf : forall e, {wf e} + {~ wf e}.
simple induction e; intros.
left.
apply wf_nil.

elim H.
intros wf_l.
elim add_typ with l a; trivial.
intros (err, expl_err, decl_err).
right.
apply decl_err_not_wf with (1 := decl_err) (2 := expl_err).

left; trivial.

intros not_wf_l.
right; red in |- *; intros.
apply not_wf_l.
inversion_clear H0.
apply typ_wf with (1 := H1).
Qed.


  Lemma decide_typ : forall e t (tp : term), {typ e t tp} + {~ typ e t tp}.
intros.
elim decide_wf with e.
intros wf_e.
elim check_typ with e t tp; trivial.
intros (err, expl_err, chk_err).
right.
apply chk_error_no_type with (1 := chk_err) (2 := expl_err).

left; trivial.

intros not_wf_e.
right; red in |- *; intros.
apply not_wf_e.
apply typ_wf with (1 := H).
Qed.

End Decidabilite_typage.
