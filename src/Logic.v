(**
 * Author:    Yuting Wang
 * Created:   Sep 5, 2019
*)

Require Import Arith.
Require Import ZArith.
Require Import List.
Require Import Utils.
Import ListNotations.

Open Scope list_scope.
Open Scope nat_scope.
Open Scope option_monad_scope.

Set Implicit Arguments.

(** * The Language of Simply Typed Lambda Calculus with Equality Proofs *)

(** The language is an extension of STLC with equality and proof terms.
    It is represented by using the hybrid de-bruijn representation first
    introduced by Stampoulis and Shao *)

(** ** The Syntax *)

(** Constants *)
Definition const := positive.

(** Types *)
Inductive ty : Type :=
| prop
| bty 
| arr : ty -> ty -> ty.

(** Terms *)
Inductive term: Type :=
| cst  : const -> term
| fvar : nat -> term
| bvar : nat -> term
| abs  : ty -> term -> term
| app  : term -> term -> term
| teq   : term -> term -> term.

Notation "t1 == t2" := (teq t1 t2) (at level 60) : stlcd_scope.

Local Open Scope stlcd_scope.

(** Proof terms *)
Inductive pterm: Type :=
| refl: term -> pterm
| trans: pterm -> pterm -> pterm
| symm : pterm -> pterm
| congAbs: ty -> pterm -> pterm
| congAppL: pterm -> pterm
| congAppR: pterm -> pterm
| congEqL: pterm -> pterm
| congEqR: pterm -> pterm
| beta: ty -> term -> term -> pterm
| conv: pterm -> pterm -> pterm.

(** Typing contexts *)
Definition tyctx := list ty.

(** Simultaenous Substitutions *)
Definition sub := list term.


(** ** The Definitions of Freshing and Binding Operations *)

(** Freshening of terms *)
Fixpoint fresh_tm (t:term) (bn fn: nat) : term :=
  match t with
  | cst _ => t
  | fvar _ => t
  | bvar i => if beq_nat i bn then fvar fn else t
  | abs ty t => 
    abs ty (fresh_tm t (S bn) fn)
  | app t1 t2 =>
    app (fresh_tm t1 bn fn) (fresh_tm t2 bn fn)
  | t1 == t2 =>
    (fresh_tm t1 bn fn) == (fresh_tm t2 bn fn)
  end.

Definition fresh_tm_0 t fn := fresh_tm t 0 fn.

(** Freshening of proof terms *)
Fixpoint fresh_ptm (pt:pterm) (bn fn: nat) : pterm :=
  match pt with
  | refl t => refl (fresh_tm t bn fn)
  | trans pt1 pt2 => 
    trans (fresh_ptm pt1 bn fn) (fresh_ptm pt2 bn fn)
  | symm pt1 =>
    symm (fresh_ptm pt1 bn fn)
  | congAbs ty pt1 =>
    congAbs ty (fresh_ptm pt1 (S bn) fn)
  | congAppL pt1 =>
    congAppL (fresh_ptm pt1 bn fn)
  | congAppR pt1 =>
    congAppR (fresh_ptm pt1 bn fn)
  | congEqL pt1 =>
    congEqL (fresh_ptm pt1 bn fn)
  | congEqR pt1 =>
    congEqR (fresh_ptm pt1 bn fn)
  | beta ty t1 t2 =>
    beta ty (fresh_tm t1 (S bn) fn) (fresh_tm t2 bn fn)
  | conv pt1 pt2 =>
    conv (fresh_ptm pt1 bn fn) (fresh_ptm pt2 bn fn)
end.

Definition fresh_ptm_0 t fn := fresh_ptm t 0 fn.


(** Binding of terms *)
Fixpoint bind_tm (t:term) (bn fn: nat) : term :=
  match t with
  | cst _ => t
  | fvar i => if beq_nat i fn then bvar bn else t
  | bvar i => t 
  | abs ty t => 
    abs ty (bind_tm t (S bn) fn)
  | app t1 t2 =>
    app (bind_tm t1 bn fn) (bind_tm t2 bn fn)
  | t1 == t2 =>
    (bind_tm t1 bn fn) == (bind_tm t2 bn fn)
  end.
  
Definition bind_tm_0 t fn := bind_tm t 0 fn.

(** Binding of proof terms *)
Fixpoint bind_ptm (pt:pterm) (bn fn: nat) : pterm :=
  match pt with
  | refl t => refl (fresh_tm t bn fn)
  | trans pt1 pt2 => 
    trans (bind_ptm pt1 bn fn) (bind_ptm pt2 bn fn)
  | symm pt1 =>
    symm (bind_ptm pt1 bn fn)
  | congAbs ty pt1 =>
    congAbs ty (bind_ptm pt1 (S bn) fn)
  | congAppL pt1 =>
    congAppL (bind_ptm pt1 bn fn)
  | congAppR pt1 =>
    congAppR (bind_ptm pt1 bn fn)
  | congEqL pt1 =>
    congEqL (bind_ptm pt1 bn fn)
  | congEqR pt1 =>
    congEqR (bind_ptm pt1 bn fn)
  | beta ty t1 t2 =>
    beta ty (fresh_tm t1 (S bn) fn) (fresh_tm t2 bn fn)
  | conv pt1 pt2 =>
    conv (bind_ptm pt1 bn fn) (bind_ptm pt2 bn fn)
end.

Definition bind_ptm_0 t fn := bind_ptm t 0 fn.


(** ** Operations on substitutions *)

(** Generate identity substitutions *)
Fixpoint idsub_acc (acc:sub) (n:nat) : sub :=
  match n with
  | O => acc
  | S n' => idsub_acc (fvar (length acc)::acc) n'
  end.

Compute (idsub_acc [] 11).

Definition idsub (n:nat) : sub :=
  idsub_acc [] n.

(** Access the i-th element of a substitution *)
(* Module ALT_SUB_INDEX. *)
(* Program Fixpoint index_sub (s:sub) (i: {n:nat | n < length s}) : term := *)
(*   match s with *)
(*   | [] => False_rec _ _ *)
(*   | t :: s' =>  *)
(*     match (proj1_sig i) with *)
(*     | O => t *)
(*     | S i' => index_sub s' (exist _ i' _) *)
(*     end *)
(*   end. *)
(* Next Obligation. *)
(*   simpl in H. eapply Nat.nlt_0_r; eauto. *)
(* Defined. *)
(* Next Obligation. *)
(*   simpl in H. apply lt_S_n. auto. *)
(* Defined. *)
(* End ALT_SUB_INDEX. *)

Definition index_sub (s:sub) (i:nat) : option term :=
  if Nat.leb i (length s -1) then 
    nth_error s (length s - 1 - i)
  else
    None.

Compute (index_sub (idsub_acc [] 11) 10).

(** Application of substitution to terms *)
Fixpoint app_sub_tm (t:term) (s:sub) : option term :=
  match t with
  | cst _ => Some t
  | fvar i => index_sub s i
  | bvar _ => Some t
  | abs ty t1 =>
    do t1' <- app_sub_tm t1 s;
    Some (abs ty t1')
  | app t1 t2 =>
    do t1' <- app_sub_tm t1 s;
    do t2' <- app_sub_tm t2 s;
    Some (app t1' t2')
  | t1 == t2 =>
    do t1' <- app_sub_tm t1 s;
    do t2' <- app_sub_tm t2 s;
    Some (t1' == t2')
  end.

(** Application of substitution to proof terms *)
Fixpoint app_sub_ptm (pt:pterm) (s:sub) : option pterm :=
  match pt with
  | refl t => 
    do t' <- app_sub_tm t s;
    Some (refl t')
  | trans pt1 pt2 =>
    do pt1' <- app_sub_ptm pt1 s;
    do pt2' <- app_sub_ptm pt2 s;
    Some (trans pt1' pt2')
  | symm pt1 =>
    do pt1' <- app_sub_ptm pt1 s;
    Some (symm pt1')
  | congAbs ty pt1 =>
    do pt1' <- app_sub_ptm pt1 s;
    Some (congAbs ty pt1')
  | congAppL pt1 =>
    do pt1' <- app_sub_ptm pt1 s;
    Some (congAppL pt1')
  | congAppR pt1 =>
    do pt1' <- app_sub_ptm pt1 s;
    Some (congAppR pt1')
  | congEqL pt1 =>
    do pt1' <- app_sub_ptm pt1 s;
    Some (congEqL pt1')
  | congEqR pt1 =>
    do pt1' <- app_sub_ptm pt1 s;
    Some (congEqR pt1')
  | beta ty t1 t2 =>
    do t1' <- app_sub_tm t1 s;
    do t2' <- app_sub_tm t2 s;
    Some (beta ty t1' t2')
  | conv pt1 pt2 =>
    do pt1' <- app_sub_ptm pt1 s;
    do pt2' <- app_sub_ptm pt2 s;
    Some (conv pt1' pt2')
end.

(** ** Operations on typing contexts *)
Definition index_ctx (ctx:tyctx) (i:nat) : option ty :=
  if Nat.leb i (length ctx -1) then 
    nth_error ctx (length ctx - 1 - i)
  else
    None.


(** ** Typing rules *)

(** Signatures *)
Definition sign := const -> ty.

(** Typing rules for terms *)
Inductive tm_of: sign -> tyctx -> term -> ty -> Prop :=
| tm_of_cst : forall sgn ctx c ty, sgn c = ty -> tm_of sgn ctx (cst c) ty
| tm_of_fvar : forall sgn ctx i ty,
    index_ctx ctx i = Some ty ->
    tm_of sgn ctx (fvar i) ty
| tm_of_abs : forall sgn ctx ty1 ty2 t n,
    length ctx = n ->
    tm_of sgn (ty1::ctx) (fresh_tm_0 t n) ty2 ->
    tm_of sgn ctx (abs ty1 t) (arr ty1 ty2)
| tm_of_app : forall sgn ctx t1 t2 ty1 ty2,
    tm_of sgn ctx t1 (arr ty1 ty2) -> 
    tm_of sgn ctx t2 ty1 -> 
    tm_of sgn ctx (app t1 t2) ty2
| tm_of_eq : forall sgn ctx t1 t2 ty,
    tm_of sgn ctx t1 ty -> 
    tm_of sgn ctx t2 ty -> 
    tm_of sgn ctx (t1 == t2) prop.


(** Typing rules for proof terms *)
Inductive ptm_of: sign -> tyctx -> pterm -> term -> Prop :=
| ptm_of_refl: forall sgn ctx t ty,
    tm_of sgn ctx t ty ->
    ptm_of sgn ctx (refl t) (t == t)
| ptm_of_trans: forall sgn ctx pt1 pt2 t1 t2 t3,
    ptm_of sgn ctx pt1 (t1 == t2) ->
    ptm_of sgn ctx pt2 (t2 == t3) ->
    ptm_of sgn ctx (trans pt1 pt2) (t1 == t3)
| ptm_of_symm: forall sgn ctx pt t1 t2,
    ptm_of sgn ctx pt (t2 == t1) ->
    ptm_of sgn ctx (symm pt) (t1 == t2)
| ptm_of_congAbs: forall sgn ctx ty pt t1 t2 n,
    length ctx = n ->
    ptm_of sgn (ty::ctx) (fresh_ptm_0 pt n) (t1 == t2) -> 
    ptm_of sgn ctx (congAbs ty pt) 
           (abs ty (bind_tm_0 t1 (length ctx)) == abs ty (bind_tm_0 t2 n))
| ptm_of_congAppL: forall sgn ctx pt t1 t1' t2,
    ptm_of sgn ctx pt (t1 == t1') ->
    ptm_of sgn ctx (congAppL pt) (app t1 t2 == app t1' t2)
| ptm_of_congAppR: forall sgn ctx pt t1 t2 t2',
    ptm_of sgn ctx pt (t2 == t2') ->
    ptm_of sgn ctx (congAppR pt) (app t1 t2 == app t1 t2')
| ptm_of_congEqL: forall sgn ctx pt t1 t1' t2,
    ptm_of sgn ctx pt (t1 == t1') ->
    ptm_of sgn ctx (congEqL pt) ((t1 == t2) == (t1' == t2))
| ptm_of_congEqR: forall sgn ctx pt t1 t2 t2',
    ptm_of sgn ctx pt (t2 == t2') ->
    ptm_of sgn ctx (congEqR pt) ((t1 == t2) == (t1 == t2'))
| ptm_of_beta: forall sgn ctx t1 t2 t3 n ty1 ty2,
    length ctx = n ->
    tm_of sgn ctx (abs ty1 t1) (arr ty1 ty2) ->
    tm_of sgn ctx t2 ty1 ->
    app_sub_tm (fresh_tm_0 t1 n) (t2::(idsub n)) = Some t3 ->
    ptm_of sgn ctx (beta ty1 t1 t2) 
           (app (abs ty1 t1) t2 == t3)
| ptm_of_conv: forall sgn ctx pt1 pt2 t1 t2,
    ptm_of sgn ctx pt1 t1 ->
    ptm_of sgn ctx pt2 (t1 == t2) ->
    ptm_of sgn ctx (conv pt1 pt2) t2.


