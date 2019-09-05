(**
 * Author:    Yuting Wang
 * Created:   Sep 5, 2019
*)

Require Import Arith.
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

(** Types *)
Inductive ty : Type :=
| prop
| tcst
| arr : ty -> ty -> ty.

(** Terms *)
Inductive term: Type :=
| cst
| fvar : nat -> term
| bvar : nat -> term
| abs  : ty -> term -> term
| app  : term -> term -> term
| eq   : term -> term -> term.

(** Proof terms *)
Inductive pterm: Type :=
| pcst
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
  | cst => cst
  | fvar _ => t
  | bvar i => if beq_nat i bn then fvar fn else t
  | abs ty t => 
    abs ty (fresh_tm t (S bn) fn)
  | app t1 t2 =>
    app (fresh_tm t1 bn fn) (fresh_tm t2 bn fn)
  | eq t1 t2 =>
    eq (fresh_tm t1 bn fn) (fresh_tm t2 bn fn)
  end.

(** Freshening of proof terms *)
Fixpoint fresh_ptm (pt:pterm) (bn fn: nat) : pterm :=
  match pt with
  | pcst => pcst
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

(** Binding of terms *)
Fixpoint bind_tm (t:term) (bn fn: nat) : term :=
  match t with
  | cst => cst
  | fvar i => if beq_nat i fn then bvar bn else t
  | bvar i => t 
  | abs ty t => 
    abs ty (bind_tm t (S bn) fn)
  | app t1 t2 =>
    app (bind_tm t1 bn fn) (bind_tm t2 bn fn)
  | eq t1 t2 =>
    eq (bind_tm t1 bn fn) (bind_tm t2 bn fn)
  end.
  
(** Binding of proof terms *)
Fixpoint bind_ptm (pt:pterm) (bn fn: nat) : pterm :=
  match pt with
  | pcst => pcst
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


(** ** Operations on substitutions *)

(** Access the i-th element of a substitution *)
Module ALT_SUB_INDEX.
Program Fixpoint index_sub (s:sub) (i: {n:nat | n < length s}) : term :=
  match s with
  | [] => False_rec _ _
  | t :: s' => 
    match (proj1_sig i) with
    | O => t
    | S i' => index_sub s' (exist _ i' _)
    end
  end.
Next Obligation.
  simpl in H. eapply Nat.nlt_0_r; eauto.
Defined.
Next Obligation.
  simpl in H. apply lt_S_n. auto.
Defined.
End ALT_SUB_INDEX.

Definition index_sub (s:sub) (i:nat) : option term :=
  nth_error s i.

(** Application of substitution to terms *)
Fixpoint app_sub_tm (t:term) (s:sub) : option term :=
  match t with
  | cst => Some cst
  | fvar i => index_sub s i
  | bvar _ => Some t
  | abs ty t1 =>
    do t1' <- app_sub_tm t1 s;
    Some (abs ty t1')
  | app t1 t2 =>
    do t1' <- app_sub_tm t1 s;
    do t2' <- app_sub_tm t2 s;
    Some (app t1' t2')
  | eq t1 t2 =>
    do t1' <- app_sub_tm t1 s;
    do t2' <- app_sub_tm t2 s;
    Some (eq t1' t2')
  end.

(** Application of substitution to proof terms *)
Fixpoint app_sub_ptm (pt:pterm) (s:sub) : option pterm :=
  match pt with
  | pcst => Some pcst
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
