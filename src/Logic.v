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
  if le_dec i (length s -1) then 
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
Definition sign := const -> option ty.
Definition empty_sign: sign := fun _ => None.

(** Typing rules for terms *)
Inductive tm_of: sign -> tyctx -> term -> ty -> Prop :=
| tm_of_cst : forall sgn ctx c ty, sgn c = Some ty -> tm_of sgn ctx (cst c) ty
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

Notation "S ; C |- t : ty" := (tm_of S C t ty)
  (at level 70, C at level 200, t at level 100, ty at level 200): stlcd_scope.


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

Notation "S; C ||- pt : t" := (ptm_of S C pt t)
  (at level 70): stlcd_scope.

Local Open Scope stlcd_scope.


(** ** Examples *)
Definition a := bty.
(** x: a -> a |- fun y:a => x y : arr a a *)
Example of_tm_ex1: tm_of empty_sign [arr a a] (abs a (app (fvar 0) (bvar 0))) (arr a a).
Proof.
  econstructor. reflexivity.
  cbn.
  econstructor. 
  constructor. cbn. reflexivity.
  constructor. cbn. auto.
Qed.

Example of_tm_ex2: forall t, 
    tm_of empty_sign [arr a a] (abs a (app (fvar 0) (bvar 0))) t ->
    t = arr a a.
Proof.
  intros t OF.
  inversion OF; subst; cbn in *.
  inversion H5; subst; cbn in *.
  inversion H3; subst; cbn in *.
  inversion H2; subst. auto.
Qed.

(** z:a -> a |- pt: (fun x:a->a => fun y:a => x y) z = (fun y:a => z y) *)
Example pof_tm_ex1: exists pt, 
    ptm_of empty_sign [arr a a] pt 
           (app (abs (arr a a) (abs a (app (bvar 1) (bvar 0)))) (fvar 0) == 
            abs a (app (fvar 0) (bvar 0))).
Proof.
  eexists.
  eapply ptm_of_beta. reflexivity.
  - econstructor. reflexivity.
    cbn. econstructor. reflexivity.
    cbn. econstructor. constructor. cbn. reflexivity.
    econstructor. reflexivity.
  - constructor. reflexivity.
  - cbn. reflexivity.
Qed.

Example pof_tm_ex2: forall pt, 
    pt = beta (arr a a) (abs a (app (bvar 1) (bvar 0))) (fvar 0) ->
    ptm_of empty_sign [arr a a] pt 
           (app (abs (arr a a) (abs a (app (bvar 1) (bvar 0)))) (fvar 0) == 
            abs a (app (fvar 0) (bvar 0))).
Proof.
  intros. subst.
  eapply ptm_of_beta. reflexivity.
  econstructor. reflexivity.
  cbn. econstructor. reflexivity.
  cbn. econstructor. econstructor. reflexivity.
  econstructor. reflexivity.
  econstructor. reflexivity.
  cbn. reflexivity.
Qed.


(** ** Decidability of substitution applications *)
Definition ty_dec (ty1 ty2: ty) : {ty1 = ty2} + {ty1 <> ty2}. 
  decide equality.
Qed.

Definition tm_dec (t1 t2: term) : {t1 = t2} + {t1 <> t2}. 
  decide equality; decide equality.
Qed.

(* Program Fixpoint ty_dec ty1 ty2 : {ty1 = ty2} + {ty1 <> ty2} := *)
(*   match ty1, ty2 with *)
(*   | prop, prop => left _ *)
(*   | bty, bty => left _ *)
(*   | arr ty1' ty1'', arr ty2' ty2'' => *)
(*     if ty_dec ty1' ty2' then *)
(*       if ty_dec ty1'' ty2'' then left _ else right _ *)
(*     else *)
(*       right _ *)
(*   | _, _ => right _ *)
(*   end. *)
(* Next Obligation. *)
(*   destruct ty1, ty2; try tauto; try (intro EQ; congruence). *)
(*   intro EQ. eapply H0; eauto. *)
(* Defined. *)
(* Next Obligation. *)
(*   split. intros [H1 H2]. congruence. *)
(*   split. intros ty1' ty1'' ty2' ty2'' [H1 H2]. congruence. *)
(*   intros [H1 H2]. congruence. *)
(* Defined. *)
(* Next Obligation. *)
(*   split. intros [H1 H2]. congruence. *)
(*   split. intros ty1' ty1'' ty2' ty2'' [H1 H2]. congruence. *)
(*   intros [H1 H2]. congruence. *)
(* Defined. *)
(* Next Obligation. *)
(*   split. intros [H1 H2]. congruence. *)
(*   split. intros ty1' ty1'' ty2' ty2'' [H1 H2]. congruence. *)
(*   intros [H1 H2]. congruence. *)
(* Defined. *)
(* Next Obligation. *)
(*   split. intros [H1 H2]. congruence. *)
(*   split. intros ty1' ty1'' ty2' ty2'' [H1 H2]. congruence. *)
(*   intros [H1 H2]. congruence. *)
(* Defined.   *)
(* Next Obligation. *)
(*   split. intros [H1 H2]. congruence. *)
(*   split. intros ty1' ty1'' ty2' ty2'' [H1 H2]. congruence. *)
(*   intros [H1 H2]. congruence. *)
(* Defined.   *)
(* Next Obligation. *)
(*   split. intros [H1 H2]. congruence. *)
(*   split. intros ty1' ty1'' ty2' ty2'' [H1 H2]. congruence. *)
(*   intros [H1 H2]. congruence. *)
(* Defined.   *)


Lemma app_sub_tm_cst: forall c s t, app_sub_tm (cst c) s = Some t -> t = (cst c).
Proof.
  simpl. intros. congruence.
Qed.

Lemma app_sub_tm_bvar: forall i s t, app_sub_tm (bvar i) s = Some t -> t = (bvar i).
Proof.
  simpl. intros. congruence.
Qed.

Lemma app_sub_tm_abs: forall ty t s t', 
    app_sub_tm (abs ty t) s = Some t' -> 
    exists t1, app_sub_tm t s = Some t1 /\ t' = abs ty t1.
Proof.
  simpl. intros.
  opt_monad_inv H.
  eauto.
Qed.

Lemma app_sub_tm_app: forall t1 t2 s t',
    app_sub_tm (app t1 t2) s = Some t' -> 
    exists t1' t2', app_sub_tm t1 s = Some t1' /\ 
               app_sub_tm t2 s = Some t2' /\
               t' = app t1' t2'.
Proof.
  simpl. intros.
  opt_monad_inv H.
  eauto.
Qed.

Lemma app_sub_tm_teq: forall t1 t2 s t',
    app_sub_tm (t1 == t2) s = Some t' -> 
    exists t1' t2', app_sub_tm t1 s = Some t1' /\ 
               app_sub_tm t2 s = Some t2' /\
               t' = (t1' == t2').
Proof.
  simpl; intros.
  opt_monad_inv H.
  eauto.
Qed.


(** Decidability of index_sub *)
Program Definition index_sub_dec t s i: 
  {index_sub s i = Some t} + {index_sub s i <> Some t} :=
  if le_dec i (length s - 1) then
    match nth_error s (length s - 1 - i) with
    | None => right _
    | Some t' => 
      if tm_dec t t' then left _ else right _
    end
  else
    right _.
Next Obligation.
  unfold index_sub. 
  destruct (le_dec i (length s - 1)); congruence.
Defined.
Next Obligation.
  unfold index_sub.
  destruct (le_dec i (length s - 1)); congruence.
Defined.
Next Obligation.
  unfold index_sub.
  destruct (le_dec i (length s - 1)); congruence.
Defined.
Next Obligation.
  unfold index_sub.
  destruct (le_dec i (length s - 1)); congruence.
Defined.

Local Ltac solve_cong := 
  lazymatch goal with
  | [ |- forall _, _ ] =>
    intro; solve_cong
  | [ |- ~ (_ /\ _) ] =>
    let H1 := fresh "H" in
    let H2 := fresh "H" in
    intros; intros (H1 & H2); congruence
  end.

Local Ltac solve_neq :=
  match goal with
  | [ |- _ <> _ ] =>
    let EQ := fresh "EQ" in
    intro EQ; opt_monad_inv EQ; simpl in *; congruence
  end.

Show Obligation Tactic.

Local Obligation Tactic := 
  Tactics.program_simpl; 
  try solve_neq; try (repeat split; solve_cong).
  
Program Fixpoint app_sub_tm_dec t s t' 
  : {app_sub_tm t s = Some t'} + {app_sub_tm t s <> Some t'} :=
  match t, t' with 
  | cst i, cst i' => 
    if Pos.eq_dec i i' then left _ else right _
  | fvar i, _ =>
    if index_sub_dec t' s i then left _ else right _
  | bvar i, bvar i' =>
    if Nat.eq_dec i i' then left _ else right _
  | abs ty t1, abs ty' t1' =>
    if ty_dec ty ty' then
      if app_sub_tm_dec t1 s t1' then left _ else right _
    else 
      right _
  | app t1 t2, app t1' t2' =>
    if app_sub_tm_dec t1 s t1' then 
      if app_sub_tm_dec t2 s t2' then left _ else right _
    else 
      right _
  | t1 == t2, t1' == t2' =>
    if app_sub_tm_dec t1 s t1' then 
      if app_sub_tm_dec t2 s t2' then left _ else right _
    else 
      right _
  | _, _ => right _
  end.
Next Obligation.
  rewrite H0. simpl. auto.
Defined.
Next Obligation.
  rewrite H, H0. simpl. congruence.
Defined.
Next Obligation.
  rewrite H, H0. simpl. congruence.
Defined.
Next Obligation.
  intro EQ.
  destruct t.
  - apply app_sub_tm_cst in EQ; subst. eapply H4; eauto.
  - eapply H; eauto.
  - apply app_sub_tm_bvar in EQ; subst. eapply H0; eauto.
  - apply app_sub_tm_abs in EQ. destruct EQ as [t1 [EQ1 EQ2]]. subst.
    eapply H1; eauto.
  - apply app_sub_tm_app in EQ.
    destruct EQ as (t1' & t2' & EQ1 & EQ2 & EQ3). subst.
    eapply H2; eauto.
  - apply app_sub_tm_teq in EQ.
    destruct EQ as (t1' & t2' & EQ1 & EQ2 & EQ3). subst.
    eapply H3; eauto.
Defined.



(** ** Decidability of typing terms *)

Definition sign_dec: forall (sgn:sign) c ty, 
    {sgn c = Some ty} + {sgn c <> Some ty}.
Proof.
  decide equality.
  apply ty_dec.
Defined.

Definition index_ctx_dec C i ty
  : {index_ctx C i = Some ty} + {index_ctx C i <> Some ty}.
Proof.
  decide equality.
  apply ty_dec.
Defined.

(* Program Fixpoint tm_of_dec S C t ty : *)
(*   {tm_of S C t ty} + {~tm_of S C t ty} := *)
(*   match t with *)
(*   | cst c =>  *)
(*     if sign_dec S c ty then left _ else right _ *)
(*   | fvar i => *)
(*     if index_ctx_dec C i ty then left _ else right _ *)
(*   | _ => right _ *)
(*   end. *)
(* Next Obligation. *)
(*   constructor. auto. *)
(* Defined. *)
(* Next Obligation. *)
(*   intro OF. apply H. inversion OF; auto. *)
(* Defined. *)
(* Next Obligation. *)
(*   constructor. auto. *)
(* Defined. *)
(* Next Obligation. *)
(*   intro OF. apply H. inversion OF; subst. auto. *)
(* Defined. *)

