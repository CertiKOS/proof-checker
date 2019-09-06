(**
 * Author:    Yuting Wang
 * Created:   Sep 5, 2019
*)


(** * Some ultility definitions *)
Set Implicit Arguments.

Definition bind (A B: Type) (e: option A) (f: A -> option B) : option B :=
  match e with
  | None => None
  | Some v => f v
  end.

Notation "'do' x <- e1 ; e2" := (bind e1 (fun x => e2))
(right associativity, x ident, at level 200): option_monad_scope.

Remark bind_inversion:
  forall (A B: Type) (a: option A) (f: A -> option B) (b: B),
  bind a f = Some b ->
  exists x, a = Some x /\ f x = Some b.
Proof.
  intros until b. destruct a; simpl; intros.
  exists a; auto.
  discriminate.
Qed.

Ltac opt_monad_inv H :=
  match type of H with 
  | (Some _ = Some _) =>
      inversion H; clear H; try subst
  | (None = Some _) =>
      discriminate
  | (bind ?a ?f = Some ?b) =>
    let x := fresh "x" in
    let EQ1 := fresh "EQ" in
    let EQ2 := fresh "EQ" in
    destruct (bind_inversion a f H) as [x [EQ1 EQ2]];
    clear H;
    try (opt_monad_inv EQ2)
  end.
