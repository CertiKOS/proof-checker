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