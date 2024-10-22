Fixpoint iter {A : Type} (f : A -> A) (n : nat) (x : A) : A :=
  match n with
  | 0 => x
  | S n' => f (iter f n' x)
  end.
