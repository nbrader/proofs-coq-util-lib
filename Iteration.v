Fixpoint iter {A : Type} (f : A -> A) (n : nat) (x : A) : A :=
  match n with
  | 0 => x
  | S n' => f (iter f n' x)
  end.

Lemma iter_m_plus_n : forall {A : Type} (f : A -> A) (m n : nat) (x : A),
  iter f m (iter f n x) = iter f (m + n) x.
Proof.
  intros A f m n x.
  induction m as [| m' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.
