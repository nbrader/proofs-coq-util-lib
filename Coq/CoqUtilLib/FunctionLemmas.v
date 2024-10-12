(* Refs:
 - horners_rule_false_2 -> (* Refs: NONE *)
*)
Theorem functions_not_equal :
  forall (X Y : Type) (f g : X -> Y),
  (exists x : X, f x <> g x) -> f <> g.
Proof.
  (* exact (
          fun (X Y : Type) (f g : X -> Y) (H : exists x : X, (f x = g x) -> False) =>
            (
              fun Heq : f = g => match H with
                | ex_intro _ x Hx => Hx (eq_ind f (fun g0 : X -> Y => f x = g0 x) eq_refl g Heq)
              end
            ) : (f = g) -> False
        ). *)
  intros X Y f g H.
  intros Heq.
  destruct H as [x0 Hx0].
  apply Hx0.
  rewrite <- Heq.
  reflexivity.
Qed.
