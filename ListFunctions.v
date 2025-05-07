Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Lists.List.
Require Import CoqUtilLib.Iteration.

Import ListNotations.

Require Import OptionFunctions.

(* Require Import FreeMonoid.StructMonoid.
Require Import FreeMonoid.MonoidFree. *)

Require Import Coq.ssr.ssrfun.

Definition tails {A : Type}: list A -> list (list A) := fold_right (fun x xsxss => match xsxss with
  | [] => [[]] (* This case is impossible. *)
  | xs :: xss => (x::xs) :: (xs::xss)
end) [[]].

Definition inits {A : Type}: list A -> list (list A) := fold_right (fun x => (cons []) ∘ map (cons x)) [[]].

Definition concat {A : Type} : list (list A) -> list A := @List.concat A.

Definition segs {A : Type} : list A -> list (list A) := concat ∘ map inits ∘ tails.

Fixpoint drop_n {A : Type} (n : nat) (l : list A) : list A :=
  match n, l with
  | 0, _ => l
  | _, [] => []
  | S n', _ :: t => drop_n n' t
  end.

Fixpoint take_n {A : Type} (n : nat) (l : list A) : list A :=
  match n, l with
  | 0, _ => []
  | S n', [] => []
  | S n', x :: t => x :: take_n n' t
  end.

Lemma take_n_app_drop_n_id : forall (A : Type) (n : nat) (l : list A),
  take_n n l ++ drop_n n l = l.
Proof.
  intros A n.
  induction n as [| n' IH]; intros l.
  - simpl. reflexivity.
  - destruct l as [| x t].
    + simpl. reflexivity.
    + simpl. rewrite IH. reflexivity.
Qed.

Lemma drop_n_S_eq :
  forall (A : Type) (n : nat) (l : list A),
    drop_n (S n) l = drop_n 1 (drop_n n l).
Proof.
  intros A n l.
  revert l. induction n as [| n' IH]; intros l.
  - simpl. reflexivity.
  - destruct l as [| x t]; simpl.
    + reflexivity.
    + apply IH.
Qed.

Lemma drop_n_is_iter :
  forall (A : Type) (n : nat) (l : list A),
    drop_n n l = iter (drop_n 1) n l.
Proof.
  intros A n l.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - destruct l.
    + replace (iter (drop_n 1) (S n') nil) with ((@drop_n A 1) (iter (drop_n 1) n' nil)) by reflexivity.
      rewrite <- IH.
      destruct n'; reflexivity.
    + replace (iter (drop_n 1) (S n') (a :: l)) with ((drop_n 1) (iter (drop_n 1) n' (a :: l))) by reflexivity.
      replace (drop_n (S n') (a :: l)) with ((drop_n (n') ((drop_n 1) (a :: l)))) by reflexivity.
      rewrite <- IH.
      destruct n'.
      * reflexivity.
      * replace (drop_n 1 (a :: l)) with (l) by reflexivity.
        replace (drop_n (S n') (a :: l)) with (drop_n n' l) by reflexivity.
        apply drop_n_S_eq.
Qed.

Lemma drop_m_drop_n_id : forall (A : Type) (m n : nat) (l : list A),
  drop_n m (drop_n n l) = drop_n (m + n) l.
Proof.
  intros A m n l.
  rewrite drop_n_is_iter.
  rewrite drop_n_is_iter.
  rewrite drop_n_is_iter.
  apply iter_m_plus_n.
Qed.

Fixpoint scan_right {A B : Type} (f : A -> B -> B) (i : B) (xs : list A) {struct xs} : list B :=
  match xs with
  | nil => [i]
  | x :: xs' => let q := fold_right f i xs' in
                f x q :: scan_right f i xs'
  end.

Fixpoint scan_left {A B : Type} (f : B -> A -> B) (xs : list A) (i : B) {struct xs} : list B :=
  i ::
    match xs with
    | nil => nil
    | x :: xs' => scan_left f xs' (f i x)
    end.

(* Lemma fold_left_comm_cons_app : forall [A B : Type] (f : A -> A -> A) (x : A) (xs ys : list A) (i : A),
  commutative f -> fold_left f ((x :: xs) ++ ys) i = fold_left f (xs ++ (x :: ys)) i.
Proof.
  intros. *)

(* Lemma foldl_comm_app : forall [A B : Type] (f : A -> A -> A) (xs ys : list A) (i : A),
  commutative f -> fold_left f (xs ++ ys) i = fold_left f (ys ++ xs) i.
Proof.
  intros. *)

Theorem cons_append : forall (X : Type) (x : X) (xs : list X),
  x :: xs = [x] ++ xs.
Proof.
  intros X x xs.
  reflexivity.
Qed.

(* Allows us to expand a left fold as if it were a right fold, provided the operation allows a form of commutativity. *)
Lemma fold_left_cons_comm : forall [A B : Type] (f : B -> A -> B) (x : A) (xs : list A) (i : B),
  (forall (i : B), commutative (fun x y => f (f i x) y)) -> fold_left f (x :: xs) i = f (fold_left f xs i) x.
Proof.
  intros A B f x xs i comH.
  simpl. (* This reduces `fold_left f (x :: xs) i` to `fold_left f xs (f i x)` *)
  revert i. (* We prepare to use induction on `xs` *)
  induction xs as [|x' xs' IH]; intros i.
  - simpl. (* Base case: `fold_left f [] (f i x)` simplifies to `f i x` *)
    reflexivity.
  - simpl in *. (* Inductive case: unfold the definition for one more element *)
    rewrite <- (IH (f i x')). (* Use the induction hypothesis *)
    f_equal.
    apply comH.
Qed.

Lemma fold_left_app_assoc : forall [A : Type] (f : A -> A -> A) (x : A) (xs : list A) (i : A),
  fold_left f (xs ++ [x]) i = f (fold_left f xs i) x.
Proof.
  intros A f x xs.
  apply fold_left_app.
Qed.

Definition middle_assoc [A : Type] (P : A -> Prop) (f : A -> A -> A) : Prop := forall (a m b : A), forall (P_m : P m), f (f a m) b = f a (f m b).

Lemma fold_left_combine_middle_assoc : forall [A : Type] (P : A -> Prop) (f : A -> A -> A) (x y : A) (xs ys : list A),
  forall (middle_assoc_P_f : middle_assoc P f),
  forall (P_x : P x),
  forall (P_y : P y),
  forall (P_xs : Forall P xs),
  forall (P_ys : Forall P ys),

  f (fold_left f xs x) (fold_left f ys y) = fold_left f (xs ++ y :: ys) x.
Proof.
  intros A P f x y xs ys.
  intros.
  apply Forall_rev in P_ys.
  rewrite <- (rev_involutive ys).
  remember (rev ys).
  induction (rev l).
  - rewrite fold_left_app_assoc.
    reflexivity.
  - admit.
  (* - 
  rewrite Forall_forall in P_ys.
  destruct P_ys.
  - rewrite fold_left_app.
    simpl.
    reflexivity.
  - replace (xs ++ y :: x0 :: l) with (xs ++ [y] ++ [x0] ++ l) by reflexivity.
    rewrite fold_left_app.
    rewrite fold_left_app.
    rewrite fold_left_app.



  - induction P_ys.
    + reflexivity.
    + replace (fold_left f ([] ++ y :: x0 :: l) x) with (fold_left f (y :: x0 :: l) x) by reflexivity.

      simpl in *.
      unfold middle_assoc in middle_assoc_P_f.
      specialize middle_assoc_P_f with (P_m := P_y) as assoc_y.
      rewrite assoc_y. clear assoc_y.

  - simpl.
    unfold middle_assoc in middle_assoc_P_f.
    specialize middle_assoc_P_f with (P_m := P_x) as assoc_x.
    specialize middle_assoc_P_f with (P_m := P_y) as assoc_y.
    rewrite assoc_y.
  rewrite fold_left_app.
  rewrite <- fold_left_app_assoc.
  simpl.
  rewrite fold_left_app.
  simpl.
  rewrite cons_append.
  simpl. (* This reduces `fold_left f (x :: xs) i` to `fold_left f xs (f i x)` *)
  revert i. (* We prepare to use induction on `xs` *)
  induction xs as [|x' xs' IH]; intros i.
  - reflexivity.
  - exact (IH (f i x')). *)

Admitted.

(* Context {A : Type} (HmagmaA : Magma A) (HsemigroupA : Semigroup A) (HmonoidA : Monoid A).

Module ABasis.
  Definition Basis := A.
End ABasis.

Module AFreeMonoid := FreeMonoidModule ABasis.

Definition identity (x : A) : A := x.

Lemma monoid_concat `{Monoid A} (idH : idempotent m_op) : let f := fold_right m_op mn_id in f ∘ concat = f ∘ map f.
Proof.
  intros.
  unfold f.
  unfold compose.
  apply functional_extensionality.
  intros.
  induction x as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite <- IH.
    apply AFreeMonoid.extend_monoid_homomorphism.
Qed. *)

Lemma fold_left_nil : forall [A B : Type] (f : A -> B -> A) (i : A),
  fold_left f nil i = i.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma fold_right_nil : forall [A B : Type] (f : B -> A -> A) (i : A),
  fold_right f i nil = i.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Theorem fold_left_right_equiv : 
  forall (A : Type) (f : A -> A -> A) (z : A) (l : list A),
    (forall x y z, f x (f y z) = f (f x y) z) -> (* Associativity of f *)
    (forall x y, f x y = f y x) -> (* Commutativity of f *)
    fold_left f l z = fold_right f z l.
Proof.
  intros A f z l H_assoc H_comm.
  apply fold_symmetric.
  - apply H_assoc.
  - apply H_comm.
Qed.

(* Non-empty lists *)
Record nelist (A : Type) :=
  new_nelist {
      ne_list : list A;
      _ : 0 < length ne_list;
    }.

Arguments ne_list {_} _.
Arguments new_nelist {_} _ _.

Definition mk_nelist {A : Type} {l : list A} (_ : 0 < length l) : nelist A :=
  new_nelist l ltac:(assumption).

(* 
Lemma lt0l : 0 < length [2].
Proof.
  auto.
Qed.

Definition n := mk_nelist lt0l.

Compute (ne_list n).
*)
