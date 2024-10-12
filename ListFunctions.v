Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import OptionFunctions.

(* Require Import FreeMonoid.StructMonoid.
Require Import FreeMonoid.MonoidFree. *)

Require Import Coq.ssr.ssrfun.

Definition tails {A : Type}: list A -> list (list A) := fold_right (fun x xsxss => match xsxss with
  | [] => [[]] (* This case is impossible. *)
  | xs :: xss => (x::xs) :: (xs::xss)
end) [[]].

(* Define the inits function using reverse and tails *)
Definition inits {A : Type}: list A -> list (list A) := fold_right (fun x => (cons []) ∘ map (cons x)) [[]].

Definition concat {A : Type} : list (list A) -> list A := @List.concat A.

Definition segs {A : Type} : list A -> list (list A) := concat ∘ map inits ∘ tails.

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
    (forall x y, f x y = f y x) -> (* Associativity of f *)
    fold_left f l z = fold_right f z l.
Proof.
  intros A f z l H_assoc H_comm.
  revert z. (* We generalize z to allow induction *)
  induction l as [| x xs IH]; intros z.
  - (* Base case: empty list *)
    reflexivity.
  - (* Inductive step: non-empty list *)
    simpl. (* Simplify both fold_left and fold_right *)
    rewrite <- IH. (* Apply the inductive hypothesis *)
    clear IH. (* No longer need the inductive hypothesis *)
    (* Now use the associativity of f to rearrange *)
    induction xs as [| y ys IHys]; simpl.
    + (* Case: xs = [] *)
      apply H_comm.
    + (* Case: xs = y :: ys *)
      rewrite (H_comm x (fold_left f ys (f z y))).
      rewrite <- (fold_left_cons_comm).
      * simpl.
        rewrite <- (H_assoc z y x).
        rewrite (H_comm y x).
        rewrite (H_assoc z x y).
        reflexivity.
      * intros.
        unfold ssrfun.commutative.
        intros.
        rewrite <- H_assoc.
        rewrite (H_comm x0 y0).
        rewrite H_assoc.
        reflexivity.
Qed.
