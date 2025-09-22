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

(* Helper lemma: relation between fold_left with different initial values *)
Lemma fold_left_transform_init : forall [A : Type] (P : A -> Prop) (f : A -> A -> A) (xs : list A) (a b : A),
  forall (middle_assoc_P_f : middle_assoc P f),
  forall (closure_P_f : forall u v, P u -> P v -> P (f u v)),
  forall (P_a : P a),
  forall (P_b : P b),
  forall (P_xs : Forall P xs),
  f a (fold_left f xs b) = fold_left f xs (f a b).
Proof.
  intros A P f xs a b middle_assoc_P_f closure_P_f P_a P_b P_xs.
  generalize dependent b.
  induction xs as [| x xs' IH]; intro b; intro P_b.

  - (* Base case: xs = [] *)
    simpl fold_left.
    reflexivity.

  - (* Inductive case: xs = x :: xs' *)
    simpl fold_left.
    (* Goal: f a (fold_left f xs' (f b x)) = fold_left f xs' (f (f a b) x) *)

    (* We need to show P (f b x) and P (f (f a b) x) to apply IH *)
    assert (P_f_b_x : P (f b x)).
    { apply closure_P_f. exact P_b.
      inversion P_xs as [| y ys P_x P_xs']. exact P_x. }

    assert (P_f_fab_x : P (f (f a b) x)).
    { apply closure_P_f. apply closure_P_f. exact P_a. exact P_b.
      inversion P_xs as [| y ys P_x P_xs']. exact P_x. }

    (* Apply IH with the tail of the list *)
    assert (P_xs_tail : Forall P xs').
    { inversion P_xs as [| y ys P_x P_xs']. exact P_xs'. }

    rewrite (IH P_xs_tail (f b x) P_f_b_x).

    (* Now use middle associativity: f (f a b) x = f a (f b x) when P x *)
    assert (P_x : P x).
    { inversion P_xs as [| y ys P_x P_xs']. exact P_x. }

    rewrite <- (middle_assoc_P_f a b x P_b).
    reflexivity.
Qed.

(*
   CLOSURE REQUIREMENT ANALYSIS:

   The closure assumption (closure_P_f) was added after discovering that the original
   lemma could not be proven without it. Extensive computational testing revealed:

   1. COMPUTATIONAL ROBUSTNESS: The property holds in ALL tested cases, even when
      closure is violated. Tests included:
      - Bounded arithmetic with non-closed generating sets
      - Modular operations (mult mod 5, add mod 3)
      - Custom operations with absorbing elements
      - Finite field operations (GF(4))
      - Operations with deliberate asymmetries

   2. PROOF METHODOLOGY REQUIREMENT: The closure assumption is needed for the
      inductive proof structure, specifically:
      - fold_left_preserves_P requires proving P(f z w) from P(z) ∧ P(w)
      - In constructive logic (Coq), this step cannot proceed without closure
      - The middle associativity property only applies to elements satisfying P

   3. OPEN QUESTION: The distinction between "necessary for this proof method" vs.
      "necessary for mathematical truth" remains unclear. The computational evidence
      suggests the property may be provable through alternative approaches that don't
      require closure, or that closure emerges naturally from middle associativity
      in ways not yet understood.

   4. CONTINUED INVESTIGATION: The user remains interested in finding counterexamples
      until they understand the meta-theoretical reasoning behind why closure appears
      to be a proof artifact rather than a mathematical necessity.

   See Python/CLOSURE_ANALYSIS_FINDINGS.py for detailed computational analysis.
*)
Lemma fold_left_combine_middle_assoc : forall [A : Type] (P : A -> Prop) (f : A -> A -> A) (x y : A) (xs ys : list A),
  forall (middle_assoc_P_f : middle_assoc P f),
  forall (closure_P_f : forall a b, P a -> P b -> P (f a b)),
  forall (P_x : P x),
  forall (P_y : P y),
  forall (P_xs : Forall P xs),
  forall (P_ys : Forall P ys),

  f (fold_left f xs x) (fold_left f ys y) = fold_left f (xs ++ y :: ys) x.
Proof.
  intros A P f x y xs ys middle_assoc_P_f closure_P_f P_x P_y P_xs P_ys.

  (* First expand the RHS using fold_left_app *)
  rewrite fold_left_app.
  simpl.

  (* Now we need to prove:
     f (fold_left f xs x) (fold_left f ys y) =
     fold_left f ys (f (fold_left f xs x) y) *)

  (* First, let's prove fold_left preserves P under our conditions *)
  assert (fold_left_preserves_P: forall zs z, P z -> Forall P zs -> P (fold_left f zs z)). {
    intro zs.
    induction zs as [| w zs' IH].
    - intros z Pz Pzs. simpl. exact Pz.
    - intros z Pz Pzs. simpl.
      inversion Pzs as [| head tail Pw Pzs' Heq].
      subst.
      (* Now apply IH with the updated initial value *)
      apply IH.
      + apply closure_P_f; auto.
      + exact Pzs'.
  }

  (* Using this, we can show (fold_left f xs x) satisfies P *)
  assert (P_fold_xs: P (fold_left f xs x)). {
    apply fold_left_preserves_P; auto.
  }

  (* Use the helper lemma to transform the goal *)
  apply fold_left_transform_init with (P := P); auto.
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
    (forall x y, f x y = f y x) -> (* Commutativity of f *)
    fold_left f l z = fold_right f z l.
Proof.
  intros A f z l H_assoc H_comm.
  apply fold_symmetric.
  - apply H_assoc.
  - apply H_comm.
Qed.
Theorem fold_left_right_rev {A B : Type} :
  forall (f : A -> B -> B) (xs : list A) (init : B),
    fold_left (fun acc x => f x acc) xs init = fold_right f init (rev xs).
Proof.
  intros f xs init.
  revert init.
  induction xs as [|x xs' IH]; intros init.
  - simpl. reflexivity.
  - simpl rev. rewrite fold_right_app. simpl.
    simpl fold_left. rewrite IH. reflexivity.
Qed.

Theorem fold_left_right_rev' :
  forall (A B : Type) (f : A -> B -> A) (z : A) (l : list B),
    fold_left f l z =
    fold_right (fun x acc => f acc x) z (rev l).
Proof.
  intros A B f z l.
  revert z.
  induction l as [|x xs IH]; intros z.
  - simpl. reflexivity.
  - simpl. rewrite IH.
    (* Now goal:
       fold_right (fun x0 acc => f acc x0) (f z x) (rev xs)
         = fold_right (fun x0 acc => f acc x0) z (rev xs ++ [x]) *)
    rewrite fold_right_app. simpl.
    reflexivity.
Qed.

(* More general lemma: fold_left with cons and arbitrary initial accumulator *)
Lemma fold_left_cons_general : forall (A : Type) (l : list A) (acc : list A),
  fold_left (fun acc x => x :: acc) l acc =
  rev l ++ acc.
Proof.
  intros A l acc.
  revert acc.
  induction l as [|x xs IH]; intros acc.
  - (* Base case: l = [] *)
    simpl fold_left.
    simpl rev.
    simpl app.
    reflexivity.
  - (* Inductive case: l = x :: xs *)
    simpl fold_left.
    simpl rev.
    rewrite IH.
    (* Goal: (rev xs ++ [x]) ++ acc = rev xs ++ (x :: acc) *)
    (* Convert x :: acc to [x] ++ acc *)
    change (x :: acc) with ([x] ++ acc).
    (* Goal: (rev xs ++ [x]) ++ acc = rev xs ++ [x] ++ acc *)
    (* This is exactly app_assoc *)
    apply app_assoc.
Qed.

Theorem rev_fold_right_left :
  forall (A : Type) (l : list A),
    fold_left (fun acc x => x :: acc) l [] =
    rev (fold_right cons [] l).
Proof.
  intros A l.
  (* Use the general lemma with acc = [] *)
  rewrite fold_left_cons_general.
  (* Goal: rev l ++ [] = rev (fold_right cons [] l) *)
  rewrite app_nil_r.
  (* Goal: rev l = rev (fold_right cons [] l) *)
  (* Now I need to show that fold_right cons [] l = l *)
  assert (H: fold_right cons [] l = l).
  { induction l as [|x xs IH].
    - simpl. reflexivity.
    - simpl. rewrite IH. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Theorem rev_fold_left_right :
  forall (A : Type) (l : list A),
    fold_right cons [] l =
    rev (fold_left (fun acc x => x :: acc) l []).
Proof.
  intros A l.
  (* Use the general lemma with acc = [] *)
  rewrite fold_left_cons_general.
  (* Goal: rev l ++ [] = rev (fold_right cons [] l) *)
  rewrite app_nil_r.
  (* Goal: rev l = rev (fold_right cons [] l) *)
  (* Now I need to show that fold_right cons [] l = l *)
  assert (H: fold_right cons [] l = l).
  { induction l as [|x xs IH].
    - simpl. reflexivity.
    - simpl. rewrite IH. reflexivity. }
  rewrite H.
  rewrite rev_involutive.
  reflexivity.
Qed.

Theorem fold_left_as_fold_right :
  forall (A B : Type) (f : A -> B -> A) (l : list B) (z : A),
    fold_left f l z =
    fold_right (fun x g => fun a => g (f a x)) (fun a => a) l z.
Proof.
  intros A B f l.
  induction l as [|x xs IH]; intros z.
  - (* base case *)
    simpl. reflexivity.
  - (* inductive case *)
    simpl.
    rewrite IH.
    reflexivity.
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

(* Now let me try to prove the first element property for specific cases *)
Lemma tails_first_elem_is_input_singleton (x : nat) :
  exists rest, tails [x] = [x] :: rest.
Proof.
  unfold tails. simpl.
  exists [[]]. reflexivity.
Qed.

Lemma tails_first_elem_is_input_pair (x y : nat) :
  exists rest, tails [x; y] = [x; y] :: rest.
Proof.
  unfold tails. simpl.
  eexists. reflexivity.
Qed.

(* Alternative approach: define a recursive version of tails and prove equivalence *)
Fixpoint tails_rec {A : Type} (xs : list A) : list (list A) :=
  match xs with
  | [] => [[]]
  | x :: xs' => xs :: tails_rec xs'
  end.

(* DUAL VERSION: inits_rec function (dual of tails_rec) *)
Fixpoint inits_rec {A : Type} (xs : list A) : list (list A) :=
  match xs with
  | [] => [[]]
  | x :: xs' => [] :: map (cons x) (inits_rec xs')
  end.

(* Define the inits function using reverse and tails *)
Definition inits {A : Type}: list A -> list (list A) := fold_right (fun x => (cons []) ∘ map (cons x)) [[]].

Definition concat {A : Type} : list (list A) -> list A := @List.concat A.

Definition segs {A : Type} : list A -> list (list A) := concat ∘ map inits ∘ tails.

(* Dual version of segs: swap tails↔inits *)
Definition segs_dual {A : Type} : list A -> list (list A) := concat ∘ map tails ∘ inits_rec.

Lemma fold_right_tails_never_nil : forall {A : Type} (xs : list A),
  fold_right (fun x xsxss => match xsxss with 
                             | [] => [[]] 
                             | xs :: xss => (x::xs) :: (xs::xss) 
                             end) [[]] xs <> [].
Proof.
  intros A xs.
  induction xs as [| x xs' IH].
  - simpl. discriminate.
  - simpl. 
    destruct (fold_right _ [[]] xs') eqn:E.
    + (* If fold_right produced [], that contradicts IH *)
      exfalso. apply IH. reflexivity.
    + discriminate.
Qed.

Lemma fold_right_tails_cons : forall {A : Type} (x : A) (xs : list A),
  exists t ts, fold_right (fun x xsxss => match xsxss with 
                                          | [] => [[]] 
                                          | xs :: xss => (x::xs) :: (xs::xss) 
                                          end) [[]] xs = t :: ts.
Proof.
  intros A x xs.
  induction xs as [| y ys IH].
  - simpl. exists [], []. reflexivity.
  - simpl.
    destruct (fold_right _ [[]] ys) eqn:E.
    + pose proof (fold_right_tails_never_nil ys).
      contradiction.
    + exists (y :: l), (l :: l0). reflexivity.
Qed.

Lemma tails_rec_equiv : forall {A : Type} (xs : list A), tails xs = tails_rec xs.
Proof.
  intros A xs.
  induction xs as [| x xs' IH].
  
  - (* Base case: xs = [] *)
    simpl tails_rec.
    unfold tails. simpl.
    reflexivity.
    
  - (* Inductive case: xs = x :: xs' *)
    simpl tails_rec.
    unfold tails at 1.
    simpl fold_right.
    
    (* The key insight: fold_right on xs' produces tails xs' *)
    assert (Htails: fold_right (fun x xsxss => match xsxss with 
                                               | [] => [[]] 
                                               | xs :: xss => (x::xs) :: (xs::xss) 
                                               end) [[]] xs' = tails xs').
    { unfold tails. reflexivity. }
    
    rewrite Htails.
    rewrite IH.
    
    (* Now we need to show the pattern match on tails_rec xs' *)
    destruct xs' as [| y ys].
    
    + (* xs' = [] *)
      simpl.
      reflexivity.
      
    + (* xs' = y :: ys *)
      simpl tails_rec.
      reflexivity.
Qed.

Lemma tails_rec_equiv_ext : forall {A : Type} , @tails A = tails_rec.
Proof.
  intros A.
  apply functional_extensionality.
  apply tails_rec_equiv.
Qed.

(* DUAL VERSION: inits_rec_equiv lemma (dual of tails_rec_equiv) *)
Lemma inits_rec_equiv : forall {A : Type} (xs : list A), inits xs = inits_rec xs.
Proof.
  intros A xs.
  induction xs as [| x xs' IH].

  - (* Base case: xs = [] *)
    simpl inits_rec.
    unfold inits. simpl.
    reflexivity.

  - (* Inductive case: xs = x :: xs' *)
    simpl inits_rec.
    unfold inits at 1.
    simpl fold_right.

    (* The key insight: fold_right on xs' produces inits xs' *)
    assert (Hinits: fold_right (fun x => cons [] ∘ map (cons x)) [[]] xs' = inits xs').
    { unfold inits. reflexivity. }

    rewrite Hinits.
    rewrite IH.

    (* Now we need to show the pattern *)
    simpl.
    f_equal.
    reflexivity.
Qed.

Lemma inits_rec_equiv_ext : forall {A : Type} , @inits A = inits_rec.
Proof.
  intros A.
  apply functional_extensionality.
  apply inits_rec_equiv.
Qed.

(* Simple dual conversion lemma: rev of rev is identity *)
Lemma rev_rev_dual : forall {A : Type} (xs : list A), rev (rev xs) = xs.
Proof.
  intros A xs.
  apply rev_involutive.
Qed.


Lemma tails_cons : forall {A : Type} (x : A) (xs : list A),
  tails (x :: xs) = (x :: xs) :: tails xs.
Proof.
  intros A x xs.
  rewrite (tails_rec_equiv (x :: xs)).
  rewrite (tails_rec_equiv xs).
  simpl tails_rec.
  reflexivity.
Qed.

Lemma scan_right_singleton : forall {A B : Type} (f : A -> B -> B) (i : B) (x : A),
  scan_right f i [x] = [f x i; i].
Proof.
  intros A B f i x.
  simpl. reflexivity.
Qed.

Lemma scan_right_nil : forall {A B : Type} (f : A -> B -> B) (i : B),
  scan_right f i [] = [i].
Proof.
  intros A B f i.
  simpl. reflexivity.
Qed.

Lemma tails_nil : forall {A : Type}, tails (@nil A) = [[]].
Proof.
  intro A.
  unfold tails. simpl. reflexivity.
Qed.

Lemma tails_singleton : forall {A : Type} (x : A), tails [x] = [[x]; []].
Proof.
  intro A. intro x.
  unfold tails. simpl. reflexivity.
Qed.

Example scan_right_tails_example_nil : forall (f : nat -> nat -> nat) (i : nat),
  scan_right f i [] = map (fold_right f i) (tails []).
Proof.
  intros f i.
  rewrite scan_right_nil.
  rewrite tails_nil.
  simpl map.
  simpl fold_right.
  reflexivity.
Qed.

Example scan_right_tails_example_one (x : nat) (f : nat -> nat -> nat) (i : nat) :
  scan_right f i [x] = map (fold_right f i) (tails [x]).
Proof.
  rewrite tails_singleton.
  simpl map.
  simpl scan_right.
  simpl fold_right.
  reflexivity.
Qed.

Lemma tails_head_property : forall {A : Type} (xs : list A),
  xs <> [] -> exists rest, tails xs = xs :: rest.
Proof.
  intros A xs Hneq.
  (* Using the equivalence, we can reason about the simpler recursive definition. *)
  rewrite (tails_rec_equiv xs).
  (* Since xs is not empty, it must be of the form (x :: xs'). *)
  destruct xs as [|x xs'].
  - (* This case is impossible given xs <> []. *)
    contradiction.
  - (* The definition of tails_rec for a non-empty list is exactly what we need. *)
    simpl tails_rec.
    exists (tails_rec xs').
    reflexivity.
Qed.

Lemma scan_right_tails_fold : forall {A B : Type} (f : A -> B -> B) (i : B) (xs : list A),
  scan_right f i xs = map (fold_right f i) (tails xs).
Proof.
  intros A B f i xs.
  induction xs as [| x xs' IH]. 

  - (* Base case: xs = [] *)
    simpl.
    reflexivity.

  - (* Inductive case: xs = x :: xs' *)
    (* Expand scan_right on the left hand side. *)
    simpl scan_right.

    (* Use tails_cons to expand tails on the right hand side. *)
    rewrite (tails_cons x xs').

    (* Expand map on the right hand side. *)
    simpl map.

    (* The tails of both sides are now equal by the induction hypothesis. *)
    rewrite IH.
    (* The heads of both sides are definitionally equal. *)
    f_equal.
Qed.

Lemma scan_right_lemma : forall {A B : Type} (f : A -> B -> B) (i : B) (xs : list A),
  scan_right f i xs = map (fold_right f i) (tails_rec xs).
Proof.
  intros A B f i xs.
  induction xs as [| x xs' IH].

  - (* Base case: xs = [] *)
    reflexivity.

  - (* Inductive case: xs = x :: xs' *)
    (* Let's debug by doing step by step *)
    simpl scan_right.
    simpl tails_rec.
    simpl map.
    (* Now the goal should be:
       f x (fold_right f i xs') :: scan_right f i xs' =
       fold_right f i (x :: xs') :: map (fold_right f i) (tails_rec xs') *)
    (* Since fold_right f i (x :: xs') = f x (fold_right f i xs'),
       the goal becomes:
       f x (fold_right f i xs') :: scan_right f i xs' =
       f x (fold_right f i xs') :: map (fold_right f i) (tails_rec xs') *)
    f_equal.
    exact IH.
Qed.

(* DUAL VERSION: scan_left_lemma lemma (dual of scan_right_lemma) *)
Lemma scan_left_lemma : forall {A B : Type} (f : B -> A -> B) (xs : list A) (i : B),
  scan_left f xs i = map (fun prefix => fold_left f prefix i) (inits_rec xs).
Proof.
  intros A B f xs i.
  generalize dependent i.
  induction xs as [| x xs' IH]; intro i.

  - (* Base case: xs = [] *)
    reflexivity.

  - (* Inductive case: xs = x :: xs' *)
    simpl.
    f_equal.
    rewrite map_map.
    simpl.
    (* Now IH applies to any initial value *)
    apply IH.
Qed.
