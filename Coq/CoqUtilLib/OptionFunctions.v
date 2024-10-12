Require Import Coq.Init.Datatypes.

(* Refs: NONE *)
Definition option_join {A: Type} : option (option A) -> option A := fun mmx => match mmx with
  | None => None
  | Some mx => match mx with
    | None => None
    | Some x => Some x
  end
end.

(* Refs:
 - option_map_2 -> (* Refs: NONE *)
*)
Definition option_apply {A B: Type} : option (A -> B) -> option A -> option B := fun mf mx => match mf with
  | None => None
  | Some f => option_map f mx
  end.

(* Refs: NONE *)
Definition option_map_2 {A B C : Type} : (A -> B -> C) -> option A -> option B -> option C := fun op mx my => option_apply (option_map op mx) my.

Definition liftOptionOpWithNoneID {A: Type} : (A -> A -> A) -> option A -> option A -> option A := fun op mx my => match mx with
  | None => match my with
    | None => None
    | Some y => Some y
  end
  | Some x => match my with
    | None => Some x
    | Some y => Some (op x y)
  end
end.

(* Refs: NONE *)
Definition fromSome {A : Type} (opt : option A) : opt <> None -> A :=
  match opt with
  | Some a => fun _ => a
  | None => fun H => False_rect _ (H eq_refl)
  end.
