(* Fixpoint EQ (m n:nat) : Prop := *)
  (* match m,n with *)
  (* | 0, 0 => True *)
  (* | S _, 0 => False *)
  (* | 0, S _ => False *)
  (* | S m',S n'=> EQ m' n' *)
  (* end. *)

Definition EQ : nat -> nat -> Type :=
  fun (m:nat) =>
    nat_rect (fun _ => nat -> Type)
             (fun (n:nat) =>
                nat_rect
                  (fun _ => Type)
                  True
                  (fun _ _ => False)
                  n)
             (fun n IH =>
                (fun (n:nat) =>
                   nat_rect
                     (fun _ => Type)
                     False
                     (fun n' IH' => IH n')
                     n))
             m.

(* Theorem X : forall x, EQ x x. *)
(* Proof. *)
(*   intro x. *)
(*   induction x. *)
(*   simpl. trivial. *)
(*   simpl. assumption. *)
(* Defined. *)



Definition X : forall x, EQ x x :=
  fun x => nat_rect (fun n => EQ n n)
                    I
                    (fun n IH => IH)
                    x.
