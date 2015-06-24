Require Import String Ring Omega Arith.

Inductive exp : Set :=
(* | Var : string -> exp *)
| Num : nat -> exp
| Plus : exp -> exp -> exp
| Times : exp -> exp -> exp.

Fixpoint eval (e : exp) (env : (string -> nat)) : nat :=
  match e with
  (* | Var x => env x *)
  | Num n => n
  | Plus a b => (eval a env) + (eval b env)
  | Times a b => (eval a env) * (eval b env)
  end.


Fixpoint eval' (e : exp) : nat :=
  match e with
  (* | Var x => env x *)
  | Num n => n
  | Plus a b => (eval' a) + (eval' b)
  | Times a b => (eval' a) * (eval' b)
  end.




Ltac t := intros; simpl;
          repeat (match goal with
                  | [ |- context [ match ?X with _ => _ end ] ] => destruct X eqn:?
                  | [ H : _ = _ |- _ ] => rewrite H
                  end; simpl; try ring).


Fixpoint optimize (e : exp) : exp :=
  match e with
  | Plus (Num a) (Num b) => Num (a + b)
  | Plus a b => Plus (optimize a) (optimize b)
  | Times a b => Times (optimize a) (optimize b)
  | _ => e
  end.


Theorem optimize_safe : forall (e : exp), eval' e = eval' (optimize e).
Proof.
  intros. induction e.
  (* Num *)
  simpl. reflexivity.
  (* Plus e1 e2 *)
  destruct e1, e2; simpl; intuition.
  (* Times e1 e2 *)
  simpl. intuition.
Qed.


Fixpoint optimize' (e : exp) : exp :=
  match e with
  | Plus (Num a) (Num b) => Num (a + b)
  | Plus (Num 0) b => optimize' b
  | Plus a b => Plus (optimize' a) (optimize' b)
  | Times a b => Times (optimize' a) (optimize' b)
  | _ => e
  end.


Theorem optimize_safe' : forall (e : exp), eval' e = eval' (optimize' e).
Proof.
  intros. induction e; try destruct e1, e2; try destruct n; simpl; intuition.
Qed.
