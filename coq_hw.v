From Coq Require Import List Arith.
Import ListNotations.

(* Arithmetic expressions language *)
Inductive expr : Type :=
| Const : nat -> expr
| Plus : expr -> expr -> expr
| Minus : expr -> expr -> expr.

(* Semantics of arithmetic expressions *)
Fixpoint eval (e : expr) : nat :=
  match e with
  | Const n => n
  | Plus e1 e2 => eval e1 + eval e2
  | Minus e1 e2 => eval e1 - eval e2
  end.

(* Stack machine instructions *)
Inductive instr :=
| Push : nat -> instr
| Add
| Sub.

(* Stack programs *)
Definition prog := list instr.

(* Stack *)
Definition stack := list nat.

(* Stack machine semantics *)
Fixpoint run (p : prog) (s : stack) {struct p}: stack :=
  match p with
  | [] => s
  | i :: p' =>
    match i with
    | Push n => run p' (n :: s)
    | Add =>
      match s with
      | a :: b :: s' => run p' (b + a :: s')
      | _ => [] (* if stack underflow -- interrupt
                   execution and return empty stack *)
      end
    | Sub =>
      match s with
      | a :: b :: s' => run p' (b - a :: s')
      | _ => [] (* if stack underflow -- interrupt
                   execution and return empty stack *)
      end
    end
  end.

(* Compilation from arithmetic expressions
   into stack programs *)
Fixpoint compile (e : expr) : prog :=
  match e with
  | Const n => [Push n]
  | Plus e1 e2 =>
    compile e1 ++ compile e2 ++ [Add]
  | Minus e1 e2 =>
    compile e1 ++ compile e2 ++ [Sub]
  end.

Lemma run_concat (p1 : prog) (p2 : prog) (s : stack) :
  run p1 s <> [] -> (run (p1 ++ p2) s = run p2 (run p1 s)).
Proof.
  revert s; induction p1; intros s.
  - reflexivity.
  - destruct a; simpl.
    + apply IHp1.
    + destruct s.
      * contradiction.
      * destruct s.
        ** contradiction.
        ** apply IHp1.
    + destruct s.
      * contradiction.
      * destruct s.
        ** contradiction.
        ** apply IHp1.
Qed.

Lemma run_has_result (e : expr) (s : stack) :
  exists a, run (compile e) s = a :: s.
Proof.
  revert s; induction e; intros s; simpl.
  - exists n.
    reflexivity. 
  - rewrite ?run_concat; destruct (IHe1 s); rewrite H.
    + destruct (IHe2 (x :: s)).
      rewrite H0. 
      simpl.
      exists (x + x0).
      reflexivity.
    + destruct (IHe2 (x :: s)).
      rewrite H0. 
      easy.
    + easy.
  - rewrite ?run_concat; destruct (IHe1 s); rewrite H.
    + destruct (IHe2 (x :: s)).
      rewrite H0.
      simpl.
      exists (x - x0).
      reflexivity. 
    + destruct (IHe2 (x :: s)).
      rewrite H0. 
      easy.
    + easy.
Qed.

Lemma run_of_compile_is_not_empty (e : expr) (s : stack) :
  run (compile e) s <> [].
Proof.
  destruct (run_has_result e s) as [a rc]; rewrite rc; discriminate.
Qed.

Lemma compile_correct_gen (e : expr) (s : stack) : 
  eval e :: s = run (compile e) s.
Proof.
  revert s.
  induction e; simpl; intros s.
  - reflexivity.
  - rewrite ?run_concat.
    rewrite <- IHe1.
    rewrite <- IHe2.
    simpl.
      * reflexivity.
      * apply run_of_compile_is_not_empty.
      * apply run_of_compile_is_not_empty.
  - rewrite ?run_concat.
    rewrite <- IHe1.
    rewrite <- IHe2.
    simpl.
      * reflexivity.
      * apply run_of_compile_is_not_empty.
      * apply run_of_compile_is_not_empty.
Qed.

Theorem compile_correct :
  forall e, [eval e] = run (compile e) [].
Proof.
  intros e.
  apply compile_correct_gen.
Qed.