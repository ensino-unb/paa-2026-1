Print nat.

Print nat_ind.

Print list.

Print list_ind.

Inductive mnat := x0:mnat | x1:mnat | S: mnat -> mnat| C: mnat -> mnat -> mnat.

Print mnat.

Print mnat_ind.

(** Construa um programa que, dado um número natural x e uma lista l de números naturais, retorne true se x ocorre em l, e f alse caso contrário. *)

From Stdlib Require Import Arith.
From Stdlib Require Import List.

Fixpoint busca_bool (x:nat) (l:list nat) : bool :=
  match l with
  | nil => false
  | h::tl => if (h =? x)
             then true
             else busca_bool x tl
  end.

(** Para qualquer lista de números naturais l, o algoritmo busca_bool(x, l) retorna true se x ocorre em l, e false, caso contrário.
*)

Theorem busca_bool_correto: forall l x, (In x l -> busca_bool x l = true) /\ (~ In x l -> busca_bool x l = false).
Proof.
  induction l as [ | h tl].
  - intro x. split.
    + intro H. simpl in H. inversion H.
    + intro H. simpl. reflexivity.
  - intro x. split.
    + intro H. simpl. case (h =? x) eqn: Heq.
      * reflexivity.
      * simpl in H. destruct H as [H | H].
        ** apply Nat.eqb_neq in Heq. contradiction.
        ** apply IHtl. exact H.
    + intro H. simpl. simpl in H.  apply Decidable.not_or in H. destruct H. case (h =? x) eqn: Heq.
      *  apply Nat.eqb_eq in Heq. contradiction.
      * apply IHtl. assumption.
Qed.

