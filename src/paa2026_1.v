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

(** Para qualquer lista l e valor x, o algoritmo busca_bool(x, l) retorna true se, e somente se, x ocorre em l.
*)

Theorem busca_bool_correto: forall l x, (busca_bool x l = true) <-> In x l.
Proof.
  induction l as [ | h tl].
  - intro x. split.
    + intro H. simpl in H. inversion H.
    + intro H. simpl in H. contradiction.
  - intro x. split.
    + intro H. simpl in *. case (h =? x) eqn: Heq.
      * left. apply Nat.eqb_eq. assumption.
      * apply IHtl in H. right. assumption.
    + intro H. simpl in *. destruct H as [Heq | Hin].
      * subst. rewrite Nat.eqb_refl. reflexivity.
      * case (h =? x) eqn: Hhx.
        ** reflexivity.
        ** apply IHtl. assumption. 
Qed.

