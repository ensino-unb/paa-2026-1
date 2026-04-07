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

(** Ordenação por inserção. *)

Fixpoint insert x l :=
  match l with
  | nil => x::nil
  | h::tl => if (x <=? h)
             then x::h::tl
             else h::(insert x tl)
  end.

Fixpoint insertion_sort l :=
  match l with
  | nil => nil
  | h::tl => insert h (insertion_sort tl)
  end.

Eval compute in insertion_sort (3::1::nil).
Eval compute in insertion_sort (3::2::7::1::nil).

Inductive Sorted (A : Type) (R : A -> A -> Prop) : list A -> Prop :=
  | Sorted_nil : Sorted _ R nil
  | Sorted_cons : forall (a : A) (l : list A),
      (forall b : A, In b l -> R a b) -> Sorted _ R l -> Sorted _ R (a :: l).

Inductive Sorted' (A : Type) (R : A -> A -> Prop) : list A -> Prop :=
| Sorted_nil' : Sorted' _ R nil
| Sorted_one' : forall x, Sorted' _ R (x::nil)
| Sorted_cons' : forall (a b: A) (l : list A),
      R a b -> Sorted' _ R (b::l) -> Sorted' _ R (a :: b :: l).


Theorem equiv_Sorted_Sorted' (A: Type): forall R l, Sorted A R l <-> Sorted' A R l. 
Proof.
Admitted.

From Stdlib Require Import Permutation.

Print Permutation.

Theorem insertion_sort_correto: forall l, sorted (insertion_sort l) /\ permutation (insertion_sort l) l.
