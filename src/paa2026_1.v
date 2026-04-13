(* begin hide *)
Print nat.

Print nat_ind.
Print list.

Print list_ind.

Inductive mnat := x0:mnat | x1:mnat | S': mnat -> mnat| C: mnat -> mnat -> mnat.

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
(* end hide *)

(** * Diferentes definições de ordenação de listas *)
(*
Inductive SortedNat: list nat -> Prop :=
  | SortedNat_nil : SortedNat nil
  | SortedNat_cons : forall (a : nat) (l : list nat),
      (forall b : nat, In b l -> le a b) -> SortedNat l -> SortedNat (a :: l).

Inductive Sorted1': (nat -> nat -> Prop) -> list nat -> Prop :=
  | Sorted1_nil' : Sorted1' le nil
  | Sorted1_cons' : forall (a : nat) (l : list nat),
      (forall b : nat, In b l -> le a b) -> Sorted1' le l -> Sorted1' le (a :: l). *)

Inductive Sorted1 (A : Type) (R : A -> A -> Prop) : list A -> Prop :=
  | Sorted1_nil : Sorted1 _ R nil
  | Sorted1_cons : forall (a : A) (l : list A),
      (forall b : A, In b l -> R a b) -> Sorted1 _ R l -> Sorted1 _ R (a :: l).

Inductive Sorted2 (A : Type) (R : A -> A -> Prop) : list A -> Prop :=
| Sorted2_nil : Sorted2 _ R nil
| Sorted2_one : forall x, Sorted2 _ R (x::nil)
| Sorted2_cons : forall (a b: A) (l : list A),
      R a b -> Sorted2 _ R (b::l) -> Sorted2 _ R (a :: b :: l).

Definition Sorted3 (A: Type) (R: A -> A -> Prop) (l: list A) :=
  match (length l) with
  | 0 => True
  | 1 => True
  | _ => forall i j d, i < j -> j < length l -> R (nth i l d) (nth j l d)
  end.

Definition Sorted4 (A: Type) (R: A -> A -> Prop) (l: list A) :=
  match (length l) with
  | 0 => True
  | 1 => True
  | _ => forall i d, 0 <= i -> i < length l -> R (nth i l d) (nth (S i) l d)
  end.

From Stdlib Require Import Sorted.
Print Stdlib.Sorting.Sorted.Sorted.

(** ** Subprojeto 1: Equivalências entre diferentes definições de ordenação *)

(** Provar que [Sorted], [Sorted1], [Sorted2] e [Sorted3] são equivalentes. *)
(*
Theorem equiv_Sorted_Sorted1 (A: Type): forall R l, Sorted1 A R l -> Sorted2 A R l. 
Proof.
  
Admitted.
*)

(** * Diferentes definições de permutação de listas *)
(** ** Subprojeto 2: Equivalências entre diferentes definições de permutação *)

From Stdlib Require Import Permutation.
Print Permutation.

Fixpoint count_occ (x: nat) (l: list nat) : nat :=
  match l with
  | nil => 0
  | h::tl => if (h =? x)
             then S (count_occ x tl)
             else count_occ x tl
  end.

Definition Permutation_occ (l1 l2: list nat) : Prop :=
  forall x, count_occ x l1 = count_occ x l2.

Theorem equiv_Permutation_Permutation_occ: forall l1 l2, Permutation l1 l2 <-> Permutation_occ l1 l2.
Proof.
Admitted.

(** Provar que [Permutation] é equivalente a definição de permutação baseada na contagem de ocorrências. *)

(** * Formalização da correção do algoritmo de ordenação por inserção. *)

(** ** O algoritmo [insertion_sort] *)

Fixpoint insert x l :=
  match l with
  | nil => x::nil
  | h::tl => if (x <=? h)
             then x::h::tl
             else h::(insert x tl)
  end.

Eval compute in insert 3 (1::2::nil).
Eval compute in insert 3 (5::1::2::nil).

Fixpoint insertion_sort l :=
  match l with
  | nil => nil
  | h::tl => insert h (insertion_sort tl)
  end.

Eval compute in insertion_sort (3::1::nil).
Eval compute in insertion_sort (3::2::7::1::1::2::nil).

Theorem insertion_sort_correcao: forall (l: list nat), Sorted le (insertion_sort l) /\ Permutation (insertion_sort l) l.
Proof.
  induction l as [ | h tl].
  - split.
    + simpl. constructor.
    + simpl. constructor.
  - split.
    + simpl. constructor. 
    +
  
