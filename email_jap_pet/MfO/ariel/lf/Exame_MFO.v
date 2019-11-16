(* Exame Métodos Formais 
   Nome:  Ariel Agne da Silveira*)

Require Import PeanoNat.

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Arguments nil {X}.
Arguments cons {X} _ _.


Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | [] => 0
  |  _ :: l' => S (length l')
  end.

Fixpoint index {X : Set} (n : nat) (l : list X) : option X :=
  match l with
  | [] => None
  | h :: t => if n =? 0 then Some h else index (pred n) t
  end. 

Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

Fixpoint repeat {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat x count')
  end.

(* Questão 1 *)

Theorem repeat_n : forall {X:Set} (n:nat) (x:X),
  length (repeat x n) = n.
Proof. 
  intros. induction n.
  - auto.
  - simpl. rewrite IHn. auto.
Qed.

(* Alguns Teoremas uteis envolvendo <=
Theorem le_pred : forall n m, n <= m -> pred n <= pred m.
Theorem le_S_n  : forall n m, S n <= S m -> n <= m.
Theorem le_0_n  : forall n, 0 <= n.
Theorem le_n_S  : forall n m, n <= m -> S n <= S m. *)

(* Questão 2 *)

Theorem repeat_index : forall {X:Set} (x:X) (i:nat) (n:nat) ,
  i <= n -> index i (repeat x (S n)) = Some x.
Proof.
  intros. induction n.
  -  induction i.
    + auto.
    + inversion H.
  - induction i.
    + auto.
    + 

  Admitted.

(* Questão 3 *) 

Theorem index_map : forall {X Y:Set} (n:nat) (f:X->Y) (l:list X) (x:X), 
  index n l = Some x -> Some (f x) = index n (map f l).
Proof.
  intros. induction l.
  - inversion H.
  - inversion H.
  Admitted.

(* Questão 4 *)

Theorem len_index_none : forall {X : Set} (n : nat) (l : list X), 
  length l = n -> index n l = None.
Proof.
  induction l.
  - intros. auto.
  - intros. 
  Admitted.


    