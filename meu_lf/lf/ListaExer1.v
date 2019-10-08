(** * M\u00e9todos Formais Lista de Exerc\u00edcios 1 *)

(*// Aluno : Caio Alexandre Kulicheski *)
From LF Require Export Induction.

(** Prove usando Coq que $\Sigma_{i=0}^{n}i = (n^2 + n)/2$ ([sum_n]). 
    No desenvolvimento desse exerc\u00edcio ser\u00e3o necess\u00e1rias algumas defini\u00e7\u00f5es 
    feitas nos m\u00f3dulos [Basics.v] e [Induction.v] s\u00e3o elas: [plus_n_O], 
    [plus_assoc], [plus_comm], [mult_comm] e [mult_S]. *)

(** A fun\u00e7\u00e3o somat\u00f3rio de n\u00fameros naturais de 0 at\u00e9 $n$ pode ser implementada 
    como: *)

Fixpoint sum (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n + sum n'
  end.

(** Com objetivo de simplificar as provas a fun\u00e7\u00e3o [div2] implementa a 
    divis\u00e3o por 2. *) 

Fixpoint div2 (n:nat) : nat :=
  match n with
  | O => O
  | S O => O 
  | S (S n') => S (div2 n')  
end.  


Lemma plus_n_0 : forall (n: nat),
  n + 0 = n.
Proof. intros n. induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity. Qed.



Theorem plus_n_1 : forall (n : nat),
  n + 1 = S (n).  
Proof. 
 intros n. induction n as [| n' IH].
  -reflexivity. 
  -simpl. rewrite IH. reflexivity .
 Qed.


Theorem plus_n_Sm : forall (n m:nat),
  n + S m = S (n + m).
Proof.
  intro n.
  intro m.  
  induction n as [| n' IH].
  simpl. reflexivity.
  simpl. rewrite IH. reflexivity.
  Qed.

Theorem mult_2_n_plus : forall (n : nat),
  n + n = 2 * n.
Proof.
  intro n.
  induction n as [| n' IH].
  - simpl. reflexivity.
  -simpl. rewrite plus_n_Sm.
  rewrite IH.
  simpl. rewrite plus_n_Sm. reflexivity.
  Qed.

Theorem mult2_div2 : forall n : nat,
  n = div2 (2 * n).
Proof.
intro n.
induction n as [| n' IH].
 - simpl. reflexivity.
 - rewrite  -> IH.
  simpl. rewrite plus_n_0. rewrite plus_n_Sm.
  rewrite mult_2_n_plus. 
 rewrite <- IH. 
 rewrite plus_n_0. 
  rewrite mult_2_n_plus.
  rewrite <- IH.  
 reflexivity. 
Qed.

Theorem div2_mult2_plus: forall (n m : nat),
  n + div2 m = div2 (2 * n + m).
Proof.
intros n m.
induction n as [| n' IH].
simpl. reflexivity.
-simpl. rewrite plus_n_0.
  rewrite plus_n_Sm.
  rewrite mult_2_n_plus.
 simpl. rewrite plus_n_0.
  rewrite mult_2_n_plus.
  rewrite IH. reflexivity.
Qed.

Theorem mult_Sn_m : forall (n m : nat),
  S n * m = m + n * m.
  Proof.
  intros n m.
  simpl.
  reflexivity.  
Qed.

Theorem sum_Sn : forall n : nat,
  sum (S n) = S n + sum n.
Proof.
  intro n.
  simpl.
 reflexivity.
  Qed.

Theorem sum_n : forall n : nat,
  sum n = div2 (n * (n + 1)).
Proof.
 intros n. induction n as [| x' IH].
 - simpl. reflexivity.
  - simpl. rewrite plus_n_1. rewrite mult_comm. rewrite mult_Sn_m. simpl. rewrite <- mult_Sn_m. rewrite plus_assoc.
    rewrite mult_2_n_plus. rewrite <- div2_mult2_plus. rewrite mult_comm. rewrite -> plus_n_1 in IH. rewrite IH. 
    reflexivity. Qed
