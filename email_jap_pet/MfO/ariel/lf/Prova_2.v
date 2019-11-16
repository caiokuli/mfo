(* Segunda Prova Métodos Formais
   Nome: Ariel Agne da Silveira*)

(* Não é permitido importar nenhuma biblioteca, qualquer lema 
   ou teorema auxiliar deve ser desenvolvido (provado) nesse 
   arquivo *)


(* No Capítulo [IndProp] é apresentado um tipo indutivo ([even]) que 
   constroi uma prova que um número natural é par: *)

Inductive even : nat -> Prop :=
| ev_0 : even 0
| ev_SS (n : nat) (H : even n) : even (S (S n)).

(* Um tipo indutivo alternativo ([le']) para provar que um número 
   natural é menor ou igual a outro pode ser definido como: *)

Inductive le' : nat -> nat -> Prop :=
  | le_0' m : le' 0 m
  | le_S' n m (H : le' n m) : le' (S n) (S m).

(* Usando esses tipos indutivos prove os teoremas abaixo: *)

(* Questão 1 *)
Lemma le'_n_Sm : forall a b, le' a b -> le' a (S b). 
Proof.
  intros. induction a.
  - apply le_0'.
  - inversion H. apply le_S'.
    + apply le_0'.
    + apply le_S'. apply IHle'. intros.
Admitted.

(* Questão 2 *)
Theorem n_le'_m__Sn_le'_Sm : forall a b, le' a b -> le' (S a) (S b).
Proof.
  intros. apply le_S'. apply H.
Qed.

(* Questão 3 *)
Theorem le_le' : forall a b, le a b <-> le' a b.
Proof.
  split.
  - intros. induction a.
    + apply le_0'.
    + 
  Admitted.

(* Questão 4 *)
Theorem ev_ev__ev : forall n m,
  even (n + m) -> even n -> even m.
Proof.
  intros. induction H0.
  - simpl in H. apply H.
  - inversion H. apply IHeven. apply H2.
Qed.