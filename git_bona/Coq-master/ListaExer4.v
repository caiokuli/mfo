
(* Alunos: Gustavo Miquelluzzi Bonassa e Victor Karnopp Neitzel *)

From LF Require Export Logic.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split.
  - intros [H1 | [H2 H3]].
    + split.
      * left. apply H1.
      * left. apply H1.
    + split.
      * right. apply H2.
      * right. apply H3.
  - intros [[H1 | H2] [H3 | H4]].
    + left. apply H1.
    + left. apply H1.
    + left. apply H3.
    + right. split. apply H2. apply H4.
Qed.

Theorem dist_exists_and : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x /\ Q x) -> (exists x, P x) /\ (exists x, Q x).
Proof.
  intros X P Q H. split.
    + destruct H. exists x. apply H.
    + destruct H. exists x. apply H.
Qed.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  induction l as [|x' l'].
  - simpl. intros [].
  - simpl. intros [H | H].
    + exists x'. split. apply H. left. reflexivity.
    + apply IHl' in H. destruct H as [t [F I]].
      exists t. split. apply F. right. apply I.
  - intros [w [F I]].
    rewrite <- F. apply In_map. apply I.
Qed.

Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros. split.
  - induction l as [|c b].
    + simpl. intro. right. apply H.
    + simpl. intros [H | H].
      * left. left. apply H.
      * apply IHb in H. destruct H.
        left. right. apply H.
        right. apply H.
  - induction l as [|b c].
    + intros [H | H].
      * inversion H.
      * simpl. apply H.
    + intros [H | H].
      * simpl. inversion H. 
        left. apply H0.
        right. apply IHc. left. apply H0.
      * simpl. right. apply IHc. right. apply H.
Qed.

(* Inspirado na função [In], defina uma função [All] que é válida quando
uma proposição [P] é válida para todos elementos de uma lista [l]: *) 

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
    | [] => True
    | x::xs => P x /\ All P xs
  end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros. split.
  - induction l as [|a b].
    + reflexivity.
    + intros. simpl. split.
      * apply H. simpl. left. reflexivity.
      * apply IHb. intros. apply H. simpl. right. apply H0.
  - induction l as [|h t].
    + intros. inversion H0.
    + intros. simpl in H0. simpl in H.
      destruct H as [H1 H2].
      destruct H0 as [H3 | H4].
      * rewrite <- H3. apply H1.
      * apply IHt. apply H2. apply H4.
Qed.

  

