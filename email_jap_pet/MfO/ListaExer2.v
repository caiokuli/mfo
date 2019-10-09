(*Guilherme Utiama e Peter Brendel*)
From LF Require Export Tactics.

Check map.

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
map f l. (*fold (fun x xs => (f x) :: xs) l [].*)

Example test_fold_map : fold_map (mult 2) [1; 2; 3] = [2; 4; 6].
Proof. reflexivity.
Qed. 

Theorem fold_map_correct : forall X Y (f: X -> Y) (l: list X),
  fold_map f l = map f l.
Proof. 
  intros. induction l.
  - simpl. reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intro n. induction n.
  - simpl. intros m. destruct m.
    + reflexivity.
    + simpl. intros que. discriminate que.
  - intros m. destruct m.
    + intros que. discriminate que.
    + intros que. injection que as q. rewrite <- plus_n_Sm in q.
      rewrite <- plus_n_Sm in q. injection q as qu.
      apply IHn in qu. rewrite qu. reflexivity.
Qed.

Theorem combine_split' : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [|h t].
  - intros l1 l2 H. simpl in H.  injection H as H1 H2. rewrite <- H1.
    rewrite <- H2. simpl. reflexivity.
  - intros l1 l2. simpl. destruct h. destruct (split t). destruct l1.
    + simpl. induction l2.
      * intros con. inversion con.
      * intros con. inversion con.
    + induction l2.
      * simpl. intros con. inversion con.
      * simpl. intros e. inversion e. simpl. rewrite IHt. reflexivity. 
        rewrite H1. rewrite H3. reflexivity.
Qed. 
    

Theorem split_combine' : forall X Y (l1 : list X) (l2 : list Y) (l : list (X*Y)),
  length l1 = length l2 -> combine l1 l2 = l -> split l = (l1, l2).
Proof.
  intros X Y l1 l2 l. generalize dependent l1. generalize dependent l2.
  induction l as [| h t IHl].
  - intros l1 l2 H1 H2. destruct l1 as [| h1 t1].
    + simpl. inversion H1. induction l2.
      * reflexivity.
      * inversion H0. 
    + simpl. induction l2. simpl. 
      * inversion H1.
      *  inversion H2.
  - intros. destruct l2, l1.
    + discriminate H0.
    + discriminate H0.
    + discriminate.
    + simpl in H0. injection H0 as H0. apply IHl in H1. simpl. destruct h.
      destruct (split t). injection H0 as H0. rewrite H0. rewrite H2. injection H1 as H10.
      rewrite H1. rewrite H10. reflexivity.
      * inversion H. reflexivity.
Qed.