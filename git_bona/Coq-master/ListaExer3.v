From LF Require Export Tactics.


Theorem combine_split' : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [ | [x y] l'].
  - intros l1 l2 H. simpl in H. injection H as H1 H2.
  rewrite <- H1. rewrite <- H2. reflexivity.
  - intros l1 l2 H. simpl in H. destruct (split) as [ t1 t2 ].
  inversion H. simpl. rewrite IHl'.
    + reflexivity.
    + reflexivity.
Qed.

Theorem split_combine' : forall X Y (l1 : list X) (l2 : list Y) (l : list (X*Y)),
  length l1 = length l2 -> combine l1 l2 = l -> split l = (l1, l2).
Proof.
  intros X Y l1 l2 l. generalize dependent l1. generalize dependent l2.
  induction l as [| h t IHl].
  - intros l1 l2 H1 H2. destruct l1 as [| h1 t1].
    + simpl in H1. destruct l2.
      * simpl. reflexivity.
      * rewrite <- H2. inversion H1.
    + simpl. destruct l2 as [| h2 t2].
      * inversion H1.
      * inversion H1. inversion H2.
  - intros l1 l2 H1 H2. destruct l1 as [| h1 t1].
    + destruct l2.
      * inversion H2.
      * inversion H2.
    + destruct l2. 
      * inversion H2.
      * simpl. inversion H1. simpl. inversion H2. rewrite H4. destruct split as [g j]. inversion H2.
inversion H2. rewrite H0. rewrite H3. apply IHl in H1. 
rewrite <- H1. rewrite <- H3. rewrite <- H3 in H2. simpl in H2. discriminate H1. rewrite <- H2. rewrite <- H3. rewrite H3. 
rewrite H2. simpl in H2. rewrite H3 in H2. rewrite <- H2. 

rewrite H3. rewrite H3 in H2. rewrite H2. destruct split as [a b].  inversion H0. rewrite H.  
    Abort.