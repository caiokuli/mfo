From LF Require Export Tactics.
(*ALuno : Caio Alenxadre Kulicheski*)
Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
 fold (fun x rest => (f x) :: rest) l [].

Example test_fold_map : fold_map (mult 2) [1; 2; 3] = [2; 4; 6].

Proof.
simpl. intros. reflexivity.
 Qed. 

Theorem fold_map_correct : forall X Y (f: X -> Y) (l: list X),
  fold_map f l = map f l.
Proof. 
  intros. simpl. unfold fold_map.
  unfold fold. induction l.
  -  simpl. reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Check plus_1_l.

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
intros n. induction n.
  - intros . destruct m. reflexivity. discriminate.
  - intros m H. destruct m. discriminate.
   simpl in H. rewrite <- plus_n_Sm in H. symmetry in H. rewrite <- plus_n_Sm in H. symmetry in H.
    injection H as H2. apply IHn in H2. rewrite H2. reflexivity.
Qed.




Theorem combine_split' : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [|h t IH1].
  
- intros l1 l2 H. simpl in H. injection H as H1 H2.
  unfold combine. simpl. rewrite <- H1. reflexivity. 
- destruct h as [h1 h2]. simpl. destruct (split t).
  intros l1 l2 H. injection H  as H1 H2.
  rewrite <- H1. rewrite <- H2. simpl.
  assert ( Hc : combine x y = t). { apply IH1. reflexivity. }
  rewrite Hc. reflexivity.
 Qed.

Theorem split_combine' : forall X Y (l1 : list X) (l2 : list Y) (l : list (X*Y)),
  length l1 = length l2 -> combine l1 l2 = l -> split l = (l1, l2).
Proof.
  intros X Y l1 l2 l. generalize dependent l1. generalize dependent l2.
  induction l as [| h t IHl].
  - intros l1 l2 H1 H2.  destruct l1 as [| h1 t1].
  + simpl in H1. destruct l2. 
  ++ reflexivity.
  ++ rewrite <- H2. inversion H1.
  + simpl.
Abort.
 


















