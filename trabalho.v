(* Trabalho Métodos Formais 
   Equipe (nomes):Caio Alexandre Kulicheski  e Mateus Tavares *)
   
(* Todas as definições necessárias devem estar neste arquivo. *)

(* Prove os cinco teoremas abaixo em Coq, para os teoremas 1, 2, 3 e 4
   também deve ser fornecida uma versão não mecanizada da prova escrita
   a mão. *)

Require Setoid.
Require Import Coq.Init.Logic.
Require Import Notations.
Require Import Relation_Operators.
Require Import Transitive_Closure.

Module ListNotations.
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.
End ListNotations.
Import ListNotations.

Inductive reg_exp {T : Type} : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp)
  | Union (r1 r2 : reg_exp)
  | Star (r : reg_exp).

Inductive exp_match {T} : list T -> reg_exp -> Prop :=
  | MEmpty : exp_match [] EmptyStr
  | MChar x : exp_match [x] (Char x)
  | MApp s1 re1 s2 re2
             (H1 : exp_match s1 re1)
             (H2 : exp_match s2 re2) :
             exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : exp_match s1 re1) :
                exp_match s1 (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : exp_match s2 re2) :
                exp_match s2 (Union re1 re2)
  | MStar0 re : exp_match [] (Star re)
  | MStarApp s1 s2 re
                 (H1 : exp_match s1 re)
                 (H2 : exp_match s2 (Star re)) :
                 exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re) (at level 80).

(* Teorema 1: Comutatividade do operador de união: *)


Theorem union_comm : forall T (s: list T) (r1 r2 : reg_exp),
  s =~ Union r1 r2 -> s =~ Union r2 r1.
Proof.
  intros. inversion H.
  - apply MUnionR. apply H2.
  - apply MUnionL.  apply H1.
  Qed.

(* Teorema 2: Idempotência do operador de união: *)

Theorem union_idem : forall T (s: list T) (r : reg_exp), 
  s =~ r <-> s =~ Union r r.
Proof. 
  intros. split.
  - intros. apply MUnionL. apply H.
  - intros. inversion H. apply H2. apply H1.  
  Qed.

(* Teorema 3: Associatividade do operador de união: *)

Theorem union_assoc : forall T (s : list T) (r1 r2 r3 : reg_exp),
  s =~ Union (Union r1 r2) r3 <-> s=~ Union r1 (Union r2 r3).
Proof.
  intros. split.
  - intros. inversion H. 
  -- inversion H2. 
  + apply MUnionL. apply H6.
  + apply MUnionR. apply MUnionL. apply H6.
  -- apply MUnionR. apply MUnionR. apply H1.

  - intros. inversion H.
  -- apply MUnionL. apply MUnionL. apply H2.
  -- inversion H1.
  ++ apply MUnionL. apply MUnionR. apply H6.
  ++ apply MUnionR. apply H6.
  Qed.

(* Teorema 4: Distributividade da concatenação sobre a união: *)
Theorem union_dist_app : forall T (s : list T) (r1 r2 r3 : reg_exp),
  s =~ App r1 (Union r2 r3) <-> s =~ Union (App r1 r2) (App r1 r3).
Proof.
  intros. split. 
  + intros . inversion H. inversion H4.
  - apply MUnionL. apply MApp.
   -- apply H3.
   -- apply H7.
  - apply MUnionR. apply MApp.
    -- apply H3.
    -- apply H7.
  + intros. inversion H. inversion H2. 
    - apply MApp. 
    -- apply H7.
    -- apply MUnionL. apply H8.
    - inversion H1. apply MApp. apply H7. apply MUnionR. apply H8. 
  Qed.


Fixpoint re_not_empty {T : Type} (re : @reg_exp T) : bool :=
  match re with
    | EmptySet => false
    | EmptyStr => true
    | Char _ => true
    | App re1 re2 => andb (re_not_empty re1) (re_not_empty re2)
    | Union re1 re2 => orb (re_not_empty re1) (re_not_empty re2)
    | Star re1 => true
end.



(* Teorema 5: *)
Theorem re_not_empty_correct : forall T (re : @reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros. split.
    + intros. induction H. induction H.
     - simpl. reflexivity.
     - simpl. reflexivity.
     - simpl. rewrite IHexp_match1. rewrite IHexp_match2. simpl. reflexivity.
     - simpl. rewrite IHexp_match. simpl. reflexivity.
     - simpl. rewrite IHexp_match. destruct (re_not_empty re1).
        simpl. reflexivity. simpl. reflexivity.
     - simpl. reflexivity.
     - apply IHexp_match2.
    + intros. induction re.
      - discriminate H.
      - exists nil. apply MEmpty.
      - exists (cons t nil). apply MChar.
      - simpl in H. 
          assert (re_not_empty re1 = true). 
          { induction (re_not_empty re1). reflexivity. discriminate H. }
          assert (re_not_empty re2 = true). 
          {rewrite H0 in H. induction (re_not_empty re2). reflexivity. discriminate H. }
       apply IHre1 in H0. apply IHre2 in H1. induction H0. induction H1.
       exists (app x x0). apply MApp. apply H0. apply H1.
      - simpl in H. assert  (re_not_empty re1 = true \/ re_not_empty re2 = true). 
      {induction (re_not_empty re1). left. reflexivity. induction (re_not_empty re2). right.
      reflexivity. discriminate H. } destruct H0. 
        -- apply IHre1 in H0. induction H0. exists x. apply MUnionL. apply H0.
        -- apply IHre2 in H0. induction H0. exists x. apply MUnionR. apply H0.
      - exists nil. apply MStar0.
Qed.
