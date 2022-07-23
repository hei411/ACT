Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.
Require Import Coq.Unicode.Utf8.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.FunctionalExtensionality.

Fixpoint exist_set{A:Type} (x:A) (s:set A):Prop :=
    match s with 
        | nil => False
        | x' ::xs => (x' = x) \/ exist_set x xs
        end.

Fixpoint forall_set {A:Type} (s:set A) (f:A->Prop) :Prop :=
    match s with 
        | nil => True
        | x :: xs => f x /\ (forall_set xs f)
        end.

Definition subset_set {A:Type} (s s' :set A):Prop := 
        forall_set s (fun a:A => In a s').

Definition equals_set {A:Type } (s s':set A):Prop := 
    subset_set s s'/\ subset_set s' s.

Axiom equals_implies_equality: forall (A:Type) (s s':set A), equals_set s s' -> s=s'.

Definition closed_containment {A:Type} (V:set A)(C:set (set A)):Prop:=
     forall_set C (fun X: set(A)=> forall (Y:set(A)), subset_set Y X -> In Y C).

Definition uni_covering {A:Type} (V:set A)(C:set (set A)):Prop :=
    forall_set V (fun a:A=> In (cons a nil) C).

Inductive  complex{A:Type}:Type := 
     | compl (V:set A)  (C:set (set A)) 
        (compl1: closed_containment V C)
        (compl2: uni_covering V C).

Inductive fin_nat_set (n:nat):Type :=
    | fn (k:nat) (p: (k<?n=true)).

Inductive chromatic_complex{A:Type}:Type := 
| chr_compl (V:set A)  (C:set (set A)) 
(compl1: closed_containment V C)
(compl2: uni_covering V C)
        (n:nat) (f:A -> (fin_nat_set n))
        (prop: forall_set C (fun x:set A => forall_set x 
        (fun v:A=> forall_set x (fun v':A => f(v)=f(v')-> v=v')))).

Inductive simplicial_map{A B:Type} (C :@complex A)(C' :@complex B):=
    | sm (f:A->B) (prop:match (C,C') with 
        | (compl _ X _ _, compl _ X' _ _)=>
            forall_set X (fun s:set A=> In (map f s) X')
        end).


Definition isomorphic_complex{A B:Type} (C :@complex A)(C' :@complex B):=   
    exists (f:simplicial_map C C') (f':simplicial_map C' C), 
    match (f,f') with
    | (sm _ _ m _, sm _ _ m' _ )=> 
    (match C with |compl V _ _ _ => forall_set V (fun x:A=> m' (m x)=x) end) /\
    (match C' with |compl V' _ _ _ => forall_set V' (fun x:B=> m (m' x)=x) end)
    end.


Lemma map_id: forall (A:Type) (a:set A), a = map  id a.
Proof. 
    intros.
    induction a;auto.
    unfold map.
    unfold map in IHa.
    rewrite <- IHa.
    reflexivity.
Qed.

Lemma stronger_forall_set: forall (A:Type) (s:set A) (f f':A->Prop), (forall x:A, (f x)-> (f' x))-> 
    forall_set s f -> forall_set s f'.
    intros A.
    induction s; intros.
    auto.
    unfold forall_set in H0.
    destruct H0.
    unfold forall_set.
    split.
    apply (H  a H0).
    apply IHs with f; auto.
    Qed.
    
Lemma identity_subst :forall (A:Type) (C:set(set A)), forall_set C (fun s:set A=> In (map id s) C).
Proof.
    intros.
    unfold forall_set.
    induction C. auto.
    split.
    rewrite <- map_id.
    simpl.
    auto.
    apply stronger_forall_set with (fun s=> In (map id s) C).
    intros.
    simpl.
    right.
    auto.
    auto.
    Qed.
    
    
Lemma id_true: forall (A:Type) (V:set A), forall_set V (λ x : A, id (id x) = x).
Proof.
    intros.
    induction V.
    simpl. auto.
    simpl.
    split; auto.
    Qed.

Theorem complex_isomorphic_with_itself :forall (A:Type) (c:complex), @isomorphic_complex A A c c.
Proof.
    intros.
    destruct c eqn:K.
    unfold isomorphic_complex.
    
    assert (p: forall_set C (fun s:set A=> In (map id s) C)).
    induction C; auto;simpl.
    split.
    left.
    apply map_id.
    apply stronger_forall_set with (fun s:set A=>In (map id s) C).
    intros.
    right;auto.
    apply (identity_subst A C).
    assert (p':match (c,c) with 
    | (compl _ X _ _, compl _ X' _ _)=>
        forall_set X (fun s:set A=> In (map id s) X')
    end).
    destruct c eqn:L;subst.
    inversion K.
    subst.
    auto.
    rewrite <-K.
    exists (sm c c id p').
    exists (sm c c id p').
    split.
    apply id_true.
    apply id_true.
    Qed.

Lemma map_lift: forall (A1 A2 A3:Type) (f1:A1->A2) (f2:A2->A3) (a:set A1), map (fun x=>f2(f1 x)) a = map f2 (map f1 a).
Proof.
    intros.
    induction a.
    auto.
    simpl.
    rewrite IHa.
    auto.
    Qed.
Lemma in_transitive_lemma: forall (A1 A2 A3:Type) (a1:set A1) (a2:set (set A2)) (a3:set (set A3)) (f1:A1->A2) (f2:A2->A3),
In (map f1 a1) a2->
(forall (a2':set A2), In a2' a2 -> In (map f2 a2') a3)->
In (map f2 (map f1 a1)) a3.
Proof.
    intros .
    induction a3;
    intros;auto.
    Qed.

Lemma forall_set_in_implies_in :forall (A B:Type) (a:A) (s:set A) (f:A->B) (s':set B),In a s -> forall_set s (fun x:A=> In (f x) s') -> In (f a) s'.
Proof.
    intros A B a.
    induction s.
    intros.
    inversion H.
    intros.
    unfold forall_set in H0.
    destruct H0.
    simpl in H.
    destruct H.
    rewrite H in H0.
    auto.
    apply IHs.
    auto. auto.
    Qed.
    
Lemma in_transitive: forall (A1 A2 A3:Type) (s1:set (set A1))   (s2:set (set A2))  (s3:set (set A3)) (f1:A1->A2) (f2:A2->A3),
    (forall_set s1 (fun x:set A1=> In (map f1 x) s2)) ->       
    (forall_set s2 (fun x:set A2=> In (map f2 x) s3)) ->
    (forall_set s1 (fun x:set A1=> In (map f2 (map f1 x)) s3)).
    Proof.
    intros A1 A2 A3.
    induction s1;
    intros; simpl;auto.
    split.
    unfold forall_set in H.
    destruct H.
    apply forall_set_in_implies_in with s2; auto.
    unfold forall_set in H.
    destruct H.
    apply IHs1 with s2; auto.
    Qed.

    
Lemma always_true: forall (A B :Type) (V:set A) (f:A->B), forall_set V (fun x:A => f x = f x).
intros.
induction V.
simpl;auto.
simpl.
split. reflexivity.
auto. Qed.

Theorem simplicial_map_transitive: forall (A1 A2 A3:Type) (C1:@complex A1) (C2:@complex A2) (C3:@complex A3) ( f1 :simplicial_map C1 C2) ( f2 :simplicial_map C2 C3),
    exists  (f3:simplicial_map C1 C3), match C1 with | compl V C compl1 compl2 => 
    match (f1, f2, f3) with
        | (sm _ _ f1' _, sm _ _ f2' _ , sm _ _ f3' _)=>
    forall_set V (fun x=> (f3' x) = f2'(f1' x)) end
    end.
    intros.
    destruct f1 eqn:E1.
    destruct f2 eqn:E2.
    remember (fun x=> f0 (f x)) as ans.
    assert (prop_required: match C1 with
    | compl V X _ _ =>
        match C3 with
        | compl V0 X' _ _ => forall_set X (λ s : set A1, In (map ans s) X')
        end
    end).
    destruct C1 eqn:C1des.
    destruct C2 eqn:C2des.
    destruct C3 eqn:C3des.
    subst.
    assert ( (λ s : set A1, In (map (λ x : A1, f0 (f x)) s) C4) = 
    (λ s : set A1, In (map  f0 (map f  s)) C4)).
    apply functional_extensionality_dep .
    intros.
    unfold In.
    rewrite map_lift.
    reflexivity.
    rewrite H.
    apply in_transitive with C0.
    auto. auto.
    exists (sm C1 C3 ans prop_required).
    destruct C1 eqn :K.
    rewrite Heqans.
    induction V.
    simpl.
    auto.
    simpl.
    split.
    reflexivity.
    apply always_true.
    Qed.



    
    