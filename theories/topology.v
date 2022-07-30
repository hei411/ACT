Require Import Coq.Lists.List.
Require Import Coq.Unicode.Utf8.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ClassicalFacts.

Section Topology.
Axiom EquivThenEqual: prop_extensionality.
Definition set{N:Type}:Type := N -> Prop.
Definition elem_set {N:Type} (n:N) (s:set):= s n.
Definition subset_set {N:Type}(s s':@set N):= forall k, s k -> s' k.
Definition equals_set {N:Type} (s s':@set N):= subset_set s s' /\ subset_set s' s.
Definition closed_containment {N:Type} (s:@set(@set N)) := 
    forall s', elem_set s' s → forall s'', subset_set s'' s' → elem_set s'' s.
Definition uni_covering {N:Type} (s:@set N) (s': @set (@set N)) := 
    forall n, elem_set n s → ∃ singleton, elem_set singleton s' /\ 
    forall n', singleton n' <-> n'=n.

Record complex{N:Type} := {
    V: @set N;
    C: @set (@set N);
    prop1: closed_containment C;
    prop2: uni_covering V C
}.

Record simplicial_map{A B:Type} {from:@complex A} {to:@complex B}:={
    func: A->B;
    prop: forall s, elem_set s from.(C) → ∃ s', elem_set s' to.(C)/\ 
    (forall a, elem_set a s -> elem_set ( func a) s') /\ 
    (forall a', elem_set a' s'-> exists a, elem_set a s /\ a' = func a) 
}.
Program Definition self_identity {N:Type} (c:@complex N):simplicial_map:= {|
    func:= λ n:N, n
|}.
Next Obligation. exists s. split; auto. split; eauto. 
Qed. 

Definition isomorphic_complex{A B:Type} (c:@complex A) (c':@complex B) := 
    ∃ (f:@simplicial_map A B c c') (g:@simplicial_map B A c' c), 
    forall a, elem_set a c.(V) → g.(func) (f.(func) a) = a /\ 
    forall b, elem_set b c'.(V) → f.(func) (g.(func) b) = b.

    
Theorem complex_isomorphic_with_itself: forall (N:Type) (c:@complex N), isomorphic_complex c c.
Proof.
    intros.
    exists (self_identity c), (self_identity c).
    intros.
    split; reflexivity.
Qed.
    
Program Definition simplicial_map_transitive {A1 A2 A3:Type} 
{C1:@complex A1} {C2:@complex A2} {C3:@complex A3} 
(m1: @simplicial_map A1 A2 C1 C2) (m2: @simplicial_map A2 A3 C2 C3): @simplicial_map A1 A3 C1 C3:=
{|
    func:= λ a, m2.(func) (m1.(func) a)
|}.
Next Obligation.
exists (λ x, ∃ a, elem_set a s /\ x = m2.(func) (m1.(func) a)).
split;
destruct m1;
destruct m2;
destruct C1; 
destruct C2;
destruct C3;
simpl in *.
apply prop0 in H as H1. destruct H1. destruct H0. 
apply prop3 in H0 as H2. destruct H2. destruct H2.
assert (x0 = (λ x1 : A3, ∃ a : A1, elem_set a s ∧ x1 = func1 (func0 a))).
apply functional_extensionality_dep; intros.
unfold elem_set in *.
destruct H1, H3.
apply EquivThenEqual. split; intros.
apply H5 in H6 as H7.
destruct H7.
 destruct H7.
 apply H4 in H7 as H9.
 destruct H9.
 destruct H9.
 exists x3; split;eauto.
 rewrite H8, H10. reflexivity.
 destruct H6.
 destruct H6.
 rewrite H7.
 apply H1 in H6.
 apply H3 in H6. auto.
unfold elem_set. unfold elem_set in *.
rewrite <- H4.
auto.
intros. split; intros.
unfold elem_set.
exists a. eauto.
unfold elem_set in H0.
destruct H0.
destruct H0.
exists x.
split. unfold elem_set.
eauto. eauto.
Qed.







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



(* **chromatic*)

Inductive fin_nat_set (n:nat):Type :=
    | fn (k:nat) (p: (k<?n=true)).


Inductive chromatic_complex{A:Type n}:Type := 
| chr_compl (V:set A)  (C:set (set A)) 
(compl1: closed_containment V C)
(compl2: uni_covering V C)
        (f:A -> N)
        (prop: forall_set C (fun x:set A => forall_set x 
        (fun v:A=> forall_set x (fun v':A => f(v)=f(v')-> v=v')))).

Definition matching (n n':nat) (t:fin_nat_set n) (t':fin_nat_set n'):Prop :=
     match (t, t') with 
        | (fn _ k _, fn _ k' _)=>k=k'
    end.

Inductive chromatic_simplicial_map{A B:Type} (C :@chromatic_complex A)(C' :@chromatic_complex B):=
    | chr_sm (f:A->B) (prop:match (C,C') with 
        | (chr_compl V X _ _ n l p, chr_compl _ X' _ _ n' l' p')=>
            forall_set X (fun s:set A=> In (map f s) X') /\
            forall_set V (fun v:A=>matching (l v) (l' (f v)))
        end).