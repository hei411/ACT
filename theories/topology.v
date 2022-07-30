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
    C_built_from_V: forall s, elem_set s C→ forall v, elem_set v s→ elem_set v V;
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
split;destruct m1, m2,C1,C2,C3; simpl in *.
apply prop0 in H as H1. destruct H1. destruct H0. 
apply prop3 in H0 as H2. destruct H2. destruct H2.
assert (x0 = (λ x1 : A3, ∃ a : A1, elem_set a s ∧ x1 = func1 (func0 a))).
apply functional_extensionality_dep; intros.
unfold elem_set in *.
destruct H1, H3.
apply EquivThenEqual. split; intros.
apply H5 in H6 as H7.
destruct H7, H7.
 apply H4 in H7 as H9.
 destruct H9, H9.
 exists x3; split;eauto.
 rewrite H8, H10. reflexivity.
 destruct H6, H6.
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
destruct H0, H0.
exists x.
split. unfold elem_set.
eauto. eauto.
Qed.




(* **chromatic*)

Record chromatic_complex{N:Type} := {
    comp: @complex N;
    n:nat;
    f:N->nat;
    chro_prop1: forall x:N, elem_set x comp.(V) → f x < n ;
    chro_prop2: forall s, elem_set s comp.(C) → forall v v', 
        (elem_set v s /\ elem_set v' s /\ f v = f v') → v =v' 
}.

Record chromatic_simplicial_map {A B:Type}{from:@chromatic_complex A} {to:@chromatic_complex B}:=
    {
        smap : @simplicial_map A B from.(comp) to.(comp) ;
        chro_map_prop: (forall x:A, elem_set x from.(comp).(V) →  from.(f) x = to.(f) (smap.(func) x))
    }.

Program Definition chromatic_self_identity {N:Type} (c:@chromatic_complex N):chromatic_simplicial_map:= 
{|
    smap:=self_identity c.(comp);
    chro_map_prop:=_
|}.

Definition isomorphic_chromatic_complex{A B:Type} (c:@chromatic_complex A) (c':@chromatic_complex B) := 
    ∃ (f:@chromatic_simplicial_map A B c c') (g:@chromatic_simplicial_map B A c' c), 
    forall a, elem_set a c.(comp).(V) → g.(smap).(func) (f.(smap).(func) a) = a /\ 
    forall b, elem_set b c'.(comp).(V) → f.(smap).(func) (g.(smap).(func) b) = b.

    
Theorem chromatic_complex_isomorphic_with_itself: forall (N:Type) (c:@chromatic_complex N), isomorphic_chromatic_complex c c.
Proof.
    intros.
    unfold isomorphic_chromatic_complex.
    exists (chromatic_self_identity c), (chromatic_self_identity c).
    intros; split; reflexivity.
Qed.

Program Definition chromatic_simplicial_map_transitive {A1 A2 A3:Type} 
{C1:@chromatic_complex A1} {C2:@chromatic_complex A2} {C3:@chromatic_complex A3} 
(m1: @chromatic_simplicial_map A1 A2 C1 C2) (m2: @chromatic_simplicial_map A2 A3 C2 C3): @chromatic_simplicial_map A1 A3 C1 C3:=
{|
    smap:= @simplicial_map_transitive A1 A2 A3 C1.(comp) C2.(comp) C3.(comp) m1.(smap) m2.(smap)
|}.
Next Obligation.
destruct m1, m2; simpl.
apply chro_map_prop0 in H as H2.
destruct smap0, smap1.
rewrite H2.
apply chro_map_prop1.
destruct C1, C2, C3.
destruct comp0, comp1, comp2; simpl in *; simpl.
apply C_built_from_V1 with (λ l, l= func0 x).
assert (elem_set (λ l, l=x) C0).
unfold uni_covering in prop5.
unfold elem_set; unfold elem_set in *.
apply prop5 in H.
destruct H.
destruct H.
assert (x0 = (λ l : A1, l = x)).
apply functional_extensionality_dep.
intros.
apply EquivThenEqual; split; intros.
rewrite H0 in H1; auto.
subst.
rewrite H0.
reflexivity.
rewrite <- H1; auto.
apply prop0 in H0 as lem1.
destruct lem1.
destruct H1.
destruct H3.
assert (x0 = (λ l : A2, l = func0 x)).
apply functional_extensionality_dep.
intros.
apply EquivThenEqual.
split; intros.
apply H4 in H5.
 destruct H5.
 destruct H5.
 unfold elem_set in H5.
 subst; reflexivity.
 subst.
 apply H3.
 unfold elem_set.
 reflexivity.
 rewrite <-H5.
 auto.
 unfold elem_set.
 reflexivity.
 Qed.
