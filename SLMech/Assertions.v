(*
 * Copyright (c) 2016, Johns Hopkins University Applied Physics Laboratory
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 *
 * 2. Redistributions in binary form must reproduce the above
 * copyright notice, this list of conditions and the following
 * disclaimer in the documentation and/or other materials provided
 * with the distribution.
 *
 * 3. Neither the name of the copyright holder nor the names of its
 * contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 *)

(** * State and trace assertions (semantics and properties) *)
Require Import ZArith.
Require Export ProgramData.
Require Import List.

Set Implicit Arguments.

(** ** State assertions : identifier generally preceded by an 's'*)
(** *** Definitions *)
Definition sprop := state -> Prop.

(** Boolean assertions *)
Inductive strue : sprop :=
  stru : forall (st : state) , strue st.
Inductive sfalse : sprop := .

Definition snot (p : sprop) : sprop :=  fun st => ~ p st.
Notation "¬ p" := (snot p) (at level 55, right associativity).

Definition sand (p q : sprop) : sprop :=  fun st => p st /\ q st.
Notation "p ∧ q" := (sand p q) (at level 62, right associativity).

Definition sor (p q : sprop) : sprop := fun st => p st \/ q st.
Notation "p ∨ q" := (sor p q) (at level 62, right associativity).

Definition simpl (p q : sprop) : sprop := fun st => p st -> q st.
Notation "p ⟶ q" := (simpl p q) (at level 60, right associativity).

Definition sprop_of_bexpr  (b : bexpr) : sprop :=
  (fun st => (bbexpr st b) = Some true).

Coercion sprop_of_bexpr : bexpr >-> sprop.

(** Quantifiers *)
Definition sexists (A : Type) (f : A -> sprop) : sprop :=
  fun st => exists x, f x st.

Definition sforall (A : Type) (f : A -> sprop) : sprop :=
  fun st => forall x, f x st.

(*A useful fact for updating sprops after a change to the store*)
Definition store_irrelevant (p : sprop) : Prop :=
  forall s l s' l' h d, (p (mkst s l h d)) -> (p (mkst s' l' h d)).

Ltac store_irrelevance :=
  match goal with
    | [H  : store_irrelevant ?p,
       P  : ?p (mkst ?s ?l ?h ?d)
       |- ?p (mkst ?s' ?l' ?h ?d)] => (unfold store_irrelevant in H ;
                                   apply (H s l) ;
                                   apply P ;
                                   fold store_irrelevant in H)
  end.

(** Empty state *)
Definition sempty_store : sprop := fun st => Vars.Empty (lc st).
Definition sempty_heap : sprop := fun st => Dom.Empty (dm st).
Definition sempty : sprop := sand sempty_store sempty_heap.

(** Star operator for state assertions *)
Inductive ssep_conj (p q : sprop) : sprop :=
| intro_ssep_conj :
    forall (s : store_f)(l : locals)(h : heap_f)(d' d : domain),
      (Dom.Subset d' d) ->
      p (mkst s l h d') ->
      q (mkst s l h (Dom.diff d d')) ->
      ssep_conj p q (mkst s l h d).

(* ⋆ -> ☆ *)
Notation "p ☆ q" := (ssep_conj p q) (at level 62, right associativity).

(*The separating conjunction is commutative*)
Lemma ssep_conj_comm :
  forall (P Q : sprop) (st : state),
    (P ☆ Q) st ->
    (Q ☆ P) st.
Proof.
  intros P Q st SC.
  elim SC.
  intros.
  assert (Dom.Subset (Dom.diff d d') d).
  intro.
  intro.
  apply DomFacts.diff_iff in H2.
  destruct H2.
  assumption.
  assert (Dom.Equal d' (Dom.diff d (Dom.diff d d'))).
  intro.
  split.
  intro.
  apply DomFacts.diff_iff.
  split.
  apply H in H3.
  assumption.
  intro.
  apply DomFacts.diff_iff in H4.
  destruct H4.
  contradiction.
  intro.
  apply DomFacts.diff_iff in H3.
  destruct H3.
  generalize (classic_set a d').
  intro.
  destruct H5.
  assumption.
  apply False_ind.
  apply H4.
  apply DomFacts.diff_iff.
  split.
  assumption.
  assumption.
  apply heap_equality in H3.
  rewrite H3 in H0.
  apply (intro_ssep_conj Q P s l h H2 H1 H0).
Qed.

(*The separating conjunction is store irrelevant if each of the
 *sprops it is composed of is also store_irrelevant*)
Lemma ssep_conj_store_irrelevant : forall p q, (store_irrelevant p) ->
                                               (store_irrelevant q) ->
                                               store_irrelevant (p ☆ q).
Proof.
  intros.
  unfold store_irrelevant.
  intros.
  inversion H1.
  apply intro_ssep_conj with (d' := d').
  assumption.
  store_irrelevance.
  store_irrelevance.
Qed.

(*separating conjunctions are associative*)
Lemma ssep_conj_assoc : forall (p1 p2 p3: sprop) (st : state),
                          ((p1☆p2) ☆ p3) st <->
                          (p1 ☆ p2 ☆ p3) st.
Proof.
  intros p1 p2 p3. split. intros L.
  inversion_clear L.
  inversion_clear H0.
  generalize (DomProps.subset_trans H2 H).
  intro.
  assert (Dom.Equal (Dom.diff d' d'0) (Dom.diff (Dom.diff d d'0) (Dom.diff d d'))).
  split.
  intro.
  apply DomFacts.diff_iff in H5.
  destruct H5.
  apply DomFacts.diff_iff.
  split.
  apply DomFacts.diff_iff.
  split.
  apply H in H5.
  assumption.
  assumption.
  intro.
  apply DomFacts.diff_iff in H7.
  destruct H7.
  contradiction.
  intro.
  apply DomFacts.diff_iff in H5.
  destruct H5.
  apply DomFacts.diff_iff in H5.
  destruct H5.
  apply DomFacts.diff_iff.
  split.
  generalize (classic_set a d').
  intro.
  destruct H8.
  assumption.
  apply False_ind.
  apply H6.
  apply DomFacts.diff_iff.
  split.
  assumption.
  assumption.
  assumption.
  apply heap_equality in H5.
  rewrite H5 in H4.
  assert (Dom.Subset (Dom.diff d d') (Dom.diff d d'0)).
  intro.
  intro.
  apply DomFacts.diff_iff in H6.
  destruct H6.
  apply DomFacts.diff_iff.
  split.
  assumption.
  intro.
  apply H7.
  apply H2 in H8.
  assumption.
  generalize (intro_ssep_conj p3 p2 s l h H6 H1 H4).
  intro.
  apply ssep_conj_comm in H7.
  generalize (intro_ssep_conj p1 (p2 ☆ p3) s l h H0 H3 H7).
  intro.
  assumption.
  intro.
  inversion_clear H.
  inversion_clear H2.
  assert (Dom.Empty (Dom.inter d'0 d')).
  intro.
  intro.
  apply DomFacts.inter_iff in H2.
  destruct H2.
  apply H in H2.
  apply DomFacts.diff_iff in H2.
  destruct H2.
  contradiction.
  assert (Dom.Subset d' (Dom.union d' d'0)).
  intro.
  intro.
  apply DomFacts.union_iff.
  left;assumption.
  assert (Dom.Subset d'0 (Dom.union d' d'0)).
  intro.
  intro.
  apply DomFacts.union_iff.
  right;assumption.
  assert (Dom.Equal (Dom.diff (Dom.diff d d') d'0) (Dom.diff d (Dom.union d' d'0))).
  split.
  intro.
  apply DomFacts.diff_iff in H7.
  destruct H7.
  apply DomFacts.diff_iff in H7.
  destruct H7.
  apply DomFacts.diff_iff.
  split.
  assumption.
  intro.
  apply DomFacts.union_iff in H10.
  destruct H10; contradiction.
  intro.
  apply DomFacts.diff_iff in H7.
  destruct H7.
  apply DomFacts.diff_iff.
  split.
  apply DomFacts.diff_iff.
  split.
  assumption.
  intro.
  apply H8.
  apply DomFacts.union_iff.
  left; assumption.
  intro.
  apply H8.
  apply DomFacts.union_iff.
  right; assumption.
  apply heap_equality in H7.
  rewrite H7 in H4.
  assert (Dom.Equal d'0 (Dom.diff (Dom.union d' d'0) d')).
  split.
  intro.
  apply DomFacts.diff_iff.
  split.
  apply DomFacts.union_iff.
  right; assumption.
  intro.
  apply (H2 a).
  apply DomFacts.inter_iff.
  auto.
  intro.
  apply DomFacts.diff_iff in H8.
  destruct H8.
  apply DomFacts.union_iff in H8.
  destruct H8.
  contradiction.
  assumption.
  apply heap_equality in H8.
  rewrite H8 in H3.
  generalize (intro_ssep_conj p1 p2 s l h H5 H1 H3).
  intro.
  assert (Dom.Subset (Dom.union d' d'0) d).
  intro.
  intro.
  apply DomFacts.union_iff in H10.
  destruct H10.
  apply H0 in H10.
  assumption.
  apply H in H10.
  apply diff_subset in H10.
  assumption.
  generalize (intro_ssep_conj (p1 ☆ p2) p3 s l h H10 H9 H4).
  intro.
  assumption.
Qed.

(*Easy way to split up a ssep_conj when the heap is empty*)
Lemma ssep_conj_empty : forall (P Q : sprop)(s : store_f)(l : locals)(h : heap_f),
                          (P ☆ Q) (mkst s l h Dom.empty) <->
                          (P (mkst s l h Dom.empty)) /\ (Q (mkst s l h Dom.empty)).
  intros.
  split.
  intro.
  split.
  inversion H.
  subst.
  assert (d' = Dom.empty).
  apply heap_equality.
  intro.
  split.
  intro.
  apply H3 in H0.
  assumption.
  intro.
  apply DomFacts.empty_iff in H0.
  contradiction.
  subst.
  assumption.
  inversion H.
  subst.
  assert (Dom.diff Dom.empty d' = Dom.empty).
  apply heap_equality.
  intro.
  split.
  intro.
  apply DomFacts.diff_iff in H0.
  destruct H0.
  assumption.
  intro.
  apply DomFacts.empty_iff in H0.
  contradiction.
  rewrite H0 in H6.
  assumption.
  intro.
  destruct H.
  apply intro_ssep_conj with (d' := Dom.empty).
  intro.
  intro.
  assumption.
  assumption.
  assert (Dom.diff Dom.empty Dom.empty = Dom.empty).
  apply heap_equality.
  intro.
  split.
  intro.
  apply DomFacts.diff_iff in H1.
  destruct H1.
  assumption.
  intro.
  apply DomFacts.empty_iff in H1.
  contradiction.
  rewrite H1.
  assumption.
Qed.


Notation "x ≐ v" := (fun (s : store) => s x = Some v) (at level 15, right associativity).
Notation "v ↦ w" := (fun (h : heap) => h v = Some w) (at level 59, no associativity).
Notation "x ≐ v" := (fun (st : state) => (sr st) x = Some v) (at level 15, right associativity).
Notation "v ↦ w" := (fun (st : state) => (hp st) v = Some w) (at level 59, no associativity).
Notation "x ≐ v" := (fun (s : store) => s x = v) (at level 15, right associativity).
Notation "v ↦ w" := (fun (h : heap) => h v = w) (at level 59, no associativity).
Notation "x ≐ v" := (fun (st : state) => (sr st) x = v) (at level 15, right associativity).
Notation "v ↦ w" := (fun (st : state) => (hp st) v = w) (at level 59, no associativity).

(*facts that are about the heap don't depend on the store*)
Lemma heap_store_irrelevant : forall v w, store_irrelevant (v ↦ w).
  intros.
  unfold store_irrelevant.
  intros.
  simpl in *.
  assumption.
Qed.

(** *** Predicates *)
(** Assertion true for any state *)
Definition suniv (p : sprop) : Prop :=
  forall (st : state), p st.

(** Precise assertion *)
(** Coercion from [prop] : lifts assertions to state assertions *)
Definition lift_prop_sprop (p : Prop) : sprop := (fun st => p).
