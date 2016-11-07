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

Require Import MSets.
Require Import Sumbool.
Require Import Equalities.
Require Import Orders.
Require Export RelationClasses.
Require Import Relation_Definitions.
Require Import SetoidClass.
Require Import Classical.
Require Import Eqdep_dec.
Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.Orders.
Require Import Peano_dec.
Require Import Coq.Arith.Le.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Arith.Compare_dec.


Require Import ZModulo.
Module Type ValueType := UsualStrOrder' <+ UsualIsEqOrig <+ HasEqDec <+ HasBoolOrdFuns'.
Require Import ZArith.

Open Scope Z.

(*Bounds for signed ints of each size*)

Definition uint32_max := 4294967296%Z.
Definition uint64_max := 18446744073709551616%Z.
Definition sint32_min := (-2147483648)%Z.
Definition sint32_max := 2147483647%Z.
Definition sint64_min := (-9223372036854775808)%Z.
Definition sint64_max := 9223372036854775807%Z.
Parameter addr_max : Z.
Axiom addr_max_pos : addr_max = uint64_max.

Definition sint32_bound z := sint32_min <= z <= sint32_max.
Definition uint32_bound z := 0 <= z < uint32_max.
Definition sint64_bound z := sint64_min <= z <= sint64_max.
Definition uint64_bound z := 0 <= z < uint64_max.


Inductive val: Type :=
  | Vundef: val  (*Represents unknown values (fresh local vars, newly allocated space, etc.)*)
  | Vsint32 z : sint32_bound z -> val (*32 bit integers (signed)*)
  | Vuint32 z:  uint32_bound z -> val (*32 bit integers (unsigned)*)
  | Vsint64 z:  sint64_bound z -> val (*64 bit integers (signed)*)
  | Vuint64 z:  uint64_bound z -> val. (*64 bit integers (unsigned)*)
(*
  TODO: address values and structures
  | Vaddr z : 0 <= z < addr_max -> val
  | Vstruct :list val -> val.
*)

(* namespace for properties associated with val being DecidableTypeBoth, i.e. decidable equality*)
Declare Module Val : ValueType.   
(* namespace for properties associated with val being part of an unordered "weak", i.e. intersection, union, etc..*)
Declare Module Rng : WSetsOn Val.

(* Keys (addrs) are integers, which gives them
 * a total ordering allowing us to build an ordered set
 *)
Module Key <: OrderedTypeWithLeibniz.
  Definition keytype := Z.

  Definition t := keytype.
  Definition eq (x y : t):= x = y.
  Definition lt (x y : t):= Z.lt x y.

  Lemma lt_trans : forall u v w : t, lt u v -> lt v w -> lt u w.
    intros. unfold lt in *. destruct u, v, w; omega.
  Qed.

  Lemma lt_not_eq : forall (v w : keytype), lt v w -> ~ eq v w.
    intros.  destruct v, w; unfold lt in *; try intro; try rewrite H0 in *; try omega.
  Qed.

  Definition eq_refl := @eq_refl keytype.
  Definition eq_sym := @eq_sym keytype.
  Definition eq_trans := @eq_trans keytype.
  Definition eq_equiv : Equivalence eq := eq_equivalence.

  Definition compare v w := Z.compare v w.
  Lemma compare_spec : forall v w : t, CompSpec eq lt v w (compare v w).
  Proof.
    intros.
    destruct (compare v w) eqn:?; constructor.
    unfold eq.
    unfold compare in Heqc.
    apply Z.compare_eq_iff in Heqc.
    assumption.
    unfold lt.
    unfold compare in Heqc.
    apply -> Z.compare_lt_iff in Heqc.
    assumption.
    unfold lt.
    unfold compare in Heqc.
    apply -> Z.compare_gt_iff in Heqc.
    assumption.
  Qed.
    
 Lemma keytype_dec :
   forall (v w : keytype),
     {v = w} + {v <> w}.
 Proof.
   intros v w.
   apply Z.eq_dec.
 Defined.

 Set Implicit Arguments.
 Lemma lt_strorder : StrictOrder lt.
   assert (Irreflexive lt).
   unfold Irreflexive.
   unfold Reflexive.
   intro.
   unfold complement.
   intro.
   apply lt_not_eq in H.
   apply H.
   reflexivity.
   assert (Transitive lt).
   unfold Transitive.
   apply lt_trans.
   apply (Build_StrictOrder lt H H0).
 Qed.
 Unset Implicit Arguments.
 
 Lemma eq_leibniz : forall (v w : keytype), eq v w -> v = w.
   unfold eq.
   auto.
 Qed.


 Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
   unfold Proper.
   unfold respectful.
   intros.
   inversion H.
   inversion H0.
   split.
   intro.
   assumption.
   intro.
   assumption.
 Qed.
 
 Definition eq_dec := keytype_dec.
End Key.

Module Keys := MakeWithLeibniz Key.
Definition addr := Keys.elt.

(* The heap is broken up into "chunks", disjoint sets of addr *)
Module ChnkFacts := WFactsOn Key Keys.
Module ChnkProps := WPropertiesOn Key Keys.
Import Keys.
Import ChnkFacts.
Import ChnkProps.

(* Set equality is now logically equivalent to leibniz equality *)
Axiom chunk_equality : 
  forall (c c' : Keys.t),
    (Keys.Equal c c') <-> c = c'.

(* This is used in the dispose rule. However, it may be better to make a
 * chunk_bits predicate instead and just assert that the addr a is the 
 * first element by virtue of it being the first element of the list.
 *)
Definition base_pointer (a : addr) (c : Keys.t) := 
  Keys.In a c /\ (forall (a' : addr), Keys.In a' c -> (Z.le a a')).

(* With the chunk_equality above we can quickly create a weak set
 * that contains chunks instead of single addresses*)
Module Chk <: UsualDecidableTypeBoth.
  Definition t := Keys.t.
  Definition eq := @Logic.eq Keys.t.
  Definition eq_refl := @eq_refl Keys.t.
  Definition eq_sym := @eq_sym Keys.t.
  Definition eq_trans := @eq_trans Keys.t.
  Definition eq_equiv : Equivalence eq := eq_equivalence.

  Lemma variable_dec :
    forall (v v' : Keys.t),
      {v = v'} + {v <> v'}.
  Proof.
    intros v v'.
    generalize (Keys.eq_dec v v').
    intro.
    inversion H.
    apply chunk_equality in H0.
    constructor.
    assumption.
    constructor 2.
    intro.
    apply H0.
    apply chunk_equality.
    assumption.
  Defined.

  Definition eq_dec := variable_dec.
End Chk.


Declare Module Dom : WSetsOn Chk.
Module DomFacts := WFactsOn Chk Dom.
Module DomProps := WPropertiesOn Chk Dom.
Definition domain := Dom.t.
Definition chunk := Dom.elt.
(*Decided to finally add this*)
Definition chunk_bits l s := elements s = l.
Import Dom.
Import DomFacts.
Import DomProps.
  
(*We define a heap as a partial function on a given domain*)
Definition heap_f := domain -> addr -> option val.

(*Curried heap_f function*)
Definition heap := addr-> option val.

(*Now that the elements of a domain are chunks (sets) we need
 *to assert that the elements of the chunks are unique*)
Axiom chunk_unique :
  forall (c c' : chunk)(a : addr),
    Keys.In a c -> Keys.In a c' -> c = c'.

(*Since we have a set consisting of sets of addresses we need
 *a new way of indicating that an address is "in" our heap*)
Parameter In' : addr -> domain -> Prop.

Parameter In'_iff : 
  forall (a : addr)(d : domain),
    In' a d <-> (exists (c : chunk), Keys.In a c /\ Dom.In c d).

(*The essential axioms indicating that heap_f types are partial functions*)
Axiom heap_f_out_of_bounds :
  forall (h : heap_f) (d : domain) (a : addr), 
    ~In' a d <-> h d a = None.

Axiom heap_pf :
  forall (h : heap_f) (d d' : domain) (a : addr)(v : val),
    d [<=] d' -> h d a = Some v -> h d' a = Some v.

(*Simply the negation of the above statement*)
Lemma heap_f_in_bounds :
  forall (h : heap_f) (d : domain) (a : addr), 
    In' a d <-> exists (v : val), h d a = Some v.
  intros.
  split.
  intro.
  generalize (classic (h d a = None)).
  intro.
  destruct H0.
  apply heap_f_out_of_bounds in H0.
  contradiction.
  destruct (h d a).
  exists v.
  reflexivity.
  apply False_ind.
  apply H0.
  reflexivity.
  intro.
  inversion H.
  generalize (classic (In' a d)).
  intro.
  destruct H1.
  assumption.
  generalize (heap_f_out_of_bounds h d a).
  intro.
  apply H2 in H1.
  rewrite H1 in H0.
  discriminate H0.
Qed.

(*For any address in a subdomain, its evaluation is
 *the same in a larger domain*)
Lemma domain_propagate : 
  forall (h : heap_f) (d d' : domain) (a : addr),
    In' a d -> d [<=] d' -> h d a = h d' a.
  intros.
  generalize (heap_f_in_bounds h d a).
  intro.
  destruct H1.
  generalize (H1 H).
  intro.
  inversion_clear H3.
  rewrite H4.
  generalize (heap_pf h d d' a x H0 H4).
  intro.
  rewrite H3.
  reflexivity.
Qed.

(*Once again set equality is logically equivalent to leibniz equality*)
Axiom heap_equality :
  forall (d d' : domain),
    d [=] d' <-> d = d'.


(*This is essential if we want to say anything at all about how we're partitioning our set*)
(*This is the idea of the excluded middle as applied to sets*)
Lemma classic_set : forall (x : chunk) (d : domain),
                      In x d \/ ~In x d.
  intros.
  generalize (classic (In x d)).
  intro.
  assumption.
Qed.

(*This allows us to partition domains when given a subdomain*)
Lemma subset_decomp : forall (s d : domain),
                          s [<=] d -> 
                          d [=] (union s (diff d s)).
  intros.
  split.
  intro.
  apply union_iff.
  generalize(classic_set a s).
  intro.
  destruct H1.
  left; assumption.
  right.
  apply diff_iff.
  split.
  assumption.
  assumption.
  intro.
  apply union_iff in H0.
  destruct H0.
  apply H in H0.
  assumption.
  apply diff_iff in H0.
  destruct H0.
  assumption.
Qed.
                                        

(*Inductive construction for domain "partition"*)
Inductive heap_bits : list domain -> domain -> Prop := 
| empty_heap : heap_bits nil empty
| non_empty_heap : forall (d k : domain) (l : list domain),
                     heap_bits l d
                     -> Empty (inter k d)
                     -> heap_bits (k::l) (union k d).

(*Function for taking the union over a list of domains*)
Fixpoint union_list (l : list domain) : domain :=
  match l with
    | nil => empty
    | a::l' => union a (union_list l')
  end.

(*My attempt at an inductive construction for pairwise disjoint lists of sets*)
Inductive pw_disjoint : list domain -> Prop :=
| pw_disjoint_nil : pw_disjoint nil
| pw_disjoint_cons : forall (a : domain) (l : list domain),
                       Empty (inter a (union_list l)) ->
                       pw_disjoint l ->
                       pw_disjoint (a::l).

(*Each element of the union must be found in one of the members*)
Lemma element_of_union : forall (l : list domain) (a : chunk),
                           In a (union_list l) ->
                           (exists (s : domain), In a s /\ List.In s l).
  induction l.
  intros.
  simpl in H.
  apply empty_iff in H.
  contradiction.
  intros.
  simpl in H.
  apply union_iff in H.
  destruct H.
  exists a.
  split.
  assumption.
  constructor.
  reflexivity.
  apply IHl in H.
  inversion H.
  destruct H0.
  exists x.
  split.
  assumption.
  simpl.
  right; assumption.
Qed.

(*The union of subdomains contains each subdomain*)
Lemma subset_of_union : forall (l : list domain) (d : domain),
                          List.In d l -> d [<=] (union_list l).
  intros.
  induction l.
  inversion H.
  inversion H;
    subst;
    intro;
    intro;
    apply union_iff;
    fold union_list.
  left; assumption.
  right.
  apply IHl in H0.
  apply H0 in H1.
  assumption.
Qed.

(*The union over two appended lists is the union of the union over each individual list*)
Lemma union_lists_union : forall (l l' : list domain),
                            union_list (l++l') [=] union (union_list l) (union_list l').
  induction l, l'.
  simpl.
  split.
  intro.
  apply empty_iff in H.
  contradiction.
  intro.
  apply union_iff in H.
  destruct H; apply empty_iff in H; contradiction.
  simpl.
  split.
  intro.
  apply union_iff.
  right; assumption.
  intro.
  apply union_iff in H.
  destruct H.
  apply empty_iff in H.
  contradiction.
  assumption.
  simpl.
  split.
  intro.
  apply union_iff.
  left.
  apply union_iff in H.
  apply union_iff.
  destruct H.
  left; assumption.
  apply IHl in H.
  apply union_iff in H.
  destruct H.
  right; assumption.
  simpl in H.
  apply empty_iff in H.
  contradiction.
  intro.
  apply union_iff in H.
  destruct H.
  apply union_iff.
  apply union_iff in H.
  destruct H.
  left; assumption.
  right.
  apply IHl.
  apply union_iff.
  left; assumption.
  apply empty_iff in H.
  contradiction.
  split.
  intro.
  simpl in *.
  apply union_iff in H.
  apply union_iff.
  destruct H.
  left.
  apply union_iff.
  left; assumption.
  apply IHl in H.
  apply union_iff in H.
  destruct H.
  left; apply union_iff.
  right; assumption.
  right.
  assumption.
  intro.
  simpl.
  apply union_iff.
  apply union_iff in H.
  destruct H.
  apply union_iff in H.
  fold union_list in H.
  destruct H.
  left; assumption.
  generalize (IHl (d::l')).
  intro.
  apply heap_equality in H0.
  rewrite H0.
  right; apply union_iff.
  left; assumption.
  generalize (IHl (d::l')).
  intro.
  apply heap_equality in H0.
  rewrite H0.
  right.
  apply union_iff.
  right; assumption.
Qed.

(*It follows from the above that the order of elements in the union_list
 does not matter.*)
Corollary union_lists_comm : forall (l l' : list domain), 
                              union_list (l++l') [=] union_list (l'++l).
intros.
generalize (union_lists_union l l').
intro.
apply heap_equality in H.
rewrite H.
generalize (union_lists_union l' l).
intro.
apply heap_equality in H0.
rewrite H0.
apply union_sym.
Qed.

(*Helpful characterization of pw_disjoint*)
Lemma pw_disjoint_lists_split : forall (l l' : list domain),
                            pw_disjoint (l++l') <->
                            pw_disjoint l /\
                            pw_disjoint l'/\
                            Empty (inter (union_list l) (union_list l')).
  induction l, l'.
  split.
  intro.
  simpl in *.
  split.
  assumption.
  split.
  assumption.
  intro.
  intro.
  apply inter_iff in H0.
  destruct H0; apply empty_iff in H0; contradiction.
  intros.
  destruct H.
  simpl in *.
  assumption.
  split.
  intros.
  simpl in *.
  split.
  constructor.
  split.
  assumption.
  intro.
  intro.
  apply inter_iff in H0.
  destruct H0.
  apply empty_iff in H0.
  contradiction.
  simpl.
  intros.
  destruct H.
  destruct H0.
  assumption.
  rewrite app_nil_r.
  split.
  intro.
  split.
  assumption.
  split.
  constructor.
  simpl.
  intro.
  intro.
  apply inter_iff in H0.
  destruct H0.
  apply empty_iff in H1.
  contradiction.
  simpl.
  intros.
  destruct H.
  assumption.
  split.
  intro.
  split.
  constructor.
  simpl in H.
  inversion_clear H.
  intro.
  intro.
  apply inter_iff in H.
  destruct H.
  apply (H0 a0).
  apply inter_iff.
  split.
  assumption.
  apply IHl in H1.
  destruct H1.
  destruct H3.
  generalize (union_lists_union l (d::l')).
  intro.
  apply H5.
  apply union_iff.
  left; assumption.
  inversion_clear H.
  apply IHl in H1.
  destruct H1.
  assumption.
  split.
  inversion_clear H.
  apply IHl in H1.
  destruct H1.
  destruct H1.
  assumption.
  inversion_clear H.
  intro.
  intro.
  apply inter_iff in H.
  destruct H.
  apply (H0 a0).
  apply inter_iff.
  split.
  apply union_iff in H.
  fold union_list in H.
  destruct H.
  assumption.
  apply IHl in H1.
  destruct H1.
  destruct H3.
  apply False_ind.
  apply (H4 a0).
  apply inter_iff.
  split; assumption.
  generalize (union_lists_comm l (d::l')).
  intro.
  apply H3.
  simpl.
  apply union_iff.
  simpl in H2.
  apply union_iff in H2.
  destruct H2.
  left; assumption.
  simpl in H.
  apply union_iff in H.
  destruct H.
  apply False_ind.
  apply (H0 a0).
  apply inter_iff.
  split.
  assumption.
  apply H3.
  simpl.
  apply union_iff.
  generalize (union_lists_union l' l).
  intro.
  apply heap_equality in H4.
  rewrite H4.
  right.
  apply union_iff.
  left; assumption.
  generalize (union_lists_union l' l).
  intro.
  apply heap_equality in H4.
  rewrite H4.
  right; apply union_iff.
  right; assumption.
  intros.
  destruct H.
  destruct H0.
  simpl in *.
  constructor.
  generalize (union_lists_union l (d::l')).
  intro.
  apply heap_equality in H2.
  rewrite H2.
  simpl.
  intro.
  intro.
  apply inter_iff in H3.
  destruct H3.
  apply (H1 a0).
  apply union_iff in H4.
  destruct H4.
  apply False_ind.
  inversion_clear H.
  apply (H5 a0).
  apply inter_iff.
  split; assumption.
  apply union_iff in H4.
  destruct H4.
  apply False_ind.
  apply (H1 a0).
  apply inter_iff.
  split; apply union_iff; left; assumption.
  apply False_ind.
  apply (H1 a0).
  apply inter_iff.
  split; apply union_iff.
  left; assumption.
  right; assumption.
  apply IHl.
  split.
  inversion_clear H.
  assumption.
  split.
  assumption.
  intro.
  intro.
  apply (H1 a0).
  apply inter_iff in H2.
  destruct H2.
  apply inter_iff.
  split.
  apply union_iff.
  right; assumption.
  simpl in H3.
  assumption.
Qed.

(*The above gives us that the order of elements in a pairwise disjoint list
  doesn't matter*)
Corollary pw_disjoint_lists_comm : forall (l l' : list domain), 
                                     pw_disjoint (l++l') <-> pw_disjoint (l'++l).
intros.
split;
intro;
apply pw_disjoint_lists_split;
apply pw_disjoint_lists_split in H;
generalize (inter_sym (union_list l) (union_list l'));
intro;
apply heap_equality in H0.
rewrite <- H0.
destruct H;
destruct H1;
split.
assumption.
split;
  assumption.
rewrite H0.
destruct H.
destruct H1.
split.
assumption.
split; assumption.
Qed.

(*The "bits" in the heap_bits exactly covers the domain*)
Lemma bits_cover_domain : forall (l : list domain) (d : domain),
                            heap_bits l d -> d [=] (union_list l).
  induction l.
  intro.
  intro.
  inversion H.
  unfold union_list.
  intro.
  split;
    intro;
    assumption.
  intro.
  intro.
  inversion H.
  subst.
  intro.
  split.
  intro.
  apply union_iff in H0.
  destruct H0.
  apply union_iff.
  fold union_list.
  left; assumption.
  apply IHl in H2.
  apply H2 in H0.
  apply union_iff.
  fold union_list.
  right;assumption.
  intro.
  unfold union_list in H0.
  fold union_list in H0.
  apply union_iff.
  apply union_iff in H0.
  destruct H0.
  left; assumption.
  apply IHl in H2.
  apply H2 in H0.
  right; assumption.
Qed.


(*If two domains are made of the same bits, then they are equal*)
Corollary compositional_equality : forall (d d' : domain) (l : list domain), 
                                     heap_bits l d -> 
                                     heap_bits l d' -> 
                                     d [=] d'.
intros.
apply bits_cover_domain in H.
apply bits_cover_domain in H0.
apply equal_sym in H0.
apply equal_trans with (s1 := d) in H0.
assumption.
assumption.
Qed.

(*Every bit in a list of heap_bits is a subset of it's respective domain.*)
Corollary subset_of_heap_bits : forall (s d : domain) (l : list domain),
                                  List.In s l ->
                                  heap_bits l d ->
                                  s [<=] d.
intros.
apply bits_cover_domain in H0.
apply subset_of_union in H.
apply heap_equality in H0.
rewrite <- H0 in H.
assumption.
Qed.

(*Remove the first heap_bit from the list*)
Lemma pop_bit : forall (d s : domain) (l : list domain),
                  heap_bits (s::l) d -> heap_bits l (diff d s).
  intros.
  inversion H.
  subst.
  assert ((diff (union s d0) s) [=] d0).
  intro.
  split.
  intro.
  apply diff_iff in H0.
  destruct H0.
  apply union_iff in H0.
  destruct H0.
  contradiction.
  assumption.
  intro.
  apply diff_iff.
  split.
  apply union_iff.
  right;assumption.
  intro.
  generalize (H4 a).
  intro.
  apply H3.
  apply inter_iff.
  split; assumption.
  apply heap_equality in H0.
  rewrite H0.
  assumption.
Qed.

(*Each of the "bits" in a list of heap_bits is disjoint from one another*)
Lemma bits_pw_disjoint : forall (l : list domain) (d : domain),
                           heap_bits l d -> 
                           pw_disjoint l.
  induction l.
  intros.
  constructor.
  intros.
  apply pop_bit in H.
  constructor.
  intro.
  intro.
  apply inter_iff in H0.
  destruct H0.
  apply bits_cover_domain in H.
  apply heap_equality in H.
  rewrite <- H in H1.
  apply diff_iff in H1.
  destruct H1.
  contradiction.
  apply IHl in H.
  assumption.
Qed.

(*This may seem like an odd corollary to have, but I believe it may
 *have future uses in Ltacs*)
Corollary heap_bits_membership : forall (l : list domain) (s d : domain)
                                        (a : addr),
                                   In' a s ->
                                   heap_bits (s::l) d ->
                                   ~In' a (union_list l).
intros.
intro.
apply pop_bit in H0.
apply bits_cover_domain in H0.
apply heap_equality in H0.
rewrite <- H0 in H1.
apply In'_iff in H.
apply In'_iff in H1.
inversion H.
inversion H1.
destruct H2, H3.
generalize (chunk_unique x x0 a H2 H3).
intro.
subst.
apply diff_iff in H5.
destruct H5.
contradiction.
Qed.

(*This gives us another characterization of our heap_bits list*)
Lemma heap_bits_iff : forall (l : list domain) (d : domain),
                        heap_bits l d <->
                        d [=] union_list l /\
                        pw_disjoint l.
  induction l.
  intros.
  split.
  intros.
  simpl in *.
  split.
  inversion H.
  reflexivity.
  constructor.
  intro.
  destruct H.
  simpl in *.
  apply heap_equality in H.
  rewrite H.
  constructor.
  intro.
  split.
  intro.
  split.
  apply bits_cover_domain in H.
  assumption.
  apply bits_pw_disjoint in H.
  assumption.
  intros.
  destruct H.
  inversion H0.
  subst.
  assert (union_list (a::l) [=] union a (union_list l)).
  split.
  intro.
  assumption.
  intro.
  assumption.
  apply equal_trans with (s1 := d) in H1; try assumption.
  assert (a [<=] d).
  apply heap_equality in H.
  rewrite H.
  apply subset_of_union.
  simpl.
  left; reflexivity.
  generalize (subset_decomp a d).
  intro.
  apply H5 in H2.
  apply heap_equality in H2.
  rewrite H2.
  constructor.
  assert (diff d a [=] union_list l).
  split.
  intro.
  apply diff_iff in H6.
  destruct H6.
  apply H1 in H6.
  apply union_iff in H6.
  destruct H6.
  contradiction.
  assumption.
  intro.
  apply diff_iff.
  split.
  apply H1.
  apply union_iff.
  right; assumption.
  intro.
  generalize (H3 a0).
  intro.
  apply H8.
  apply inter_iff.
  split.
  assumption.
  assumption.
  apply IHl.
  split; assumption.
  intro.
  intro.
  apply inter_iff in H6.
  destruct H6.
  apply diff_iff in H7.
  destruct H7.
  contradiction.
Qed.



(*Breaking down heap_bits nicely, not currently used*)
Lemma heap_bits_lists_sep : forall (d : domain) (l l' : list domain),
                              heap_bits (l++l') d <->
                              heap_bits l (diff d (union_list l')) /\
                              heap_bits l' (diff d (union_list l)) /\
                              d [=] union (union_list l) (union_list l') /\
                              Empty (inter (union_list l) (union_list l')).
  intros.
  split.
  intro.
  split.
  apply heap_bits_iff in H.
  destruct H.
  apply heap_bits_iff.
  split.
  split.
  intro.
  apply diff_iff in H1.
  destruct H1.
  apply H in H1.
  apply union_lists_union in H1.
  apply union_iff in H1.
  destruct H1.
  assumption.
  contradiction.
  intro.
  apply diff_iff.
  split.
  generalize (union_iff (union_list l) (union_list l') a).
  intros.
  generalize (union_lists_union l l').
  intro.
  apply heap_equality in H3.
  apply heap_equality in H.
  rewrite <- H in H3.
  rewrite <- H3 in H2.
  apply H2.
  left; assumption.
  intro.
  apply pw_disjoint_lists_split in H0.
  destruct H0.
  destruct H3.
  apply (H4 a).
  apply inter_iff.
  split; assumption.
  apply pw_disjoint_lists_split in H0.
  destruct H0.
  assumption.
  split.
  apply heap_bits_iff in H.
  destruct H.
  apply heap_bits_iff.
  split.
  split.
  intro.
  apply diff_iff in H1.
  destruct H1.
  apply H in H1.
  apply union_lists_union in H1.
  apply union_iff in H1.
  destruct H1.
  contradiction.
  assumption.
  intro.
  apply diff_iff.
  split.
  generalize (union_iff (union_list l) (union_list l') a).
  intros.
  generalize (union_lists_union l l').
  intro.
  apply heap_equality in H3.
  apply heap_equality in H.
  rewrite <- H in H3.
  rewrite <- H3 in H2.
  apply H2.
  right; assumption.
  intro.
  apply pw_disjoint_lists_split in H0.
  destruct H0.
  destruct H3.
  apply (H4 a).
  apply inter_iff.
  split; assumption.
  apply pw_disjoint_lists_split in H0.
  destruct H0.
  destruct H1.
  assumption.
  split.
  apply heap_bits_iff in H.
  destruct H.
  generalize (union_lists_union l l').
  intro.
  apply heap_equality in H.
  apply heap_equality in H1.
  apply heap_equality.
  rewrite H.
  rewrite H1.
  reflexivity.
  apply heap_bits_iff in H.
  destruct H.
  apply pw_disjoint_lists_split in H0.
  destruct H0.
  destruct H1.
  assumption.
  intros.
  destruct H.
  destruct H0.
  destruct H1.
  apply heap_bits_iff.
  split.
  generalize (union_lists_union l l').
  intro.
  apply heap_equality in H3.
  apply heap_equality in H1.
  rewrite H1.
  rewrite H3.
  reflexivity.
  apply pw_disjoint_lists_split.
  split.
  apply heap_bits_iff in H.
  destruct H.
  assumption.
  split.
  apply heap_bits_iff in H0.
  destruct H0.
  assumption.
  assumption.
Qed.

(*The above along with the previous two commutativity corollaries, allow us to
 show that the heap_bits are append commutative.*)
Corollary heap_bits_lists_comm : forall (d : domain) (l l' : list domain),
                             heap_bits (l++l') d -> heap_bits (l'++l) d.
intros.
apply heap_bits_iff.
apply heap_bits_iff in H.
rewrite union_lists_comm.
destruct H.
split.
assumption.
apply pw_disjoint_lists_comm.
assumption.
Qed.

(*Removing the first bit is not fundamentally different from removing
 *a bit in the middle*)
Corollary remove_bit : forall (d s : domain) (l l': list domain),
                         heap_bits (l++s::l') d -> heap_bits (l++l') (diff d s).
intros.
apply heap_bits_lists_comm in H.
simpl in H.
apply pop_bit in H.
apply heap_bits_lists_comm in H.
assumption.
Qed.

(*Lets you add or remove the empty set from your bits at will*)
Lemma identity_bit : forall (d : domain) (l : list domain),
                       heap_bits l d <-> heap_bits (empty::l) d.
  intros.
  assert (d [=] (union empty d)).
  intro.
  split.
  intro.
  apply union_iff.
  right; assumption.
  intro.
  apply union_iff in H.
  destruct H.
  apply empty_iff in H.
  contradiction.
  assumption.
  apply heap_equality in H.
  split.
  intro.
  rewrite H.
  apply non_empty_heap.
  assumption.
  intro.
  intro.
  apply inter_iff in H1.
  destruct H1.
  apply empty_iff in H1.
  contradiction.
  intro.
  rewrite H in H0.
  inversion H0.
  assert (Empty empty).
  apply empty_spec.
  apply empty_union_1 with (s' := d0) in H6.
  assert (Empty empty).
  apply empty_spec.
  apply empty_union_1 with (s' := d) in H7.
  apply heap_equality in H6.
  apply heap_equality in H7.
  rewrite H3 in H6.
  rewrite H6 in H7.
  rewrite <- H7.
  assumption.
Qed.

(*Bit of a helper lemma, removing a subset from one of the bits removes that
  subset from the overall domain*)
Lemma remove_sub_bit : forall (s s' d : domain) (l : list domain),
                         s' [<=] s ->
                         heap_bits (s::l) d ->
                         heap_bits ((diff s s')::l) (diff d s').
  intros.
  assert (s [<=] d).
  apply subset_of_heap_bits with (l := (s::l)).
  simpl.
  left; reflexivity.
  assumption.
  assert (s' [<=] d).
  apply subset_trans with (s3 := d) in H.
  assumption.
  assumption.
  apply pop_bit in H0.
  apply non_empty_heap with (k := (diff s s')) in H0.
  assert (union (diff s s') (diff d s) [=] (diff d s')).
  intro.
  split.
  intro.
  apply union_iff in H3.
  destruct H3.
  apply diff_iff in H3.
  destruct H3.
  apply diff_iff.
  split.
  apply H1 in H3.
  assumption.
  assumption.
  apply diff_iff in H3.
  apply diff_iff.
  destruct H3.
  split.
  assumption.
  intro.
  apply H4.
  apply H in H5.
  assumption.
  intro.
  apply diff_iff in H3.
  destruct H3.
  apply union_iff.
  generalize (classic_set a s).
  intro.
  destruct H5.
  left.
  apply diff_iff.
  split.
  assumption.
  assumption.
  right.
  apply diff_iff.
  split.
  assumption.
  assumption.
  apply heap_equality in H3.
  rewrite H3 in H0.
  assumption.
  intro.
  intro.
  apply inter_iff in H3.
  destruct H3.
  apply diff_iff in H3.
  apply diff_iff in H4.
  destruct H3.
  destruct H4.
  contradiction.
Qed.

(*If a bit can be broken down into smaller bits then both decompositions together
 make up the larger domain*)
Lemma bit_decomposition_first : forall (l' : list domain), 
                                forall (s d : domain) (l : list domain),
                                  heap_bits (s::l) d ->
                                  heap_bits l' s ->
                                  heap_bits (l'++l) d.
  induction l'.
  intros.
  simpl.
  inversion H0.
  rewrite <- H2 in H.
  apply identity_bit in H.
  assumption.
  intros.
  simpl.
  generalize (IHl' (diff s a) (diff d a) l).
  intros.
  assert (a [<=] s).
  apply subset_of_heap_bits with (s := a) in H0.
  assumption.
  simpl.
  left; reflexivity.
  assert (s [<=] d).
  apply subset_of_heap_bits with (s := s) in H.
  assumption.
  simpl.
  left; reflexivity.
  apply pop_bit in H0.
  apply remove_sub_bit with (s' := a) in H.
  apply H1 in H.
  apply non_empty_heap with (k := a) in H.
  assert (union a (diff d a) [=] d).
  intro.
  split.
  intro.
  apply union_iff in H4.
  destruct H4.
  apply H2 in H4.
  apply H3 in H4.
  assumption.
  apply diff_iff in H4.
  destruct H4.
  assumption.
  intro.
  apply union_iff.
  generalize (classic_set a0 a).
  intro.
  destruct H5.
  left; assumption.
  right.
  apply diff_iff.
  split.
  assumption.
  assumption.
  apply heap_equality in H4.
  rewrite <- H4.
  assumption.
  intro.
  intro.
  apply inter_iff in H4.
  destruct H4.
  apply diff_iff in H5.
  destruct H5.
  contradiction.
  assumption.
  assumption.
Qed.

(*If a single bit can be further decomposed then that decomposition can replace the bit*)
Corollary bit_decomp : forall (l1 l2 l3: list domain) (s d : domain),
                         heap_bits (l1++s::l3) d ->
                         heap_bits l2 s ->
                         heap_bits (l1++l2++l3) d.
intros.
apply heap_bits_lists_comm in H.
simpl in H.
generalize (bit_decomposition_first l2 s d (l3++l1)).
intro.
apply heap_bits_lists_comm.
rewrite <- (List.app_assoc l2 l3 l1).
apply H1.
assumption.
assumption.
Qed.

(*Basic set fact, useful for the separating conjunction*)
Lemma diff_subset : forall (d d' : domain),
                      Dom.Subset (Dom.diff d d') d.
  intros.
  intro.
  intro.
  apply DomFacts.diff_iff in H.
  destruct H.
  assumption.
Qed.

(*Another useful lemma for the separating conjunction*)
Lemma double_diff : forall (s d : domain),
                      Dom.Subset s d -> Dom.Equal s (Dom.diff d (Dom.diff d s)).
  intros.
  split.
  intro.
  apply DomFacts.diff_iff.
  split.
  apply H in H0.
  assumption.
  intro.
  apply DomFacts.diff_iff in H1.
  destruct H1.
  contradiction.
  intro.
  apply DomFacts.diff_iff in H0.
  destruct H0.
  generalize (classic_set a s).
  intro.
  destruct H2.
  assumption.
  apply False_ind.
  apply H1.
  apply DomFacts.diff_iff.
  split.
  assumption.
  assumption.
Qed.

(*Ok, so the next three Ltacs are supposed to gather two heap_bits lists into one if possible*)
(*Someone that isn't terrible at writing Ltacs should probably have another go at this*)
Ltac heap_bits_gather :=
  let HB := fresh "HB" in
  match goal with
      | HB1 : heap_bits ?l2 ?s,
            HB2 : heap_bits (?l1 ++ ?s :: ?l3) ?d |-_ =>
       (generalize (bit_decomp l1 l2 l3 s d HB2 HB1);intro HB; simpl in HB; clear HB1; clear HB2)
  end.

Ltac split_on H s l l1 l2:=
  match l2 with
    |s::?tl => assert (l = (l1++(s::tl))) as H; auto; subst
    |?x::?tl => split_on H s l (l1++(x::nil)) tl
    |nil=>idtac
  end.

Ltac heap_bits_bubble :=
  let HB := fresh "HB" in
  match goal with
    |HB1 : heap_bits ?l1 empty,
           HB2 : heap_bits ?l2 ?d1 |- _ =>
     inversion HB1; subst; clear HB1
    |HB1 : heap_bits ?l1 ?d1,
           HB2: heap_bits ?l2 ?d2 |-_ =>
     try split_on HB d1 l2 (nil : list domain) l2; try split_on HB d2 l1 (nil : list domain) l1
     ;try rewrite HB in HB1; try rewrite HB in HB2; clear HB; heap_bits_gather
    | _ => idtac
  end.

(*A set is disjoint with the union of a family of sets iff it is disjoint with each set in the family separately, not currently in use*)
Lemma disjoint_with_union : forall (l : list domain) (a : domain),
                              Empty (inter a (union_list l)) <-> forall (s : domain), List.In s l -> Empty (inter a s).
  intros.
  split.
  intro.
  intros.
  intro.
  intro.
  generalize (H a0).
  intro.
  apply H2.
  apply inter_iff in H1.
  destruct H1.
  apply inter_iff.
  split.
  assumption.
  apply subset_of_union in H0.
  apply H0 in H3.
  assumption.
  intros.
  intro.
  intro.
  apply inter_iff in H0.
  destruct H0.
  apply element_of_union in H1.
  inversion H1.
  destruct H2.
  apply H in H3.
  generalize (H3 a0).
  intro.
  apply H4.
  apply inter_iff.
  split.
  assumption.
  assumption.
Qed.

(*Two elements of a pw_disjoint list are either identical or have no elements in common*)
Lemma pw_disjoint_elem : forall (s s' : domain)(l : list domain),
                          pw_disjoint l ->
                          List.In s l ->
                          List.In s' l ->
                          s [=] s' \/
                          Empty (inter s s').
  intros.
  induction l.
  inversion H0.
  inversion H0.
  inversion H1.
  rewrite <- H2.
  rewrite <- H3.
  left.
  apply heap_equality.
  reflexivity.
  right.
  inversion_clear H.
  rewrite H2 in H4.
  apply subset_of_union in H3.
  intro.
  intro.
  apply inter_iff in H.
  destruct H.
  apply H3 in H6.
  generalize (H4 a0).
  intro.
  apply H7.
  apply inter_iff.
  split;
  assumption.
  inversion H1.
  right.
  inversion_clear H.
  rewrite H3 in H4.
  apply subset_of_union in H2.
  intro.
  intro.
  apply inter_iff in H.
  destruct H.
  apply H2 in H.
  generalize (H4 a0).
  intro.
  apply H7.
  apply inter_iff.
  split;
  assumption.
  inversion_clear H.
  apply IHl;
  assumption.
Qed.                          

(*** Store stuff starts here ***)

(* Making vars into an ordered type so that there is a total
 * ordering on them
 *)

Module Var <: OrderedTypeWithLeibniz.
  Inductive variable : Set :=
  | var : forall (id : Z), variable.


  (* TODO: add types to vars.
   * The types will determine how the actual values are handled when they are stored or retrieved.  I think that
   * the typing is permanent and so casting only changes the interpretation of the information after it is retrieved.
   * Thus not much work needs to go into this at this point.
   *)
  (* 
  Inductive tag : Set :=
  | Muint32
  | Muint64
  | Msint32
  | Msint64
  | MStruct : list tag -> tag.

  Definition t := (prod (tag) (variable)).
   *)
  
  Definition t := variable.
  Definition eq (v w : t) := v = w.
  Definition lt (v w : t) := 
    match (v, w) with
      | (var n, var m) => n < m
    end.

  Lemma lt_trans : forall u v w : t, lt u v -> lt v w -> lt u w.
    intros. unfold lt in *. destruct u, v, w.  simpl in *.  omega.
  Qed.

  Lemma lt_not_eq : forall (v w : t), lt v w -> ~ eq v w.
    intros. destruct v, w. unfold lt in *. simpl in *. intro. unfold eq in H0. simpl in H0.
    injection H0. intros. rewrite H1 in H.
    omega.
  Qed.

  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Definition eq_equiv : Equivalence Logic.eq := @eq_equivalence t.

  Fixpoint compare (v w : t) :=
    match (v, w) with
        |(var n, var m) => Z.compare n m
    end.

  Lemma var_compare_eq : forall (v w : t), compare v w = Eq -> eq v w.
    intros.
    destruct v, w.
    inversion H.
    apply Z.compare_eq in H1.
    rewrite H1.
    unfold eq.
    simpl.
    reflexivity.
  Qed.

  Lemma var_compare_lt : forall (v w : t), lt v w <-> compare v w = Lt.
    destruct v, w.
    unfold compare.
    apply Z.compare_lt_iff.
  Qed.
  
  Lemma var_compare_gt : forall (v w : t), lt w v <-> compare v w = Gt.
    destruct v, w.
    unfold compare.
    apply iff_sym.
    apply Z.compare_gt_iff.
  Qed.

  Definition compare_spec : forall (x y : t), CompareSpec (eq x y)(lt x y)(lt y x)(compare x y)
    :=
      fun x y : t =>
        let c := compare x y in
        let Heqc := Logic.eq_refl in
        match
          c as c0
          return (compare x y = c0 -> CompareSpec (eq x y) (lt x y) (lt y x) c0)
        with
          | Eq =>
            fun Heqc0 : compare x y = Eq =>
              CompEq (lt x y) (lt y x) (var_compare_eq x y Heqc0)
          | Lt =>
            fun Heqc0 : compare x y = Lt =>
              CompLt (eq x y) (lt y x)
                     ((fun H : forall n m : t, lt n m <-> compare n m = Lt =>
                         let a := x in
                         (fun H0 : forall m : t, lt a m <-> compare a m = Lt =>
                            let a0 := y in
                            (fun H1 : lt x a0 <-> compare x a0 = Lt =>
                               match H1 with
                                 | conj _ H2 => H2 Heqc0
                               end) (H0 a0)) (H a)) var_compare_lt)
          | Gt =>
            fun Heqc0 : compare x y = Gt =>
              CompGt (eq x y) (lt x y)
                     ((fun H : forall n m : t, lt m n <-> compare n m = Gt =>
                         let a := x in
                         (fun H0 : forall m : t, lt m a <-> compare a m = Gt =>
                            let a0 := y in
                            (fun H1 : lt a0 x <-> compare x a0 = Gt =>
                               match H1 with
                                 | conj _ H2 => H2 Heqc0
                               end) (H0 a0)) (H a)) var_compare_gt)
        end Heqc.

  Lemma variable_dec :
    forall (v w : t),
      {eq v w} + {~eq v w}.
  Proof.
    intros v w.
    destruct v, w.
    unfold eq.
    decide equality.
    decide equality.
    decide equality.
    decide equality.
  Defined.

  Set Implicit Arguments.
  Lemma lt_strorder : StrictOrder lt.
    assert (Irreflexive lt).
    unfold Irreflexive.
    unfold Reflexive.
    intro.
    unfold complement.
    intro.
    apply lt_not_eq in H.
    apply H.
    reflexivity.
    assert (Transitive lt).
    unfold Transitive.
    apply lt_trans.
    apply (Build_StrictOrder lt H H0).
  Qed.
  Unset Implicit Arguments.
  
  Lemma eq_leibniz : forall (v w : t), eq v w -> v = w.
    unfold eq.
    auto.
  Qed.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
    unfold Proper.
    unfold respectful.
    intros.
    inversion H.
    inversion H0.
    split.
    intro.
    assumption.
    intro.
    assumption.
  Qed.
  
  Definition eq_dec := variable_dec.
End Var.

Module Vars := MakeWithLeibniz Var.
Definition var := Vars.elt.
Definition locals := Vars.t.
Module VarsFacts := WFactsOn Var Vars.
Module VarsProps := WPropertiesOn Var Vars.
Import Vars.
Import VarsFacts.
Import VarsProps.
Definition store_bits l s := elements s = l.
Definition store_f := locals -> var -> option val.
Definition store := var -> option val.

(*Much like heap_f, store_f is a partial function over
 *a locals domain*)
Axiom store_f_out_of_bounds :
  forall (s : store_f) (l : locals) (v : var), 
    ~Vars.In v l <-> s l v = None.

Axiom store_pf :
  forall (s : store_f) (l l' : locals) (x : var)(v : val),
    Vars.Subset l l' -> s l x = Some v -> s l' x = Some v.

(*The negation of store_f_out_of_bounds*)
Lemma store_f_in_bounds : 
  forall (s : store_f) (l : locals) (v : var), 
    Vars.In v l <->  exists x, s l v = Some x.
  intros.
  split.
  intro.
  generalize (classic (s l v = None)).
  intro.
  destruct H0.
  apply store_f_out_of_bounds in H0.
  contradiction.
  destruct (s l v).
  exists v0.
  reflexivity.
  apply False_ind.
  apply H0.
  reflexivity.
  intro.
  inversion H.
  generalize (classic (Vars.In v l)).
  intro.
  destruct H1.
  assumption.
  generalize (store_f_out_of_bounds s l v).
  intro.
  apply H2 in H1.
  rewrite H1 in H0.
  discriminate H0.
Qed.

(*Similar to the propagation of the heap, only without the
 *augmented In' function*)
Lemma locals_propagate : 
  forall (s : store_f) (l l' : locals) (x : var),
    In x l -> Vars.Subset l l' -> s l x = s l' x.
  intros.
  generalize (store_f_in_bounds s l x).
  intro.
  destruct H1.
  generalize (H1 H).
  intro.
  inversion_clear H3.
  rewrite H4.
  generalize (store_pf s l l' x x0 H0 H4).
  intro.
  rewrite H3.
  reflexivity.
Qed.

(*Set equality is again leibniz equality in this model*)
Axiom store_equality :
  forall (l l' : locals),
    Vars.Equal l l' <-> l = l'.

(*With the new machinery we have some annoyances that must be cleared up.*)
(*The more generic InA is essentially the same as List.In in our case*)
Lemma InA_ListIn_iff: forall (v : var) (vl : list var),
                        InA Logic.eq v vl <-> List.In v vl.
Proof.
  induction vl.
  split;
    intro;
    inversion H.
  split;
    intro;
    inversion_clear H;
    try rewrite H0.
  constructor.
  reflexivity.
  apply IHvl in H0.
  constructor 2.
  assumption.
  constructor.
  reflexivity.
  apply IHvl in H0.
  constructor 2.
  assumption.
Qed.

(*Similarly, the more generic NoDupA is essentially the same as List.NoDup*)
Lemma NoDupA_ListNoDup_iff: forall (vl : list var),
                              NoDupA Logic.eq vl <-> NoDup vl.
Proof.
  induction vl.
  split;
    intro;
    constructor.
  split.
  intro.
  constructor 2.
  inversion_clear H.
  intro.
  apply H0.
  apply InA_ListIn_iff.
  assumption.
  inversion_clear H.
  apply IHvl.
  assumption.
  intro.
  constructor 2.
  intro.
  inversion_clear H.
  apply H1.
  apply InA_ListIn_iff.
  assumption.
  apply IHvl.
  inversion_clear H.
  assumption.
Qed.

Lemma locals_def : forall (vl : list var) (l : locals),
                     store_bits vl l ->
                     (forall (v : var), List.In v vl <-> In v l).
Proof.
  intros.
  split.
  intro.
  inversion H.
  rewrite <- H1 in H0.
  apply InA_ListIn_iff in H0.
  assumption.
  intro.
  inversion H.
  apply InA_ListIn_iff.
  assumption.
Qed.

(* The existing machinery makes this trivial. *)
(* The list in store_bits has no duplicates *)
Lemma locals_nodup : forall (vl : list var) (l : locals),
                       store_bits vl l ->
                       NoDup vl.
Proof.
  intros.
  inversion H.
  apply NoDupA_ListNoDup_iff.
  apply elements_spec2w.
Qed.

(* This is a basic fact about lists, if your list has no duplicates
 * then the head of the list cannot appear again in the tail of the list
 *)
Lemma nodup_rem : forall {A : Type} (v w : A) (l : list A),
                    NoDup (v::l) ->
                    List.In w l ->
                    v <> w.
Proof.
  intros A v w l NODUP INW.
  inversion_clear NODUP as [|foo bar NOTIN NODUP'].
  intro.
  rewrite H in NOTIN.
  contradiction.
Qed.

(* A rehash of the above using the fact that the store_bits list
 * has no duplicates
 *)
Lemma locals_neq : forall (v w : var) (vl : list var) (l : locals),
                     store_bits (v::vl) l ->
                     List.In w vl ->
                     v <> w.
Proof.
  intros v w vl l.
  intro.
  apply locals_nodup in H.
  apply nodup_rem.
  assumption.
Qed.

(* The list of elemens in store_bits is canonical since it is
 * listed in terms of the total ordering
 *)
Lemma sb_canonical : forall (vl vl' : list var) (l : locals),
                       store_bits vl l ->
                       store_bits vl' l ->
                       vl = vl'.
  intros.
  unfold store_bits in *.
  rewrite H in H0.
  assumption.
Qed.

(* If the store_bits for a given locals, l, is a sublist of the store_bits
 * for another locals, l', then l is a subset of l'
 *)
Lemma locals_subset : forall (vl : list var)(l l' : locals)(x : var),
                        store_bits (x::vl) l' ->
                        store_bits vl l ->
                        Vars.Subset l l'.
  intros.
  intro.
  intro.
  apply locals_def with (v := a) in H.
  apply locals_def with (v := a) in H0.
  apply H.
  apply H0 in H1.
  simpl.
  right; assumption.
Qed.

Import List.

(*A set of ltacs that are useful in showing that two variables are not equal*)
Ltac contradict_locals variable :=
  match goal with 
    | ND : NoDup (?hd :: ?lst) |- _ =>
      inversion_clear ND ;
        match goal with
          | NI : ~ In variable ?lst, ND2 : NoDup ?lst |- _ =>
            simpl in NI; unfold not in NI; apply NI; clear ND2 NI 
          | NI : ~ In ?hd ?lst, ND2 : NoDup ?lst |- _ => clear NI; contradict_locals variable
        end
  end.

Ltac process_or variable :=
  match goal with
    | |- variable = variable \/ ?p => left;reflexivity
    | |- variable = variable => reflexivity
    | |- _\/_ => right;process_or variable
    | |-_ => idtac
end.

Ltac vunq :=
  match goal with
    | L : store_bits ?lst ?st |- ?a <> ?b =>
      intro;subst;apply locals_nodup in L;contradict_locals b; process_or b
    | |- _ => error
end.

(*Helpful notation to remove cluttering up heap_bits after a few allocs*)
Notation "'|{' a '}|'" := (Dom.singleton a) (at level 59, right associativity).
