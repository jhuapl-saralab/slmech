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

Require Import ZArith.
Require Import Lists.List.
Require Import Sorting.Sorted.
Require Import SequentialProof.
Require Import Assertions.
Require Import ProgramData.
Require Import ProgramSemantics.
Require Import String.
Require Import Ascii.
Require Import Automation.


Inductive heap_string : option val -> string -> sprop := 
| heap_string_null :
    forall (a : val) (st : state),
      (a ↦ (Z_to_uint64 0)) st ->
      heap_string (Some a) EmptyString st
| heap_string_step :
    forall (a : val) p q  (st : state),
      ((a ↦ Some (vnat (nat_of_ascii p)))☆(heap_string (vadd (Some a) (Z_to_uint64 1)) q)) st -> 
      heap_string (Some a) (String p q) st.

(*The store has no effect on a heap_string*)
Lemma heap_string_store_irrelevant : forall sv a, store_irrelevant (heap_string a sv).
  induction sv.
  unfold store_irrelevant.
  intros a s l s' l' h d H.
  inversion H.
  apply heap_string_null.
  simpl in *.
  assumption.

  unfold store_irrelevant.
  intros a0 s l s' l' h d H.
  inversion H.
  apply heap_string_step.
  inversion H4.
  subst.
  simpl in *.
  apply intro_ssep_conj with (d' := d').
  assumption.
  simpl.
  assumption.
  generalize (IHsv (vadd (Some a1) (Z_to_uint64 1))).
  intro.
  unfold store_irrelevant in H0.
  apply H0 with (s := s)(l := l).
  assumption.
Qed.

(*Less than relation for ascii characters*)
Definition aR a b := lt (nat_of_ascii a) (nat_of_ascii b).
Theorem aR_trans : Transitive aR.
Proof.
unfold Transitive.
unfold aR.
intros.
apply (lt_trans (nat_of_ascii x) (nat_of_ascii y) (nat_of_ascii z)) ; assumption.
Qed.

(*Inductive definition for a boolean less than operator over strings*)
Fixpoint sR a b :=
  match (a, b) with
    | (String a' a, String b' b) =>
      match (ascii_dec a' b') with
        | left _ => (sR a b)
        | right _ => (aR a' b')
      end
    | (EmptyString, _) => True
    | (_, EmptyString ) => False
  end.

Theorem sR_trans : Transitive sR.
unfold Transitive.
induction x.
intros.
unfold sR.
trivial.
intros.
destruct y ; unfold sR in H ; try contradiction ; fold (sR x y) in H.
destruct z ; unfold sR in H0 ; try contradiction ; fold (sR y z) in H0.
unfold sR ; fold (sR x z).
case (ascii_dec a a0) in H ;
  case (ascii_dec a0 a1) in H0 ;
  case (ascii_dec a a1) ;
  intros ;
  try subst a0 ;
  try subst a1 ;
  try (contradiction n ; reflexivity) ;
  try assumption ;
  try apply (IHx y z H H0).
unfold aR in *.
contradict H0.
apply (lt_asym (nat_of_ascii a) (nat_of_ascii a0)).
assumption.
generalize aR_trans.
unfold Transitive.
intros.
apply (H1 a a0 a1 H H0).
Qed.

(*Comparison of strings using sR*)
Fixpoint string_compare a b :=
  match (a, b) with
    | (String a' a, String b' b) =>
      match nat_compare (nat_of_ascii a') (nat_of_ascii b') with
        | Lt => Lt
        | Gt => Gt
        | Eq => string_compare a b
      end
    | (EmptyString, EmptyString) => Eq
    | (EmptyString, _) => Lt
    | (_, EmptyString) => Gt
  end.

(*
 * Axiomatic definition of the C strcmp function.
 * allows reasoning about programs that use strcmp.
 *)
Parameter strcmp : expr -> expr -> expr.

Axiom strcmp_spec : 
  forall (e0 e1 : expr) (s0 s1 : string)(l : locals)
         (v0 v1 : val) (s : store_f) (h1 h2 : heap_f)(d1 d2 : domain), 
    (s l) [[e0]] = Some v0 ->
    (s l) [[e1]] = Some v1 ->
    heap_string (Some v0) s0 (mkst s l h1 d1) -> 
    heap_string (Some v1) s1 (mkst s l h2 d2) ->
    ((s l) ⟦ strcmp e0 e1 ⟧ = match string_compare s0 s1 with
                                | Eq => Some (0:val)
                                | Lt => Some ((-1)%Z :val)
                                | Gt => Some (1:val)
                              end).

