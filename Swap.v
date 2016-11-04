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
Require Import ZArith.
Require Import String.
Require Import Ascii.
Require Import Setoid.
Require Import SetoidClass.
Require Import Morphisms.
Require Import Basics. 
Require Import SLMech.SequentialProof.
Require Import SLMech.Assertions.
Require Import SLMech.ProgramData.
Require Import SLMech.ProgramSemantics.
Require Import SLMech.Automation.

Theorem Swap :
  forall (x y z : var) (vx vy : val) (s : store_f) (h : heap_f) (l : locals) (d : domain) (st2 : state),
    (((fun st => (store_bits (x::y::nil) (lc st))) ☆
     (x ≐ Some vx) ☆
     (y ≐ Some vy)) {|srf := s ; lc := l; hpf := h; dm := d|}) ->
    (completes {|srf := s ; lc := l; hpf := h; dm := d|} st2
     (local z skip;;
       (z ≔ x);;
       (x ≔ y);;
       (y ≔ z);; ret ;; skip)) ->
    (((x ≐ Some vy) ☆ (y ≐ Some vx)) st2).
Proof.
  intros.
  nova_star H.
  program_paths H0.
  apply intro_ssep_conj with (d' := d).
  unfold Dom.Subset.
  intros.
  auto.
  simpl.
  auto.
  simpl.
  auto.
Qed.
