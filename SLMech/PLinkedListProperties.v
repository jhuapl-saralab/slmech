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
Require Import Memory.
Require Import ProgramData.
Require Import Assertions.
Require Import ProgramSemantics.
Require Import Automation.
Require Import List.

Set Implicit Arguments.

(*
 * Polymorphic linked list predicate.
 * Associates a linked list like data structure in the heap with a Coq list.
 * Parameters:
 *   elemT: an element type
 *   next:  a predicate relating the address of a node to the address of the next
 *   elem:  a predicate relating the address of a node to an instance of the element type
 *)
Inductive poly_linked_list (elemT : Type)  (next : addr -> addr -> sprop) (elem : addr -> elemT -> sprop):
  list addr -> list elemT -> val -> sprop :=
  | p_linked_list_null :
      forall (s : store_f)(l : locals)(h : heap_f)(term : val),
        poly_linked_list next elem nil nil term (mkst s l h Dom.empty)
  | p_linked_list_list :
      forall (a : addr) (e : elemT) (term : val) (al : list addr) (el : list elemT) (s : store_f) (h : heap_f)(l : locals)(d : domain),
        (al <> nil -> ~ ((hd (aval term) al) = term)) ->
        ((elem a e)☆(next a (hd (aval term) al))☆(poly_linked_list next elem al el term)) (mkst s l h d) ->
        poly_linked_list next elem (a::al) (e::el) term (mkst s l h d).

(*Linked lists independant from the store*)
Theorem poly_linked_list_store_irrelevant : forall (elemT : Type)
                                                   (next : addr -> addr -> sprop)
                                                   (elem : addr -> elemT -> sprop),
                                              (forall a a', store_irrelevant (next a a')) ->
                                              (forall a e, store_irrelevant (elem a e)) ->
                                              (forall al el term, store_irrelevant (poly_linked_list next elem al el term)).
Proof.
intros elemT next elem next_irrelevance elem_irrelevance.
induction al.
intros el term.
induction el;
unfold store_irrelevant ;
intros s l s' l' h d H.
inversion H.
apply p_linked_list_null.
inversion H.
induction el.
intros term.
unfold store_irrelevant.
intros s l s' l' h d H.
inversion H.
intros term.
unfold store_irrelevant.
intros s l s' l' h d H.
inversion H.
apply p_linked_list_list.
apply H5.
inversion H10.
inversion H17.
apply intro_ssep_conj with (d := d) (d' := d').
apply H14.
specialize elem_irrelevance with (a := a) (e := a0).
store_irrelevance.
apply intro_ssep_conj with (d := (Dom.diff d d')) (d' := d'0).
apply H21.
specialize next_irrelevance with (a := a) (a' := hd (aval term) al).
store_irrelevance.
specialize IHal with (el  := el) (term := term).
store_irrelevance.
Qed.


Hint Constructors poly_linked_list.
