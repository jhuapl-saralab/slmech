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

Require Import Setoid.
Require Import Sorted.
Require Import List.
Require Import Morphisms.

(*Helpful lemma for deconstructing a separating conjunction*)
Lemma unravel_star : forall (P Q : sprop)(s : store_f)(l : locals)
                            (h : heap_f)(d : domain),
                         (P☆Q)(mkst s l h d) ->
                         exists (d1 d2 : domain),
                           heap_bits (d1::d2::nil) d /\
                           P (mkst s l h d1) /\
                           Q (mkst s l h d2).
  intros.
  inversion_clear H.
  exists d'.
  exists (Dom.diff d d').
  split.
  apply heap_bits_iff.
  split.
  split.
  intro.
  apply DomFacts.union_iff.
  generalize (classic_set a d').
  intros.
  destruct H3.
  left; assumption.
  right.
  apply DomFacts.union_iff.
  left.
  apply DomFacts.diff_iff.
  split;assumption.
  intro.
  apply DomFacts.union_iff in H.
  destruct H.
  apply H0 in H.
  assumption.
  apply DomFacts.union_iff in H.
  destruct H.
  apply DomFacts.diff_iff in H.
  destruct H.
  assumption.
  apply DomFacts.empty_iff in H.
  contradiction.
  constructor.
  intro.
  intro.
  apply DomFacts.inter_iff in H.
  destruct H.
  simpl in H3.
  apply DomFacts.union_iff in H3.
  destruct H3.
  apply DomFacts.diff_iff in H3.
  destruct H3.
  contradiction.
  apply DomFacts.empty_iff in H3.
  contradiction.
  constructor.
  intro.
  intro.
  apply DomFacts.inter_iff in H.
  destruct H.
  simpl in H3.
  apply DomFacts.empty_iff in H3.
  contradiction.
  constructor.
  split; assumption.
Qed.

(* Recursively explode nested stars (separating conjunctions) in the hypothesis H. *)
Ltac nova_star H :=
  match type of H with
    | (_ ☆ _) {|srf := _ ; lc := _ ; hpf := _ ; dm := _|} =>
      apply unravel_star in H;
        let dom1 := fresh "d" in 
        let dom2 := fresh "d" in
        let TMP1 := fresh "TMP" in
        let TMP2 := fresh "TMP" in 
        let HB := fresh "HB" in
        let SPROP_L := fresh "SPROP" in
        let SPROP_R := fresh "SPROP" in
        inversion_clear H as [dom1 TMP1];
          inversion_clear TMP as [dom2 TMP2];
          destruct TMP2 as [HB TMP1];
          destruct TMP1 as [SPROP_L SPROP_R];
          try heap_bits_bubble;
          nova_star SPROP_L;
          nova_star SPROP_R
    | _ => simpl in H
  end.

(* In the hypothesis H, simplify occurrences of the expression e evaluated in store s with locals l. *) 
Ltac simplify_expression H s l e := 
  match e with
    | vexpr ?e0 => match type of H with
                                   (* if we've gotten e down to a var in the
                                    * original hypothesis H, then just leave it
                                    * be. Otherwise, if we can find a definition
                                    * for e, rewrite with the definition. 
                                    *)
                                   | s l ⟦ e0 ⟧ = Some ?v => idtac
                                   | _ => match goal with
                                            | [H0 : s l ⟦ e0 ⟧ = Some ?v |- _] => rewrite H0 in H
                                          end
                      end 
    | bexpr ?e0 => match type of H with
                                   (* if we've gotten e down to a var in the
                                    * original hypothesis H, then just leave it
                                    * be. Otherwise, if we can find a definition
                                    * for e, rewrite with the definition. 
                                    *)
                                   | s l ⟦ e0 ⟧ = Some ?v => idtac
                                   | _ => match goal with
                                            | [H0 : s l ⟦ e0 ⟧ = Some ?v |- _] => rewrite H0 in H
                                          end
                      end 
    | eplus ?e0 ?e1 =>simplify_expression H s l e0 ; 
                          simplify_expression H s l e1

    | eminus ?e0 ?e1 => simplify_expression H s l e0 ; 
                           simplify_expression H s l e1

    | emul ?e0 ?e1 => simplify_expression H s l e0 ; 
                         simplify_expression H s l e1

    | emod ?e0 ?e1 => simplify_expression H s l e0 ; 
                         simplify_expression H s l e1 

    | eimm ?e0     => try (unfold e0 in H ; simpl in H)

    | evar ?e0     => try match goal with
                            |[K : s l e0 = _ |- _] =>
                             rewrite K in H
                          end

    | band ?b0 ?b1 =>simplify_expression H s l b0 ; 
                          simplify_expression H s l b1

    | bor ?b0 ?b1 => simplify_expression H s l b0 ; 
                           simplify_expression H s l b1

    | bnot ?b0 => simplify_expression H s l b0
                                      
    | beq ?e0 ?e1 => simplify_expression H s l e0 ; 
                         simplify_expression H s l e1 

    | blt ?e0 ?e1 => simplify_expression H s l e0 ; 
                         simplify_expression H s l e1 

    | bgt ?e0 ?e1 => simplify_expression H s l e0 ; 
                         simplify_expression H s l e1 

    | ble ?e0 ?e1 => simplify_expression H s l e0 ; 
                         simplify_expression H s l e1 

    | bge ?e0 ?e1 => simplify_expression H s l e0 ; 
                         simplify_expression H s l e1 

    | bbool ?b0     => try (unfold b0 in H ; simpl in H)

    | _               => try (unfold e in H  ; simpl in H)
  end.

(* simplify all expressions in the hypothesis H *)
Ltac simpl_hyp H :=
  match type of H with
    | ?s ?l ⟦ ?e ⟧ = Some ?v => simpl in H ;
                               match e with
                                 | evar _ => idtac (* So the hypothesis does not eat itself*)
                                 | _ => simplify_expression H s l e
                               end               
    | (bbexpr (sr {| srf := ?s; lc := ?l; hpf := ?h; dm := ?d |}) ?be) = Some ?b => simpl in H;
                                                                                   simplify_expression H s l be
  end.

(* Eliminate references to temporary variables generated by assignment
 * and load statements. Doesn't clear the store/heap bindings, just pushes
 * the values through.
 *)
Ltac propagate := match goal with
                    | H: ?s ?l ⟦ ?e ⟧ = Some ?v |- _ => simpl in H ; rewrite <- H in *
                    | H: ?h ?d ?k = Some ?v |- _ => simpl in H; rewrite <- H in *
                    | _ => idtac
                  end.
