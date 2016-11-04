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

(** * Rules on sequential programs and soundness *)
Require Import ZArith.
Require Import Memory.
Require Import ProgramData.
Require Import Assertions.
Require Import ProgramSemantics.
Require Import Automation.

Require Import Setoid.
Require Import Sorted.
Require Import List.
Require Import Morphisms.
Require Import Classical.

Lemma bexpr_trichotomy : forall (b : bexpr)(st : state),
                           bbexpr st b = Some true \/
                           bbexpr st b = Some false \/
                           bbexpr st b = None.
  intros.
  induction (bbexpr st b).
  induction a.
  left; reflexivity.
  right; left; reflexivity.
  right; right; reflexivity.
Qed.

Lemma eq_bexpr_eq : forall (e1 e2 : expr)(s : store_f)(l : locals)(h : heap_f)(d : domain),
                      sprop_of_bexpr (e1 == e2) (mkst s l h d) <->
                      (exists (v : val), (s l) [[e1]] = Some v /\ (s l) [[e2]] = Some v /\ v <> Vundef).
  intros. split. intros.
  unfold sprop_of_bexpr in H.
  inversion H.
  induction (s l [[e1]]), (s l [[e2]]); try discriminate.
  destruct (valeq a v).
  exists v. rewrite e in *.
  induction v;
    try discriminate;
    try constructor;
    try reflexivity;
    try constructor;
    try reflexivity;
    try intro;
    try discriminate.
  apply False_ind.
  induction a, v; try discriminate.
  intros.
  destruct H.
  destruct H.
  destruct H0.
  unfold sprop_of_bexpr.
  simpl.
  rewrite H, H0.
  induction x; try (destruct (valeq _ _)); try reflexivity; try apply False_ind; try apply n; try reflexivity.
  apply False_ind.
  apply H1.
  reflexivity.
Qed.

Lemma bor_bexpr_or : forall (be1 be2 : bexpr)(s : store_f)(l : locals)(h : heap_f)(d : domain),
                       sprop_of_bexpr (be1 || be2) (mkst s l h d) <->
                       (exists (b1 b2 : bool), 
                          bbexpr (mkst s l h d) be1 = Some b1 /\
                          bbexpr (mkst s l h d) be2 = Some b2 /\
                          (b1  = true \/ b2 = true)).
  intros.
  split.
  intro.
  unfold sprop_of_bexpr in *.
  simpl in *.
  induction (bbexpr (s l) be1), (bbexpr (s l) be2); try discriminate.
  inversion H.
  apply orb_true_iff in H1.
  exists a, b.
  destruct H1; rewrite H0; constructor; try reflexivity; constructor; try reflexivity.
  left.
  simpl. reflexivity.
  right. symmetry. apply orb_true_iff. right; reflexivity.
  intros.
  destruct H.
  destruct H.
  destruct H.
  destruct H0.
  unfold sprop_of_bexpr in *.
  simpl in *.
  destruct H1.
  rewrite H1 in H. rewrite H.
  rewrite H0.
  simpl.
  reflexivity.
  rewrite H1 in H0. rewrite H0.
  rewrite H.
  assert (x || true = true).
  apply orb_true_iff.
  right; reflexivity.
  rewrite H2.
  reflexivity.
Qed.
  
Lemma band_bexpr_and : forall (be1 be2 : bexpr)(s : store_f)(l : locals)(h : heap_f)(d : domain),
                         sprop_of_bexpr (be1 && be2)(mkst s l h d) <->
                         sprop_of_bexpr be1 (mkst s l h d) /\
                         sprop_of_bexpr be2 (mkst s l h d).
  intros.
  split.
  intro.
  unfold sprop_of_bexpr in *.
  simpl in *.
  induction (bbexpr (s l) be1), (bbexpr (s l) be2); try discriminate.
  inversion H.
  rewrite H1.
  apply andb_true_iff in H1.
  destruct H1.
  rewrite H0, H1.
  constructor. reflexivity.
  reflexivity.
  intros.
  destruct H.
  unfold sprop_of_bexpr in *.
  simpl in *.
  induction (bbexpr (s l) be1), (bbexpr (s l) be2); try discriminate.
  assert (a && b = true).
  inversion H. inversion H0.
  simpl. reflexivity.
  rewrite H1.
  reflexivity.
Qed.  

Lemma leq_bexpr_ltb_eq : forall (e1 e2 : expr)(s : store_f)(l : locals)(h : heap_f)(d : domain),
                           sprop_of_bexpr (e1 <= e2) (mkst s l h d) <->
                           (sprop_of_bexpr (e1 == e2)(mkst s l h d) \/
                           sprop_of_bexpr (e1 < e2) (mkst s l h d)).
  intros.
  split.
  intros.
  unfold ble in H.
  apply bor_bexpr_or in H.
  destruct H. destruct H.
  destruct H. destruct H0.
  destruct H1. subst.
  right.
  unfold sprop_of_bexpr.
  assumption.
  subst.
  left.
  assumption.
  intros.
  unfold sprop_of_bexpr in *.
  apply bor_bexpr_or.
  destruct H.
  exists false, true.
  constructor.
  apply eq_bexpr_eq in H.
  destruct H.
  destruct H.
  destruct H0.
  induction x;
    simpl;
    rewrite H, H0;
    simpl;
    try assert (z <? z = false);
    try unfold Z.ltb;
    try assert (z = z);
    try reflexivity;
    try apply Z.compare_eq_iff in H2;
    try apply Z.compare_eq_iff in H3;
    try rewrite H2;
    try rewrite H3;
    try reflexivity;
    try rewrite H2;
    try rewrite H3;
    try reflexivity.
  apply False_ind. apply H1. reflexivity.
  constructor.
  assumption.
  right; reflexivity.
  exists true, false.
  constructor.
  assumption.
  constructor.
  simpl in *.
  induction (s l [[e1]]), (s l [[e2]]).
  induction a, v;
    simpl in *;
    try discriminate;
    try destruct (Z.eq_dec z0 z);
    try reflexivity;
    try rewrite e in H;
    apply False_ind;
    inversion H; try reflexivity;
    apply Zlt_is_lt_bool in H1;
    try omega.
  simpl in H. discriminate.
  simpl in H. discriminate.
  simpl in H. discriminate.
  left. reflexivity.
Qed.

Lemma not_bexpr : forall (b : bexpr)(s : store_f)(l : locals)(h : heap_f)(d : domain),
                    bbexpr (mkst s l h d) b <> None ->
                    (sprop_of_bexpr (bnot (b))(mkst s l h d) <-> ~(sprop_of_bexpr (b) (mkst s l h d))).
  intros.
  split.
  intro.
  intro.
  unfold sprop_of_bexpr in *.
  simpl in *.
  induction (bbexpr (s l) b).
  inversion H0.
  inversion H1.
  induction a; simpl in H3; try discriminate.
  discriminate.
  intros.
  unfold sprop_of_bexpr in *.
  simpl in *.
  induction (bbexpr (s l) b).
  induction a.
  apply False_ind.
  apply H0.
  reflexivity.
  simpl.
  reflexivity.
  apply False_ind.
  apply H.
  reflexivity.
Qed.
  

Lemma geq_bexpr_gtb_eq : forall (e1 e2 : expr)(s : store_f)(l : locals)(h : heap_f)(d : domain),
                        sprop_of_bexpr (e1 >= e2) (mkst s l h d) <->
                        (sprop_of_bexpr (e1 == e2)(mkst s l h d) \/
                         sprop_of_bexpr (e1 > e2) (mkst s l h d)).
  intros.
  split.
  intros.
  unfold ble in H.
  apply bor_bexpr_or in H.
  destruct H. destruct H.
  destruct H. destruct H0.
  destruct H1. subst.
  right.
  unfold sprop_of_bexpr.
  assumption.
  subst.
  left.
  assumption.
  intros.
  unfold sprop_of_bexpr in *.
  apply bor_bexpr_or.
  destruct H.
  exists false, true.
  constructor.
  apply eq_bexpr_eq in H.
  destruct H.
  destruct H.
  destruct H0.
  induction x;
    simpl;
    rewrite H, H0;
    simpl;
    try assert (z >? z = false);
    try unfold Z.gtb;
    try assert (z = z);
    try reflexivity;
    try apply Z.compare_eq_iff in H2;
    try apply Z.compare_eq_iff in H3;
    try rewrite H2;
    try rewrite H3;
    try reflexivity;
    try rewrite H2;
    try rewrite H3;
    try reflexivity.
  apply False_ind. apply H1. reflexivity.
  constructor.
  assumption.
  right; reflexivity.
  exists true, false.
  constructor.
  assumption.
  constructor.
  simpl in *.
  induction (s l [[e1]]), (s l [[e2]]).
  induction a, v;
    simpl in *;
    try discriminate;
    try destruct (Z.eq_dec z0 z);
    try reflexivity;
    try rewrite e in H;
    apply False_ind;
    inversion H; try reflexivity;
    apply Zgt_is_gt_bool in H1;
    try omega.
  simpl in H. discriminate.
  simpl in H. discriminate.
  simpl in H. discriminate.
  left. reflexivity.
Qed.


(*Ltac for resolving obvious contradictions usually found after an ifelse step*)
Ltac obvious_contr :=
  match goal with
    | H : ?a <> ?a |- _ =>
      apply False_ind; apply H; reflexivity
  end.
  
Lemma abort_doesnt_complete : forall (c : stmt)(s1 s2 : state),
                                completes s1 s2 (abort;;c) -> False.
  intros.
  unfold completes in H.
  destruct H.
  destruct H.
  case H; intro; subst.
  apply abort_seq_step_skip_false in H0.
  contradiction.
  apply abort_seq_step_ret_false in H0.
  contradiction.
Qed.

Lemma steps_skip_atom_split : forall (c : stmt)(a : atom)(s1 s2 : state),
                             steps ((astmt a);;c)(skip, s1)(skip, s2) -> 
                             (exists (s3 : state), step a (skip, s1)(skip, s3) /\
                                                   steps c (skip, s3)(skip, s2)).
  intros.
  inversion H.
  subst.
  inversion H3. subst. induction t2.
  exists s3.
  constructor; assumption.
  apply skip_follows_abort_false in H7. contradiction.
  apply skip_follows_ret_false in H7. contradiction.
Qed.

Lemma steps_ret_atom_split : forall (c : stmt)(a : atom)(s1 s2 : state),
                               steps ((astmt a);;c)(skip, s1)(ret, s2) -> 
                               a = (terminal ret) \/
                               (exists (s3 : state), step a (skip, s1)(skip, s3) /\
                               steps c (skip, s3)(ret, s2)).
  intros.
  inversion H.
  subst.
  inversion H3. subst. induction t2.
  right;exists s3.
  constructor;assumption.
  apply ret_follows_abort_false in H7. contradiction.
  induction a; inversion H2.
  subst. induction t; inversion H4.
  left; reflexivity.
Qed.

Lemma completes_atom_split : forall (c : stmt)(a : atom)(s1 s2 : state),
                               completes s1 s2 ((astmt a);;c)
                                         -> (a = (terminal ret) \/
                                            (exists (s3 : state), step a (skip, s1)(skip, s3) /\
                                            completes s3 s2 c)).
  intros.
  unfold completes in *.
  inversion H.
  induction x.
  destruct H0.
  apply steps_skip_atom_split in H1.
  inversion H1.
  right; exists x.
  constructor.
  inversion H2.
  assumption.
  exists skip.
  constructor.
  left; reflexivity.
  destruct H2.
  assumption.
  destruct H0.
  case H0; discriminate.
  destruct H0.
  apply steps_ret_atom_split in H1.
  destruct H1.
  left; assumption.
  right. destruct H1. exists x.
  constructor.
  destruct H1.
  assumption.
  exists ret.
  constructor.
  right; reflexivity.
  destruct H1.
  assumption.
Qed.

Lemma completes_skip_term_split : forall (c : stmt)(s1 s2 : state),
                                completes s1 s2 (skip;;c) -> completes s1 s2 c.
  intros.
  unfold completes in H.
  destruct H.
  destruct H.
  induction x.
  inversion H0.
  subst.
  inversion H4.
  subst.
  inversion H3.
  subst.
  inversion H5.
  subst.
  unfold completes.
  exists skip.
  constructor; assumption.
  case H; intro; discriminate.
  inversion H0.
  subst.
  inversion H4.
  subst.
  inversion H3.
  subst.
  inversion H5.
  subst.
  unfold completes.
  exists ret.
  constructor; assumption.
Qed.

Lemma completes_ret_term_split : forall (c : stmt) (s1 s2 : state),
                                   completes s1 s2 (ret;;c) -> s1 = s2.
  intros.
  unfold completes in H.
  destruct H.
  destruct H.
  induction x.
  inversion_clear H0. inversion_clear H1. inversion_clear H0. inversion H1. subst.
  apply skip_follows_ret_false in H2. contradiction.
  destruct H; discriminate.
  inversion_clear H0. inversion_clear H1. inversion_clear H0. inversion H1. subst.
  generalize (steps_well_defined c s3 s3 s2 ret ret ret (steps_returned c s3) H2).
  intro.
  inversion H0.
  reflexivity.
Qed.

Lemma completes_abort_term_false : forall (c : stmt)(s1 s2 : state),
                                     completes s1 s2 (abort;;c) -> False.
  intros.
  unfold completes in H.
  destruct H.
  destruct H.
  case H; intro; subst.
  inversion_clear H0. inversion_clear H1. inversion_clear H0. inversion H1. subst.
  generalize (steps_well_defined c s3 s3 s2 abort abort skip (steps_aborted c s3) H2).
  intro.
  discriminate.
  inversion_clear H0. inversion_clear H1. inversion_clear H0. inversion H1. subst.
  generalize (steps_well_defined c s3 s3 s2 abort abort ret (steps_aborted c s3) H2).
  intro.
  discriminate.
Qed.


Lemma final_skip : forall (s1 s2 : state),
                       completes s1 s2 skip -> s1 = s2.
  intros.
  unfold completes in H.
  destruct H.
  destruct H.
  induction x.
  inversion H0.
  subst.
  inversion H3.
  subst.
  inversion H4.
  reflexivity.
  case H; intro; discriminate.
  inversion H0.
  subst.
  inversion H3.
  subst.
  inversion H4.
Qed.

Lemma completes_ifelse_stmt_split : forall (s1 s2 : state)(c1 c2 c3: stmt)(b : bexpr),
                                      completes s1 s2 ((ifelse b c1 c2);; c3) ->
                                      ((bbexpr s1 b) = Some true /\ completes s1 s2 (c1;;c3)) \/
                                      ((bbexpr s1 b) = Some false /\ completes s1 s2 (c2;;c3)).
  intros.
  unfold completes in H.
  destruct H.
  destruct H.
  destruct H.
  subst.
  inversion H0.  subst.
  inversion H3; subst.
  right.
  constructor.
  assumption.
  unfold completes.
  exists skip.
  constructor.
  left; reflexivity.
  induction t2.
  apply (steps_seq c2 c3 s1 s3 s2 skip skip skip H9 H7).
  apply skip_follows_abort_false in H7. contradiction.
  apply skip_follows_ret_false in H7. contradiction.
  left.
  constructor.  assumption.
  unfold completes.
  exists skip.
  constructor.
  left; reflexivity.
  induction t2.
  apply (steps_seq c1 c3 s1 s3 s2 skip skip skip H9 H7).
  apply skip_follows_abort_false in H7.  contradiction.
  apply skip_follows_ret_false in H7. contradiction.
  apply skip_follows_abort_false in H7. contradiction.
  subst.
  inversion H0; subst.
  inversion H3; subst.
  right.
  constructor. assumption.
  unfold completes.
  exists ret.
  constructor.
  right; reflexivity.
  induction t2.
  apply (steps_seq _ _ _ _ _ _ _ _ H9 H7).
  apply ret_follows_abort_false in H7. contradiction.
  apply (steps_seq _ _ _ _ _ _ _ _ H9 H7).
  left.
  constructor.  assumption.
  unfold completes.
  exists ret.
  constructor.
  right; reflexivity.
  induction t2.
  apply (steps_seq _ _ _ _ _ _ _ _ H9 H7).
  apply ret_follows_abort_false in H7.  contradiction.
  apply (steps_seq _ _ _ _ _ _ _ _ H9 H7).
  apply ret_follows_abort_false in H7. contradiction.
Qed.

Lemma completes_while_stmt_split : forall (s1 s2 : state)(c1 c2 : stmt)(b : bexpr),
                                     completes s1 s2 ((while b c1);;c2) -> (exists (s3 : state),
                                                                              skips s1 s3 (while b c1)
                                                                              /\ completes s3 s2 c2)
                                                                            \/ returns s1 s2 (while b c1).
  intros.
  unfold completes in H.
  inversion_clear H. destruct H0. inversion_clear H. subst.
  inversion_clear H0.
  induction t2.
  left.
  exists s3.
  constructor.
  unfold skips.
  assumption.
  unfold completes.
  exists skip.
  constructor.
  left; reflexivity.
  assumption.
  apply skip_follows_abort_false in H1. contradiction.
  apply skip_follows_ret_false in H1. contradiction.
  subst.
  inversion_clear H0.
  induction t2.
  left.
  exists s3.
  constructor.
  unfold skips.
  assumption.
  unfold completes.
  exists ret.
  constructor.
  right; reflexivity.
  assumption.
  apply ret_follows_abort_false in H1. contradiction.
  right.
  generalize (steps_well_defined _ _ _ _ _ _ _ H1 (steps_returned _ _)).
  intro.
  inversion H0. subst.
  unfold returns.
  assumption.
Qed.

(** triples *)

(*
   This definition describes a Hoare triple: assuming that we have a
   trace that both satisfies P, and that we can use to take a step,
   then it satisfies Q. Partial correctess makes no guarantee that the
   step can (or will) be taken. We don't use this.

Definition ht_stmt (P : tprop) (C : stmt) (Q : tprop) : Prop := 
  forall (t t' : trace) tid,
    P t -> step_thread_star (mk_thread C tid, t) (mk_thread skip tid, t')
    -> Q t'.
*)


(*

The semantics of sequential triples require that the precondition
implies a safe computation as in Def. 8, p 4 of Parkinson's "Variables
as Resource in Hoare Logics." As Xinyu points out, this only works for
deterministic programs; the triple (sextuple?) that we will use for
concurrent programs must admit many possible traces t' in the second
term of the conjunct.

*)

Inductive striple (P : sprop) (C : stmt) (Q : sprop) : Prop := 
| ttriple_intro : (forall (st st' : state),
  P st -> ( ~ (aborts st st' C) /\
    (completes st st' C -> Q st'))) -> striple P C Q.


Ltac skip_steps_to_skip Crun := 
  match type of Crun with
      | steps ?tid (skip, ?t1) (skip, ?t2) =>
        inversion Crun; subst; clear Crun;
        [idtac |
         match goal with
           | H : step ?tid (skip, _) (_, _) |- _ => inversion H
         end]
  end.


Ltac prog_rassoc H :=
  repeat match type of H with 
    | steps ((?c1;;?c2);;?c3) (skip, ?st1) (skip, ?st2) => 
      change (steps' st1 st2 ((c1;;c2);;c3) skip) in H;
        rewrite (assoc_prog_equiv c1 c2 c3) in H;
        unfold steps' in H
    | completes ?st1 ?st2 ((?c1;;?c2);;?c3) => 
        rewrite (assoc_prog_equiv c1 c2 c3) in H;
        unfold steps' in H
  end.

Ltac make_neq w :=
  match goal with
    | [LOCALS : store_bits ?l ?s |- _] =>
      let LOCALSX := fresh "LOCALS" in
      generalize (locals_nodup LOCALS); intros LOCALSX
  end;

  repeat
    match goal with
      | [NODUP : NoDup (w :: ?l) |- _] =>
        (* idtac "matched w at front of nodup list"; *)
          fail 1
      | [NODUP : NoDup (?v :: ?l) |- _] =>
        (* idtac "matched not w at front of nodup list"; *)
        let NOTIN := fresh "NOTIN" in
        let NODUPX := fresh "NODUP" in
        let INWL := fresh "INWL" in
        let VNW := fresh "VNW" in
        assert (In w l) as INWL by (compute; tauto);
          assert (v<>w) as VNW by (apply (nodup_rem NODUP INWL)); clear INWL;
          inversion_clear NODUP as [|foo bar NOTIN NODUPX]; clear NOTIN
    end;

  (* idtac "entering second repeat"; *)
  repeat
    match goal with
      | [NODUP : NoDup nil |- _] =>
        (* idtac "nodup nil"; *)
          fail 1
      | [NODUPW : NoDup (w::?l),
         NODUPV : NoDup (?v::?l') |- _] =>
        (* idtac "found not w after w"; *)
        let NOTIN := fresh "NOTIN" in
        let NODUPX := fresh "NODUP" in
        let INVL := fresh "INVL" in
        let VNW := fresh "VNW" in
        assert (In v l) as INVL by (compute; tauto);
          assert (w<>v) as VNW by (apply (nodup_rem NODUPW INVL)); clear INVL;
          apply not_eq_sym in VNW;
          inversion_clear NODUPV as [|foo bar NOTIN NODUPX]; clear NOTIN
      | [NODUP : NoDup (w :: ?l) |- _] =>
        (* idtac "matched w at front of nodup list 2"; *)
          let foo := fresh "foo" in
          let bar := fresh "bar" in
          let NOTIN := fresh "NOTIN" in
        let NODUPX := fresh "NODUPFOO" in
        inversion NODUP as [|foo bar NOTIN NODUPX]; subst foo bar; clear NOTIN
        (* idtac "got here" *)
    end;

  (* idtac "entering third repeat"; *)
  repeat
    match goal with
      | [NODUP : NoDup _ |- _] => clear NODUP
    end.

Ltac clean_neq w :=
  repeat
    match goal with
      | [NEQ : _ <> w |- _] => clear NEQ
    end.

Ltac assert_completes a name := 
  match goal with 
    | H : steps (?c1, ?st1) (a, ?st2),
      b : a = skip \/ a = ret |- _ => 
      assert (completes st1 st2 c1) as name; [
          exists a; split; assumption
               | clear a b H]
  end.

Ltac skipc Crun := 
  prog_rassoc Crun; 
  match type of Crun with
    | completes ?st1 ?st2 (astmt (tatom skip);;?c1) => apply completes_skip_term_split in Crun
  end.

Ltac localc Crun := 
  let a := fresh "a" with
          b := fresh "b" with
              c := fresh "c" in
  prog_rassoc Crun
  ;match type of Crun with
    | completes ?st1 ?st2 (astmt (local ?v _);;?c2)
      => apply completes_atom_split in Crun
         ; destruct Crun as [a | b]; [discriminate
                          | destruct b as [c Crun]
                            ; destruct Crun as [a Crun]
                            ; inversion a
                            ; subst
                            ; clear a
                          ]
  end.

(*Simple Ltac for updating store_bits whenever a new variable
 *gets added to locals*)
Ltac update_locals :=
  let TMP := fresh "TMP" in
  match goal with
    | [NEW : store_bits (?v::?vl) ?l',
             OLD : store_bits ?vl ?l,
                   OLDEST : store_bits ?vl' ?l |- _] =>
      generalize (sb_canonical vl vl' l OLD OLDEST) as TMP;
        intro;rewrite TMP in NEW; clear OLD; clear OLDEST;
        clear TMP; clear vl; clear l
    | [NEW : store_bits (?v::?vl) ?l',
             OLD : store_bits ?vl Vars.empty |- _] =>
      compute in OLD; rewrite <- OLD in NEW; clear OLD; clear vl
  end.


(*Pops off the assignment step *)
Ltac assignc Crun := 
  let a := fresh "a"
           with b := fresh "b"
                    with c := fresh "c" in                           
  prog_rassoc Crun
  ;match type of Crun with
    | completes ?st1 ?st2 (astmt ?c1;;?c2)
      => apply completes_atom_split in Crun
         ; destruct Crun as [a | b]; [discriminate
                          | destruct b as [c Crun]
                            ; destruct Crun as [a Crun]
                            ; inversion a
                            ; subst
                            ; clear a
                          ]
  end.

Ltac heapwritec Crun := 
  let a := fresh "a"
           with b := fresh "b"
                    with c := fresh "c" in                           
  prog_rassoc Crun
  ;match type of Crun with
    | completes ?st1 ?st2 (astmt ?c1;;?c2)
      => apply completes_atom_split in Crun
         ; destruct Crun as [a | b]; [discriminate
                          | destruct b as [c Crun]
                            ; destruct Crun as [a Crun]
                            ; inversion a
                            ; subst
                            ; clear a
                          ]
  end.

Ltac allocc Crun := 
  let a := fresh "a"
           with b := fresh "b"
                    with c := fresh "c" in                           
  prog_rassoc Crun
  ;match type of Crun with
    | completes ?st1 ?st2 (astmt ?c1;;?c2)
      => apply completes_atom_split in Crun
         ; destruct Crun as [a | b]; [discriminate
                          | destruct b as [c Crun]
                            ; destruct Crun as [a Crun]
                            ; inversion a
                            ; subst
                            ; clear a
                          ]
  end.

Ltac retc Crun := 
  prog_rassoc Crun; 
  match type of Crun with
    | completes ?st1 ?st2 (astmt (tatom ret);;?c1) => (apply completes_ret_term_split in Crun); subst
  end.

Ltac loadc Crun := 
  let a := fresh "a"
           with b := fresh "b"
                    with c := fresh "c" in                           
  prog_rassoc Crun
  ;match type of Crun with
    | completes ?st1 ?st2 (astmt ?c1;;?c2)
      => apply completes_atom_split in Crun
         ; destruct Crun as [a | b]; [discriminate
                          | destruct b as [c Crun]
                            ; destruct Crun as [a Crun]
                            ; inversion a
                            ; subst
                            ; clear a
                          ]
  end.

Ltac disposec Crun := 
  let a := fresh "a"
           with b := fresh "b"
                    with c := fresh "c" in                           
  prog_rassoc Crun
  ;match type of Crun with
    | completes ?st1 ?st2 (astmt ?c1;;?c2)
      => apply completes_atom_split in Crun
         ; destruct Crun as [a | b]; [discriminate
                          | destruct b as [c Crun]
                            ; destruct Crun as [a Crun]
                            ; inversion a
                            ; subst
                            ; clear a
                          ]
  end.

Ltac whilec Crun := 
  let a := fresh "a" with
           b := fresh "b" with
                c := fresh "c" with
                     e := fresh "e" in
  prog_rassoc Crun; 
  match type of Crun with
    | completes ?st1 ?st2 ((while ?p ?q);;?c1) => 
      unfold completes in Crun; inversion Crun as [a [b c] ]; subst; clear Crun
  end.

Set Implicit Arguments.


Lemma seq_completes : forall c1 c2 st1 st2,
        completes st1 st2 (c1;;c2) ->
        (exists st', (skips st1 st' c1 /\ completes st' st2 c2)) \/
                    (returns st1 st2 c1).
  intros.
  inversion H.
  destruct H0.
  inversion_clear H1.
  case H0; intro; subst.
  induction t2.
  left;exists s2.
  unfold skips.
  constructor.
  assumption.
  unfold completes.
  exists skip.
  constructor.
  left; reflexivity.
  assumption.
  apply skip_follows_abort_false in H3.
  contradiction.
  apply skip_follows_ret_false in H3.
  contradiction.
  induction t2.
  left; exists s2.
  unfold skips; unfold completes.
  constructor.
  assumption.
  exists ret.
  constructor. right; reflexivity.
  assumption.
  apply ret_follows_abort_false in H3.  contradiction.
  right; unfold returns.
  generalize (steps_well_defined c2 s2 st2 s2 ret ret ret H3 (steps_returned c2 s2)).
  intro.
  inversion H1.
  subst.
  assumption.
Qed.

Lemma ret_completes : forall st, completes st st ret.
unfold completes; intros. exists ret. split. right. reflexivity. apply step_steps. apply step_state_step.
apply state_step_ret. intro. discriminate. Qed.

Lemma skip_completes : forall st, completes st st skip.
unfold completes; intros. exists skip. split. left. reflexivity. apply step_steps. apply step_state_step.
apply state_step_skip. Qed.

Unset Implicit Arguments.

Lemma seq_completing : forall C1 C2 st st'',
  steps (C1;; C2)(skip, st) (skip, st'') ->
  (exists st', steps (C1)(skip, st) (skip, st') /\ 
             steps (C2)(skip, st') (skip, st'')).
apply seq_composition.
Qed.

Lemma seq_forever : forall C1 C2 st st'',
  steps (C1;; C2)(skip, st) (abort, st'') ->
  steps (C1)(skip, st) (abort, st'') \/
  (exists st', steps (C1)(skip, st) (skip, st') /\
              steps (C2)(skip, st') (abort, st'')).
apply complete_seq_a.
Qed.

Lemma ld_abort_one_step : 
  forall x v st st', steps (x ≔[ v])(skip, st) (abort, st') ->
    exists st'', step (x ≔[ v])(skip, st) (abort, st'').
intros.
inversion H.
subst.
exists st'.
assumption.
Qed.

Lemma skip_star_same : forall st st', steps (skip) (skip, st) (skip, st') -> st = st'.
intros.
inversion H. subst. inversion H2. inversion H3. reflexivity. Qed.

Lemma ld_skip_one_step : 
  forall x v st st', steps (x ≔[ v])(skip, st) (skip, st') ->
    step (x ≔[ v])(skip, st) (skip, st').
intros.
inversion H. subst. assumption. Qed.

Definition bexpr_to_sprop (e : bexpr) : sprop := 
  fun st => bbexpr (sr st) e = Some true.

Coercion bexpr_to_sprop : bexpr >-> sprop.


Lemma terminating_program_does_not_abort : forall c z st,
  steps (c)(skip, st) (skip, z) ->
  (forall st', ~ steps (c)(skip, st) (abort, st')).
intros.
intro.
generalize (steps_well_defined c st z st' skip skip abort H H0).
intro.
discriminate.
Qed.

Ltac optional_equality :=
  match goal with
    |[H : Some ?x = None |- _] =>
     try discriminate H; optional_equality
    |[H : None = Some ?x |- _] =>
     try discriminate H; optional_equality
    |[H : Some ?x = Some ?y |- _] =>
     inversion H; subst; clear H; optional_equality
    |[H : None = None |- _] =>
     clear H; optional_equality
    | _ => idtac
  end.

(* Special case that follows a call to alloc, may need more testing*)
Ltac clean_store' s s' :=
  let TMP1 := fresh "TMP1" with
              TMP2 := fresh "TMP2" in
  match goal with
    |[H : forall (x' : var), ?x <> x' -> ?y <> x' -> (s ?l x') = (s' ?l x'),
        K : s ?l ?x = Some _ |- _ ] =>
     clear K; try clean_store' s s'
    |[H : forall (x' : var), ?x <> x' -> ?y <> x' -> (s ?l x') = (s' ?l x'),
        K : s ?l ?y = Some _ |- _] =>
     clear K; try clean_store' s s'
    |[H : forall (x' : var), ?x <> x' -> ?y <> x' -> (s ?l x') = (s' ?l x'),
        K : s ?l ?z = Some _ |- _] =>
     assert (x <> z) as TMP1
     ;[try vunq
      | assert (y <> z) as TMP2
        ;[ try vunq
         | apply (H z TMP1) in TMP2
           ;rewrite TMP2 in K
           ;clear TMP2
           ;clear TMP1]
      ]; try clean_store' s s'
    |[H : forall (x' : var), ?x <> x' -> ?y <> x' -> (s ?l x') = (s' ?l x') |- _] =>
     clear H
  end.

(*This should update all of the relevant store functions and store_irrelevant sprops
 *after a change to locals has occured*)
Ltac update_locals_sf :=
  let y := fresh "y" with
           SUBST := fresh "SUBST" with
                    TMP1 := fresh "TMP1" with
                            TMP2 := fresh "TMP2" with
                                    TMP := fresh "TMP" in
  match goal with
    | K : store_irrelevant (?P), 
          S : ?P {| srf := ?s; lc := ?l; hpf := ?h; dm := ?d |},
          OLDEST : store_bits ?vl' ?l,
          OLD : store_bits ?vl ?l,
          NEW : store_bits (?x::?vl) ?l' |- _ =>
      assert(P {| srf := s; lc := l'; hpf := h; dm := d |})
      ;[store_irrelevance
       | clear S]
    | H : ?s ?l ?y = Some ?v,
          OLDEST : store_bits ?vl' ?l,
          OLD : store_bits ?vl ?l,
          NEW : store_bits (?x::?vl) ?l' |- _ =>
      generalize (locals_subset vl l l' x NEW OLD) as SUBST
      ;intro; assert (Vars.In y l) as TMP1;
      [generalize (locals_def vl' l OLDEST y) as TMP;
        intro; assert (In y vl') as TMP2;
        simpl;
        process_or y;
        apply TMP in TMP2;
        assumption
      |generalize (locals_propagate s l l' y TMP1 SUBST);
        intro TMP2;
        rewrite TMP2 in H; update_locals_sf];
      clear TMP1 TMP2 SUBST
    | |- _ => idtac
  end.    

(*updates the store bits after a change to locals has occured*)
Ltac update_locals_sb :=
  let TMP := fresh "TMP" in
  match goal with
    | [NEW : store_bits (?v::?vl) ?l',
             OLD : store_bits ?vl ?l,
                   OLDEST : store_bits ?vl' ?l |- _] =>
      repeat update_locals_sf; generalize (sb_canonical vl vl' l OLD OLDEST) as TMP;
        intro;rewrite TMP in NEW;
        clear OLD OLDEST TMP vl l
    | [NEW : store_bits (?v::?vl) ?l',
             OLD : store_bits ?vl Vars.empty |- _] =>
      compute in OLD; rewrite <- OLD in NEW; clear OLD vl
    | |-_ => idtac
  end.


Import Dom.

(*
 * An unfortunate axioms to put a bandaid over the fact that our
 * data model is mostly abstract. Specifically, converting an adress
 * to a value and back doesn't change the address.
 *)
Axiom bijective_coercion_1 : forall (a : addr), (aval (vaddr a) = a).

(*Two Ltacs to clean up the heap_bits by removing the empty subdomains*)
Ltac remove_empty_bits l H :=
  match l with
    | nil => idtac
    | empty::_ => apply identity_bit in H
    | _::?tl => remove_empty_bits tl H
  end.

Ltac heap_bits_cleanup :=
  match goal with
    | H : heap_bits ?l ?d |- _ => remove_empty_bits l H
    | |-_ => idtac
  end.

(*Special ltac for heap_f functions whos domains can be
 *reduced to a single chunk, best used after an alloc*)
Ltac find_singleton a l l':=
  match l with
    | nil => idtac
    | (singleton a)::_ =>
      assert (In a (singleton a));
        [apply DomFacts.singleton_iff;
          reflexivity
        | assert (List.In (singleton a) l');
          [simpl;
            process_or (singleton a)
          | idtac]
        ]
    | _::?tl => find_singleton a tl l'
  end.

(*Often there are artifacts left over after a call to heapwrite or loadc that
 *rely on intermediate "facts" about the store (i.e. There will be a hypothesis
 *such as H0 : (s l) x = Some 4 then a call to heapwrite will leave us with
 *the additional hypotheses H1 : (s l) x = Some v and H2 : h d v = Some u).  
 *this ltac attempts to rewrite the old (usually more meaningful) value in the store
 *in place of the new less meaningful value.*)
Ltac old_is_new_sf :=
  let TMP := fresh "TMP" in
  match goal with
    |OLDS : ?s ?l ?x = Some ?v,
            NEWS : ?s ?l ?x = Some ?w,
                   NEWH : ?h ?d (aval ?w) = Some ?u |- _ =>
     rewrite OLDS in NEWS; injection NEWS as TMP; clear NEWS; symmetry in TMP; subst;
     try rewrite bijective_coercion_1 in NEWH
    |OLDV : ?s ?l ?x = Some ?v,
            NEWV : ?s ?l ?y = Some ?w,
                   NEWU : forall (z' : var), ?z <> z' -> (?s ?l z') = (?s' ?l z'),
  NEWS : ?s' ?l ?z = Some ?w |- _ => rewrite OLDV in NEWV; injection NEWV; intro; subst;
                                     optional_equality
      | |-_ => idtac
end.

(*This is an attempt to update any references to an old store_f while removing
 *outdated information*)
Ltac clean_store s s' :=
  let TMP := fresh "TMP" in 
  match goal with
    |[H : forall (x' : var), ?x <> x' -> (s ?l x') = (s' ?l x'),
        K : s ?l ?x = Some _ |- _ ] =>
     clear K; try clean_store s s'
    |[H : forall (x' : var), ?x <> x' -> (s ?l x') = (s' ?l x'),
        K : s ?l ?y = Some _,
        S: ?y = ?x |- _] =>
     clear K; try clean_store s s'
    |[H : forall (x' : var), ?x <> x' -> (s ?l x') = (s' ?l x'),
        K : s ?l ?y = Some _,
        S: ?x = ?y |- _] =>
     clear K; try clean_store s s'
    |[H : forall (x' : var), ?x <> x' -> (s ?l x') = (s' ?l x'),
        K : s ?l ?y = Some _ |- _] =>
     assert (x <> y) as TMP; try vunq; apply H in TMP; rewrite TMP in K
     ;clear TMP; try clean_store s s'
    |[H : forall (x' : var), ?x <> x' -> (s ?l x') = (s' ?l x'),
        K : store_irrelevant (?P), 
        S : ?P {| srf := s; lc := ?l; hpf := ?h; dm := ?d |} |- _] =>
     assert(P {| srf := s'; lc := l; hpf := h; dm := d |})
     ;[store_irrelevance
      | clear S]; try clean_store s s'
    | |- _ => idtac
  end.

(*Calls to the various simplifying and updating ltacs for stores*)
Ltac update_store_f :=
  match goal with
    |[H : ?s ?l [[?e]] = Some ?v |- _] =>
     simpl_hyp H; simpl in H; old_is_new_sf; optional_equality(*; update_store_f*)
    |[H : forall (x' : var), ?x <> x' -> (?s ?l x') = (?s' ?l x') |- _] =>
     old_is_new_sf; clean_store s s'; clear H; clear s
    |[H : forall (x' : var), ?x <> x' -> ?y <> x' -> (?s ?l x') = (?s' ?l x') |- _] =>
     old_is_new_sf; clean_store' s s'; clear H; clear s
    | |- _ => idtac
  end.

(*This is similar to the old_is_new_sf ltac, only the situation is reversed*)
Ltac old_is_new_hf :=
  let TMP := fresh "TMP" in
  match goal with
    |OLDH : ?h ?d ?a = Some ?v,
            NEWH : ?h ?d ?a = Some ?w,
                   NEWS : ?s ?l ?x = Some ?w |- _ =>
     rewrite OLDH in NEWH; injection NEWH as TMP; clear NEWH; symmetry in TMP; subst
  end.

(*Essentially this is for the situation where a heapfunction will evaluate to
 *two values on the same address, this shows that the two addresses must be
 *the same and subsequently uses the subst ltac to rewrite them all*)
Ltac clean_heaps :=
    let TMP1 := fresh "TMP1" with
                TMP2 := fresh "TMP2" with
                TMP3 := fresh "TMP3" in
    match goal with
      | HB : heap_bits ?l ?d,
             H1 : ?h ?d ?v1 = Some ?v2,
             H2 : ?h ?d' ?v1 = Some ?v3 |- _ =>
        assert (List.In d' l) as TMP1
         ;[ simpl; process_or d' 
          | generalize (subset_of_heap_bits d' d l TMP1 HB) as TMP2; intro; clear TMP1;
            generalize (heap_f_in_bounds h d' v1) as TMP1; intro; destruct TMP1 as [TMP1 TMP3];
            clear TMP1; assert (In' v1 d') as TMP1
            ;[ apply TMP3; exists v3; assumption
             |  generalize (domain_propagate h d' d v1 TMP1 TMP2)];
            clear TMP3; intro TMP3; rewrite <- TMP3 in H1; rewrite H2 in H1; optional_equality
          ]; clear TMP1 TMP2 TMP3
    end.

(*Two ltacs for dismantling a separating conjunction in the post condition
 *in the special case that one of the sprops in question is heap irrelevant*)
  Ltac clean_empty_diff :=
    let TMP1 := fresh "TMP1" with
         TMP2 := fresh "TMP2" with
         TMP3 := fresh "TMP3" in
    match goal with
      | |-_{| srf := ?s; lc := ?l; hpf := ?h; dm := (Dom.diff ?d Dom.empty)|} =>
        assert (Dom.Equal Dom.empty Dom.empty) as TMP1
        ;[apply heap_equality; reflexivity
         | generalize (DomProps.empty_is_empty_2 TMP1) as TMP2; intro;
           generalize (DomProps.empty_diff_2 d TMP2) as TMP3; intro;
           apply heap_equality in TMP3; rewrite TMP3]
        ;clear TMP1 TMP2 TMP3
    end.

  Ltac separate_on_empty_heap :=
    let TMP := fresh "TMP" in
    match goal with
        | |- (?S ☆ ?P) {| srf := ?s; lc := ?l; hpf := ?h; dm := ?d |} =>
          generalize (DomProps.subset_empty d) as TMP; intro; apply (intro_ssep_conj S P s l h TMP); 
          simpl; try assumption; try clean_empty_diff; clear TMP
    end.

(*Two ltacs similar to the separate_on_empty pair, that dismantle a separating
 *conjunction using a specific bit in heap_bits*)
Ltac delete_bits' b :=
  let TMP1 := fresh "TMP1" in
  match goal with
    |H : heap_bits ?ld ?d |- _ =>
     split_on TMP1 b ld (nil : list domain) ld; rewrite TMP1 in H; apply remove_bit in H;
     simpl in H; clear TMP1
  end.

  Ltac separate_on d' :=
    let TMP1 := fresh "TMP1" with
        TMP2 := fresh "TMP2" in
    match goal with
      |H : heap_bits ?ld ?d |- (?S ☆ ?P) {| srf := ?s; lc := ?l; hpf := ?h; dm := ?d |} =>
        assert(List.In d' ld) as TMP1;
         [simpl; process_or d'
         | generalize (subset_of_heap_bits d' d ld TMP1 H) as TMP2; intro;
           apply (intro_ssep_conj S P s l h TMP2)]
         ;clear TMP1 TMP2; delete_bits' d'
    end.

(*Ltac for removing a bit in heap_bits after a dispose call, currently very limited in use*)
 Ltac delete_bits :=
   let TMP := fresh "TMP" with
              TMP1 := fresh "TMP1" with
                      TMP2 := fresh "TMP2" in
   match goal with
     | H : heap_bits ?l ?d,
           K : ?d' [=] remove ?a ?d |- _ =>
       split_on TMP (singleton a) l (nil : list domain) l;
         rewrite TMP in H; apply remove_bit in H; simpl in H; clear TMP;
         assert (remove a d [=] diff d (singleton a)) as TMP
         ;[intro; split
           ;[intro TMP1; apply DomFacts.remove_iff in TMP1; destruct TMP1;
             apply DomFacts.diff_iff; split; [assumption
                                             | intro TMP1;
                                               apply DomFacts.singleton_iff in TMP1;
                                               contradiction]
            | intro TMP1; apply DomFacts.diff_iff in TMP1; destruct TMP1 as [TMP1 TMP2];
              apply DomFacts.remove_iff; split
              ;[assumption | intro; apply TMP2; apply DomFacts.singleton_iff; assumption]
            ]
          | apply heap_equality in K; apply heap_equality in TMP; rewrite <- TMP in H;
            rewrite <- K in H]; clear K TMP
   end.


(*attempts to refine the domain of any heap_f partial function to a single
 *bit found in heap_bits, currently very limited in use as it only handles
 *singleton bits (for use after an alloc)*)
Ltac refine_heap_f :=
  let TMP0 := fresh "TMP0" with
      TMP1 := fresh "TMP1" in
      heap_bits_cleanup;
      match goal with
        (*alloc case*)
        | K : ?h ?d ?a = Some ?v,
              L : heap_bits ?l ?d,
                  M : Keys.In ?a ?c |- _=>
          find_singleton c l l
          ;match goal with
             |H : In c (singleton c),
                  J : List.In (singleton c) l |- _ =>
              assert (In' a (singleton c)) as TMP0
              ;[apply In'_iff; exists c; split
                ;[assumption | apply DomFacts.singleton_iff; reflexivity]
               | generalize (subset_of_heap_bits (singleton c) d l J L); intro TMP1
                 ;generalize (domain_propagate h (singleton c) d a TMP0 TMP1)
                 ;clear TMP0 TMP1; intro TMP0; rewrite <- TMP0 in K]
              ;clear H J TMP0
             | |-_ => idtac
           end
        | |-_ => idtac
      end.

Ltac clean_values :=
  match goal with
    | H : Z_to_uint64 ?z = Some ?v |- _ => compute in H
                                           ; try optional_equality
                                           ; simpl in *
                                           ; clean_values
    | H : Some ?v = Z_to_uint64 ?z |- _ => compute in H
                                           ; try optional_equality
                                           ; simpl in *
                                           ; clean_values
    | H : Z_to_sint64 ?z = Some ?v |- _ => compute in H
                                           ; try optional_equality
                                           ; simpl in *
                                           ; clean_values
    | H : Some ?v = Z_to_sint64 ?z |- _ => compute in H
                                           ; try optional_equality
                                           ; simpl in *
                                           ; clean_values
    | H : Z_to_uint32 ?z = Some ?v |- _ => compute in H
                                           ; try optional_equality
                                           ; simpl in *
                                           ; clean_values
    | H : Some ?v = Z_to_uint32 ?z |- _ => compute in H
                                           ; try optional_equality
                                           ; simpl in *
                                           ; clean_values
    | H : Z_to_sint32 ?z = Some ?v |- _ => compute in H
                                           ; try optional_equality
                                           ; simpl in *
                                           ; clean_values
    | H : Some ?v = Z_to_sint32 ?z |- _ => compute in H
                                           ; try optional_equality
                                           ; simpl in *
                                           ; clean_values
    | |- _ => idtac
  end.

Ltac ifelsec Crun :=
  let a := fresh "IF_STMT_BEXPR"
           with b := fresh "b"
                     with c := fresh "c" in
  prog_rassoc Crun
  ; match type of Crun with
      | completes ?st1 ?st2 ((ifelse ?b ?c1 ?c2);;?c3)
        => apply completes_ifelse_stmt_split in Crun
           ; destruct Crun as [Crun | Crun]
           ; destruct Crun as [a Crun]
           ; simpl_hyp a
    end.

Lemma verbose_state : forall (P : sprop),
                             (forall (st : state), P st) <->
                             (forall (s : store_f)(l : locals)(h : heap_f)(d : domain),
                                P (mkst s l h d)).
  intros.
  split.
  intros.
  apply H.
  intros.
  induction st.
  apply H.
Qed.

Lemma verbose_while_rule_skip : forall (b : bexpr)(c : stmt)(LI : sprop),
                                     (forall (s : store_f)(l : locals)
                                             (h : heap_f)(d : domain)(st : state),
                                        steps c (skip, (mkst s l h d))(skip, st) ->
                                        sprop_of_bexpr b (mkst s l h d) /\ LI (mkst s l h d)  ->
                                        LI st) ->
                                     (forall (s' : store_f)(l' : locals)
                                             (h' : heap_f)(d' : domain)(st' : state),
                                        LI (mkst s' l' h' d') ->
                                        steps (while b c)(skip, (mkst s' l' h' d'))(skip, st')->
                                        not ((sprop_of_bexpr b) st') /\ LI st').
intros.
assert (forall (s s' : state), steps c (skip, s)(skip, s') ->
        sprop_of_bexpr b s /\ LI s -> LI s'). 
intros.
induction s.
apply (H srf lc hpf dm s'0 H2 H3).
apply (while_rule_skip b c LI H2 (mkst s' l' h' d') st' H0 H1).
Qed.


(*Workhorse ltac for consuming and updating as much of the program as possible*)
(*Due to how much memory is used by the Ltacs I've decided to have this end at any occurance of an ifelse stmt*)
Ltac program_paths Crun :=         
  prog_rassoc Crun; match goal with 
    | H : completes ?st1 ?st2 (astmt (tatom skip);;?c1) |- _ => skipc Crun; program_paths Crun
    | H : completes ?st1 ?st2 (astmt (local ?v skip);;?c1) |- _ => localc Crun; update_locals_sb; program_paths Crun
    | H : completes ?st1 ?st2 ((ifelse ?t ?c1 ?c2);;?c3) |- _ => ifelsec Crun; clean_values
    | H : completes ?st1 ?st2 (astmt (dispose ?e);;?c1) |- _ => disposec Crun; program_paths Crun
    | H : completes ?st1 ?st2 (astmt (assign ?p ?q);;?c1) |- _ => assignc Crun; repeat update_store_f; program_paths Crun
    | H : completes ?st1 ?st2 (astmt (pcons ?p ?q ?r);;?c1) |- _ => allocc Crun
                                                                    ; repeat update_store_f
                                                                    ; heap_bits_bubble
                                                                    ;program_paths Crun
    | H : completes ?st1 ?st2 (astmt (tatom ret);;?c1) |- _ => retc Crun; program_paths Crun
    | H : completes ?st1 ?st2 (astmt (tatom skip)) |- _ => (apply final_skip in Crun); subst; clean_values
    | H : completes ?st1 ?st2 (astmt (heapload ?p ?q);;?c1) |- _ => loadc Crun; repeat update_store_f; program_paths Crun
    | H : completes ?st1 ?st2 (astmt (heapwrite ?e1 ?e2);;?c1) |- _ => heapwritec Crun; program_paths Crun
    | H : completes ?st1 ?st2 (astmt (tatom abort);;?c1) |- _ => (apply abort_doesnt_complete in Crun); contradiction
    | |- _ => clean_values; idtac
  end.


(*The motivation for this follows from the current implementation
 *of heap_writes the idea being that we should, at some point, have
 *already obtained the In' statements then an Ltac similar to vunq
 *can go through and rewrite fairly large numbers of heap statements*)
Lemma separate_frame : forall (v w : val)(h h' : heap_f)(l : list domain)
                              (s d' d : domain) (a : addr),
                         (forall (v' : val), (aval v' <> aval v) ->
                                             h d (aval v') =  h' d (aval v')) ->
                         In' (aval v) s ->
                         In' (aval w) d' ->
                         List.In s l ->
                         List.In d' l ->
                         heap_bits l d ->
                         s <> d' ->
                         h d' (aval w) = h' d' (aval w).
  intros.
  generalize (classic (aval w = aval v)).
  intro.
  destruct H6.
  rewrite H6 in *.
  apply In'_iff in H0.
  inversion_clear H0.
  destruct H7.
  apply In'_iff in H1.
  inversion_clear H1.
  destruct H8.
  generalize (chunk_unique x x0 (aval v) H0 H1).
  intro.
  subst.
  apply bits_pw_disjoint in H4.
  generalize (pw_disjoint_elem s d' l H4 H2 H3).
  intro.
  destruct H9.
  apply heap_equality in H9.
  contradiction.
  apply False_ind.
  generalize (H9 x0).
  intro.
  apply H10.
  apply DomFacts.inter_iff.
  split; assumption.
  apply H in H6.
  generalize (subset_of_heap_bits d' d l H3 H4).
  intro.
  generalize (domain_propagate h d' d (aval w) H1 H7).
  intro.
  generalize (domain_propagate h' d' d (aval w) H1 H7).
  intro.
  rewrite H9.
  rewrite H8.
  rewrite H6.
  reflexivity.
Qed.
  
  

(*****DEMOS GO HERE******)
(*Toy lemma for showing off the automation of the store stuff*)
Lemma basic_local_and_assignment : forall (w x y z : var) (a : val) (s : store_f)(l : locals)
                   (h : heap_f)(d : domain)(st2 : state),
              (store_bits (w::nil) l) /\ (w  ≐  Some a) (mkst s l h d) /\ 
              (completes (mkst s l h d) st2
                         (local x skip;;
                          local z skip;;
                          skip;;
                          (x  ≔ eimm (Z_to_uint64 (1)));;
                          local y skip;;
                          (y  ≔ (w + eimm (Z_to_uint64(7))));;
                          (z  ≔ (w - y));;
                          skip)
              ) ->
              (w ≐ Some a)st2 /\
              (x ≐ (Z_to_uint64 (1)))st2 /\
              (y ≐ (vadd (Some a) (Z_to_uint64 7)))st2 /\
              (z ≐ (vsub (Some a) (vadd (Some a) (Z_to_uint64 7))))st2.
  intros.
  destruct H. destruct H0.
  simpl in H0.
  program_paths H1.
(*  rewrite H5 in *.*)
  rewrite <- H6 in *.
  rewrite <- H7 in *.
  constructor. assumption.
  constructor. assumption.
  constructor. assumption.
  induction a; simpl in *; inversion H6; subst; assumption.
Qed.

Lemma basic_ifelse : forall (x y : var)(s : store_f)(l : locals)(h : heap_f)(st2 : state),
                       (completes (mkst s l h Dom.empty) st2
                                  (
                                    local x skip;;
                                    local y skip;;
                                    (x  ≔ eimm (Z_to_uint64 0));;
                                    (y  ≔ eimm (Z_to_uint64 1));;
                                    (ifelse (x == y) (x ≔ (x + y)) (y ≔ (eminus x y)) );;
                                    skip
                                  )
                       ) ->  
                       ( (y ≐ (Z_to_uint64 (-1)%Z)) st2 /\ (x  ≐ (Z_to_uint64 0)) st2).
  intros.
  program_paths H.
  discriminate.
  program_paths H.
  constructor; assumption.
Qed.

(*Much more challenging.  This runs into the problem of our not-quite-so-well-defined
data model.  Ltac creation is effectively stalled.*)
Lemma bar : forall (x y z memaddr err : var)(s : store_f)(l : locals)
                   (h : heap_f)(st2 : state),
              (store_bits (err::memaddr::nil) l /\
               (completes (mkst s l h Dom.empty) st2
                          (
                            local x skip;;
                            local y skip;;
                            local z skip;;
                            
                            〈err, memaddr〉 ≔ alloc(2);;
                            (ifelse (err == eimm (Some ERR_SUCCESS) )(
                              (x  ≔ 2);;
                              (y  ≔ 1);;
                              (z  ≔ memaddr);;
                              ([z]≔ (x + y));;
                              (x  ≔[z]);;
                              skip)
                              skip);;
                            skip
                          )
               )
              )
                ->
               (sexists (fun (a : addr) =>
                           (memaddr ≐ Some (vaddr a)) ☆
                           (a ↦ (vadd (Z_to_uint64 1) (Z_to_uint64 2))) ☆
                           (err ≐ Some ERR_SUCCESS) ☆
                           (x ≐ vadd (Z_to_uint64 1) (Z_to_uint64 2)) ☆
                           (y ≐  Z_to_uint64 1) ☆
                           (z ≐ Some (vaddr a))
                        )
               ) st2 \/ (err ≐ Some ERR_ERROR )st2.
  intros.
  destruct H.
  program_paths H0.
  program_paths H0.
  left.
  exists a0.
  separate_on_empty_heap.
  unfold base_pointer in H16.
  destruct H16.
  generalize (bits_cover_domain (|{c0}|::nil) d' H14).
  intro.
  simpl in H1.
  assert ((union (|{c0}|) empty) = |{c0}|).
  apply heap_equality.
  unfold Equal.
  intros.
  split.
  intro.
  apply DomFacts.union_iff in H2.
  destruct H2.
  assumption.
  apply DomFacts.empty_iff in H2.
  contradiction.
  intro.
  apply DomFacts.union_iff.
  left; assumption.
  rewrite H2 in H1.
  apply heap_equality in H1.
  subst.
  separate_on (|{c0}|).
  separate_on_empty_heap.
  separate_on_empty_heap.
  rewrite H17 in H21.
  rewrite <- H21 in H23.
  assumption.
  separate_on_empty_heap.
  induction ERR_SUCCESS; try discriminate; try destruct (valeq _ _); try discriminate; try obvious_contr.
  program_paths H0.
  left.
  exists a0.
  separate_on_empty_heap.
  unfold base_pointer in H16.
  destruct H16.
  rewrite H22 in H24.
  rewrite <- H24 in H26.
  refine_heap_f.
  separate_on (|{c0}|).
  separate_on_empty_heap.
  separate_on_empty_heap.
  separate_on_empty_heap.
  destruct (valeq ERR_SUCCESS ERR_SUCCESS).
  try optional_equality.
  try obvious_contr.
  induction ERR_SUCCESS; try discriminate; try destruct (valeq _ _); try discriminate; try obvious_contr.
  obvious_contr.
  destruct (valeq ERR_ERROR ERR_SUCCESS).
  generalize (error_vals). intro. rewrite e in H. try obvious_contr. try optional_equality.
  induction ERR_ERROR, ERR_SUCCESS; try discriminate; try destruct (valeq _ _); try discriminate; try obvious_contr.
  program_paths H0.
  right.
  simpl.
  assumption.
Qed.

Ltac assert_LI LI Crun :=
  let a := fresh "while_rule_body" with
           t1 := fresh "TMP1" with
                 t2 := fresh "loop_invariant_init" in
  match type of Crun with
    | steps (while ?b ?c)(skip, ?s1) (skip, ?st2) =>
      (assert (LI s1 /\
               forall (s : store_f)(l : locals)
                      (h : heap_f)(d : domain)(st : state),
                 steps c (skip, (mkst s l h d))(skip, st) ->
                 sprop_of_bexpr b (mkst s l h d) /\
                 LI (mkst s l h d) ->
                 LI st) as t1)
      ;[clear Crun
       |destruct t1 as [t2 a]; (generalize
                                  (verbose_while_rule_skip b c LI a
                                                           (srf s1)
                                                           (lc s1)
                                                           (hpf s1)
                                                           (dm s1)
                                                           st2
                                                           t2
                                                           Crun))
        ;clear a
        ;clear t2
        ;clear Crun]
  end.

(*Experimental attempt to move past while statements*)
Lemma basic_while : forall (x y : var)(s : store_f)(l : locals)(h : heap_f)(d : domain)(st2 : state),
                      (completes (mkst s l h d) st2
                                 (local x skip;;
                                  local y skip;;
                                  (y ≔ 1);;
                                  (x ≔ 0);;
                                  while (x < 4)
                                  ( (y ≔ y + 1);;
                                    (x ≔ x + 1);;
                                    skip);;
                                  skip)) ->
                      (y ≐ (Z_to_uint64 5)) st2 /\ (x ≐ (Z_to_uint64 4)) st2.
  intros.
  program_paths H.
  apply (completes_while_stmt_split) in H.
  inversion_clear H.
  inversion_clear H0 as [s H].
  destruct H.
  unfold skips in H.
  assert_LI (fun (st : state) =>
             (lc st = l'0)
             /\ (hpf st = h)
             /\ (dm st = d)
             /\ (exists (z1 : Z), (st [[x]] = Z_to_uint64 z1)
                                 /\ 0 <= z1 <= 4
                                 /\ (st [[y]] = Z_to_uint64 (z1 + 1)))) H.
  simpl in *.
  constructor. constructor. reflexivity.
  constructor. reflexivity.
  constructor. reflexivity.
  exists 0.
  constructor.
  assumption.
  constructor.
  omega.
  assumption.
  intros.
  destruct H1.
  destruct H2.
  destruct H3.
  destruct H5.
  destruct H6.
  destruct H6.
  destruct H7.
  unfold sprop_of_bexpr in H1.
  simpl in H1.
  apply steps_skip_atom_split in H.
  destruct H.
  destruct H.
  inversion H. subst.
  simpl in H17.
  rewrite H8 in H17.
  rewrite <- H17 in H22.
  clear H17. clear H8.
  simpl in H22.
  assert (y <> x).
  vunq.
  apply H21 in H2.
  rewrite H2 in H1.
  rewrite H2 in H6.
(*  rewrite H6 in H1.*)
  clear H2.
  clear H.
(*  simpl in H1.*)
  apply steps_skip_atom_split in H9.
  destruct H9.
  destruct H.
  inversion H. subst.
  simpl in H10.
  rewrite H6 in H10.
  rewrite <- H10 in H18.
  rewrite H6 in H1.
  assert (x <> y).
  vunq.
  apply H17 in H3.
  rewrite H3 in *.
  clear H17.
  clear H.
  clear H21.
  clear H6.
  clear H3.
  inversion_clear H2.
  inversion_clear H.
  inversion H2. subst. clear H2.
  simpl in *.
  constructor. reflexivity.
  constructor. reflexivity.
  constructor. reflexivity.
  exists (x0 mod uint64_max + 1 mod uint64_max)%Z.
(*  rewrite <- H14 in H19.*)
  constructor.
  assumption.
  assert (0 <= 1 < uint64_max).
  unfold uint64_max.
  omega.
  generalize (Zmod_small 1 uint64_max H).
  intro.
  rewrite H2 in *.
  assert (0 <= x0 < uint64_max).
  unfold uint64_max.
  omega.
  generalize (Zmod_small x0 uint64_max H3).
  intro.
  rewrite H5 in *.
  assert (0 <= 4 < uint64_max).
  unfold uint64_max.
  omega.
  generalize (Zmod_small 4 uint64_max H6).
  intro.
  rewrite H8 in *.
  assert (0 <= (x0 + 1) < uint64_max).
  unfold uint64_max.
  omega.
  generalize (Zmod_small (x0 + 1) uint64_max H9).
  intro.
  rewrite H14 in *.
  inversion H1.
  apply Zlt_is_lt_bool in H16.
  constructor.
  omega.
  assumption.
  simpl in *.
  intros.
  destruct H.
  destruct H1.
  destruct H2.
  destruct H3.
  destruct H5.
  destruct H5.
  destruct H6.
  program_paths H0.
  assert (x0 = 4).
  unfold sprop_of_bexpr in H.
  generalize (bexpr_trichotomy (x < 4)%bexpr st2).
  intro.
  destruct H0.
  rewrite H0 in H.
  obvious_contr.
  destruct H0.
  Focus 2.
  simpl in *.
  rewrite H5 in H0.
  simpl in H0.
  discriminate.
  simpl in H0.
  rewrite H5 in H0.
  simpl in H0.
  assert (0 <= x0 < uint64_max).
  unfold uint64_max.
  omega.
  generalize (Zmod_small (x0) uint64_max H1).
  intro.
  rewrite H2 in H0.
  assert (0 <= 4 < uint64_max).
  unfold uint64_max.
  omega.
  generalize (Zmod_small (4) uint64_max H3).
  intro.
  rewrite H8 in H0.
  inversion H0.
  generalize (Zlt_cases x0 4).
  intro.
  rewrite H10 in H9.
  omega.
  rewrite H0 in *.
  simpl in *.
  constructor.
  assumption.
  assumption.
  apply False_ind.
  inversion_clear H0.
  destruct H.
  assert (forall n : nat,
            (forall (st1' st2' : state),
               steps (partial_while (x < 4) ((y ≔ y + 1);; (x ≔ x + 1);; skip) n)
                     (skip, st1')
                     (ret, st2') -> False)).
  intro.
  induction n.
  simpl.
  intros.
  inversion_clear H0. inversion_clear H1. inversion_clear H0.
  intros.
  simpl in H0.
  inversion H0. subst. clear H0.
  inversion_clear H9. inversion_clear H0. inversion_clear H1.
  subst. clear H0.
  inversion_clear H9.
  induction t2.
  apply steps_skip_atom_split in H0.
  destruct H0.
  destruct H0.
  apply IHn in H1.
  assumption.
  apply ret_follows_abort_false in H1.
  assumption.
  apply steps_ret_atom_split in H0.
  destruct H0.
  discriminate.
  destruct H0.
  destruct H0.
  apply steps_ret_atom_split in H2.
  destruct H2. discriminate.
  destruct H2.
  destruct H2.
  inversion_clear H5. inversion_clear H6. inversion_clear H5.
  apply (H0 x0) in H.
  assumption.
Qed.