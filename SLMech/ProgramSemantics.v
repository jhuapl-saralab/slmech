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


(** * Operational semantics *)
(** We use a transition semantics *)

Require Import ZArith.
Require Import List.
Require Export Equality.

Require Import ProgramData.
Require Import Assertions.
Require Import Coq.Logic.Classical_Prop.

Require Import Setoid.
Require Import Morphisms.
Require Import Basics. 

Open Scope type_scope.

Parameter aval : val -> addr.
Coercion aval : val >-> addr.
Parameter next : addr -> addr.
Parameter nval : val -> nat.
Coercion nval : val >->nat.

Fixpoint partial_while (b : bexpr)(c : stmt)(n : nat) : stmt :=
  match n with
      |O => abort
      |S(m) => ifelse b (c;;(partial_while b c m)) skip
  end.

(*Rules for stepping through a program*)
Inductive state_step : term -> (term * state) -> (term * state) -> Prop :=
  | state_step_skip :  (*Skip does not change the state*)
      forall (t : term) (s : state),
        state_step skip (t, s)(t, s)
  | state_step_abort : (*Abort only changes the state to aborted if it wasn't already in a return state*)
      forall (t : term) (s : state),
        t <> ret -> state_step abort (t, s)(abort, s)
  | state_step_ret : (*Return only changes the state to returned if it wasn't already in an aborted state*)
      forall (t : term)(s : state),
        t <> abort -> state_step ret (t, s)(ret, s)

with step : atom -> (term * state) -> (term * state) -> Prop :=
  | step_state_step : 
      forall (t t1 t2 : term)(s1 s2 : state),
        state_step t (t1, s1)(t2, s2) -> step (terminal t)(t1, s1)(t2, s2)

  | step_assign :
    forall (s s' : store_f) (l : locals) (h : heap_f) (d : domain)
           (x : var) (e : expr) (v : val),
      (s l) [[e]] = Some v ->
      (forall (x' : var), x <> x' -> (s l x') = (s' l x')) ->
      (s' l x = Some v) ->
      step (assign x e) (skip , (mkst s l h d)) (skip, (mkst s' l h d))

  | step_assign_fail :
    forall (s : store_f) (l : locals) (h : heap_f) (d : domain)
           (x : var) (e : expr) (v : val),
           ((s l) [[e]] = None \/
             ((s l) [[e]] = Some v /\ ~Vars.In x l)) ->
           step (assign x e) (skip, mkst s l h d) (abort, mkst s l h d)

  | step_heapload :
    forall (s s': store_f) (l : locals) (h : heap_f)
           (d : domain)(x : var) (e : expr) (v1 v2 : val),
      (s l) [[e]] = Some v1 ->
      (h d v1) = Some v2 ->
      (forall (x' : var), x <> x' -> (s l x') = (s' l x')) ->
      (s' l x = Some v2) ->
      step (heapload x e) (skip, mkst s l h d) (skip, (mkst s' l h d))

  | step_heapload_fail :
    forall  (s : store_f) (l : locals) (h : heap_f) (d : domain)
            (x : var) (e : expr) (v1 v2 : val),
      ( (s l) [[e]] = None \/
       ( (s l) [[e]] = Some v1 /\ (~In' (aval v1) d  \/
                                      ((h d v1) = Some v2 /\ ~Vars.In x l)))) ->
      step (heapload x e) (skip, (mkst s l h d)) (abort, (mkst s l h d))

  | step_heapwrite :
    forall (s : store_f) (l : locals) (h h': heap_f) (d : domain)
           (e1 e2 : expr) (v1 v2 : val),
      (s l) [[e1]] = Some v1 ->
      (s l) [[e2]] = Some v2 ->
      (forall v3, v3 <> v1 -> (h d v3) = (h' d v3)) ->
      (h' d v1) = Some v2 ->
      step (heapwrite e1 e2) (skip, (mkst s l h d)) (skip, (mkst s l h' d))

  | step_heapwrite_fail :
    forall (s : store_f) (l : locals) (h : heap_f) (d : domain)
           (e1 e2 : expr) (v1 v2 : val),
      ((s l) [[e1]] = None \/
       (s l) [[e2]] = None \/
       ((s l) [[e1]] = Some v1 /\ 
        (s l) [[e2]] = Some v2 /\
        ~(In' (aval v1) d))) ->
      step (heapwrite e1 e2)(skip, (mkst s l h d)) (abort, (mkst s l h d))

  | step_pcons :
    forall (h : heap_f) (d d': domain) (err memaddr : var) (l : locals)
           (e : expr) (v : val) (s s' : store_f) (a : addr) (c : chunk)(ld : list domain),
           (s l ) [[e]]  = Some v ->
           heap_bits ld d ->
           heap_bits ((Dom.singleton c)::ld) d' ->
           Keys.cardinal(c) = (nval v) ->
           base_pointer a c ->
           (forall (x' : var), memaddr <> x' -> err <> x' -> (s l x') = (s' l x')) ->
           (s' l memaddr = Some (vaddr a)) ->
           (s' l err = Some ProgramData.ERR_SUCCESS) ->
           step (pcons err memaddr e)(skip, (mkst s l h d)) (skip, (mkst s' l h d'))

  | step_pcons_oom :
    forall (h : heap_f) (d : domain) (l : locals) (err memaddr : var)
      (e : expr) (s s' : store_f),

           (* out of memory! *)
           (forall (x' : var), err <> x' -> (s l x') = (s' l x')) ->
           (s' l err = Some ProgramData.ERR_ERROR) ->
           step (pcons err memaddr e)(skip, (mkst s l h d))(skip, (mkst s' l h d))

  | step_pcons_fail :
    forall (h : heap_f) (err memaddr : var) (l : locals)(d : domain)
           (e : expr) (s : store_f) (a : addr),

           (s l) [[e]] = None \/
            ~Vars.In memaddr l \/
            ~Vars.In err l ->
           step (pcons err memaddr e)(skip, (mkst s l h d)) (abort, (mkst s l h d))

  | step_dispose :
    forall (s : store_f)(l : locals)(h h' : heap_f) (d d' : domain) 
           (e : expr) (v : val),
      (s l) [[e]] = Some v ->
      (*You should only be able to free a chunk if you free from the base pointer*)
      (exists (c : chunk), (base_pointer (aval v) c)
                           /\ Dom.In c d
                           /\ Dom.Equal d' (Dom.remove c d)) ->
      step (dispose e) (skip, (mkst s l h d)) (skip, (mkst s l h d'))

  | step_dispose_fail :
    forall (s : store_f) (l : locals) (h : heap_f) (d : domain) 
           (e : expr) (v : val),
      (s l) [[e]] = None \/
       (s l) [[e]] = Some v /\ ~In' (aval v) d ->
      step (dispose e)(skip, (mkst s l h d)) (abort, (mkst s l h d))
           
  | step_local : 
      forall (s : store_f)(l l' : locals)(h : heap_f)(d : domain)
             (v : var) (vl : list var)(t : term),
        store_bits vl l ->
        store_bits (v::vl) l'->
        s l' v = Some Vundef ->
        step (local v t)(skip, (mkst s l h d)) (skip, (mkst s l' h d))

  | step_local_fail :
      forall (v : var)(s : store_f)(l : locals)(h : heap_f)(d : domain)(t : term),
        Vars.In v l ->
        step (local v t)(skip, (mkst s l h d)) (abort, (mkst s l h d))

with

steps : stmt -> (term * state) -> (term * state) -> Prop :=

  | steps_aborted : (*An aborted state does not change for any given stmt*)
      forall (c : stmt)(s : state),
        steps c (abort, s)(abort, s)

  | steps_returned : (*When hitting a return stmt, you ignore any following statements*)
      forall (c : stmt)(s : state),
        steps c (ret, s)(ret, s)

  | step_steps : forall (a : atom)(st1 st2 : state)(t1 t2 : term),
                   step a (t1, st1)(t2, st2) ->
                   steps (atomistic a) (t1, st1)(t2, st2)

  (*If some chain of length n reaches a skip, then the loop halts*)
  | steps_while_halt : forall (b : bexpr)(c : stmt) (s1 s2 : state),
                         (exists (n : nat), steps(partial_while b c n)(skip, s1)(skip, s2)) ->
                         steps(while b c)(skip, s1)(skip, s2)

  (*Here we're equivocating between a "real" abort and an infinite loop*)
  | steps_while_abort : forall (b : bexpr)(c : stmt) (s1 s2 : state),
                          (forall (n : nat), steps (partial_while b c n)(skip, s1)(abort, s2)) ->
                          steps(while b c)(skip, s1)(abort, s2)

  (*If some chain of length n reaches a return statement, then the loop halts and goes into a return*)
  | steps_while_ret : forall (b : bexpr)(c : stmt) (s1 s2 : state),
                        (exists (n : nat), steps(partial_while b c n)(skip, s1)(ret, s2)) ->
                        steps(while b c)(skip, s1)(ret, s2)

  | steps_seq : forall (c1 c2 : stmt) (s1 s2 s3 : state) (t1 t2 t3 : term), 
                  steps c1 (t1, s1)(t2, s2) ->
                  steps c2 (t2, s2)(t3, s3) ->
                  steps (c1;;c2) (t1, s1)(t3, s3)

  | step_ifelse_false :
    forall (st1 st2 : state) (b : bexpr) (c1 c2 : stmt)(t : term),
      bbexpr st1 b = Some false ->
      steps (c2) (skip, st1)(t, st2) ->
      steps (ifelse b c1 c2)(skip, st1) (t, st2)

  | step_ifelse_true :
    forall (st1 st2 : state) (b : bexpr) (c1 c2 : stmt)(t : term),
      bbexpr st1 b = Some true ->
      steps (c1)(skip, st1)(t, st2) ->
      steps (ifelse b c1 c2)(skip, st1) (t, st2)

  | step_ifelse_fail :
    forall (st : state) (b : bexpr) (c1 c2 : stmt),
      bbexpr st b = None ->
      steps (ifelse b c1 c2) (skip, st) (abort, st).

Axiom steps_well_defined :
      forall (c : stmt)(s1 s2 s3 : state)(t1 t2 t3 : term),
        steps c (t1, s1)(t2, s2) -> steps c (t1, s1)(t3, s3) -> (t2, s2) = (t3, s3).

Lemma step_well_defined :
  forall (a : atom) (s1 s2 s3 : state)(t1 t2 t3 : term),
    step a (t1, s1)(t2, s2) -> step a (t1, s1)(t3, s3) -> (t2, s2) = (t3, s3).
  intros.
  apply step_steps in H.
  apply step_steps in H0.
  apply (steps_well_defined a s1 s2 s3 t1 t2 t3 H H0).
Qed.

Lemma state_step_well_defined :
  forall (t : term)(s1 s2 s3 : state)(t1 t2 t3 : term),
    state_step t (t1, s1)(t2,s2) -> state_step t (t1, s1)(t3, s3) -> (t2, s2) = (t3, s3).
  intros.
  apply step_state_step in H.
  apply step_state_step in H0.
  apply (step_well_defined t s1 s2 s3 t1 t2 t3 H H0).
Qed.

Lemma skip_follows_abort_false : forall (c : stmt)(s1 s2 : state),
                                   steps c (abort, s1)(skip, s2) -> False.
  intros.
  generalize (steps_well_defined c s1 s1 s2 abort abort skip (steps_aborted c s1) H).
  intro.
  discriminate.
Qed.

Lemma skip_follows_ret_false : forall (c : stmt)(s1 s2 : state),
                                   steps c (ret, s1)(skip, s2) -> False.
  intros.
  generalize (steps_well_defined c s1 s1 s2 ret ret skip (steps_returned c s1) H).
  intro.
  discriminate.
Qed.

Lemma ret_follows_abort_false : forall (c : stmt)(s1 s2 : state),
                                   steps c (abort, s1)(ret, s2) -> False.
  intros.
  generalize (steps_well_defined c s1 s1 s2 abort abort ret (steps_aborted c s1) H).
  intro.
  discriminate.
Qed.


Lemma abort_follows_ret_false : forall (c : stmt)(s1 s2 : state),
                                   steps c (ret, s1)(abort, s2) -> False.
  intros.
  generalize (steps_well_defined c s1 s1 s2 ret ret abort (steps_returned c s1) H).
  intro.
  discriminate.
Qed.

Lemma seq_composition : forall a b st1 st2, steps (a;;b)(skip, st1)(skip, st2) -> (exists st', steps (a)(skip, st1)(skip, st') /\ steps(b)(skip, st')(skip, st2)).
  intros.
  inversion H. subst.
  induction t2.
  exists s2.
  constructor; assumption.
  apply (skip_follows_abort_false b s2 st2) in H7.
  contradiction.
  apply (skip_follows_ret_false b s2 st2) in H7.
  contradiction.
Qed.

Lemma partial_while_rule_skip : forall (b : bexpr)(c : stmt)(LI : sprop),
                             (forall (s s' : state), steps (c)(skip, s)(skip, s') ->
                                                     (sprop_of_bexpr b) s /\ LI s ->
                                                     LI s') ->
                             forall (n : nat), (forall (s1 s2 : state), LI s1 ->
                                                                        steps(partial_while b c n)(skip, s1)(skip, s2)->
                                                                        not ((sprop_of_bexpr b) s2) /\ LI s2).
  intros b c LI.
  intro.
  intro.
  induction n.
  simpl. intros. inversion H1. subst. inversion H4. subst. inversion H5.
  simpl. intros.
  inversion_clear H1. inversion H3. subst. inversion H5. subst. inversion H6. subst. constructor. unfold sprop_of_bexpr.
  rewrite H2.
  discriminate.
  assumption.
  apply seq_composition in H3. destruct H3. destruct H1.
  assert ((sprop_of_bexpr b s1) /\ LI s1). constructor. unfold sprop_of_bexpr. assumption. assumption.
  apply (IHn x s2 (H s1 x H1 H4) H3).
Qed.

Corollary while_rule_skip : forall (b : bexpr)(c : stmt)(LI : sprop),
                         (forall (s s' : state), steps(c)(skip, s)(skip, s') ->
                                                 (sprop_of_bexpr b) s /\ LI s ->
                                                 LI s') ->
                         (forall (s1 s2 : state), LI s1 ->
                                                  steps(while b c)(skip, s1)(skip, s2)->
                                                  not ((sprop_of_bexpr b) s2) /\ LI s2).
intros.
inversion H1.
subst.
inversion H3.
apply (partial_while_rule_skip b c LI H x s1 s2 H0 H2).
Qed.

Lemma partial_while_rule_ret : forall (b : bexpr)(c : stmt)(LI : sprop),
                         (forall (s s' : state), steps(c)(skip, s)(skip, s') ->
                                                 (sprop_of_bexpr b) s /\ LI s ->
                                                 LI s') ->
                         (forall (n : nat)(s1 s2 : state), LI s1 ->
                                                  steps(partial_while b c n)(skip, s1)(ret, s2) ->
                                                  (exists (s3 : state),
                                                     (sprop_of_bexpr b) s3
                                                     /\ LI s3
                                                     /\ steps (c)(skip, s3)(ret, s2))).
  intros b c LI.
  intro.
  intro.
  induction n.
  simpl. intros. inversion_clear H1. inversion_clear H2. inversion H1.
  simpl. intros.
  inversion_clear H1. inversion_clear H3. inversion_clear H1. inversion_clear H3.
  inversion_clear H3.
  induction t2.
  apply H in H1.
  apply (IHn s3 s2 H1 H4).
  constructor; assumption.
  apply ret_follows_abort_false in H4.
  contradiction.
  exists s1.
  generalize (steps_well_defined (partial_while b c n) s3 s2 s3 ret ret ret H4 (steps_returned (partial_while b c n) s3)).
  intro.
  inversion H3. subst.
  constructor. assumption. constructor. assumption. assumption.
Qed.

Corollary while_rule_ret : forall (b : bexpr)(c : stmt)(LI : sprop),
                             (forall (s s' : state), steps c (skip, s)(skip, s') ->
                                                     (sprop_of_bexpr b) s /\ LI s ->
                                                     LI s') ->
                             (forall (s1 s2 : state), LI s1 ->
                                                      steps (while b c)(skip, s1)(ret, s2) ->
                                                      (exists (s3 : state),
                                                         (sprop_of_bexpr b) s3
                                                         /\ LI s3
                                                         /\ steps c (skip, s3)(ret, s2))).
intros.
inversion_clear H1.
destruct H2.
apply (partial_while_rule_ret b c LI H x s1 s2 H0 H1).
Qed.
  

(* simple lemmas about zero-arity statements *)

Lemma skip_steps_ret_false :
  forall st st', steps (skip)(skip, st) (ret, st') -> False.
intros. inversion H. subst.
inversion H2. subst. inversion H3.
Qed.


Lemma skip_steps_abort_false :
  forall st st', steps (skip)(skip, st) (abort, st') -> False.
intros. inversion H; subst; clear H.
inversion H2. subst. inversion H1.
Qed.


Lemma abort_steps_skip_false :
  forall st st', steps (abort)(skip, st) (skip, st') -> False.
intros. inversion H; subst; clear H.
inversion H2. subst. inversion H1.
Qed.

Lemma abort_steps_ret_false :
  forall st st', steps (abort)(skip, st) (ret, st') -> False.
intros. inversion H; subst; clear H.
inversion H2. subst. inversion H1.
Qed.

Lemma ret_steps_skip_false :
  forall st st', steps (ret)(skip, st) (skip, st') -> False.
intros. inversion H; subst; clear H.
inversion H2. subst. inversion H1.
Qed.

Lemma ret_steps_abort_false :
  forall st st', steps (ret)(skip, st) (abort, st') -> False.
intros. inversion H; subst; clear H.
inversion H2. subst. inversion H1.
Qed.

Lemma ret_seq_steps_skip_false : forall c st1 st2,
       steps (ret;; c)(skip, st1) (skip, st2) -> False.
intros. inversion H; subst; clear H.
inversion H3; subst; clear H3. 
induction t2. inversion H1. subst. inversion H2.
inversion H1. subst. inversion H2.
apply (skip_follows_ret_false c s2 st2). assumption.
Qed.


Lemma abort_seq_step_skip_false :
  forall st st' c, steps (abort;; c)(skip, st) (skip, st') -> False.
intros.
intros. inversion H; subst; clear H.
induction t2. inversion H3. subst. inversion H1. subst. inversion H2.
apply (skip_follows_abort_false c s2 st'). assumption.
inversion H3. subst. inversion H1. subst. inversion H2.
Qed.

Lemma abort_seq_step_ret_false :
  forall st st' c, steps (abort;; c)(skip, st) (ret, st') -> False.
intros.
intros. inversion H; subst; clear H.
inversion H3; subst; clear H3. 
induction t2. inversion H1. subst. inversion H2.
apply (ret_follows_abort_false c s2 st'). assumption.
inversion H1. subst. inversion H2.
Qed.

Definition completes st1 st2 P := exists c, (c=skip\/c=ret)/\steps (P)(skip, st1) (c, st2).
Definition skips st1 st2 P := steps (P)(skip, st1) (skip, st2).
Definition returns st1 st2 P := steps (P)(skip, st1) (ret, st2).
Definition aborts st1 st2 P := steps (P)(skip, st1) (abort, st2).

Lemma skip_ret_false : forall st1 st2 P, 
              skips st1 st2 P -> ~ returns st1 st2 P.
intros.
unfold skips in H.
intro.
unfold returns in H0.
generalize (steps_well_defined P st1 st2 st2 skip skip ret H H0).
intro.
discriminate.
Qed.

Lemma skip_abort_false : forall st1 st2 P, 
              skips st1 st2 P -> ~ aborts st1 st2 P.
intros.
intro.
unfold skips in H.
unfold aborts in H0.
generalize (steps_well_defined P st1 st2 st2 skip skip abort H H0).
intro.
discriminate.
Qed.

Lemma ret_skip_false : forall st1 st2 P, 
              returns st1 st2 P -> ~ skips st1 st2 P.
intros.
intro.
unfold returns in H.
unfold skips in H0.
generalize (steps_well_defined P st1 st2 st2 skip ret skip H H0).
intros.
discriminate.
Qed.

Lemma ret_abort_false : forall st1 st2 P, 
              returns st1 st2 P -> ~ aborts st1 st2 P.
intros.
intro.
unfold returns in H.
unfold aborts in H0.
generalize (steps_well_defined P st1 st2 st2 skip ret abort H H0).
intro.
discriminate.
Qed.

Lemma abort_skip_false : forall st1 st2 P, 
              aborts st1 st2 P -> ~ skips st1 st2 P.
intros.
intro.
unfold aborts in H.
unfold skips in H0.
generalize (steps_well_defined P st1 st2 st2 skip abort skip H H0).
intro.
discriminate.
Qed.

Lemma abort_ret_false : forall st1 st2 P, 
              aborts st1 st2 P -> ~ returns st1 st2 P.
intros.
intro.
unfold aborts in H.
unfold returns in H0.
generalize (steps_well_defined P st1 st2 st2 skip abort ret H H0).
intro.
discriminate.
Qed.


Lemma abort_complete_false :
  forall st st', completes st st' abort -> False.
  intros. unfold completes in H.
  inversion H; subst; clear H.
  inversion_clear H0.
  inversion_clear H; subst.
  eapply abort_steps_skip_false; apply H1.
  eapply abort_steps_ret_false; apply H1.
Qed.

Lemma abort_seq_complete_false :
  forall st st' c, completes st st' (abort;;c) -> False.
  intros. unfold completes in H.
  inversion H; subst; clear H.
  inversion_clear H0.
  inversion_clear H; subst.
  eapply abort_seq_step_skip_false; apply H1.
  eapply abort_seq_step_ret_false; apply H1.
Qed.

Ltac abort_doesnt_lead_to_skip :=
 match goal with
     | H : steps ?tid (abort;; ?c, ?t1) (skip, ?t2) |- _ =>
       apply False_ind; 
       apply (abort_seq_step_skip_false tid t1 t2 c);
       assumption
     | H : steps ?tid (abort, ?t1) (skip, ?t2) |- _ => 
       apply False_ind;
       apply (abort_steps_skip_false tid t1 t2);
       assumption
 end.



Ltac abort_doesnt_complete :=
 match goal with
     | H : completes ?st1 ?st2 (abort;; ?c) |- _ =>
       apply False_ind; 
       apply (abort_seq_complete_false st1 st2 c);
       assumption
     | H : completes ?st1 ?st2 abort |- _ =>
       apply False_ind; 
       apply (abort_complete_false st1 st2);
       assumption
 end.

Lemma run_result : forall st1 c,
     (exists st2, skips st1 st2 c) \/
     (exists st2, returns st1 st2 c) \/
     (exists st2, aborts st1 st2 c) \/
     (forall st2, ~ (skips st1 st2 c) /\
                  ~ (returns st1 st2 c) /\
                  ~ (aborts st1 st2 c)).
intros. unfold skips, returns, aborts.
generalize (classic (exists st2, steps (c)(skip, st1) (skip, st2))).
intro. inversion H; clear H. left; assumption.
generalize (classic (exists st2, steps (c)(skip, st1) (ret, st2))).
intro. inversion H; clear H. right; left; assumption.
generalize (classic (exists st2, steps (c)(skip, st1) (abort, st2))).
intro. inversion H; clear H. right; right; left; assumption.
right; right; right.
intros.

split.
intro; apply H0; exists st2; assumption.
split.
intro; apply H1; exists st2; assumption.
intro; apply H2; exists st2; assumption.

Qed.


(********)

(* 
 * Two programs p1 and p2 have "equivalent effects" if for every
 * possible input state, they eventually do the same thing. When one
 * aborts, the other aborts. When one completes, the other completes with
 * the same output. And when one doesn't terminate, the other also
 * doesn't terminate.
 *)
Definition equiv_effect p1 p2 := forall st st',
      ((steps (p1)(skip, st) (skip, st') <-> steps (p2)(skip, st) (skip, st')) /\
      (steps (p1)(skip, st) (ret, st') <-> steps (p2)(skip, st) (ret, st')) /\
      (steps (p1)(skip, st) (abort, st') <-> steps (p2)(skip, st) (abort, st'))).

Lemma equiv_effect_trans : Transitive equiv_effect.
unfold Transitive, equiv_effect, iff. 
intros. 

specialize (H st st'); inversion_clear H; inversion_clear H2;
specialize (H0 st st'); inversion_clear H0; inversion_clear H4;
inversion_clear H ; inversion_clear H0;
inversion_clear H1; inversion_clear H2;
inversion_clear H3; inversion_clear H5.


split; split; try split; intros; [

apply H1; apply H0; assumption |
apply H8; apply H9; assumption |

apply H ; apply H4; assumption |
apply H6; apply H7; assumption |

apply H3; apply H2; assumption |
apply H10; apply H11; assumption ].
Qed.


Lemma equiv_effect_sym : Symmetric equiv_effect.
unfold Symmetric, equiv_effect, iff. 
intros. specialize (H st st'). inversion_clear H. inversion_clear H0. inversion_clear H1.
inversion_clear H0. inversion_clear H3.
split; split; try split; assumption.
Qed.

Lemma equiv_effect_refl : Reflexive equiv_effect.
unfold Reflexive, equiv_effect, iff. 
intros. tauto.
Qed.



Add Parametric Relation : stmt
    equiv_effect
    reflexivity proved by equiv_effect_refl
    symmetry proved by equiv_effect_sym
    transitivity proved by equiv_effect_trans
as equiv_effect_rel. 


Lemma assoc_prog_equiv : forall p1 p2 p3, equiv_effect (seq (seq p1 p2) p3) (seq p1 (seq p2 p3)).
intros. unfold equiv_effect. intros.
unfold iff. split; intros; split; intros.
inversion H.
subst.
inversion H3. subst.
generalize (steps_seq p2 p3 s0 s2 st' t0 t2 skip H9 H7).
intro.
apply (steps_seq p1 (p2;;p3) st s0 st' skip t0 skip H4 H0).
inversion H.
subst. inversion H7. subst.
generalize (steps_seq p1 p2 st s2 s0 skip t2 t0 H3 H4).
intro.
apply (steps_seq (p1;;p2) p3 st s0 st' skip t0 skip H0 H9).
split.
intro.
inversion H.
subst.
inversion H3. subst.
generalize (steps_seq p2 p3 s0 s2 st' t0 t2 ret H9 H7).
intro.
apply (steps_seq p1 (p2;;p3) st s0 st' skip t0 ret H4 H0).
intros.
inversion H. subst.
inversion H7. subst.
generalize (steps_seq p1 p2 st st' st' skip ret ret H3 (steps_returned p2 st')).
intro.
apply (steps_seq (p1;;p2) p3 st st' st' skip ret ret H0 (steps_returned p3 st')).
subst.
generalize (steps_seq p1 p2 st s2 s0 skip t2 t0 H3 H4).
intro.
apply (steps_seq (p1;;p2) p3 st s0 st' skip t0 ret H0 H9).
split.
intros.
inversion H.
subst. inversion H3. subst.
generalize (steps_seq p2 p3 s0 s2 st' t0 t2 abort H9 H7).
intro.
apply (steps_seq p1 (p2;;p3) st s0 st' skip t0 abort H4 H0).
intros.
inversion H.
subst. 
inversion H7. subst.
generalize (steps_aborted p2 st').
intro.
generalize (steps_seq p1 p2 st st' st' skip abort abort H3 H0).
intro.
generalize (steps_aborted p3 st').
intro.
apply (steps_seq (p1;;p2) p3 st st' st' skip abort abort H1 H2).
subst.
generalize (steps_seq p1 p2 st s2 s0 skip t2 t0 H3 H4).
intro.
apply (steps_seq (p1;;p2) p3 st s0 st' skip t0 abort H0 H9).
Qed.


Definition equiv_machine_state (par1 par2: prod stmt state) := 
  match (par1, par2) with
    | ((p1,st1), (p2,st2)) => equiv_effect p1 p2 /\ st1 = st2
  end.


Lemma equiv_machine_state_trans : Transitive equiv_machine_state.
unfold Transitive, equiv_machine_state.
intros. destruct x, y, z.
inversion_clear H. inversion_clear H0.
split.
apply (equiv_effect_trans s s1); assumption.
rewrite H2. assumption.
Qed.

Lemma equiv_machine_state_sym : Symmetric equiv_machine_state.
unfold Symmetric, equiv_machine_state.
intros. destruct x, y.
inversion_clear H.
split; symmetry; assumption.
Qed.

Lemma equiv_machine_state_refl : Reflexive equiv_machine_state.
unfold Reflexive, equiv_machine_state.
intros; destruct x; split; reflexivity.
Qed.

Add Parametric Relation : (@prod stmt state)
    equiv_machine_state
    reflexivity proved by equiv_machine_state_refl
    symmetry proved by equiv_machine_state_sym
    transitivity proved by equiv_machine_state_trans
as equiv_machine_state_rel.


Definition steps' st1 st2 p1 p2 := steps p1 (skip, st1) (skip, st2) -> steps p2 (skip, st1) (skip, st2).

Add Parametric Morphism (st1 st2 : state) :
  (steps' st1 st2)
   with signature (equiv_effect ==> equiv_effect ==> impl)
     as steps_mor.
unfold impl.
intros.
unfold equiv_effect, iff, steps' in *.

specialize (H st1 st2).
specialize (H0 st1 st2).
inversion_clear H.
inversion_clear H0.
inversion_clear H2.
inversion_clear H3.
inversion_clear H4.
inversion_clear H.
intro.
apply H4.
apply H1.
apply H5.
apply H.
Qed.

Add Parametric Morphism  (st1 st2 : state) :
  (completes st1 st2)
   with signature (equiv_effect ==> impl)
     as completes_mor.
  unfold impl.
intros.
unfold equiv_effect, iff, completes in *.
specialize (H st1 st2).
inversion_clear H0.
exists x0.
inversion_clear H.
inversion_clear H0.
inversion_clear H2.
inversion_clear H0.
inversion_clear H4.
inversion_clear H1.
split.
assumption.
elim H4 ; intros ; subst x0.
apply (H H7).
apply (H2 H7).
Qed.

Lemma complete_seq_a : forall c1 c2 st1 st2,
      steps (seq c1 c2)(skip, st1) (abort, st2) -> steps (c1)(skip, st1) (abort, st2) \/
                                                 (exists st', steps (c1)(skip, st1) (skip, st') /\
                                                             steps (c2)(skip, st') (abort, st2)).
intros.
inversion H. subst.
induction t2. 
right. exists s2. constructor; assumption.
generalize (steps_well_defined c2 s2 s2 st2 abort abort abort (steps_aborted c2 s2) H7).
intro.
inversion H0.
subst.
left. assumption.
generalize (steps_well_defined c2 s2 s2 st2 ret ret abort (steps_returned c2 s2) H7).
intro.
discriminate.
Qed.

Lemma one_skip_result : forall st st'  c,
         steps (c)(skip, st) (skip, st') ->
         ~(exists st'', steps (c)(skip, st) (ret, st'')).
intros st st' c H0.
intro.
inversion_clear H.
generalize (steps_well_defined c st st' x skip skip ret H0 H1).
intro.
discriminate.
Qed.
