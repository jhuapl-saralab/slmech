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

Require Import Equalities.
Require Import SetoidClass.
Require Import Orders.
Require Import FSets.
Require Import Peano_dec.
Require Export BoolEq.
Require Import ZArith.
Require Import ProofIrrelevance.

Require Export Memory.

Require Import Lists.List.

(*Returns the integer value inside of the val type if it exists*)
Definition get_Z (v : val): option Z :=
  match v with
    | Vsint64 z P => Some z
    | Vuint64 z P => Some z
    | Vsint32 z P => Some z
    | Vuint32 z P => Some z
    | Vundef => None
  end.

Definition get_Z_ov (ov : option val): option Z :=
  match ov with
    | None => None
    | Some v => get_Z v
  end.

(*Decidible equality for vals, requires proof_irrelevance for the range
  proofs*)
Definition valeq (x y: val): {x=y} + {x<>y}.
Proof.
  induction x, y; try (right; discriminate); try (left; reflexivity);
  [unfold sint32_bound in *| unfold uint32_bound in * | unfold sint64_bound in * | unfold uint64_bound in *];
  assert ({z0 = z} + {z0 <> z}); try apply Z.eq_dec; 
                                  destruct H; try (
                                    subst;
                                    try generalize (proof_irrelevance _ s s0);
                                    try generalize (proof_irrelevance _ u u0);
                                    intro;
                                    subst;
                                    left; reflexivity);
                                  try (
                                    right;intro;
                                    apply n;
                                    injection H;
                                    auto).
Defined.

(*Casts a given input val to a val of type sint64 whenever possible.
  Returns None in the case of overflow or when trying to cast from
  vundef.*)
Definition val_to_sint64 : val -> option val.
  intro.
  elim H.
  apply None.
  intros.
  assert (sint64_min <= z <= sint64_max).
  unfold sint32_bound in s.
  unfold sint64_min, sint64_max, sint32_min, sint32_max in *.
  omega.
  apply (Some (Vsint64 z H0)).
  intros.
  unfold uint32_bound in u.
  assert (sint64_min <= z <= sint64_max).
  unfold sint64_min, sint64_max, uint32_max in *.
  omega.
  apply (Some (Vsint64 z H0)).
  intros.
  apply (Some (Vsint64 z s)).
  intros.
  case_eq ((sint64_min <=? z) && (z <=? sint64_max)).
  intro.
  apply andb_true_iff in H0.
  destruct H0.
  assert (sint64_min <= z <= sint64_max).
  apply Zle_is_le_bool in H0.
  apply Zle_is_le_bool in H1.
  unfold uint64_bound in u.
  omega.
  apply (Some (Vsint64 z H2)).
  intro.
  apply None.
Defined.

(*Casts an input val to a uint64 whenever possible.  Returns
  None only when trying to cast from vundef.*)
Definition val_to_uint64 : val -> option val.
  intro.
  assert (0 < uint64_max).
  unfold uint64_max.
  omega.
  elim H;
    intros;
    [apply None| idtac | idtac | idtac | idtac];
    apply (Z.mod_pos_bound z uint64_max) in H0;
    apply (Some (Vuint64 (z mod uint64_max) H0)).
Defined.

(*Casts an input val to a sint32 whenever possible.  Returns
  None in the cases of overflow, underflow or trying to cast
  from vundef.*)
Definition val_to_sint32 : val -> option val.
  intros.
  elim H.
  apply None.
  intros.
  apply (Some (Vsint32 z s)).
  intros.
  case_eq ((sint32_min <=? z) && (z <=? sint32_max)).
  intros.
  apply andb_true_iff in H0.
  destruct H0.
  apply Zle_is_le_bool in H0.
  apply Zle_is_le_bool in H1.
  assert (sint32_min <= z <= sint32_max).
  omega.
  apply (Some (Vsint32 z H2)).
  intros.
  apply None.
  intros.
  case_eq ((sint32_min <=? z) && (z <=? sint32_max)).
  intros.
  apply andb_true_iff in H0.
  destruct H0.
  apply Zle_is_le_bool in H0.
  apply Zle_is_le_bool in H1.
  assert (sint32_min <= z <= sint32_max).
  omega.
  apply (Some (Vsint32 z H2)).
  intro.
  apply None.
  intros.
  case_eq ((sint32_min <=? z) && (z <=? sint32_max)).
  intros.
  apply andb_true_iff in H0.
  destruct H0.
  apply Zle_is_le_bool in H0.
  apply Zle_is_le_bool in H1.
  assert (sint32_min <= z <= sint32_max).
  omega.
  apply (Some (Vsint32 z H2)).
  intro.
  apply None.
Defined.

(*Casts a given val to vuint32 whenver possible.  Returns
  None whenever the input value is vundef.*)
Definition val_to_uint32 : val -> option val.
  intro.
  assert (0 < uint32_max).
  unfold uint32_max.
  omega.
  elim H;
    intros;
    [apply None| idtac | idtac | idtac | idtac];
    apply (Z.mod_pos_bound z uint32_max) in H0;
    apply (Some (Vuint32 (z mod uint32_max) H0)).
Defined.

(*Takes in an integer and either constructs a sint64
  val from that integer or returns None in the case of 
  overflow or underflow.*)
Definition Z_to_sint64 : Z -> option val.
  intro z.
  case_eq (sint64_min <=? z).
  case_eq (z <=? sint64_max).
  intros.
  apply Zle_is_le_bool in H.
  apply Zle_is_le_bool in H0.
  assert (sint64_min <= z <= sint64_max).
  constructor; assumption.
  apply (Some (Vsint64 z H1)).
  intros.
  apply None.
  intro.
  apply None.
Defined.

(*Takes in an integer and returns an uint64 from that integer.*)
Definition Z_to_uint64 : Z -> option val.
  intro z.
  assert (0 < uint64_max).
  unfold Z.lt.
  simpl.
  reflexivity.
  apply (Z.mod_pos_bound z uint64_max) in H.
  apply (Some (Vuint64 (z mod uint64_max) H)).
Defined.

Definition Z_to_Vuint64 : Z -> val.
  intro z.
  assert (0 < uint64_max).
  unfold Z.lt.
  simpl.
  reflexivity.
  apply (Z.mod_pos_bound z uint64_max) in H.
  apply (Vuint64 (z mod uint64_max) H).
Defined.

(*Takes in an integer and either constructs a sint32
  val from that integer or returns None in the case of 
  overflow or underflow.*)
Definition Z_to_sint32: Z -> option val.
  intro z.
  case_eq (sint32_min <=? z).
  case_eq (z <=? sint32_max).
  intros.
  apply Zle_is_le_bool in H.
  apply Zle_is_le_bool in H0.
  assert (sint32_min <= z <= sint32_max).
  constructor; assumption.
  apply (Some (Vsint32 z H1)).
  intros.
  apply None.
  intro.
  apply None.
Defined.

(*Takes in an integer and returns an uint32 from that integer.*)
Definition Z_to_uint32 : Z -> option val.
  intro z.
  assert (0 < uint32_max).
  unfold Z.lt.
  simpl.
  reflexivity.
  apply (Z.mod_pos_bound z uint32_max) in H.
  apply (Some (Vuint32 (z mod uint32_max) H)).
Defined.

(*This lifts a binary operation in Z to a binary operation in option val with the 
  correct casting*) 
(*TODO: This can definitely be improved with a total order on the types.*)
Definition promote_arith (b : Z -> Z -> Z) (ov1 ov2 : option val) : option val :=
  match ov1 with
      | None => None
      | Some v1 =>
        match ov2 with
            | None => None
            | Some v2 =>
              match v1, v2 with
                  | Vundef, _ => None
                  | _, Vundef => None
                  | Vuint64 n1 P1, Vuint64 n2 P2 => (Z_to_uint64 (b n1 n2))
                  | Vuint64 n1 P1, Vsint64 n2 P2 => (Z_to_uint64 (b n1 n2))
                  | Vuint64 n1 P1, Vuint32 n2 P2 => (Z_to_uint64 (b n1 n2))
                  | Vuint64 n1 P1, Vsint32 n2 P2 => (Z_to_uint64 (b n1 n2))
                  | Vsint64 n1 P1, Vuint64 n2 P2 => (Z_to_uint64 (b n1 n2))
                  | Vsint64 n1 P1, Vsint64 n2 P2 => (Z_to_sint64 (b n1 n2))
                  | Vsint64 n1 P1, Vuint32 n2 P2 => (Z_to_sint64 (b n1 n2))
                  | Vsint64 n1 P1, Vsint32 n2 P2 => (Z_to_sint64 (b n1 n2))
                  | Vuint32 n1 P1, Vuint64 n2 P2 => (Z_to_uint64 (b n1 n2))
                  | Vuint32 n1 P1, Vsint64 n2 P2 => (Z_to_sint64 (b n1 n2))
                  | Vuint32 n1 P1, Vuint32 n2 P2 => (Z_to_uint32 (b n1 n2))
                  | Vuint32 n1 P1, Vsint32 n2 P2 => (Z_to_uint32 (b n1 n2))
                  | Vsint32 n1 P1, Vuint64 n2 P2 => (Z_to_uint64 (b n1 n2))
                  | Vsint32 n1 P1, Vsint64 n2 P2 => (Z_to_sint64 (b n1 n2))
                  | Vsint32 n1 P1, Vuint32 n2 P2 => (Z_to_uint32 (b n1 n2))
                  | Vsint32 n1 P1, Vsint32 n2 P2 => (Z_to_sint32 (b n1 n2))
              end
        end
  end.


Definition vadd (ov1 ov2: option val): option val := promote_arith Z.add ov1 ov2.
Definition vsub (ov1 ov2: option val): option val := promote_arith Z.sub ov1 ov2.
Definition vmul (ov1 ov2: option val): option val := promote_arith Z.mul ov1 ov2.

(*Have to deal with division and modulo by 0 separately as the original Z.div and 
 Z.modulo allow this.*)
Definition vdiv (ov1 ov2: option val): option val := 
  match ov2 with
    | None => None
    | Some v2 =>
      match get_Z v2 with
        | None => None
        | Some 0 => None
        |_ => promote_arith Z.div ov1 ov2
      end
  end.

Definition vmod (ov1 ov2: option val): option val :=
  match ov2 with
    | None => None
    | Some v2 =>
      match get_Z v2 with
        | None => None
        | Some 0 => None
        | _ => promote_arith Z.modulo ov1 ov2
      end
  end.

Parameter vaddr : addr -> val.
Coercion vaddr : addr >-> val.

Section Expression.
  Parameter vnat : nat -> val.
  Coercion vnat : nat >-> val.

(*The usual inductive definition of expressions*)
  Inductive expr : Type :=
  | evar : var -> expr
  | eimm : option val -> expr
  | eplus : expr -> expr -> expr
  | eminus : expr -> expr -> expr
  | emul : expr -> expr -> expr
  | emod : expr -> expr -> expr.

  Coercion evar : var >-> expr.
(*  Coercion eimm : (option val) >-> expr.*)

(*This is another area where typing is important, mixing types in
  vplus, vminus, etc. is going to cause complications.  -TJ*)
  Fixpoint vexpr (s : store)(e : expr) {struct e} : option val :=
    match e with
      | eimm vl => vl
      | evar vr => s vr
      | eplus e1 e2 => vadd (vexpr s e1) (vexpr s e2)
      | eminus e1 e2 => vsub (vexpr s e1) (vexpr s e2)
      | emul e1 e2 => vmul (vexpr s e1)( vexpr s e2)
      | emod e1 e2 => vmod (vexpr s e1)( vexpr s e2)
    end.

  Section Eq_expr.

    Variable s : store.
    
    Inductive eq_expr (e e' : expr) : Prop :=
      | eq_expr_none : (* We either want this or we don't. 7/30/2014 *)
                       (* This might have helped back when we were splitting stores. Maybe? *)
          e = e' ->
          vexpr s e = None ->
          eq_expr e e'
      | eq_expr_some :
          (exists (v : val),
             vexpr s e = Some v /\ vexpr s e' = Some v) ->
          eq_expr e e'.

    Lemma eq_expr_refl :
      forall (e : expr),
        eq_expr e e.
    Proof.
      intros e.
      case_eq (vexpr s e).
      intros v VE.
      apply eq_expr_some.
      exists v.
      auto.

      intros VE.
      apply eq_expr_none; auto.
    Qed.

    Lemma eq_expr_sym :
      forall (e e' : expr),
        eq_expr e e' ->
        eq_expr e' e.
    Proof.
      intros e e' EE.
      induction EE.
      apply eq_expr_none ; subst e ; auto.
      apply eq_expr_some.
      elim H; intros v H'; elim H'; clear H H'; intros v' H.
      exists v.
      split ; assumption.
    Qed.

    Lemma eq_expr_trans :
      forall (e e' e'' : expr),
        eq_expr e e' ->
        eq_expr e' e'' ->
        eq_expr e e''.
    Proof.
      intros e e' e'' EE' E'E''.
      destruct EE'; destruct E'E''.
      apply eq_expr_none.
      transitivity e'.
      assumption.
      assumption.
      assumption.

      elim H1; clear H1; intros v [VE' VE''].
      rewrite H in H0.
      rewrite H0 in VE'.
      discriminate.

      
      elim H; clear H; intros v [VE VE'].
      rewrite VE' in H1; discriminate.

      elim H; clear H; intros v [VE VE'].
      elim H0; clear H0; intros v' [VE'2 VE''].
      rewrite VE' in VE'2; inversion VE'2; subst.
      apply eq_expr_some; exists v'.
      split ; assumption.
    Qed.

    Definition eq_expr_equiv : Equivalence eq_expr :=
      Build_Equivalence expr eq_expr eq_expr_refl eq_expr_sym eq_expr_trans.
(*    Instance expr_setoid : Setoid expr :=
      { equiv := eq_expr; setoid_equiv := eq_expr_equiv }.*)

  End Eq_expr.
  Hint Resolve eq_expr_refl eq_expr_sym eq_expr_trans.
(*Similar inductive definition of boolean expressions*)
(*The new types are going to necessarily change the way these comparisons 
  work. Particularly, the comparisons between different types.  Though
  in the case of just the unsigned integers this is not as problematic 
  as this should just mean casting to the larger size.  -TJ*)
  Inductive bexpr : Type :=
  | bbool : bool -> bexpr
  | beq : expr -> expr -> bexpr
  | band : bexpr -> bexpr -> bexpr
  | bor : bexpr -> bexpr -> bexpr
  | bnot : bexpr -> bexpr
  | blt : expr -> expr -> bexpr
  | bgt : expr -> expr -> bexpr.

Definition ble a b := bor (blt a b) (beq a b).
Definition bge a b := bor (bgt a b) (beq a b).

(*This takes an expression from Z*Z to bool and lifts it to an expression from option val*option val to bool.
  At some point we will likely need to modify or remove this as it is not congruent with how C works.*)
Definition promote_bool (b : Z -> Z -> bool) (ov1 ov2 : option val) : option bool :=
  match ov1 with
      | None => None
      | Some v1 =>
        match ov2 with
            | None => None
            | Some v2 =>
              match v1, v2 with
                  | Vundef, _ => None
                  | _, Vundef => None
                  | Vuint64 n1 P1, Vuint64 n2 P2 => Some (b n1 n2)
                  | Vuint64 n1 P1, Vsint64 n2 P2 => Some (b n1 (Z.modulo n2 uint64_max))
                  | Vuint64 n1 P1, Vuint32 n2 P2 => Some (b n1 n2)
                  | Vuint64 n1 P1, Vsint32 n2 P2 => Some (b n1 (Z.modulo n2 uint64_max))
                  | Vsint64 n1 P1, Vuint64 n2 P2 => Some (b (Z.modulo n1 uint64_max) n2)
                  | Vsint64 n1 P1, Vsint64 n2 P2 => Some (b n1 n2)
                  | Vsint64 n1 P1, Vuint32 n2 P2 => Some (b n1 n2)
                  | Vsint64 n1 P1, Vsint32 n2 P2 => Some (b n1 n2)
                  | Vuint32 n1 P1, Vuint64 n2 P2 => Some (b n1 n2)
                  | Vuint32 n1 P1, Vsint64 n2 P2 => Some (b n1 n2)
                  | Vuint32 n1 P1, Vuint32 n2 P2 => Some (b n1 n2)
                  | Vuint32 n1 P1, Vsint32 n2 P2 => Some (b n1 (Z.modulo n2 uint32_max))
                  | Vsint32 n1 P1, Vuint64 n2 P2 => Some (b n1 n2)
                  | Vsint32 n1 P1, Vsint64 n2 P2 => Some (b n1 n2)
                  | Vsint32 n1 P1, Vuint32 n2 P2 => Some (b (Z.modulo n1 uint32_max) n2)
                  | Vsint32 n1 P1, Vsint32 n2 P2 => Some (b n1 n2)
              end
        end
  end.

Definition veqb (ov1 ov2 : option val) : option bool := promote_bool Z.eqb ov1 ov2.
Definition vltb (ov1 ov2 : option val) : option bool := promote_bool Z.ltb ov1 ov2.
Definition vgtb (ov1 ov2 : option val) : option bool := promote_bool Z.gtb ov1 ov2.

(*Definition vgeb (ov1 ov2 : option val) : option bool := promote_bool Z.geb ov1 ov2.
Definition vleb (ov1 ov2 : option val) : option bool := promote_bool Z.leb ov1 ov2.
*)
  Fixpoint bbexpr (s : store) (b : bexpr) : option bool :=
    match b with
      | bbool b => Some b
      | beq e1 e2 => (*veqb (vexpr s e1) (vexpr s e2)*)
        match (vexpr s e1, vexpr s e2) with
          | (Some v1, Some v2) => match (v1, v2) with
                                      | (Vundef, _) => None
                                      | (_, Vundef) => None
                                      | (_, _) =>
                                        match valeq v1 v2 with
                                          | left _ => Some true
                                          | right _ => Some false
                                        end
                                  end
          | _ => None
        end
      | band b1 b2 =>
        match (bbexpr s b1, bbexpr s b2) with
          | (Some b1', Some b2') => Some (andb b1' b2')
          | _ => None
        end
      | bor b1 b2 =>
        match (bbexpr s b1, bbexpr s b2) with
          | (Some b1', Some b2') => Some (orb b1' b2')
          | _ => None
        end
      | bnot b1 =>
        match (bbexpr s b1) with
          | Some b1' => Some (negb b1')
          | _ => None
        end
      | blt e1 e2 => vltb (vexpr s e1) (vexpr s e2)
      | bgt e1 e2 => vgtb (vexpr s e1) (vexpr s e2)
(*      | ble e1 e2 => vleb (vexpr s e1) (vexpr s e2)
      | bge e1 e2 => vgeb (vexpr s e1) (vexpr s e2)*)
    end.
  
  Definition eq_bexpr (s : store) (e e' : bexpr) : Prop :=
    bbexpr s e = bbexpr s e'.

  Lemma eq_bexpr_refl :
    forall (s : store) (e : bexpr),
      eq_bexpr s e e.
  Proof.
    intros. unfold eq_bexpr. auto.
  Qed.

  Lemma eq_bexpr_sym :
    forall (s : store) (e e' : bexpr),
      eq_bexpr s e e' ->
      eq_bexpr s e' e.
  Proof.
    intros. unfold eq_bexpr in H. unfold eq_bexpr. symmetry. auto.
  Qed.

  Lemma eq_bexpr_trans :
    forall (s : store) (e e' e'' : bexpr),
      eq_bexpr s e e' ->
      eq_bexpr s e' e'' ->
      eq_bexpr s e e''.
  Proof.
    intros. unfold eq_bexpr in *.
    rewrite H.
    assumption.
  Qed.

  Definition eq_bexpr_equiv : forall (s : store), Equivalence (eq_bexpr s).
    intros s.
    apply (Build_Equivalence bexpr (eq_bexpr s) (eq_bexpr_refl s) (eq_bexpr_sym s) (eq_bexpr_trans s)).
  Defined.
  
(*  Instance bexpr_setoid : forall (s : store), Setoid bexpr :=
    { equiv := (eq_bexpr s); setoid_equiv := (eq_bexpr_equiv s) }.*)
End Expression.

(* Coercion expr_imm_list lv := map expr_imm lv. *)

(*Parameter vZ : Z -> val.*)
(*Coercion vZ : Z >-> val.*)
Definition vZ : Z -> val := fun (z : Z) => Z_to_Vuint64 z.
Coercion vZ : Z >-> val.
Definition exprZ : Z -> expr := fun (z : Z) => eimm (Some (vZ z)).
Coercion exprZ : Z >-> expr.

Bind Scope expr_scope with expr.
Delimit Scope expr_scope with expr.

(* CDM 8/8/14 : I made the +,-,* levels up.
   I have no idea what they should be. *)
Notation "a + b" := (eplus a b) : expr_scope.
Notation "a - b" := (eminus a b) : expr_scope.
Notation "a * b" := (emul a b) : expr_scope.
(* Notation "a 'mod' b" := (expr_mod a b) (at level 61, left associativity) : expr_scope. *)

Bind Scope bexpr_scope with bexpr.
Delimit Scope bexpr_scope with bexpr.

Notation "s [[ e ]]" := (vexpr s e) (at level 50, no associativity).
Notation "s ⟦ e ⟧" := (vexpr s e) (at level 50, no associativity).

Notation "a && b" := (band a b) : bexpr_scope.
Notation "a || b" := (bor a b) : bexpr_scope.
Notation "a < b" := (blt a b) (at level 70) : bexpr_scope.
Notation "a > b" := (bgt a b) (at level 70) : bexpr_scope.
Notation "a <= b" := (ble a b) (at level 70) : bexpr_scope.
Notation "a >= b" := (bge a b) (at level 70) : bexpr_scope.
Notation "a == b" := (beq a b) (at level 70) : bexpr_scope.
Notation "! a" := (bnot a) (at level 65) : bexpr_scope.

Lemma eq_expr_val_voe :
  forall (e : expr) (v : val) (s : store),
    @eq_expr s e (eimm (Some v)) <->
    s ⟦ e ⟧ = Some v.
Proof.
  intros e v s.
  split.
  intros EE.
  destruct EE.
  subst.
  simpl in *.
  reflexivity.

  elim H; clear H; intros v' H.
  destruct H.
  simpl in H0.
  destruct H0.
  assumption.
  
  intro.
  apply eq_expr_some.
  exists v.
  simpl.
  auto.
Qed.

(*Note: The converse is not true, because e and e' can be different
  expressions, both of which vexpruate to None. *)
Lemma eq_expr_voe :
  forall (e e' : expr) (s : store),
    @eq_expr s e e' ->
    s ⟦ e ⟧ = s ⟦ e' ⟧.
Proof.
  intros e e' s.
  case_eq (s ⟦ e' ⟧).
  intros v EV' EE.
  rewrite <- eq_expr_val_voe in *.
  apply (eq_expr_trans _ _ _ _ EE EV').

  intros SEN' EE.
  inversion EE; subst; clear EE.
  assumption.
  inversion H; subst; clear H.
  destruct H0 as [FOO BAR].
  rewrite SEN' in BAR; discriminate.
Qed.

(*these should go in a more specific file - TJM*)
Variable ERR_SUCCESS : val.
Variable ERR_ERROR : val.
Axiom error_vals : ERR_ERROR <> ERR_SUCCESS.

Inductive term : Type :=
| skip : term
| abort : term
| ret : term.

Inductive atom : Type :=
  | terminal : term -> atom
  | assign : var -> expr -> atom            (* x := E *)
  | heapload : var -> expr -> atom          (* x := [E] *) (* local var, load addr *)
  | heapwrite : expr -> expr -> atom        (* [E1] := E2 *) (* store addr, value *)
  | pcons : var -> var -> expr -> atom      (* (err,memaddr) := pcons(e) *)
  | dispose : expr -> atom                  (* dispose(E) *)
  | local : var -> term -> atom.            (* {local i ...} *) (* local var *)

Inductive stmt : Type :=
  | atomistic : atom -> stmt
  | ifelse : bexpr -> stmt -> stmt -> stmt
  | while : bexpr -> stmt -> stmt
  | atomic : stmt -> stmt
  | seq : stmt -> stmt -> stmt.

Notation "a ';;' b" := (seq a b) (at level 60, right associativity).
Notation "a '≔[' b ']'" := (heapload a b) (at level 61, left associativity).
Notation "a '≔' b" := (assign a b) (at level 61, left associativity).
Notation "'[' a ']≔' b" := (heapwrite a b) (at level 61, left associativity).
Notation "'〈' err ',' t '〉' '≔' 'alloc(' e ')'" := (pcons err t e) (at level 61, left associativity).

(* State *)
Record state : Type := mkst
  {srf : store_f;
   lc : locals;
   hpf : heap_f;
   dm : domain}.

Coercion srf : state >-> store_f.
Coercion lc : state >-> locals.
Coercion hpf : state >-> heap_f.
Coercion dm : state >-> domain.
Definition sr st : store := (srf st) (lc st).
Coercion sr : state >-> store.
Definition hp st : heap := (hpf st) (dm st).
Coercion hp : state >-> heap.
Definition tatom t : atom := terminal t.
Coercion tatom : term >-> atom.
Definition astmt a : stmt := atomistic a.
Coercion astmt : atom >->stmt.
 
(*Equal expressions under a store/locals pair are still equal
 *even when the rest of the state is included*)
Lemma eq_expr_hp :
  forall s l h d (e e' : expr),
    @eq_expr (s l) e e' -> @eq_expr (sr (mkst s l h d)) e e'.
Proof.
  auto.
Qed.

Lemma eq_expr_heap :
  forall s l h d (e e' : expr),
    @eq_expr (s l) e e' -> @eq_expr (mkst s l h d) e e'.
Proof.
  intros s l h d e e' EE.
  simpl; assumption.
Qed.
Hint Resolve eq_expr_heap.

Add Parametric Morphism (s : store) : (vexpr s)
    with signature ((@eq_expr s) ==> Logic.eq)
      as voe_mor.
Proof.
  intros e e' EE.
  inversion EE.
  rewrite H; auto.
  inversion H; subst; clear H.
  elim H0. intros.
  rewrite H. rewrite H1.
  reflexivity.
Qed.

(**** Thread and trace stuff that isn't really used currently ****)
(** Threads : statements with a thread ID *)
Parameter thread_id : Set.
Parameter thread_id_dec_eq : forall (x y : thread_id), {x = y} + {x <> y}.
Parameter generic_id : thread_id.

Record thread : Type := mk_thread
  {stmt_of_thread : stmt;
   thread_id_of_thread : thread_id}.

Definition trace_elt : Type := (state * thread_id)%type.
Inductive trace : Type :=
  | trace_head : trace_elt -> trace
  | trace_cons : trace_elt -> trace -> trace.
Infix "<<" := (trace_cons) (at level 60, right associativity).

Fixpoint append_trace (tr tr' : trace) : trace :=
  match tr with
    | trace_head t => t << tr'
    | trace_cons h t => h << (append_trace t tr')
  end.

Infix "++" := append_trace.

Fixpoint tlength (tr : trace) : nat :=
  match tr with
    | trace_head _ => 1%nat
    | trace_cons _ rest => S (tlength rest)
  end.

Lemma tlength_gt_0 :
  forall (tr : trace),
    (tlength tr > 0)%nat.
Proof.
  intro tr.
  induction tr; unfold tlength; auto.
Qed.

Fixpoint tskip (n : nat) (tr : trace) : trace :=
  match n with
    | O => tr
    | S n' => match tr with
                | trace_head _ => tr
                | trace_cons _ rest => tskip n' rest
              end
  end.

Lemma tskip1 :
  forall (t : trace_elt) (tr : trace),
    (tskip 1 (t << tr)) = tr.
Proof.
  auto.
Qed.

Lemma tskipn :
  forall (n : nat) (tr : trace),
    tskip (S n) tr = tskip n (tskip 1 tr).
Proof.
  induction n; [auto | induction tr; auto].
Qed.

(* extension t t' says that t' is a t with additional trace step(s)
   added to it *)
Inductive extension : trace -> trace -> Prop :=
  | onestep_ext : forall (tr : trace) (t : trace_elt), extension tr (t << tr)
  | nsteps_ext : forall (tr tr' : trace) (t : trace_elt),
                   extension tr tr' -> extension tr (t << tr').

Lemma extensions_longer :
  forall (tr tr' : trace),
    extension tr tr' -> ((tlength tr) < (tlength tr'))%nat.
Proof.
  intros tr tr' ETR.
  induction ETR;  try (apply Lt.lt_trans with (m := (tlength tr'))); auto.
Qed.

Lemma extension_tskipn:
  forall (tr tr' : trace),
    extension tr tr' ->
    exists (n : nat), (n > 0)%nat /\ (tr = tskip n tr')%nat.
Proof.
  intros tr tr' EXT.
  induction tr'.
  apply (extensions_longer tr (trace_head t)) in EXT.
  unfold tlength in EXT at 2.
  generalize (tlength_gt_0 tr); intro OOPS; omega.

  inversion EXT; subst.
  exists 1%nat.
  auto.

  specialize (IHtr' H1).
  elim IHtr'; clear IHtr'; intros n IHtr'.
  destruct IHtr' as [IHtr IHtr'].
  exists (S n).
  split. omega.
  unfold tskip.
  fold tskip.
  assumption.
Qed.

Lemma extension_not_refl :
  forall (tr : trace),
    ~ extension tr tr.
Proof.
  unfold not.
  intros tr ERFL.
  apply (extensions_longer tr tr) in ERFL.
  omega. 
Qed.

Lemma extension_trans :
  forall (tr tr' tr'' : trace),
    extension tr tr' ->
    extension tr' tr'' ->
    extension tr tr''.
Proof.
  induction 2; constructor; auto.
Qed.
Hint Resolve extension_trans.

Lemma trace_cons_and_append_assoc :
  forall (t : trace_elt) (tr tr' : trace),
    (t << tr) ++ tr' = t << (tr ++ tr').
Proof.
  auto.
Qed.

Lemma extension_one :
  forall (t : trace_elt) (tr tr' : trace),
    extension tr (t << tr') ->
    tr = tr' \/ extension tr tr'.
Proof.
  inversion 1; subst; auto.
Qed.

Lemma appending_extends :
  forall (tr tr' : trace),
    extension tr (tr' ++ tr).
Proof.
  induction tr'; simpl; constructor.
  inversion IHtr'; subst; repeat constructor; assumption.
Qed.

Lemma tlength_additive :
  forall (tr tr' : trace),
    tlength (tr ++ tr') = (tlength tr + tlength tr')%nat.
Proof.
  intros tr tr'.
  induction tr; auto.

  simpl; rewrite IHtr; auto.
Qed.

Lemma head_lt_whole :
  forall (tr tr' : trace),
    ((tlength tr) < tlength (tr ++ tr'))%nat.
Proof.
  intros tr tr'.
  generalize (tlength_gt_0 tr'); intros TL.
  rewrite (tlength_additive tr tr').
  omega.
Qed.

Definition progression (tr tr' : trace) : Prop :=
  extension tr tr' \/ tr = tr'.

Lemma progress_trans :
  forall (tr tr' tr'' : trace),
    progression tr tr' ->
    progression tr' tr'' ->
    progression tr tr''.
Proof.
  intros tr tr' tr'' PR1 PR2.
  unfold progression in *. 
  elim PR1 ; elim PR2 ; intros ; try subst tr' ; try (left ; assumption).
  left. apply (extension_trans tr tr' tr'' H0 H).
  subst tr. right. reflexivity.
Qed.

Lemma extend_progress :
  forall (tr tr' tr'' : trace),
    extension tr tr' -> progression tr' tr'' -> extension tr tr''.
Proof.
  destruct 2; eauto. subst tr'. assumption.
Qed.

(** Programs : list of threads *)
Definition program : Type := list thread.

Fixpoint program_is_skip (p : program) : Prop :=
  match p with
    | nil => True
    | ph :: pt => stmt_of_thread ph = skip /\ program_is_skip pt
  end.

Require Eqdep_dec Arith.

Lemma sint32_underflow : forall (n : Z), n < sint32_min -> Z_to_sint32 n = None.
  intros.
  case_eq (sint32_min <=? n).
  intro.
  apply Zle_is_le_bool in H0.
  omega.
  intro.
  generalize (eq_refl (sint32_min <=? n)).
  intro.
  generalize (Eqdep_dec.UIP_dec bool_dec H1 (@eq_refl bool (Z.leb sint32_min n))).
  intro.
  unfold Z_to_sint32.
  set (B := (fun x => (sint32_min <=? n) = x)).
  assert ((existT B (sint32_min <=? n) H1) = (existT B false H0)).
  rewrite <- H0.
  rewrite H2.
  reflexivity.
  rewrite <- H2.
  dependent rewrite -> H3.
  reflexivity.
Qed.

Lemma sint32_overflow : forall (n : Z), sint32_max < n -> Z_to_sint32 n = None.
  intros.
  case_eq (sint32_min <=? n).
  intro.
  case_eq (n <=? sint32_max).
  intro.
  apply Zle_is_le_bool in H1.
  omega.
  intro.
  generalize (eq_refl (n <=? sint32_max)).
  intro.
  generalize (eq_refl (sint32_min <=? n)).
  intro.
  generalize (Eqdep_dec.UIP_dec bool_dec H2 (@eq_refl bool (n <=? sint32_max))).
  intro.
  generalize (Eqdep_dec.UIP_dec bool_dec H3 (@eq_refl bool (sint32_min <=? n))).
  intro.
  unfold Z_to_sint32.
  set (B1 := (fun x => (n <=? sint32_max) = x)).
  assert ((existT B1 (n <=? sint32_max) H2) = (existT B1 false H1)).
  rewrite <- H1.
  rewrite H4.
  reflexivity.
  rewrite <- H4.
  dependent rewrite -> H6.
  set (B2 := (fun x => (sint32_min <=? n) = x)).
  assert ((existT B2 (sint32_min <=? n) H3) = (existT B2 true H0)).
  rewrite H5.
  rewrite <- H0.
  reflexivity.
  rewrite <- H5.
  dependent rewrite -> H7.
  reflexivity.
  intro.
  assert (sint32_min <= n).
  unfold sint32_min, sint32_max in *.
  omega.
  apply Zle_is_le_bool in H1.
  rewrite H1 in H0.
  discriminate.
Qed.

Lemma sint32_in_bounds : forall (z : Z), sint32_min <= z <= sint32_max
                                         <-> (exists (P : sint32_min <= z <= sint32_max), Z_to_sint32 z = Some (Vsint32 z P)).
  intro.
  split.
  intros.
  destruct H.
  assert ((sint32_min <=? z) = true).
  apply Zle_is_le_bool.
  assumption.
  assert ((z <=? sint32_max) = true).
  apply Zle_is_le_bool.
  assumption.
  generalize (eq_refl (z <=? sint32_max)).
  generalize (eq_refl (sint32_min <=? z)).
  intros.
  generalize (Eqdep_dec.UIP_dec bool_dec H4 (@eq_refl bool (z <=? sint32_max))).
  generalize (Eqdep_dec.UIP_dec bool_dec H3 (@eq_refl bool (sint32_min <=? z))).
  intros.
  unfold Z_to_sint32.
  set (B1 := (fun x => (z <=? sint32_max) = x)).
  set (B2 := (fun x => (sint32_min <=? z) = x)).
  assert ((existT B1 (z <=? sint32_max) H4) = (existT B1 true H2)).
  rewrite H6.
  rewrite <- H2.
  reflexivity.
  assert ((existT B2 (sint32_min <=? z) H3) = (existT B2 true H1)).
  rewrite H5.
  rewrite <- H1.
  reflexivity.
  rewrite <- H5.
  rewrite <- H6.
  dependent rewrite -> H7.
  dependent rewrite -> H8.
  exists (conj
             (match Zle_is_le_bool sint32_min z with
              | conj _ H10 => H10
              end H1)
             (match Zle_is_le_bool z sint32_max with
              | conj _ H10 => H10
              end H2)).
  reflexivity.
  intros.
  elim H; intros; assumption.
Qed.

Lemma sint32_out_of_bounds : forall (z : Z), z < sint32_min \/ sint32_max < z <-> Z_to_sint32 z = None.
  intro.
  split.
  intro.
  destruct H.
  apply sint32_underflow; assumption.
  apply sint32_overflow; assumption.
  intro.
  assert (sint32_min <= z <= sint32_max \/ (z < sint32_min \/ sint32_max < z)).
  unfold sint32_min, sint32_max.
  omega.
  destruct H0.
  apply sint32_in_bounds in H0.
  elim H0; intros; rewrite H1 in H; discriminate.
  assumption.
Qed.

Lemma sint64_underflow : forall (n : Z), n < sint64_min -> Z_to_sint64 n = None.
  intros.
  case_eq (sint64_min <=? n).
  intro.
  apply Zle_is_le_bool in H0.
  omega.
  intro.
  generalize (eq_refl (sint64_min <=? n)).
  intro.
  generalize (Eqdep_dec.UIP_dec bool_dec H1 (@eq_refl bool (Z.leb sint64_min n))).
  intro.
  unfold Z_to_sint64.
  set (B := (fun x => (sint64_min <=? n) = x)).
  assert ((existT B (sint64_min <=? n) H1) = (existT B false H0)).
  rewrite <- H0.
  rewrite H2.
  reflexivity.
  rewrite <- H2.
  dependent rewrite -> H3.
  reflexivity.
Qed.

Lemma sint64_overflow : forall (n : Z), sint64_max < n -> Z_to_sint64 n = None.
  intros.
  case_eq (sint64_min <=? n).
  intro.
  case_eq (n <=? sint64_max).
  intro.
  apply Zle_is_le_bool in H1.
  omega.
  intro.
  generalize (eq_refl (n <=? sint64_max)).
  intro.
  generalize (eq_refl (sint64_min <=? n)).
  intro.
  generalize (Eqdep_dec.UIP_dec bool_dec H2 (@eq_refl bool (n <=? sint64_max))).
  intro.
  generalize (Eqdep_dec.UIP_dec bool_dec H3 (@eq_refl bool (sint64_min <=? n))).
  intro.
  unfold Z_to_sint64.
  set (B1 := (fun x => (n <=? sint64_max) = x)).
  assert ((existT B1 (n <=? sint64_max) H2) = (existT B1 false H1)).
  rewrite <- H1.
  rewrite H4.
  reflexivity.
  rewrite <- H4.
  dependent rewrite -> H6.
  set (B2 := (fun x => (sint64_min <=? n) = x)).
  assert ((existT B2 (sint64_min <=? n) H3) = (existT B2 true H0)).
  rewrite H5.
  rewrite <- H0.
  reflexivity.
  rewrite <- H5.
  dependent rewrite -> H7.
  reflexivity.
  intro.
  assert (sint64_min <= n).
  unfold sint64_min, sint64_max in *.
  omega.
  apply Zle_is_le_bool in H1.
  rewrite H1 in H0.
  discriminate.
Qed.

Lemma sint64_in_bounds : forall (z : Z), sint64_min <= z <= sint64_max
                                         <-> (exists (P : sint64_min <= z <= sint64_max), Z_to_sint64 z = Some (Vsint64 z P)).
  intro.
  split.
  intros.
  destruct H.
  assert ((sint64_min <=? z) = true).
  apply Zle_is_le_bool.
  assumption.
  assert ((z <=? sint64_max) = true).
  apply Zle_is_le_bool.
  assumption.
  generalize (eq_refl (z <=? sint64_max)).
  generalize (eq_refl (sint64_min <=? z)).
  intros.
  generalize (Eqdep_dec.UIP_dec bool_dec H4 (@eq_refl bool (z <=? sint64_max))).
  generalize (Eqdep_dec.UIP_dec bool_dec H3 (@eq_refl bool (sint64_min <=? z))).
  intros.
  unfold Z_to_sint64.
  set (B1 := (fun x => (z <=? sint64_max) = x)).
  set (B2 := (fun x => (sint64_min <=? z) = x)).
  assert ((existT B1 (z <=? sint64_max) H4) = (existT B1 true H2)).
  rewrite H6.
  rewrite <- H2.
  reflexivity.
  assert ((existT B2 (sint64_min <=? z) H3) = (existT B2 true H1)).
  rewrite H5.
  rewrite <- H1.
  reflexivity.
  rewrite <- H5.
  rewrite <- H6.
  dependent rewrite -> H7.
  dependent rewrite -> H8.
  exists (conj
             (match Zle_is_le_bool sint64_min z with
              | conj _ H10 => H10
              end H1)
             (match Zle_is_le_bool z sint64_max with
              | conj _ H10 => H10
              end H2)).
  reflexivity.
  intro.
  elim H; intros.
  assumption.
Qed.

Lemma sint64_out_of_bounds : forall (z : Z), z < sint64_min \/ sint64_max < z <-> Z_to_sint64 z = None.
  intro.
  split.
  intro.
  destruct H.
  apply sint64_underflow; assumption.
  apply sint64_overflow; assumption.
  intro.
  assert ((sint64_min <= z <= sint64_max)\/(z < sint64_min \/ sint64_max < z)).
  unfold sint64_min, sint64_max.
  omega.
  destruct H0.
  apply sint64_in_bounds in H0.
  elim H0; intros; rewrite H1 in H; discriminate.
  assumption.
Qed.
