(** Support for atoms, i.e., objects with decidable equality.  We
    provide here the ability to generate an atom fresh for any finite
    collection, e.g., the lemma [atom_fresh_for_set], and a tactic to
    pick an atom fresh for the current proof context.

    Authors: Arthur Charguéraud and Brian Aydemir.

    Implementation note: In older versions of Coq, [OrderedTypeEx]
    redefines decimal constants to be integers and not natural
    numbers.  The following scope declaration is intended to address
    this issue.  In newer versions of Coq, the declaration should be
    benign. *)

Require Import List.
Require Import Max.
Require Import OrderedType.
Require Import OrderedTypeEx.
Open Scope nat_scope.

Require Import FiniteSets.
Require Import FSetDecide.
Require Import FSetNotin.
Require Import ListFacts.


(* ********************************************************************** *)
(** * Definition *)

(** Labels are structureless objects such that we can always generate
    one fresh from a finite collection.  Equality on labels is [eq] and
    decidable.  We use Coq's module system to make abstract the
    implementation of labels.  The [Export LabelImpl] line below allows
    us to refer to the type [atom] and its properties without having
    to qualify everything with "[LabelImpl.]". *)

Module Type LABEL.

  Parameter label : Set.

  Parameter label_fresh_for_list :
    forall (xs : list label), {x : label | ~ List.In x xs}.

  Declare Module Label_as_OT : UsualOrderedType with Definition t := label.

  Parameter eq_label_dec : forall x y : label, {x = y} + {x <> y}.

End LABEL.

(** The implementation of the above interface is hidden for
    documentation purposes. *)

Module LabelImpl : LABEL.

  (* begin hide *)

  Definition label := nat.

  Lemma max_lt_r : forall x y z,
    x <= z -> x <= max y z.
  Proof.
    induction x. auto with arith.
    induction y; auto with arith.
      simpl. induction z. intuition. auto with arith.
  Qed.

  Lemma nat_list_max : forall (xs : list nat),
    { n : nat | forall x, In x xs -> x <= n }.
  Proof.
    induction xs as [ | x xs [y H] ].
    (* case: nil *)
    exists 0. inversion 1.
    (* case: cons x xs *)
    exists (max x y). intros z J. simpl in J. destruct J as [K | K].
      subst. auto with arith.
      auto using max_lt_r.
  Qed.

  Lemma label_fresh_for_list :
    forall (xs : list nat), { n : nat | ~ List.In n xs }.
  Proof.
    intros xs. destruct (nat_list_max xs) as [x H].
    exists (S x). intros J. lapply (H (S x)). intuition. trivial.
  Qed.

  Module Label_as_OT := Nat_as_OT.
  Module Facts := OrderedTypeFacts Label_as_OT.

  Definition eq_label_dec : forall x y : label, {x = y} + {x <> y} :=
    Facts.eq_dec. 

  (* end hide *)

End LabelImpl.

Export LabelImpl.


(* ********************************************************************** *)
(** * Finite sets of labels *)


(* ********************************************************************** *)
(** ** Definitions *)

Module LabelSet : FiniteSets.S with Module E := Label_as_OT :=
  FiniteSets.Make Label_as_OT.

(** The type [labels] is the type of finite sets of [label]s. *)

Notation labels := LabelSet.F.t.

Notation "{}L" :=
  LabelSet.F.empty : metatheory_scope.

(** Basic operations on finite sets of labels are available, in the
    remainder of this file, without qualification.  We use [Import]
    instead of [Export] in order to avoid unnecessary namespace
    pollution. *)

Import LabelSet.F.

(** We instantiate two modules which provide useful lemmas and tactics
    work working with finite sets of labels. *)

Module LabelSetDecide := FSetDecide.Decide LabelSet.F.
Module LabelSetNotin  := FSetNotin.Notin   LabelSet.F.
Module LabelSetFacts  := FSetFacts.Facts   LabelSet.F.
Module LabelSetProperties := FSetProperties.Properties LabelSet.F.

(* *********************************************************************** *)
(** ** Tactics for working with finite sets of labels *)

(** The tactic [fsetdec] is a general purpose decision procedure
    for solving facts about finite sets of labels. *)

Ltac lsetdec := try apply LabelSet.eq_if_Equal; LabelSetDecide.fsetdec.

(** The tactic [notin_simpl] simplifies all hypotheses of the form [(~
    In x F)], where [F] is constructed from the empty set, singleton
    sets, and unions. *)

Ltac lnotin_simpl := LabelSetNotin.notin_simpl_hyps.

(** The tactic [notin_solve], solves goals of the form [(~ In x F)],
    where [F] is constructed from the empty set, singleton sets, and
    unions.  The goal must be provable from hypothesis of the form
    simplified by [notin_simpl]. *)

Ltac lnotin_solve := LabelSetNotin.notin_solve.


(* *********************************************************************** *)
(** ** Lemmas for working with finite sets of labels *)

(** We make some lemmas about finite sets of labels available without
    qualification by using abbreviations. *)

Notation leq_if_Equal        := LabelSet.eq_if_Equal.
Notation lnotin_empty        := LabelSetNotin.notin_empty.
Notation lnotin_singleton    := LabelSetNotin.notin_singleton.
Notation lnotin_singleton_rw := LabelSetNotin.notin_singleton_rw.
Notation lnotin_union        := LabelSetNotin.notin_union.


(* ********************************************************************** *)
(** * Additional properties *)

(** One can generate an label fresh for a given finite set of labels. *)

Lemma label_fresh_for_set : forall L : labels, { x : label | ~ In x L }.
Proof.
  intros L. destruct (label_fresh_for_list (elements L)) as [a H].
  exists a. intros J. contradiction H.
  rewrite <- InA_iff_In. auto using elements_1.
Qed.


(* ********************************************************************** *)
(** * Additional tactics *)


(* ********************************************************************** *)
(** ** #<a name="pick_fresh"></a># Picking a fresh label *)

(** We define three tactics which, when combined, provide a simple
    mechanism for picking a fresh label.  We demonstrate their use
    below with an example, the [example_pick_fresh] tactic.

   [(gather_labels_with F)] returns the union of [(F x)], where [x]
   ranges over all objects in the context such that [(F x)] is
   well typed.  The return type of [F] should be [labels].  The
   complexity of this tactic is due to the fact that there is no
   support in [Ltac] for folding a function over the context. *)

Ltac gather_labels_with F :=
  let rec gather V :=
    match goal with
    | H: ?S |- _ =>
      let FH := constr:(F H) in
      match V with
      | empty => gather FH
      | context [FH] => fail 1
      | _ => gather (union FH V)
      end
    | _ => V
    end in
  let L := gather empty in eval simpl in L.

(** [(beautify_lset V)] takes a set [V] built as a union of finite
    sets and returns the same set with empty sets removed and union
    operations associated to the right.  Duplicate sets are also
    removed from the union. *)

Ltac beautify_lset V :=
  let rec go Acc E :=
     match E with
     | union ?E1 ?E2 => let Acc1 := go Acc E2 in go Acc1 E1
     | empty => Acc
     | ?E1 => match Acc with
              | empty => E1
              | context [E1] => Acc
              | _ => constr:(union E1 Acc)
              end
     end
  in go empty V.

(** The tactic [(pick fresh Y for L)] takes a finite set of labels [L]
    and a fresh name [Y], and adds to the context an label with name
    [Y] and a proof that [(~ In Y L)], i.e., that [Y] is fresh for
    [L].  The tactic will fail if [Y] is already declared in the
    context. *)

Tactic Notation "pick" "fresh" "label" ident(Y) "for" constr(L) :=
  let Fr := fresh "Fr" in
  let L := beautify_lset L in
  (destruct (label_fresh_for_set L) as [Y Fr]).


(* ********************************************************************** *)
(** ** Demonstration *)

(** The [example_pick_fresh] tactic below illustrates the general
    pattern for using the above three tactics to define a tactic which
    picks a fresh label.  The pattern is as follows:
      - Repeatedly invoke [gather_labels_with], using functions with
        different argument types each time.
      - Union together the result of the calls, and invoke
        [(pick fresh ... for ...)] with that union of sets. *)

Ltac example_pick_fresh Y :=
  let A := gather_labels_with (fun x : labels => x) in
  let B := gather_labels_with (fun x : label => singleton x) in
  pick fresh label Y for (union A B).

Lemma example_pick_fresh_use : forall (x y z : label) (L1 L2 L3: labels), True.
(* begin show *)
Proof.
  intros x y z L1 L2 L3. example_pick_fresh k.

  (** At this point in the proof, we have a new label [k] and a
      hypothesis [Fr : ~ In k (union L1 (union L2 (union L3 (union
      (singleton x) (union (singleton y) (singleton z))))))]. *)

  trivial.
Qed.

(* end show *)

Notation "x =l= y" := (eq_label_dec x y) (at level 67) : metatheory_scope.

Definition labels_disjoint (xs : labels) (ys: labels) : Prop :=
  LabelSet.F.Empty (LabelSet.F.inter xs ys).