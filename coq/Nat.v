Require Import OrderedTypeEx.
Require Import OrderedType.
Require Import Metatheory.

Require Import FSetFacts.

(** Helpers, defining a set of natural numbers. *)
Module Type NATSET.
  Declare Module OT : UsualOrderedType with Definition t := nat.
  Parameter eq_nat_dec : forall x y : nat, {x = y} + {x <> y}.
End NATSET.

(** The implementation of the above interface is hidden for
    documentation purposes. *)

Module NatSetImpl : NATSET.
  (* begin hide *)
  Module OT := Nat_as_OT.
  Module Facts := OrderedTypeFacts OT.
  Definition eq_nat_dec : forall x y : nat, {x = y} + {x <> y} :=
    Facts.eq_dec. 
  (* end hide *)
End NatSetImpl.

(** Defining a set of Natural Numbers. *)
Module NatSet : FiniteSets.S with Module E := NatSetImpl.OT :=
  FiniteSets.Make NatSetImpl.OT.

(** The type [nats] is the type of finite sets of [nat]s. *)
Notation nats := NatSet.F.t.
Notation "{}N" :=
  NatSet.F.empty : metatheory_scope.

(** We instantiate two modules which provide useful lemmas and tactics
    work working with finite sets of atoms. *)

Module NatSetDecide := FSetDecide.Decide NatSet.F.
Module NatSetNotin  := FSetNotin.Notin   NatSet.F.
Module NatSetFacts  := FSetFacts.Facts NatSet.F.
Module NatSetProperties := FSetProperties.Properties NatSet.F.

(* *********************************************************************** *)
(** ** Tactics for working with finite sets of nats *)

(** The tactic [fnsetdec] is a general purpose decision procedure
    for solving facts about finite sets of atoms. *)

Ltac fnsetdec := try apply NatSet.eq_if_Equal; NatSetDecide.fsetdec.

(** The tactic [notin_simpl] simplifies all hypotheses of the form [(~
    In x F)], where [F] is constructed from the empty set, singleton
    sets, and unions. *)

Ltac nnotin_simpl := NatSetNotin.notin_simpl_hyps.

(** The tactic [notin_solve], solves goals of the form [(~ In x F)],
    where [F] is constructed from the empty set, singleton sets, and
    unions.  The goal must be provable from hypothesis of the form
    simplified by [notin_simpl]. *)

Ltac nnotin_solve := NatSetNotin.notin_solve.