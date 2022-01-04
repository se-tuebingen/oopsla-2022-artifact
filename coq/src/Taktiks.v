(** Borrowed from
    https://gitlab.mpi-sws.org/iris/stdpp/-/blob/master/theories/tactics.v *)

(** The tactic [select pat tac] finds the last (i.e., bottommost) hypothesis
matching [pat] and passes it to the continuation [tac]. Its main advantage over
using [match goal with ] directly is that it is shorter. If [pat] matches
multiple hypotheses and [tac] fails, then [select tac] will not backtrack on
subsequent matching hypotheses.

The tactic [select] is written in CPS and does not return the name of the
hypothesis due to limitations in the Ltac1 tactic runtime (see
https://gitter.im/coq/coq?at=5e96c82f85b01628f04bbb89). *)
Tactic Notation "select" open_constr(pat) tactic3(tac) :=
  lazymatch goal with
  (** Before running [tac] on the hypothesis [H] we must first unify the
      pattern [pat] with the term it matched against. This forces every evar
      coming from [pat] (and in particular from the holes [_] it contains and
      from the implicit arguments it uses) to be instantiated. If we do not do
      so then shelved goals are produced for every such evar. *)
  | H : pat |- _ => let T := (type of H) in unify T pat; tac H
  end.
(** [select_revert] reverts the first hypothesis matching [pat]. *)
Tactic Notation "revert" "select" open_constr(pat) := select pat (fun H => revert H).

Tactic Notation "rename" "select" open_constr(pat) "into" ident(name) :=
  select pat (fun H => rename H into name).

Tactic Notation "inversion" "select" open_constr(pat) :=
  select pat (fun H => inversion H).

Tactic Notation "destruct" "select" open_constr(pat) :=
  select pat (fun H => destruct H).

Tactic Notation "destruct" "select" open_constr(pat) "as" simple_intropattern(destruct_pat) :=
  select pat (fun H => destruct H as destruct_pat).

Ltac solve_using_assumption follow :=
  match goal with
  | H : context G [?g] |- _ =>
    match goal with
    | |- ?g => solve [eapply H; follow]
    end
  end.

Tactic Notation "solve" "using" "assumption" "and" tactic3(tac) :=
  solve_using_assumption tac.

