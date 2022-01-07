(** #
<div class="source">
  The source of this file can be found on
  <a href="{{site.github}}/blob/main/coq/SystemC/Infrastructure.v">Github</a>.
</div>
# *)

Require Import Taktiks.
Require Export SystemC.Definitions.

(** This file is a (more-or-less) straight forward adaptation of
    the infrastructure code that is necessary to work with locally nameless.

    All lemmas and proofs are just concerned with binding and are not especially
    interesting. *)

(** ** Free Variables *)

(** *** Free Expression Variables *)
Fixpoint fv_ee (e : exp) {struct e} : atoms :=
  match e with
  | exp_bvar i => {}
  | exp_fvar x => singleton x
  | exp_const => {}
  | exp_box C b => fv_eb b
  end
with fv_es (s : stm) {struct s} : atoms :=
  match s with
  | stm_ret e => fv_ee e
  | stm_val T s1 s2 => (fv_es s1) `union` (fv_es s2)
  | stm_def C S1 b s => (fv_eb b) `union` (fv_es s)
  | stm_vapp b e => (fv_eb b) `union` (fv_ee e)
  | stm_bapp b C g => (fv_eb b) `union` (fv_eb g)
  | stm_try C T1 T b g => (fv_es b) `union` (fv_es g)
  | stm_reset l C b g => (fv_es b) `union` (fv_es g)
  | stm_perform b e => fv_eb b `union` fv_ee e
  end
with fv_eb (b : blk) {struct b} : atoms :=
  match b with
  | blk_bvar i => {}
  | blk_fvar x => {}
  | blk_vabs T s => fv_es s
  | blk_babs S1 s => fv_es s
  | blk_tabs s => fv_eb s
  | blk_tapp s T => fv_eb s
  | blk_unbox e => fv_ee e
  | blk_handler l => {}
  end.

(** *** Free Block Term Variables *)
Fixpoint fv_be (e : exp) {struct e} : atoms :=
  match e with
  | exp_bvar i => {}
  | exp_fvar x => {}
  | exp_const => {}
  | exp_box C1 b => fv_bb b
  end
with fv_bs (s : stm) {struct s} : atoms :=
  match s with
  | stm_ret e => fv_be e
  | stm_val T s1 s2 => (fv_bs s1) `union` (fv_bs s2)
  | stm_def C1 S1 b s => (fv_bb b) `union` (fv_bs s)
  | stm_vapp b e => (fv_bb b) `union` (fv_be e)
  | stm_bapp b C1 g => (fv_bb b) `union` (fv_bb g)
  | stm_try C T1 T b g => (fv_bs b) `union` (fv_bs g)
  | stm_reset l C b g => (fv_bs b) `union` (fv_bs g)
  | stm_perform b e => fv_bb b `union` fv_be e
  end
with fv_bb (b : blk) {struct b} : atoms :=
  match b with
  | blk_bvar i => {}
  | blk_fvar x => (singleton x)
  | blk_vabs T s => (fv_bs s)
  | blk_babs S1 s => (fv_bs s)
  | blk_tabs s => fv_bb s
  | blk_tapp s T => fv_bb s
  | blk_unbox e => (fv_be e)
  | blk_handler l => {}
  end.

(** *** Free Block Type Variables *)
Fixpoint fv_cvt (T : vtyp) {struct T} : atoms :=
  match T with
  | typ_base => {}
  | typ_capt S1 C1 => (fv_cbt S1) `union` (cset_fvars C1)
  | typ_fvar a => {}
  | typ_bvar n => {}
  end
with fv_cbt (S1 : btyp) {struct S1} : atoms :=
  match S1 with
  | typ_vfun T1 T2 => (fv_cvt T1) `union` (fv_cvt T2)
  | typ_bfun S1 T => (fv_cbt S1) `union` (fv_cvt T)
  | typ_eff T1 T => (fv_cvt T1) `union` (fv_cvt T)
  | typ_tfun T => (fv_cbt T)
  end.

Fixpoint fv_ce (e : exp) {struct e} : atoms :=
  match e with
  | exp_bvar i => {}
  | exp_fvar x => {}
  | exp_const => {}
  | exp_box C1 b => (cset_fvars C1) `union` (fv_cb b)
  end

with fv_cs (s : stm) {struct s} : atoms :=
  match s with
  | stm_ret e => (fv_ce e)
  | stm_val T s1 s2 => (fv_cvt T) `union` (fv_cs s1) `union` (fv_cs s2)
  | stm_def C1 S1 b s => (cset_fvars C1) `union` (fv_cbt S1) `union` (fv_cb b) `union` (fv_cs s)
  | stm_vapp b e => (fv_cb b) `union` (fv_ce e)
  | stm_bapp b C1 g => (fv_cb b) `union` (cset_fvars C1) `union` (fv_cb g)
  | stm_try C1 T1 T b g => (fv_cvt T1) `union` (fv_cvt T) `union` (cset_fvars C1) `union` (fv_cs b) `union` (fv_cs g)
  | stm_reset l C1 b g => (cset_fvars C1) `union` (fv_cs b) `union` (fv_cs g)
  | stm_perform b e => fv_cb b `union` fv_ce e
  end

with fv_cb (b : blk) {struct b} : atoms :=
  match b with
  | blk_bvar i => {}
  | blk_fvar x => singleton x
  | blk_vabs T s => (fv_cvt T) `union` (fv_cs s)
  | blk_babs S1 s => (fv_cbt S1) `union` (fv_cs s)
  | blk_tabs s => (fv_cb s)
  | blk_tapp s T => (fv_cb s) `union` (fv_cvt T)
  | blk_unbox e => (fv_ce e)
  | blk_handler l => {}
  end.

(** *** Free Type Variables *)
Fixpoint fv_tvt (T : vtyp) {struct T} : atoms :=
match T with
  | typ_base => {}
  | typ_capt S1 C1 => (fv_tbt S1)
  | typ_fvar a => singleton a
  | typ_bvar n => {}
  end
with fv_tbt (S1 : btyp) {struct S1} : atoms :=
  match S1 with
  | typ_vfun T1 T2 => (fv_tvt T1) `union` (fv_tvt T2)
  | typ_bfun S1 T => (fv_tbt S1) `union` (fv_tvt T)
  | typ_eff T1 T => (fv_tvt T1) `union` (fv_tvt T)
  | typ_tfun T => (fv_tbt T)
  end.

Fixpoint fv_te (e : exp) {struct e} : atoms :=
  match e with
  | exp_bvar i => {}
  | exp_fvar x => {}
  | exp_const => {}
  | exp_box C b => fv_tb b
  end
with fv_ts (s : stm) {struct s} : atoms :=
  match s with
  | stm_ret e => fv_te e
  | stm_val T s1 s2 => (fv_tvt T) `union` (fv_ts s1) `union` (fv_ts s2)
  | stm_def C S1 b s => (fv_tbt S1) `union` (fv_tb b) `union` (fv_ts s)
  | stm_vapp b e => (fv_tb b) `union` (fv_te e)
  | stm_bapp b C g => (fv_tb b) `union` (fv_tb g)
  | stm_try C T1 T b g => (fv_tvt T1) `union` (fv_tvt T) `union` (fv_ts b) `union` (fv_ts g)
  | stm_reset l C b g => (fv_ts b) `union` (fv_ts g)
  | stm_perform b e => fv_tb b `union` fv_te e
  end
with fv_tb (b : blk) {struct b} : atoms :=
  match b with
  | blk_bvar i => {}
  | blk_fvar x => {}
  | blk_vabs T s => fv_tvt T `union` fv_ts s
  | blk_babs S1 s => fv_tbt S1 `union` fv_ts s
  | blk_tabs s => fv_tb s
  | blk_tapp s T => fv_tvt T `union` fv_tb s
  | blk_unbox e => fv_te e
  | blk_handler l => {}
  end.

Definition fv_bbind (b : binding) : atoms :=
  match b with
  | bind_val T => {}
  | bind_blk s tracked => (fv_cbt s)
  | bind_blk s (capture C2) => (fv_cbt s) `union` (cset_fvars C2)
  | bind_typ => {}
  end.

Ltac gather_atoms :=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in

  let C := gather_atoms_with (fun x : exp => fv_ee x) in
  let D := gather_atoms_with (fun x : exp => fv_be x) in
  let E := gather_atoms_with (fun x : exp => fv_ce x) in

  let F := gather_atoms_with (fun x : stm => fv_bs x) in
  let G := gather_atoms_with (fun x : stm => fv_es x) in
  let H := gather_atoms_with (fun x : stm => fv_cs x) in

  let I := gather_atoms_with (fun x : blk => fv_bb x) in
  let J := gather_atoms_with (fun x : blk => fv_eb x) in
  let K := gather_atoms_with (fun x : blk => fv_cb x) in

  let L := gather_atoms_with (fun x : cap => cset_fvars x) in
  let M := gather_atoms_with (fun x : vtyp => fv_cvt x) in
  let N := gather_atoms_with (fun x : btyp => fv_cbt x) in
  let O := gather_atoms_with (fun x : vtyp => fv_tvt x) in
  let P := gather_atoms_with (fun x : btyp => fv_tbt x) in

  let Q := gather_atoms_with (fun x : exp => fv_te x) in
  let R := gather_atoms_with (fun x : stm => fv_ts x) in
  let S := gather_atoms_with (fun x : blk => fv_tb x) in

  let Z := gather_atoms_with (fun x : env => dom x) in

  constr:(A `union` B `union` C `union` D `union` E `union` F `union` G `union` H `union` I `union` J `union` K `union` L `union` M `union` N
          `union` O `union` P `union` Q `union` R `union` S `union` Z).

(** The second step in defining "[pick fresh]" is to define the tactic
    itself.  It is based on the [(pick fresh ... for ...)] tactic
    defined in the [Atom] library.  Here, we use [gather_atoms] to
    construct the set [L] rather than leaving it to the user to
    provide.  Thus, invoking [(pick fresh x)] introduces a new atom
    [x] into the current context that is fresh for "everything" in the
    context. *)

Tactic Notation "pick" "fresh" ident(x) :=
  let L := gather_atoms in (pick fresh x for L).


(** *** #<a name="apply_fresh"></a># The "[pick fresh and apply]" tactic *)

(** This tactic is implementation specific only because of its
    reliance on [gather_atoms], which is itself implementation
    specific.  The definition below may be copied between developments
    without any changes, assuming that the other other developments
    define an appropriate [gather_atoms] tactic.  For documentation on
    the tactic on which the one below is based, see the
    [Metatheory] library. *)

Tactic Notation
      "pick" "fresh" ident(atom_name) "and" "apply" constr(lemma) :=
  let L := gather_atoms in
  pick fresh atom_name excluding L and apply lemma.



Lemma subst_ee_intro_rec : forall x e u k,
  x `notin` fv_ee e ->
  open_ee_rec k u e = subst_ee x u (open_ee_rec k (exp_fvar x) e)
with subst_es_intro_rec : forall x e u k,
  x `notin` fv_es e ->
  open_es_rec k u e = subst_es x u (open_es_rec k (exp_fvar x) e)
with subst_eb_intro_rec : forall x e u k,
  x `notin` fv_eb e ->
  open_eb_rec k u e = subst_eb x u (open_eb_rec k (exp_fvar x) e).
Proof with auto*.
------
  induction e; intros u k Fr; simpl in *; f_equal...
  Case "exp_bvar".
    destruct (k === n)... simpl. destruct (x == x)...
  Case "exp_fvar".
    destruct (a == x)... contradict Fr; fsetdec.
------
  induction e; intros u k Fr; simpl in *; f_equal...
------
  induction e; intros u k Fr; simpl in *; f_equal...
Qed.

Lemma subst_ee_intro : forall x e u,
  x `notin` fv_ee e ->
  open_ee e u = subst_ee x u (open_ee e x)
with subst_es_intro : forall x e u,
  x `notin` fv_es e ->
  open_es e u = subst_es x u (open_es e x)
with subst_eb_intro : forall x e u,
  x `notin` fv_eb e ->
  open_eb e u = subst_eb x u (open_eb e x).
Proof with auto*.
------
  intros.
  unfold open_ee.
  apply subst_ee_intro_rec...
------
  intros.
  unfold open_es.
  apply subst_es_intro_rec...
------
  intros.
  unfold open_eb.
  apply subst_eb_intro_rec...
Qed.

Lemma subst_be_intro_rec : forall x e u k,
  x `notin` fv_be e ->
  open_be_rec k u e = subst_be x u (open_be_rec k (blk_fvar x) e)
with subst_bs_intro_rec : forall x e u k,
  x `notin` fv_bs e ->
  open_bs_rec k u e = subst_bs x u (open_bs_rec k (blk_fvar x) e)
with subst_bb_intro_rec : forall x e u k,
  x `notin` fv_bb e ->
  open_bb_rec k u e = subst_bb x u (open_bb_rec k (blk_fvar x) e).
Proof with auto*.
------
  induction e; intros u k Fr; simpl in *; f_equal...
------
  induction e; intros u k Fr; simpl in *; f_equal...
------
  induction e; intros u k Fr; simpl in *; f_equal...
  Case "exp_bvar".
    destruct (k === n)... simpl. destruct (x == x)...
  Case "exp_fvar".
    destruct (a == x)... contradict Fr; fsetdec.
Qed.

Lemma subst_be_intro : forall x e u,
  x `notin` fv_be e ->
  open_be e u = subst_be x u (open_be e x)
with subst_bs_intro : forall x e u,
  x `notin` fv_bs e ->
  open_bs e u = subst_bs x u (open_bs e x)
with subst_bb_intro : forall x e u,
  x `notin` fv_bb e ->
  open_bb e u = subst_bb x u (open_bb e x).
Proof with auto*.
------
  intros.
  unfold open_be.
  apply subst_be_intro_rec...
------
  intros.
  unfold open_bs.
  apply subst_bs_intro_rec...
------
  intros.
  unfold open_bb.
  apply subst_bb_intro_rec...
Qed.

Lemma subst_cvt_intro_rec : forall X T2 U k,
  X `notin` fv_cvt T2 ->
  open_cvt_rec k U T2 = subst_cvt X U (open_cvt_rec k (cset_fvar X) T2)
with subst_cbt_intro_rec : forall X T2 U k,
  X `notin` fv_cbt T2 ->
  open_cbt_rec k U T2 = subst_cbt X U (open_cbt_rec k (cset_fvar X) T2).
Proof with auto*.
------
  induction T2; intros U k Fr; simpl in *; try trivial.
  - f_equal.
    eapply subst_cbt_intro_rec...
    eapply subst_cc_intro_rec...
------
  induction T2; intros U k Fr; simpl in *; f_equal...
Qed.

Lemma subst_cvt_intro : forall X T2 U,
  X `notin` fv_cvt T2 ->
  open_cvt T2 U = subst_cvt X U (open_cvt T2 (cset_fvar X))
with subst_cbt_intro : forall X T2 U,
  X `notin` fv_cbt T2 ->
  open_cbt T2 U = subst_cbt X U (open_cbt T2 (cset_fvar X)).
Proof with auto*.
------
  intros.
  unfold open_cvt.
  apply subst_cvt_intro_rec...
------
  intros.
  unfold open_cbt.
  apply subst_cbt_intro_rec...
Qed.

Lemma subst_ce_intro_rec : forall x e u C k,
  x `notin` fv_ce e ->
  open_ce_rec k u C e = subst_ce x u C (open_ce_rec k x (cset_fvar x) e)
with subst_cs_intro_rec : forall x e u C k,
  x `notin` fv_cs e ->
  open_cs_rec k u C e = subst_cs x u C (open_cs_rec k x (cset_fvar x) e)
with subst_cb_intro_rec : forall x e u C k,
  x `notin` fv_cb e ->
  open_cb_rec k u C e = subst_cb x u C (open_cb_rec k x (cset_fvar x) e).
Proof with eauto using
  subst_cvt_intro_rec,
  subst_cc_intro_rec,
  subst_cbt_intro_rec.
------
  induction e; intros; simpl in *; f_equal...
------
  induction e; intros; simpl in *; f_equal...
------
  induction e; intros; try solve [simpl in *; f_equal; eauto using subst_cvt_intro_rec, subst_cc_intro_rec, subst_cbt_intro_rec].
  - simpl in *.
    destruct (k === n); subst...
    unfold subst_cb.
    destruct (x == x)... fsetdec.
  - simpl in *.
    destruct (a == x)... fsetdec.
Qed.


Lemma subst_ce_intro : forall x e u C,
  x `notin` fv_ce e ->
  open_ce e u C = subst_ce x u C (open_ce e x (cset_fvar x))
with subst_cs_intro : forall x e u C,
  x `notin` fv_cs e ->
  open_cs e u C = subst_cs x u C (open_cs e x (cset_fvar x))
with subst_cb_intro : forall x e u C,
  x `notin` fv_cb e ->
  open_cb e u C = subst_cb x u C (open_cb e x (cset_fvar x)).
Proof with auto*.
------
  intros.
  unfold open_ce.
  apply subst_ce_intro_rec...
------
  intros.
  unfold open_cs.
  apply subst_cs_intro_rec...
------
  intros.
  unfold open_cb.
  apply subst_cb_intro_rec...
Qed.


(** ** Opening Closed Lemmas *)
(** The naming scheme of the aux lemmas is:
<<
    open_EXPRe_rec j u e = open_CE_rec i P C (open_EXPR_rec j u e)
>>
**)

Lemma open_cvt_rec_capt_aux : forall T j V i U,
  i <> j ->
  capt V ->
  (cset_fvars V) `disjoint` (cset_fvars U) ->
  labels_disjoint (cset_lvars V) (cset_lvars U) ->
  open_cvt_rec j V T = open_cvt_rec i U (open_cvt_rec j V T) ->
  T = open_cvt_rec i U T
with open_cbt_rec_capt_aux : forall T j V i U,
  i <> j ->
  capt V ->
  (cset_fvars V) `disjoint` (cset_fvars U) ->
  labels_disjoint (cset_lvars V) (cset_lvars U) ->
  open_cbt_rec j V T = open_cbt_rec i U (open_cbt_rec j V T) ->
  T = open_cbt_rec i U T.
Proof with eauto using open_cset_rec_capt_aux.
------
  induction T; intros j V i U Neq Hclosed Hdisjoint Ldisjoint H; simpl in *; inversion H; f_equal...
------
  induction T; intros j V i U Neq Hclosed Hdisjoint Ldisjoint H; simpl in *; inversion H; f_equal...
Qed.

Lemma open_cvt_rec_type_aux : forall T j U i C,
  open_tvt_rec j U T = open_cvt_rec i C (open_tvt_rec j U T) ->
  T = open_cvt_rec i C T
with open_cbt_rec_type_aux : forall T j U i C,
  open_tbt_rec j U T = open_cbt_rec i C (open_tbt_rec j U T) ->
  T = open_cbt_rec i C T.
Proof with eauto.
------
  intros * H. induction T; simpl in *; f_equal;
    try solve [inversion H; eauto*].
------
  intros * H. induction T; simpl in *; f_equal;
    try solve [inversion H; eauto*].
Qed.

Lemma open_cvt_rec_vtype : forall T U k,
  vtype T ->
  T = open_cvt_rec k U T
with open_cbt_rec_btype : forall T U k,
  btype T ->
  T = open_cbt_rec k U T.
Proof with eauto.
------
  intros * Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
------
  intros * Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
  - unfold open_cvt in *.
    pick fresh X.
    eapply open_cvt_rec_capt_aux with (j := 0) (V := (cset_fvar X)); simpl...
    + unfold disjoint. fsetdec.
    + unfold labels_disjoint. clear Fr H IHHtyp. lsetdec.
  - unfold open_tbt in *.
    pick fresh X.
    eapply open_cbt_rec_type_aux with (j := 0) (U := X)...
Qed.

Lemma open_ee_rec_expr_aux : forall e j v u i,
  i <> j ->
  open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) ->
  e = open_ee_rec i u e
with open_eb_rec_expr_aux : forall e j v u i,
  i <> j ->
  open_eb_rec j v e = open_eb_rec i u (open_eb_rec j v e) ->
  e = open_eb_rec i u e
with open_es_rec_expr_aux : forall e j v u i,
  i <> j ->
  open_es_rec j v e = open_es_rec i u (open_es_rec j v e) ->
  e = open_es_rec i u e.
Proof with eauto*.
------
  induction e; intros * Neq H; simpl in *; inversion H; f_equal...
  Case "exp_bvar".
    destruct (j===n)... destruct (i===n)...
------
  induction e; intros * Neq H; simpl in *; inversion H; f_equal...
------
  induction e; intros * Neq H; simpl in *; inversion H; f_equal...
Qed.

Lemma open_ce_rec_capt_aux : forall e j v u i (C D : cap),
  i <> j ->
  capt C ->
  (cset_fvars C) `disjoint` (cset_fvars D) ->
  labels_disjoint (cset_lvars C) (cset_lvars D) ->
  open_ce_rec j v C e = open_ce_rec i u D (open_ce_rec j v C e) ->
  e = open_ce_rec i u D e
with open_cb_rec_capt_aux : forall e j v u i (C D : cap),
  i <> j ->
  capt C ->
  (cset_fvars C) `disjoint` (cset_fvars D) ->
  labels_disjoint (cset_lvars C) (cset_lvars D) ->
  open_cb_rec j v C e = open_cb_rec i u D (open_cb_rec j v C e) ->
  e = open_cb_rec i u D e
with open_cs_rec_capt_aux : forall e j v u i (C D : cap),
  i <> j ->
  capt C ->
  (cset_fvars C) `disjoint` (cset_fvars D) ->
  labels_disjoint (cset_lvars C) (cset_lvars D) ->
  open_cs_rec j v C e = open_cs_rec i u D (open_cs_rec j v C e) ->
  e = open_cs_rec i u D e.
Proof with eauto using open_cset_rec_capt_aux, open_cvt_rec_capt_aux, open_cbt_rec_capt_aux.
------
  induction e; intros * Neq Hclosed Hdisjoint Ldisjoint H; simpl in *; inversion H; f_equal...
------
  induction e; intros * Neq Hclosed Hdisjoint Ldisjoint H; simpl in *; inversion H; f_equal...
  - destruct (j===n)... destruct (i===n)...
    subst. fnsetdec.
------
  induction e; intros * Neq Hclosed Hdisjoint Ldisjoint H; simpl in *; inversion H; f_equal...
Qed.

Lemma open_ce_rec_expr_aux : forall e j u C i P ,
  open_ee_rec j u e = open_ce_rec i P C (open_ee_rec j u e) ->
  e = open_ce_rec i P C e
with open_cb_rec_expr_aux : forall e j u C i P ,
  open_eb_rec j u e = open_cb_rec i P C (open_eb_rec j u e) ->
  e = open_cb_rec i P C e
with open_cs_rec_expr_aux : forall e j u C i P ,
  open_es_rec j u e = open_cs_rec i P C (open_es_rec j u e) ->
  e = open_cs_rec i P C e.
Proof with eauto using open_cset_rec_capt_aux, open_cvt_rec_capt_aux, open_cbt_rec_capt_aux.
------
  induction e; intros * H; simpl in *; inversion H; f_equal; auto*...
------
  induction e; intros * H; simpl in *; inversion H; f_equal; auto*...
------
  induction e; intros * H; simpl in *; inversion H; f_equal; auto*...
Qed.

Lemma open_ce_rec_type_aux : forall e j u C i P ,
  open_te_rec j u e = open_ce_rec i P C (open_te_rec j u e) ->
  e = open_ce_rec i P C e
with open_cb_rec_type_aux : forall e j u C i P ,
  open_tb_rec j u e = open_cb_rec i P C (open_tb_rec j u e) ->
  e = open_cb_rec i P C e
with open_cs_rec_type_aux : forall e j u C i P ,
  open_ts_rec j u e = open_cs_rec i P C (open_ts_rec j u e) ->
  e = open_cs_rec i P C e.
Proof with eauto using open_cset_rec_capt_aux, open_cvt_rec_capt_aux, open_cbt_rec_capt_aux,
  open_cvt_rec_type_aux, open_cbt_rec_type_aux.
------
  induction e; intros * H; simpl in *; inversion H; f_equal; auto*...
------
  induction e; intros * H; simpl in *; inversion H; f_equal; auto*...
------
  induction e; intros * H; simpl in *; inversion H; f_equal; auto*...
Qed.


Lemma open_ee_rec_type_aux : forall e j U i f,
  open_te_rec j U e = open_ee_rec i f (open_te_rec j U e) ->
  e = open_ee_rec i f e
with open_eb_rec_type_aux : forall e j U i f,
  open_tb_rec j U e = open_eb_rec i f (open_tb_rec j U e) ->
  e = open_eb_rec i f e
with open_es_rec_type_aux : forall e j U i f,
  open_ts_rec j U e = open_es_rec i f (open_ts_rec j U e) ->
  e = open_es_rec i f e.
Proof with eauto using open_cset_rec_capt_aux, open_cvt_rec_capt_aux, open_cbt_rec_capt_aux,
  open_cvt_rec_type_aux, open_cbt_rec_type_aux.
------
  induction e; intros * H; simpl in *; inversion H; f_equal; auto*...
------
  induction e; intros * H; simpl in *; inversion H; f_equal; auto*...
------
  induction e; intros * H; simpl in *; inversion H; f_equal; auto*...
Qed.


Lemma open_be_rec_type_aux : forall e j U i f,
  open_te_rec j U e = open_be_rec i f (open_te_rec j U e) ->
  e = open_be_rec i f e
with open_bb_rec_type_aux : forall e j U i f,
  open_tb_rec j U e = open_bb_rec i f (open_tb_rec j U e) ->
  e = open_bb_rec i f e
with open_bs_rec_type_aux : forall e j U i f,
  open_ts_rec j U e = open_bs_rec i f (open_ts_rec j U e) ->
  e = open_bs_rec i f e.
Proof with eauto using open_cset_rec_capt_aux, open_cvt_rec_capt_aux, open_cbt_rec_capt_aux,
  open_cvt_rec_type_aux, open_cbt_rec_type_aux.
------
  induction e; intros * H; simpl in *; inversion H; f_equal; auto*...
------
  induction e; intros * H; simpl in *; inversion H; f_equal; auto*...
------
  induction e; intros * H; simpl in *; inversion H; f_equal; auto*...
Qed.


Lemma open_be_rec_expr_aux : forall e j u i P,
  open_ee_rec j u e = open_be_rec i P (open_ee_rec j u e) ->
  e = open_be_rec i P e
with open_bb_rec_expr_aux : forall e j u i P ,
  open_eb_rec j u e = open_bb_rec i P (open_eb_rec j u e) ->
  e = open_bb_rec i P e
with open_bs_rec_expr_aux : forall e j u i P ,
  open_es_rec j u e = open_bs_rec i P (open_es_rec j u e) ->
  e = open_bs_rec i P e.
Proof with eauto using open_cset_rec_capt_aux, open_cvt_rec_capt_aux, open_cbt_rec_capt_aux.
------
  induction e; intros * H; simpl in *; inversion H; f_equal; auto*...
------
  induction e; intros * H; simpl in *; inversion H; f_equal; auto*...
------
  induction e; intros * H; simpl in *; inversion H; f_equal; auto*...
Qed.

Lemma open_ce_rec_block_aux : forall e j u C i P,
  i <> j ->
  open_be_rec j u e = open_ce_rec i P C (open_be_rec j u e) ->
  e = open_ce_rec i P C e
with open_cb_rec_block_aux : forall e j u C i P,
  i <> j ->
  open_bb_rec j u e = open_cb_rec i P C (open_bb_rec j u e) ->
  e = open_cb_rec i P C e
with open_cs_rec_block_aux : forall e j u C i P,
  i <> j ->
  open_bs_rec j u e = open_cs_rec i P C (open_bs_rec j u e) ->
  e = open_cs_rec i P C e.
Proof with eauto using open_cset_rec_capt_aux, open_cvt_rec_capt_aux, open_cbt_rec_capt_aux.
------
  induction e; intros * Neq H; simpl in *; inversion H; f_equal; auto*...
------
  induction e; intros * Neq H; simpl in *; inversion H; f_equal; auto*...
  - destruct (j===n)... destruct (i===n)... subst. contradiction.
------
  induction e; intros * Neq H; simpl in *; inversion H; f_equal; auto*...
Qed.

Lemma open_be_rec_capt_aux : forall e j u C i P,
  i <> j ->
  open_ce_rec j u C e = open_be_rec i P (open_ce_rec j u C e) ->
  e = open_be_rec i P e
with open_bb_rec_capt_aux : forall e j u C i P,
  i <> j ->
  open_cb_rec j u C e = open_bb_rec i P (open_cb_rec j u C e) ->
  e = open_bb_rec i P e
with open_bs_rec_capt_aux : forall e j u C i P,
  i <> j ->
  open_cs_rec j u C e = open_bs_rec i P (open_cs_rec j u C e) ->
  e = open_bs_rec i P e.
Proof with eauto using open_cset_rec_capt_aux, open_cvt_rec_capt_aux, open_cbt_rec_capt_aux.
------
  induction e; intros * Neq H; simpl in *; inversion H; f_equal; auto*...
------
  induction e; intros * Neq H; simpl in *; inversion H; f_equal; auto*...
  - destruct (j===n)... destruct (i===n)... subst. contradiction.
------
  induction e; intros * Neq H; simpl in *; inversion H; f_equal; auto*...
Qed.

Lemma open_be_rec_block_aux : forall e j u i P,
  i <> j ->
  open_be_rec j u e = open_be_rec i P (open_be_rec j u e) ->
  e = open_be_rec i P e
with open_bb_rec_block_aux : forall e j u i P,
  i <> j ->
  open_bb_rec j u e = open_bb_rec i P (open_bb_rec j u e) ->
  e = open_bb_rec i P e
with open_bs_rec_block_aux : forall e j u i P,
  i <> j ->
  open_bs_rec j u e = open_bs_rec i P (open_bs_rec j u e) ->
  e = open_bs_rec i P e.
Proof with eauto using open_cset_rec_capt_aux, open_cvt_rec_capt_aux, open_cbt_rec_capt_aux.
------
  induction e; intros * Neq H; simpl in *; inversion H; f_equal; auto*...
------
  induction e; intros * Neq H; simpl in *; inversion H; f_equal; auto*...
  - destruct (j===n)... destruct (i===n)... subst. contradiction.
------
  induction e; intros * Neq H; simpl in *; inversion H; f_equal; auto*...
Qed.

Lemma open_ee_rec_capt_aux : forall e j D u i P ,
  open_ce_rec j D u e = open_ee_rec i P (open_ce_rec j D u e) ->
  e = open_ee_rec i P e
with open_eb_rec_capt_aux : forall e j D u i P ,
  open_cb_rec j D u e = open_eb_rec i P (open_cb_rec j D u e) ->
  e = open_eb_rec i P e
with open_es_rec_capt_aux : forall e j D u i P ,
  open_cs_rec j D u e = open_es_rec i P (open_cs_rec j D u e) ->
  e = open_es_rec i P e.
Proof with eauto using open_cset_rec_capt_aux, open_cvt_rec_capt_aux, open_cbt_rec_capt_aux.
------
  induction e; intros * H; simpl in *; inversion H; f_equal; auto*...
------
  induction e; intros * H; simpl in *; inversion H; f_equal; auto*...
------
  induction e; intros * H; simpl in *; inversion H; f_equal; auto*...
Qed.

Lemma open_ee_rec_block_aux : forall e j u i P ,
  open_be_rec j u e = open_ee_rec i P (open_be_rec j u e) ->
  e = open_ee_rec i P e
with open_eb_rec_block_aux : forall e j u i P ,
  open_bb_rec j u e = open_eb_rec i P (open_bb_rec j u e) ->
  e = open_eb_rec i P e
with open_es_rec_block_aux : forall e j u i P ,
  open_bs_rec j u e = open_es_rec i P (open_bs_rec j u e) ->
  e = open_es_rec i P e.
Proof with eauto using open_cset_rec_capt_aux, open_cvt_rec_capt_aux, open_cbt_rec_capt_aux.
------
  induction e; intros * H; simpl in *; inversion H; f_equal; auto*...
------
  induction e; intros * H; simpl in *; inversion H; f_equal; auto*...
------
  induction e; intros * H; simpl in *; inversion H; f_equal; auto*...
Qed.

Lemma open_ce_rec_expr : forall e U C k,
  expr e ->
  e = open_ce_rec k U C e
with open_cb_rec_block : forall e U C k,
  block e ->
  e = open_cb_rec k U C e
with open_cs_rec_stmt : forall e U C k,
  stmt e ->
  e = open_cs_rec k U C e.
Proof with eauto using open_cvt_rec_vtype, open_cbt_rec_btype.
------
  intros * WF. revert k.
  induction WF; intros k; simpl; f_equal...
------
  intros * WF. revert k.
  induction WF; intros k; simpl; trivial; f_equal; simpl...
  - unfold open_es in *.
    pick fresh x.
    eapply open_cs_rec_expr_aux with (j := 0) (u := x)...
  - unfold open_cs in *.
    pick fresh x.
    eapply open_cs_rec_capt_aux with (j := 0) (v := blk_fvar x) (C := cset_fvar x)...
    unfold disjoint, cset_fvars, cset_fvar; destruct C; fsetdec.
    unfold labels_disjoint, cset_fvars, cset_fvar; destruct C; lsetdec.
  - pick fresh x.
    eapply open_cb_rec_type_aux with (u := x)...
------
  intros * WF. revert k.
  induction WF; intros k; simpl; f_equal...
  - unfold open_es in *.
    pick fresh x.
    eapply open_cs_rec_expr_aux with (j := 0) (u := x)...
  - unfold open_bs in *.
    pick fresh x.
    eapply open_cs_rec_block_aux with (j := 0) (u := x)...
  - unfold open_cs in *.
    pick fresh x.
    eapply open_cs_rec_capt_aux with (j := 0) (v := blk_fvar x) (C := cset_fvar x)...
    unfold disjoint, cset_fvars, cset_fvar; destruct C; fsetdec.
    unfold labels_disjoint, cset_fvars, cset_fvar; destruct C; lsetdec.
  - unfold open_cs in *.
    unfold open_es in *.
    unfold open_bs in *.
    pick fresh v. pick fresh kont.
    eapply open_cs_rec_expr_aux with (j := 0) (u := v); intuition.
    eapply open_cs_rec_block_aux with (j := 0) (u := kont); intuition.
    solve using assumption and notin_solve.
  - unfold open_cs in *.
    unfold open_es in *.
    unfold open_bs in *.
    pick fresh v. pick fresh kont.
    eapply open_cs_rec_expr_aux with (j := 0) (u := v); intuition.
    eapply open_cs_rec_block_aux with (j := 0) (u := kont); intuition.
    solve using assumption and notin_solve.
Qed.

Lemma open_ee_rec_expr : forall e U k,
  expr e ->
  e = open_ee_rec k U e
with open_eb_rec_block : forall e U k,
  block e ->
  e = open_eb_rec k U e
with open_es_rec_stmt : forall e U k,
  stmt e ->
  e = open_es_rec k U e.
Proof with auto*.
------
  intros * WF. revert k.
  induction WF; intros k; simpl; f_equal...
------
  intros * WF. revert k.
  induction WF; intros k; simpl; f_equal...
  - unfold open_es in *.
    pick fresh x.
    eapply open_es_rec_expr_aux with (j := 0) (v := exp_fvar x)...
  - unfold open_cs in *.
    pick fresh x.
    eapply open_es_rec_capt_aux with (j := 0) (D := blk_fvar x)...
  - unfold open_tb in *.
    pick fresh X.
    eapply open_eb_rec_type_aux with (U := X)...
------
  intros * WF. revert k.
  induction WF; intros k; simpl; f_equal...
  - unfold open_es in *.
    pick fresh x.
    eapply open_es_rec_expr_aux with (j := 0) (v := exp_fvar x)...
  - unfold open_bs in *.
    pick fresh x.
    eapply open_es_rec_block_aux with (j := 0) (u := blk_fvar x)...
  - unfold open_cs in *.
    pick fresh x.
    eapply open_es_rec_capt_aux with (j := 0) (D := blk_fvar x)...
  - unfold open_bs in *.
    unfold open_es in *.
    pick fresh v. pick fresh kont.
    eapply open_es_rec_expr_aux with (j := 0) (v := v); intuition.
    eapply open_es_rec_block_aux with (j := 0) (u := kont); intuition.
    solve using assumption and notin_solve.
  - unfold open_bs in *.
    unfold open_es in *.
    pick fresh v. pick fresh kont.
    eapply open_es_rec_expr_aux with (j := 0) (v := v); intuition.
    eapply open_es_rec_block_aux with (j := 0) (u := kont); intuition.
    solve using assumption and notin_solve.
Qed.


Lemma open_be_rec_expr : forall e U k,
  expr e ->
  e = open_be_rec k U e
with open_bb_rec_block : forall e U k,
  block e ->
  e = open_bb_rec k U e
with open_bs_rec_stmt : forall e U k,
  stmt e ->
  e = open_bs_rec k U e.
Proof with eauto using open_cvt_rec_vtype, open_cbt_rec_btype.
------
  intros * WF. revert k.
  induction WF; intros k; simpl; f_equal...
------
  intros e U k WF. revert k.
  induction WF; intros k; simpl; f_equal...
  - unfold open_es in *.
    pick fresh x.
    eapply open_bs_rec_expr_aux with (j := 0) (u := exp_fvar x)...
  - unfold open_es in *. unfold open_cs in *.
    pick fresh x.
    eapply open_bs_rec_capt_aux with (j := 0) (u := blk_fvar x) (C := cset_fvar x)...
  - unfold open_tb in *.
    pick fresh X.
    eapply open_bb_rec_type_aux with (U := X)...
------
  intros * WF. revert k.
  induction WF; intros k; simpl; f_equal...
  - unfold open_es in *.
    pick fresh x.
    eapply open_bs_rec_expr_aux with (j := 0) (u := exp_fvar x)...
  - unfold open_es in *. unfold open_bs in *.
    pick fresh x.
    eapply open_bs_rec_block_aux with (j := 0) (u := blk_fvar x)...
  - unfold open_es in *. unfold open_cs in *.
    pick fresh x.
    eapply open_bs_rec_capt_aux with (j := 0) (u := blk_fvar x) (C := cset_fvar x)...
  - unfold open_bs in *.
    unfold open_es in *.
    pick fresh v. pick fresh kont.
    eapply open_bs_rec_expr_aux with (j := 0) (u := v); intuition.
    eapply open_bs_rec_block_aux with (j := 0) (u := kont); intuition.
    solve using assumption and notin_solve.
  - unfold open_bs in *.
    unfold open_es in *.
    pick fresh v. pick fresh kont.
    eapply open_bs_rec_expr_aux with (j := 0) (u := v); intuition.
    eapply open_bs_rec_block_aux with (j := 0) (u := kont); intuition.
    solve using assumption and notin_solve.
Qed.


(** * Substitution / Opening Lemmas
 **************************************)

Lemma subst_ee_open_ee_rec : forall e1 e2 x u k,
  expr u ->
  subst_ee x u (open_ee_rec k e2 e1) =
    open_ee_rec k (subst_ee x u e2) (subst_ee x u e1)
with subst_eb_open_eb_rec : forall e1 e2 x u k,
  expr u ->
  subst_eb x u (open_eb_rec k e2 e1) =
    open_eb_rec k (subst_ee x u e2) (subst_eb x u e1)
with subst_es_open_es_rec : forall e1 e2 x u k,
  expr u ->
  subst_es x u (open_es_rec k e2 e1) =
    open_es_rec k (subst_ee x u e2) (subst_es x u e1).
Proof with auto*.
------
  intros * WP. revert k.
  induction e1; intros k; simpl; f_equal...
  - Case "exp_bvar".
    destruct (k === n); subst...
  - Case "exp_fvar".
    destruct (a == x); subst... apply open_ee_rec_expr...
------
  intros * WP. revert k.
  induction e1; intros k; simpl; f_equal...
------
  intros * WP. revert k.
  induction e1; intros k; simpl; f_equal...
Qed.

Lemma subst_ee_open_ee : forall e1 e2 x u,
  expr u ->
  subst_ee x u (open_ee e1 e2) =
    open_ee (subst_ee x u e1) (subst_ee x u e2)
with subst_eb_open_eb : forall e1 e2 x u,
  expr u ->
  subst_eb x u (open_eb e1 e2) =
    open_eb (subst_eb x u e1) (subst_ee x u e2)
with subst_es_open_es : forall e1 e2 x u,
  expr u ->
  subst_es x u (open_es e1 e2) =
    open_es (subst_es x u e1) (subst_ee x u e2).
Proof with auto*.
------
  intros.
  unfold open_ee.
  apply subst_ee_open_ee_rec...
------
  intros.
  unfold open_eb.
  apply subst_eb_open_eb_rec...
------
  intros.
  unfold open_es.
  apply subst_es_open_es_rec...
Qed.

Lemma subst_ee_open_ee_var : forall (x y:atom) u e,
  y <> x ->
  expr u ->
  open_ee (subst_ee x u e) y = subst_ee x u (open_ee e y)
with subst_eb_open_eb_var : forall (x y:atom) u e,
  y <> x ->
  expr u ->
  open_eb (subst_eb x u e) y = subst_eb x u (open_eb e y)
with subst_es_open_es_var : forall (x y:atom) u e,
  y <> x ->
  expr u ->
  open_es (subst_es x u e) y = subst_es x u (open_es e y).
Proof with auto*.
------
  intros * Neq Wu.
  unfold open_ee.
  rewrite subst_ee_open_ee_rec...
  simpl.
  destruct (y == x)...
------
  intros * Neq Wu.
  unfold open_eb.
  rewrite subst_eb_open_eb_rec...
  simpl.
  destruct (y == x)...
------
  intros x y u e Neq Wu.
  unfold open_es.
  rewrite subst_es_open_es_rec...
  simpl.
  destruct (y == x)...
Qed.

Lemma subst_ee_open_ce_rec : forall e f C x u k,
  expr u ->
  subst_ee x u (open_ce_rec k f C e) =
    open_ce_rec k (subst_eb x u f) C (subst_ee x u e)
with subst_eb_open_cb_rec : forall e f C x u k,
  expr u ->
  subst_eb x u (open_cb_rec k f C e) =
    open_cb_rec k (subst_eb x u f) C (subst_eb x u e)
with subst_es_open_cs_rec : forall e f C x u k,
  expr u ->
  subst_es x u (open_cs_rec k f C e) =
    open_cs_rec k (subst_eb x u f) C (subst_es x u e).
Proof with auto*.
------
  intros * WP. revert k.
  induction e; intros k; simpl; f_equal...
  - Case "exp_fvar".
    destruct (a == x); subst... apply open_ce_rec_expr...
------
  intros * WP. revert k.
  induction e; intros k; simpl; f_equal...
  - destruct (k === n); subst...
------
  intros * WP. revert k.
  induction e; intros k; simpl; f_equal...
Qed.

Lemma subst_ee_open_ce : forall e f C x u,
  expr u ->
  subst_ee x u (open_ce e f C) = open_ce (subst_ee x u e) (subst_eb x u f) C
with subst_eb_open_cb : forall e f C x u,
  expr u ->
  subst_eb x u (open_cb e f C) = open_cb (subst_eb x u e) (subst_eb x u f) C
with subst_es_open_cs : forall e f C x u,
  expr u ->
  subst_es x u (open_cs e f C) = open_cs (subst_es x u e) (subst_eb x u f) C.
Proof with auto*.
------
  intros.
  unfold open_ce.
  apply subst_ee_open_ce_rec...
------
  intros.
  unfold open_cb.
  apply subst_eb_open_cb_rec...
------
  intros.
  unfold open_cs.
  apply subst_es_open_cs_rec...
Qed.

Lemma subst_ee_open_ce_var : forall e x (y : atom) u,
  expr u ->
  open_ce (subst_ee x u e) y (cset_fvar y) = subst_ee x u (open_ce e y (cset_fvar y))
with subst_eb_open_cb_var : forall e x (y : atom) u,
  expr u ->
  open_cb (subst_eb x u e) y (cset_fvar y) = subst_eb x u (open_cb e y (cset_fvar y))
with subst_es_open_cs_var : forall e x (y : atom) u,
  expr u ->
  open_cs (subst_es x u e) y (cset_fvar y) = subst_es x u (open_cs e y (cset_fvar y)).
Proof with auto*.
------
  intros.
  rewrite subst_ee_open_ce...
------
  intros.
  rewrite subst_eb_open_cb...
------
  intros.
  rewrite subst_es_open_cs...
Qed.

Lemma subst_ee_open_be_rec : forall e f x u k,
  expr u ->
  subst_ee x u (open_be_rec k f e) =
    open_be_rec k (subst_eb x u f) (subst_ee x u e)
with subst_eb_open_bb_rec : forall e f x u k,
  expr u ->
  subst_eb x u (open_bb_rec k f e) =
    open_bb_rec k (subst_eb x u f) (subst_eb x u e)
with subst_es_open_bs_rec : forall e f x u k,
  expr u ->
  subst_es x u (open_bs_rec k f e) =
    open_bs_rec k (subst_eb x u f) (subst_es x u e).
Proof with auto*.
------
  intros * WP. revert k.
  induction e; intros k; simpl; f_equal...
  - Case "exp_fvar".
    destruct (a == x); subst... apply open_be_rec_expr...
------
  intros * WP. revert k.
  induction e; intros k; simpl; f_equal...
  - destruct (k === n); subst...
------
  intros * WP. revert k.
  induction e; intros k; simpl; f_equal...
Qed.

Lemma subst_ee_open_be : forall e f x u,
  expr u ->
  subst_ee x u (open_be e f) = open_be (subst_ee x u e) (subst_eb x u f)
with subst_eb_open_bb : forall e f x u,
  expr u ->
  subst_eb x u (open_bb e f) = open_bb (subst_eb x u e) (subst_eb x u f)
with subst_es_open_bs : forall e f x u,
  expr u ->
  subst_es x u (open_bs e f) = open_bs (subst_es x u e) (subst_eb x u f).
Proof with auto*.
------
  intros.
  unfold open_be.
  apply subst_ee_open_be_rec...
------
  intros.
  unfold open_bb.
  apply subst_eb_open_bb_rec...
------
  intros.
  unfold open_bs.
  apply subst_es_open_bs_rec...
Qed.

Lemma subst_ee_open_be_var : forall e x (y : atom) u,
  expr u ->
  open_be (subst_ee x u e) y = subst_ee x u (open_be e y)
with subst_eb_open_bb_var : forall e x (y : atom) u,
  expr u ->
  open_bb (subst_eb x u e) y = subst_eb x u (open_bb e y)
with subst_es_open_bs_var : forall e x (y : atom) u,
  expr u ->
  open_bs (subst_es x u e) y = subst_es x u (open_bs e y).
Proof with auto*.
------
  intros.
  rewrite subst_ee_open_be...
------
  intros.
  rewrite subst_eb_open_bb...
------
  intros.
  rewrite subst_es_open_bs...
Qed.


Lemma subst_be_open_ee_rec : forall e1 e2 Z P k,
  block P ->
  subst_be Z P (open_ee_rec k e2 e1) =
    open_ee_rec k (subst_be Z P e2) (subst_be Z P e1)
with subst_bb_open_eb_rec : forall e1 e2 Z P k,
  block P ->
  subst_bb Z P (open_eb_rec k e2 e1) =
    open_eb_rec k (subst_be Z P e2) (subst_bb Z P e1)
with subst_bs_open_es_rec : forall e1 e2 Z P k,
  block P ->
  subst_bs Z P (open_es_rec k e2 e1) =
    open_es_rec k (subst_be Z P e2) (subst_bs Z P e1).
Proof with auto*.
------
  induction e1; intros; simpl; f_equal...
  Case "exp_bvar".
    destruct (k === n)...
------
  induction e1; intros; try solve [simpl; f_equal; eauto].
  - simpl; f_equal. destruct (a == Z)... apply open_eb_rec_block...
------
  induction e1; intros; simpl; f_equal...
Qed.

Lemma subst_be_open_ee : forall e1 e2 Z P,
  block P ->
  subst_be Z P (open_ee e1 e2) = open_ee (subst_be Z P e1) (subst_be Z P e2)
with subst_bb_open_eb : forall e1 e2 Z P,
  block P ->
  subst_bb Z P (open_eb e1 e2) = open_eb (subst_bb Z P e1) (subst_be Z P e2)
with subst_bs_open_es : forall e1 e2 Z P,
  block P ->
  subst_bs Z P (open_es e1 e2) = open_es (subst_bs Z P e1) (subst_be Z P e2).
Proof with auto*.
------
  intros.
  unfold open_ee.
  apply subst_be_open_ee_rec...
------
  intros.
  unfold open_eb.
  apply subst_bb_open_eb_rec...
------
  intros.
  unfold open_es.
  apply subst_bs_open_es_rec...
Qed.

Lemma subst_be_open_ee_var : forall Z (x:atom) P e,
  block P ->
  open_ee (subst_be Z P e) x = subst_be Z P (open_ee e x)
with subst_bb_open_eb_var : forall Z (x:atom) P e,
  block P ->
  open_eb (subst_bb Z P e) x = subst_bb Z P (open_eb e x)
with subst_bs_open_es_var : forall Z (x:atom) P e,
  block P ->
  open_es (subst_bs Z P e) x = subst_bs Z P (open_es e x).
Proof with auto*.
------
  intros.
  rewrite subst_be_open_ee...
------
  intros.
  rewrite subst_bb_open_eb...
------
  intros.
  rewrite subst_bs_open_es...
Qed.

Lemma subst_be_open_be_rec : forall e1 e2 Z P k,
  block P ->
  subst_be Z P (open_be_rec k e2 e1) =
    open_be_rec k (subst_bb Z P e2) (subst_be Z P e1)
with subst_bb_open_bb_rec : forall e1 e2 Z P k,
  block P ->
  subst_bb Z P (open_bb_rec k e2 e1) =
    open_bb_rec k (subst_bb Z P e2) (subst_bb Z P e1)
with subst_bs_open_bs_rec : forall e1 e2 Z P k,
  block P ->
  subst_bs Z P (open_bs_rec k e2 e1) =
    open_bs_rec k (subst_bb Z P e2) (subst_bs Z P e1).
Proof with auto*.
------
  induction e1; intros; simpl; f_equal...
------
  induction e1; intros; try solve [simpl; f_equal; eauto].
  - simpl; f_equal. destruct (k === n)...
  - simpl; f_equal. destruct (a == Z); subst...
    apply open_bb_rec_block...
------
  induction e1; intros; simpl; f_equal...
Qed.

Lemma subst_be_open_be : forall e1 e2 Z P,
  block P ->
  subst_be Z P (open_be e1 e2) = open_be (subst_be Z P e1) (subst_bb Z P e2)
with subst_bb_open_bb : forall e1 e2 Z P,
  block P ->
  subst_bb Z P (open_bb e1 e2) = open_bb (subst_bb Z P e1) (subst_bb Z P e2)
with subst_bs_open_bs : forall e1 e2 Z P,
  block P ->
  subst_bs Z P (open_bs e1 e2) = open_bs (subst_bs Z P e1) (subst_bb Z P e2).
Proof with auto*.
------
  intros.
  unfold open_be.
  apply subst_be_open_be_rec...
------
  intros.
  unfold open_bb.
  apply subst_bb_open_bb_rec...
------
  intros.
  unfold open_bs.
  apply subst_bs_open_bs_rec...
Qed.

Lemma subst_be_open_be_var : forall Z (x:atom) P e,
  Z <> x ->
  block P ->
  open_be (subst_be Z P e) x = subst_be Z P (open_be e x)
with subst_bb_open_bb_var : forall Z (x:atom) P e,
  Z <> x ->
  block P ->
  open_bb (subst_bb Z P e) x = subst_bb Z P (open_bb e x)
with subst_bs_open_bs_var : forall Z (x:atom) P e,
  Z <> x ->
  block P ->
  open_bs (subst_bs Z P e) x = subst_bs Z P (open_bs e x).
Proof with auto*.
------
  intros.
  rewrite subst_be_open_be...
  induction (subst_be Z P e);
    simpl; destruct (x == Z)...
------
  intros.
  rewrite subst_bb_open_bb...
  induction (subst_bb Z P e);
    simpl; destruct (x == Z)...
------
  intros.
  rewrite subst_bs_open_bs...
  induction (subst_bs Z P e);
    simpl; destruct (x == Z)...
Qed.

Lemma subst_ce_open_ee_rec : forall e1 e2 Z P C k,
  block P ->
  subst_ce Z P C (open_ee_rec k e2 e1) =
    open_ee_rec k (subst_ce Z P C e2) (subst_ce Z P C e1)
with subst_cb_open_eb_rec : forall e1 e2 Z P C k,
  block P ->
  subst_cb Z P C (open_eb_rec k e2 e1) =
    open_eb_rec k (subst_ce Z P C e2) (subst_cb Z P C e1)
with subst_cs_open_es_rec : forall e1 e2 Z P C k,
  block P ->
  subst_cs Z P C (open_es_rec k e2 e1) =
    open_es_rec k (subst_ce Z P C e2) (subst_cs Z P C e1).
Proof with auto*.
------
  induction e1; intros; simpl; f_equal...
  Case "exp_bvar".
    destruct (k === n)...
------
  induction e1; intros; try solve [simpl; f_equal; eauto].
  - simpl; f_equal. destruct (a == Z)... apply open_eb_rec_block...
------
  induction e1; intros; simpl; f_equal...
Qed.

Lemma subst_ce_open_ee : forall e1 e2 Z P C,
  block P ->
  subst_ce Z P C (open_ee e1 e2) = open_ee (subst_ce Z P C e1) (subst_ce Z P C e2)
with subst_cb_open_eb : forall e1 e2 Z P C,
  block P ->
  subst_cb Z P C (open_eb e1 e2) = open_eb (subst_cb Z P C e1) (subst_ce Z P C e2)
with subst_cs_open_es : forall e1 e2 Z P C,
  block P ->
  subst_cs Z P C (open_es e1 e2) = open_es (subst_cs Z P C e1) (subst_ce Z P C e2).
Proof with auto*.
------
  intros.
  unfold open_ee.
  apply subst_ce_open_ee_rec...
------
  intros.
  unfold open_eb.
  apply subst_cb_open_eb_rec...
------
  intros.
  unfold open_es.
  apply subst_cs_open_es_rec...
Qed.

Lemma subst_ce_open_ee_var : forall Z (x:atom) P C e,
  block P ->
  open_ee (subst_ce Z P C e) x = subst_ce Z P C (open_ee e x)
with subst_cb_open_eb_var : forall Z (x:atom) P C e,
  block P ->
  open_eb (subst_cb Z P C e) x = subst_cb Z P C (open_eb e x)
with subst_cs_open_es_var : forall Z (x:atom) P C e,
  block P ->
  open_es (subst_cs Z P C e) x = subst_cs Z P C (open_es e x).
Proof with auto*.
------
  intros.
  rewrite subst_ce_open_ee...
------
  intros.
  rewrite subst_cb_open_eb...
------
  intros.
  rewrite subst_cs_open_es...
Qed.


Lemma subst_be_open_ce_rec : forall e1 e2 Z P C k,
  block P ->
  subst_be Z P (open_ce_rec k e2 C e1) =
    open_ce_rec k (subst_bb Z P e2) C (subst_be Z P e1)
with subst_bb_open_cb_rec : forall e1 e2 Z P C k,
  block P ->
  subst_bb Z P (open_cb_rec k e2 C e1) =
    open_cb_rec k (subst_bb Z P e2) C (subst_bb Z P e1)
with subst_bs_open_cs_rec : forall e1 e2 Z P C k,
  block P ->
  subst_bs Z P (open_cs_rec k e2 C e1) =
    open_cs_rec k (subst_bb Z P e2) C (subst_bs Z P e1).
Proof with auto*.
------
  induction e1; intros; simpl; f_equal...
------
  induction e1; intros; try solve [simpl; f_equal; eauto].
  - simpl; f_equal. destruct (k === n)...
  - simpl; f_equal. destruct (a == Z); subst...
    apply open_cb_rec_block...
------
  induction e1; intros; simpl; f_equal...
Qed.


Lemma subst_be_open_ce : forall e1 e2 Z P C,
  block P ->
  subst_be Z P (open_ce e1 e2 C) = open_ce (subst_be Z P e1) (subst_bb Z P e2) C
with subst_bb_open_cb : forall e1 e2 Z P C,
  block P ->
  subst_bb Z P (open_cb e1 e2 C) = open_cb (subst_bb Z P e1) (subst_bb Z P e2) C
with subst_bs_open_cs : forall e1 e2 Z P C,
  block P ->
  subst_bs Z P (open_cs e1 e2 C) = open_cs (subst_bs Z P e1) (subst_bb Z P e2) C.
Proof with auto*.
------
  intros.
  unfold open_ce.
  apply subst_be_open_ce_rec...
------
  intros.
  unfold open_cb.
  apply subst_bb_open_cb_rec...
------
  intros.
  unfold open_cs.
  apply subst_bs_open_cs_rec...
Qed.

Lemma subst_be_open_ce_var : forall Z (x:atom) P e,
  block P ->
  x <> Z ->
  open_ce (subst_be Z P e) x (cset_fvar x) = subst_be Z P (open_ce e x (cset_fvar x))
with subst_bb_open_cb_var : forall Z (x:atom) P e,
  block P ->
  x <> Z ->
  open_cb (subst_bb Z P e) x (cset_fvar x) = subst_bb Z P (open_cb e x (cset_fvar x))
with subst_bs_open_cs_var : forall Z (x:atom) P e,
  block P ->
  x <> Z ->
  open_cs (subst_bs Z P e) x (cset_fvar x) = subst_bs Z P (open_cs e x (cset_fvar x)).
Proof with auto*.
------
  intros.
  rewrite subst_be_open_ce...
  unfold subst_bb; destruct (x == Z)...
------
  intros.
  rewrite subst_bb_open_cb...
  unfold subst_bb; destruct (x == Z)...
------
  intros.
  rewrite subst_bs_open_cs...
  unfold subst_bb; destruct (x == Z)...
Qed.


Lemma subst_ce_open_be_rec : forall e1 e2 Z P C k,
  block P ->
  subst_ce Z P C (open_be_rec k e2 e1) =
    open_be_rec k (subst_cb Z P C e2) (subst_ce Z P C e1)
with subst_cb_open_bb_rec : forall e1 e2 Z P C k,
  block P ->
  subst_cb Z P C (open_bb_rec k e2 e1) =
    open_bb_rec k (subst_cb Z P C e2) (subst_cb Z P C e1)
with subst_cs_open_bs_rec : forall e1 e2 Z P C k,
  block P ->
  subst_cs Z P C (open_bs_rec k e2 e1) =
    open_bs_rec k (subst_cb Z P C e2) (subst_cs Z P C e1).
Proof with auto*.
------
  induction e1; intros; simpl; f_equal...
------
  induction e1; intros; try solve [simpl; f_equal; eauto].
  - simpl; f_equal. destruct (k === n)...
  - simpl; f_equal. destruct (a == Z); subst...
    apply open_bb_rec_block...
------
  induction e1; intros; simpl; f_equal...
Qed.


Lemma subst_ce_open_be : forall e1 e2 Z P C,
  block P ->
  subst_ce Z P C (open_be e1 e2) = open_be (subst_ce Z P C e1) (subst_cb Z P C e2)
with subst_cb_open_bb : forall e1 e2 Z P C,
  block P ->
  subst_cb Z P C (open_bb e1 e2) = open_bb (subst_cb Z P C e1) (subst_cb Z P C e2)
with subst_cs_open_bs : forall e1 e2 Z P C,
  block P ->
  subst_cs Z P C (open_bs e1 e2) = open_bs (subst_cs Z P C e1) (subst_cb Z P C e2).
Proof with auto*.
------
  intros.
  unfold open_be.
  apply subst_ce_open_be_rec...
------
  intros.
  unfold open_bb.
  apply subst_cb_open_bb_rec...
------
  intros.
  unfold open_bs.
  apply subst_cs_open_bs_rec...
Qed.

Lemma subst_ce_open_be_var : forall Z (x:atom) P C e,
  block P ->
  x <> Z ->
  open_be (subst_ce Z P C e) x  = subst_ce Z P C (open_be e x)
with subst_cb_open_bb_var : forall Z (x:atom) P C e,
  block P ->
  x <> Z ->
  open_bb (subst_cb Z P C e) x = subst_cb Z P C (open_bb e x)
with subst_cs_open_bs_var : forall Z (x:atom) P C e,
  block P ->
  x <> Z ->
  open_bs (subst_cs Z P C e) x = subst_cs Z P C (open_bs e x).
Proof with auto*.
------
  intros.
  rewrite subst_ce_open_be...
  unfold subst_cb; destruct (x == Z)...
------
  intros.
  rewrite subst_cb_open_bb...
  unfold subst_cb; destruct (x == Z)...
------
  intros.
  rewrite subst_cs_open_bs...
  unfold subst_cb; destruct (x == Z)...
Qed.

Lemma subst_cvt_open_cvt_rec : forall T C1 C2 X k,
  capt C1 ->
  subst_cvt X C1 (open_cvt_rec k C2 T) =
    open_cvt_rec k (subst_cset X C1 C2) (subst_cvt X C1 T)
with subst_cbt_open_cbt_rec : forall T C1 C2 X k,
  capt C1 ->
  subst_cbt X C1 (open_cbt_rec k C2 T) =
    open_cbt_rec k (subst_cset X C1 C2) (subst_cbt X C1 T).
Proof with eauto using subst_cset_open_cset_rec.
------
  intros T1 T2 X P k WP. revert k.
  induction T1; intros k; simpl; f_equal...
------
  intros T1 T2 X P k WP. revert k.
  induction T1; intros k; simpl; f_equal...
Qed.

Lemma subst_cvt_open_cvt : forall T C1 C2 X,
  capt C1 ->
  subst_cvt X C1 (open_cvt T C2) =
    open_cvt (subst_cvt X C1 T) (subst_cset X C1 C2)
with subst_cbt_open_cbt : forall T C1 C2 X,
  capt C1 ->
  subst_cbt X C1 (open_cbt T C2) =
    open_cbt (subst_cbt X C1 T) (subst_cset X C1 C2).
Proof with eauto using subst_cset_open_cset_rec.
------
  intros.
  unfold open_cvt.
  apply subst_cvt_open_cvt_rec...
------
  intros.
  unfold open_cbt.
  apply subst_cbt_open_cbt_rec...
Qed.

Lemma subst_cvt_open_cvt_var : forall T C1 X (x:atom),
  x <> X ->
  capt C1 ->
  subst_cvt X C1 (open_cvt T (cset_fvar x)) =
    open_cvt (subst_cvt X C1 T) (cset_fvar x)
with subst_cbt_open_cbt_var : forall T C1 X (x:atom),
  x <> X ->
  capt C1 ->
  subst_cbt X C1 (open_cbt T (cset_fvar x)) =
    open_cbt (subst_cbt X C1 T) (cset_fvar x).
Proof with auto*.
------
  intros.
  rewrite subst_cvt_open_cvt...
  rewrite subst_cset_fresh_id...
------
  intros.
  rewrite subst_cbt_open_cbt...
  rewrite subst_cset_fresh_id...
Qed.

Lemma subst_ce_open_ce_rec : forall e1 e2 Z P C D k,
  block P ->
  capt D ->
  subst_ce Z P D (open_ce_rec k e2 C e1) =
    open_ce_rec k (subst_cb Z P D e2) (subst_cset Z D C) (subst_ce Z P D e1)
with subst_cb_open_cb_rec : forall e1 e2 Z P C D k,
  block P ->
  capt D ->
  subst_cb Z P D (open_cb_rec k e2 C e1) =
    open_cb_rec k (subst_cb Z P D e2) (subst_cset Z D C) (subst_cb Z P D e1)
with subst_cs_open_cs_rec : forall e1 e2 Z P C D k,
  block P ->
  capt D ->
  subst_cs Z P D (open_cs_rec k e2 C e1) =
    open_cs_rec k (subst_cb Z P D e2) (subst_cset Z D C) (subst_cs Z P D e1).
Proof with eauto using subst_cset_open_cset_rec, subst_cvt_open_cvt_rec, subst_cbt_open_cbt_rec.
------
  induction e1; intros; simpl; f_equal...
------
  induction e1; intros; simpl; f_equal...
  - simpl; f_equal. destruct (k === n)...
  - simpl; f_equal. destruct (a == Z); subst...
    apply open_cb_rec_block...
------
  induction e1; intros; simpl; f_equal...
Qed.

Lemma subst_ce_open_ce : forall e1 e2 Z P C D,
  block P ->
  capt D ->
  subst_ce Z P D (open_ce e1 e2 C) = open_ce (subst_ce Z P D e1) (subst_cb Z P D e2) (subst_cset Z D C)
with subst_cb_open_cb : forall e1 e2 Z P C D,
  block P ->
  capt D ->
  subst_cb Z P D (open_cb e1 e2 C) = open_cb (subst_cb Z P D e1) (subst_cb Z P D e2) (subst_cset Z D C)
with subst_cs_open_cs : forall e1 e2 Z P C D,
  block P ->
  capt D ->
  subst_cs Z P D (open_cs e1 e2 C) = open_cs (subst_cs Z P D e1) (subst_cb Z P D e2) (subst_cset Z D C).
Proof with auto*.
------
  intros. unfold open_ce. apply subst_ce_open_ce_rec...
------
  intros. unfold open_cb. apply subst_cb_open_cb_rec...
------
  intros. unfold open_cs. apply subst_cs_open_cs_rec...
Qed.

Lemma subst_ce_open_ce_var : forall Z (x:atom) P e D,
  block P ->
  capt D ->
  x <> Z ->
  open_ce (subst_ce Z P D e) x (cset_fvar x) = subst_ce Z P D (open_ce e x (cset_fvar x))
with subst_cb_open_cb_var : forall Z (x:atom) P e D,
  block P ->
  capt D ->
  x <> Z ->
  open_cb (subst_cb Z P D e) x (cset_fvar x) = subst_cb Z P D (open_cb e x (cset_fvar x))
with subst_cs_open_cs_var : forall Z (x:atom) P e D,
  block P ->
  capt D ->
  x <> Z ->
  open_cs (subst_cs Z P D e) x (cset_fvar x) = subst_cs Z P D (open_cs e x (cset_fvar x)).
Proof with auto*.
------
  intros.
  rewrite subst_ce_open_ce...
  unfold subst_cb, subst_cset, cset_references_fvar_dec, cset_fvar, cset_remove_fvar, cset_union.
  destruct (x == Z)...
  unfold cset_fvars.
  destruct D; destruct_set_mem Z (singleton x)... exfalso. fsetdec.
------
  intros.
  rewrite subst_cb_open_cb...
  unfold subst_cb, subst_cset, cset_references_fvar_dec, cset_fvar, cset_remove_fvar, cset_union.
  destruct (x == Z)...
  unfold cset_fvars.
  destruct D; destruct_set_mem Z (singleton x)... exfalso. fsetdec.
------
  intros.
  rewrite subst_cs_open_cs...
  unfold subst_cb, subst_cset, cset_references_fvar_dec, cset_fvar, cset_remove_fvar, cset_union.
  destruct (x == Z)...
  unfold cset_fvars.
  destruct D; destruct_set_mem Z (singleton x)... exfalso. fsetdec.
Qed.

Lemma subst_te_open_ee_rec : forall e1 e2 X U k,
  subst_te X U (open_ee_rec k e2 e1) =
    open_ee_rec k (subst_te X U e2) (subst_te X U e1)
with subst_tb_open_eb_rec : forall e1 e2 X U k,
  subst_tb X U (open_eb_rec k e2 e1) =
    open_eb_rec k (subst_te X U e2) (subst_tb X U e1)
with subst_ts_open_es_rec : forall e1 e2 X U k,
  subst_ts X U (open_es_rec k e2 e1) =
    open_es_rec k (subst_te X U e2) (subst_ts X U e1).
Proof with auto*.
------
  intros *. revert k.
  induction e1; intros k; simpl; f_equal...
  - Case "exp_bvar".
    destruct (k === n); subst...
------
  intros *. revert k.
  induction e1; intros k; simpl; f_equal...
------
  intros *. revert k.
  induction e1; intros k; simpl; f_equal...
Qed.

Lemma subst_te_open_ee : forall e1 e2 X U,
  subst_te X U (open_ee e1 e2) =
    open_ee (subst_te X U e1) (subst_te X U e2)
with subst_tb_open_eb : forall e1 e2 X U,
  subst_tb X U (open_eb e1 e2) =
    open_eb (subst_tb X U e1) (subst_te X U e2)
with subst_ts_open_es : forall e1 e2 X U,
  subst_ts X U (open_es e1 e2) =
    open_es (subst_ts X U e1) (subst_te X U e2).
Proof with auto*.
------
  intros.
  unfold open_ee.
  apply subst_te_open_ee_rec...
------
  intros.
  unfold open_eb.
  apply subst_tb_open_eb_rec...
------
  intros.
  unfold open_es.
  apply subst_ts_open_es_rec...
Qed.

Lemma subst_te_open_be_rec : forall e1 e2 X U k,
  subst_te X U (open_be_rec k e2 e1) =
    open_be_rec k (subst_tb X U e2) (subst_te X U e1)
with subst_tb_open_bb_rec : forall e1 e2 X U k,
  subst_tb X U (open_bb_rec k e2 e1) =
    open_bb_rec k (subst_tb X U e2) (subst_tb X U e1)
with subst_ts_open_bs_rec : forall e1 e2 X U k,
  subst_ts X U (open_bs_rec k e2 e1) =
    open_bs_rec k (subst_tb X U e2) (subst_ts X U e1).
Proof with auto*.
------
  intros *. revert k.
  induction e1; intros k; simpl; f_equal...
------
  intros *. revert k.
  induction e1; intros k; simpl; f_equal...
  destruct (k === n)...
------
  intros *. revert k.
  induction e1; intros k; simpl; f_equal...
Qed.


Lemma subst_te_open_be : forall e1 e2 X U,
  subst_te X U (open_be e1 e2) =
    open_be (subst_te X U e1) (subst_tb X U e2)
with subst_tb_open_bb : forall e1 e2 X U,
  subst_tb X U (open_bb e1 e2) =
    open_bb (subst_tb X U e1) (subst_tb X U e2)
with subst_ts_open_bs : forall e1 e2 X U,
  subst_ts X U (open_bs e1 e2) =
    open_bs (subst_ts X U e1) (subst_tb X U e2).
Proof with auto*.
------
  intros.
  unfold open_be.
  apply subst_te_open_be_rec...
------
  intros.
  unfold open_tb.
  apply subst_tb_open_bb_rec...
------
  intros.
  unfold open_ts.
  apply subst_ts_open_bs_rec...
Qed.

Lemma subst_tvt_intro_rec : forall X T U k,
  X `notin` fv_tvt T ->
  open_tvt_rec k U T = subst_tvt X U (open_tvt_rec k X T)
with subst_tbt_intro_rec : forall X T U k,
  X `notin` fv_tbt T ->
  open_tbt_rec k U T = subst_tbt X U (open_tbt_rec k X T).
Proof with auto*; try notin_solve.
------
  induction T; intros * Fr; simpl in *; f_equal...
  - Case "typ_fvar".
    destruct (a == X)...
  - Case "typ_bvar".
    destruct (k === n); simpl...
    destruct (X == X)...
------
  induction T; intros * Fr; simpl in *; f_equal...
Qed.

Lemma subst_te_intro_rec : forall X e T k,
  X `notin` fv_te e ->
  open_te_rec k T e = subst_te X T (open_te_rec k X e)
with subst_ts_intro_rec : forall X e T k,
  X `notin` fv_ts e ->
  open_ts_rec k T e = subst_ts X T (open_ts_rec k X e)
with subst_tb_intro_rec : forall X e T k,
  X `notin` fv_tb e ->
  open_tb_rec k T e = subst_tb X T (open_tb_rec k X e).
Proof with auto using subst_tvt_intro_rec, subst_tbt_intro_rec.
------
  induction e; intros u k Fr; simpl in *; f_equal...
------
  induction e; intros u k Fr; simpl in *; f_equal...
------
  induction e; intros u k Fr; simpl in *; f_equal...
Qed.

Lemma subst_be_fresh : forall a s1 s2,
  a `notin` fv_be s2 ->
  subst_be a s1 s2 = s2
with subst_bs_fresh : forall a s1 s2,
  a `notin` fv_bs s2 ->
  subst_bs a s1 s2 = s2
with subst_bb_fresh : forall a s1 s2,
  a `notin` fv_bb s2 ->
  subst_bb a s1 s2 = s2.
Proof with eauto.
  all : intros * Fr; induction s2; simpl in *; f_equal...
  destruct (a0 == a); notin_solve.
Qed.

Lemma subst_ee_fresh : forall a s1 s2,
  a `notin` fv_ee s2 ->
  subst_ee a s1 s2 = s2
with subst_es_fresh : forall a s1 s2,
  a `notin` fv_es s2 ->
  subst_es a s1 s2 = s2
with subst_eb_fresh : forall a s1 s2,
  a `notin` fv_eb s2 ->
  subst_eb a s1 s2 = s2.
Proof with eauto.
  all : intros * Fr; induction s2; simpl in *; f_equal...
  destruct (a0 == a); notin_solve.
Qed.

Lemma subst_ee_through_subst_be : forall a1 a2 s1 s2 s,
  a1 `notin` (fv_eb s1 `union` fv_bb s1 `union` fv_be s2 `union` singleton a2) ->
  a2 `notin` (fv_eb s1 `union` fv_bb s1 `union` fv_be s2 `union` singleton a1) ->
  subst_be a1 s1 (subst_ee a2 s2 s) = subst_ee a2 s2 (subst_be a1 s1 s)
with subst_es_through_subst_bs : forall a1 a2 s1 s2 s,
  a1 `notin` (fv_eb s1 `union` fv_bb s1 `union` fv_be s2 `union` singleton a2) ->
  a2 `notin` (fv_eb s1 `union` fv_bb s1 `union` fv_be s2 `union` singleton a1) ->
  subst_bs a1 s1 (subst_es a2 s2 s) = subst_es a2 s2 (subst_bs a1 s1 s)
with subst_eb_through_subst_bb : forall a1 a2 s1 s2 s,
  a1 `notin` (fv_eb s1 `union` fv_bb s1 `union` fv_be s2 `union` singleton a2) ->
  a2 `notin` (fv_eb s1 `union` fv_bb s1 `union` fv_be s2 `union` singleton a1) ->
  subst_bb a1 s1 (subst_eb a2 s2 s) = subst_eb a2 s2 (subst_bb a1 s1 s).
Proof with eauto.
------
  intros * Fra1 Fra2.
  induction s; simpl in *; f_equal...
  * destruct (a == a2)...
    apply subst_be_fresh...
------
  intros * Fra1 Fra2;
  induction s; simpl in *; f_equal...
------
  intros * Fra1 Fra2.
  induction s; simpl in *; f_equal...
  * destruct (a == a1)...
    (* a2 isn't in s1. *)
    symmetry.
    apply subst_eb_fresh...
Qed.


Lemma subst_tvt_intro : forall X T2 U,
  X `notin` fv_tvt T2 ->
  open_tvt T2 U = subst_tvt X U (open_tvt T2 X)
with subst_tbt_intro : forall X T2 U,
  X `notin` fv_tbt T2 ->
  open_tbt T2 U = subst_tbt X U (open_tbt T2 X).
Proof with auto*.
------
  intros.
  unfold open_tvt.
  apply subst_tvt_intro_rec...
------
  intros.
  unfold open_tbt.
  apply subst_tbt_intro_rec...
Qed.

Lemma open_tvt_rec_type_aux : forall T j V i U,
  i <> j ->
  open_tvt_rec j V T = open_tvt_rec i U (open_tvt_rec j V T) ->
  T = open_tvt_rec i U T
with open_tbt_rec_type_aux : forall T j V i U,
  i <> j ->
  open_tbt_rec j V T = open_tbt_rec i U (open_tbt_rec j V T) ->
  T = open_tbt_rec i U T.
Proof with eauto*.
------
  induction T; intros j V i U Neq H; simpl in *; inversion H; f_equal...
  Case "typ_bvar".
    destruct (j === n)... destruct (i === n)...
------
  induction T; intros j V i U Neq H; simpl in *; inversion H; f_equal...
Qed.

Lemma open_tvt_rec_capt_aux : forall T j C i U,
  open_cvt_rec j C T = open_tvt_rec i U (open_cvt_rec j C T) ->
  T = open_tvt_rec i U T
with open_tbt_rec_capt_aux : forall T j C i U,
  open_cbt_rec j C T = open_tbt_rec i U (open_cbt_rec j C T) ->
  T = open_tbt_rec i U T.
Proof with eauto*.
------
  induction T; intros * H; simpl in *; inversion H; f_equal...
------
  induction T; intros * H; simpl in *; inversion H; f_equal...
Qed.


Lemma open_tvt_rec_vtype : forall T U k,
  vtype T ->
  T = open_tvt_rec k U T
with open_tbt_rec_btype : forall T U k,
  btype T ->
  T = open_tbt_rec k U T.
Proof with auto*.
------
  intros T U k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
------
  intros T U k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
  - Case "typ_tabs".
    unfold open_cvt in *.
    pick fresh X.
    apply (open_tvt_rec_capt_aux T 0 (cset_fvar X))...
  - Case "typ_all".
    unfold open_tbt in *.
    pick fresh X.
    apply (open_tbt_rec_type_aux T 0 (typ_fvar X))...
Qed.

Lemma subst_tvt_open_tvt_rec : forall T1 T2 X P k,
  vtype P ->
  subst_tvt X P (open_tvt_rec k T2 T1) =
    open_tvt_rec k (subst_tvt X P T2) (subst_tvt X P T1)
with subst_tbt_open_tbt_rec : forall T1 T2 X P k,
  vtype P ->
  subst_tbt X P (open_tbt_rec k T2 T1) =
    open_tbt_rec k (subst_tvt X P T2) (subst_tbt X P T1).
Proof with auto*.
------
  intros * WP. revert k.
  induction T1; intros k; simpl; f_equal...
  - Case "typ_fvar".
    destruct (a == X); subst... apply open_tvt_rec_vtype...
  - Case "typ_bvar".
    destruct (k === n); subst...
------
  intros * WP. revert k.
  induction T1; intros k; simpl; f_equal...
Qed.

Lemma subst_tvt_open_tvt_var : forall (X Y:atom) P T,
  Y <> X ->
  vtype P ->
  open_tvt (subst_tvt X P T) Y = subst_tvt X P (open_tvt T Y)
with subst_tbt_open_tbt_var : forall (X Y:atom) P T,
  Y <> X ->
  vtype P ->
  open_tbt (subst_tbt X P T) Y = subst_tbt X P (open_tbt T Y).
Proof with auto*.
-------
  intros X Y P T Neq Wu.
  unfold open_tvt.
  rewrite subst_tvt_open_tvt_rec...
  simpl.
  destruct (Y == X)...
-------
  intros X Y P T Neq Wu.
  unfold open_tbt.
  rewrite subst_tbt_open_tbt_rec...
  simpl.
  destruct (Y == X)...
Qed.


Lemma subst_tvt_open_cvt_rec : forall T1 C X P k,
  vtype P ->
  subst_tvt X P (open_cvt_rec k C T1) =
    open_cvt_rec k C (subst_tvt X P T1)
with subst_tbt_open_cbt_rec : forall T1 C X P k,
  vtype P ->
  subst_tbt X P (open_cbt_rec k C T1) =
    open_cbt_rec k C (subst_tbt X P T1).
Proof with auto*.
------
  intros * WP. revert k.
  induction T1; intros k; simpl; f_equal...
  - Case "typ_fvar".
    destruct (a == X); subst... apply open_cvt_rec_vtype...
------
  intros * WP. revert k.
  induction T1; intros k; simpl; f_equal...
Qed.

Lemma subst_tvt_open_cvt_var : forall (X Y:atom) P T,
  vtype P ->
  open_cvt (subst_tvt X P T) (cset_fvar Y) =
    subst_tvt X P (open_cvt T (cset_fvar Y))
with subst_tbt_open_cbt_var : forall (X Y:atom) P T,
  vtype P ->
  open_cbt (subst_tbt X P T) (cset_fvar Y) =
    subst_tbt X P (open_cbt T (cset_fvar Y)).
Proof with eauto.
-------
  intros * Wu.
  unfold open_cvt.
  rewrite subst_tvt_open_cvt_rec...
-------
  intros * Wu.
  unfold open_cbt.
  rewrite subst_tbt_open_cbt_rec...
Qed.

Lemma subst_cvt_fresh : forall X C T,
  X `notin` fv_cvt T ->
  T = subst_cvt X C T
with subst_cbt_fresh : forall X C T,
  X `notin` fv_cbt T ->
  T = subst_cbt X C T.
Proof with eauto using subst_cset_fresh.
------
  intros * Fr.
  induction T; simpl in *; f_equal...
------
  intros * Fr.
  induction T; simpl in *; f_equal...
Qed.

Lemma subst_cvt_open_tvt_rec : forall T C1 U X k,
  capt C1 ->
  subst_cvt X C1 (open_tvt_rec k U T) =
    open_tvt_rec k (subst_cvt X C1 U)  (subst_cvt X C1 T)
with subst_cbt_open_tbt_rec : forall T C1 U X k,
  capt C1 ->
  subst_cbt X C1 (open_tbt_rec k U T) =
    open_tbt_rec k (subst_cvt X C1 U) (subst_cbt X C1 T).
Proof with eauto using subst_cset_open_cset_rec, subst_cvt_fresh, subst_cbt_fresh.
------
  intros *. revert k.
  induction T; intros k Capt; simpl; f_equal...
  destruct (k === n)...
------
  intros *. revert k.
  induction T; intros k Capt; simpl; f_equal...
Qed.

Lemma subst_cvt_open_tvt : forall T C1 U X,
  capt C1 ->
  subst_cvt X C1 (open_tvt T U) =
    open_tvt (subst_cvt X C1 T) (subst_cvt X C1 U)
with subst_cbt_open_tbt : forall T C1 U X,
  capt C1 ->
  subst_cbt X C1 (open_tbt T U) =
    open_tbt (subst_cbt X C1 T) (subst_cvt X C1 U).
Proof with eauto using subst_cset_open_cset_rec.
------
  intros.
  unfold open_tvt.
  apply subst_cvt_open_tvt_rec...
------
  intros.
  unfold open_tbt.
  apply subst_cbt_open_tbt_rec...
Qed.

Lemma subst_cvt_open_tvt_var : forall T C1 X Y,
  Y <> X ->
  capt C1 ->
  subst_cvt X C1 (open_tvt T Y) =
    open_tvt (subst_cvt X C1 T) Y
with subst_cbt_open_tbt_var : forall T C1 X Y,
  Y <> X ->
  capt C1 ->
  subst_cbt X C1 (open_tbt T Y) =
    open_tbt (subst_cbt X C1 T) Y.
Proof with auto*.
------
  intros.
  rewrite subst_cvt_open_tvt...
------
  intros.
  rewrite subst_cbt_open_tbt...
Qed.

Lemma subst_tvt_open_cvt : forall T1 C X P,
  vtype P ->
  subst_tvt X P (open_cvt T1 C) =
    open_cvt (subst_tvt X P T1) C
with subst_tbt_open_cbt : forall T1 C X P,
  vtype P ->
  subst_tbt X P (open_cbt T1 C) =
    open_cbt (subst_tbt X P T1) C.
Proof with auto*.
------
  intros * WP.
  apply subst_tvt_open_cvt_rec...
------
  intros * WP.
  apply subst_tbt_open_cbt_rec...
Qed.


Lemma subst_te_open_ce_rec : forall e1 e2 C X U k,
  vtype U ->
  subst_te X U (open_ce_rec k e2 C e1) =
    open_ce_rec k (subst_tb X U e2) C (subst_te X U e1)
with subst_tb_open_cb_rec : forall e1 e2 C X U k,
  vtype U ->
  subst_tb X U (open_cb_rec k e2 C e1) =
    open_cb_rec k (subst_tb X U e2) C (subst_tb X U e1)
with subst_ts_open_cs_rec : forall e1 e2 C X U k,
  vtype U ->
  subst_ts X U (open_cs_rec k e2 C e1) =
    open_cs_rec k (subst_tb X U e2) C (subst_ts X U e1).
Proof with eauto using subst_tbt_open_cbt_rec, subst_tvt_open_cvt_rec.
------
  intros * H. revert k.
  induction e1; intros k; simpl; f_equal...
------
  intros * H. revert k.
  induction e1; intros k; simpl; f_equal...
  destruct (k === n)...
------
  intros * H. revert k.
  induction e1; intros k; simpl; f_equal...
Qed.

Lemma subst_te_open_ce : forall e1 e2 C X U,
  vtype U ->
  subst_te X U (open_ce e1 e2 C) =
    open_ce (subst_te X U e1) (subst_tb X U e2) C
with subst_tb_open_cb : forall e1 e2 C X U,
  vtype U ->
  subst_tb X U (open_cb e1 e2 C) =
    open_cb (subst_tb X U e1) (subst_tb X U e2) C
with subst_ts_open_cs : forall e1 e2 C X U,
  vtype U ->
  subst_ts X U (open_cs e1 e2 C) =
    open_cs (subst_ts X U e1) (subst_tb X U e2) C.
Proof with eauto using subst_tbt_open_cbt_rec, subst_tvt_open_cvt_rec.
------
  intros * H.
  apply subst_te_open_ce_rec...
------
  intros * H.
  apply subst_tb_open_cb_rec...
------
  intros * H.
  apply subst_ts_open_cs_rec...
Qed.


Lemma subst_tvt_open_tvt : forall T1 T2 X P,
  vtype P ->
  subst_tvt X P (open_tvt T1 T2) =
    open_tvt (subst_tvt X P T1) (subst_tvt X P T2)
with subst_tbt_open_tbt : forall T1 T2 X P,
  vtype P ->
  subst_tbt X P (open_tbt T1 T2) =
    open_tbt (subst_tbt X P T1) (subst_tvt X P T2).
Proof with auto.
------
  intros * WP.
  apply subst_tvt_open_tvt_rec...
------
  intros * WP.
  apply subst_tbt_open_tbt_rec...
Qed.


Lemma subst_tvt_fresh : forall X U T,
  X `notin` fv_tvt T ->
  T = subst_tvt X U T
with subst_tbt_fresh : forall X U T,
  X `notin` fv_tbt T ->
  T = subst_tbt X U T.
Proof with eauto; try notin_solve.
------
  intros * Fr.
  induction T; simpl in *; f_equal...
  destruct (a == X)...
------
  intros * Fr.
  induction T; simpl in *; f_equal...
Qed.

Lemma subst_te_intro : forall x e u,
  x `notin` fv_te e ->
  open_te e u = subst_te x u (open_te e x)
with subst_ts_intro : forall x e u,
  x `notin` fv_ts e ->
  open_ts e u = subst_ts x u (open_ts e x)
with subst_tb_intro : forall x e u,
  x `notin` fv_tb e ->
  open_tb e u = subst_tb x u (open_tb e x).
Proof with auto*.
------
  intros.
  unfold open_te.
  apply subst_te_intro_rec...
------
  intros.
  unfold open_ts.
  apply subst_ts_intro_rec...
------
  intros.
  unfold open_tb.
  apply subst_tb_intro_rec...
Qed.


Lemma subst_te_open_te_rec : forall e1 W X U k,
  vtype U ->
  subst_te X U (open_te_rec k W e1) =
    open_te_rec k (subst_tvt X U W) (subst_te X U e1)
with subst_tb_open_tb_rec : forall e1 W X U k,
  vtype U ->
  subst_tb X U (open_tb_rec k W e1) =
    open_tb_rec k (subst_tvt X U W) (subst_tb X U e1)
with subst_ts_open_ts_rec : forall e1 W X U k,
  vtype U ->
  subst_ts X U (open_ts_rec k W e1) =
    open_ts_rec k (subst_tvt X U W) (subst_ts X U e1).
Proof with eauto using subst_tvt_open_tvt_rec, subst_tbt_open_tbt_rec.
------
  intros * WU. revert k.
  induction e1; intros k; simpl; f_equal...
------
  intros * WU. revert k.
  induction e1; intros k; simpl; f_equal...
------
  intros * WU. revert k.
  induction e1; intros k; simpl; f_equal...
Qed.

Lemma subst_te_open_te : forall e1 W X U,
  vtype U ->
  subst_te X U (open_te e1 W) =
    open_te (subst_te X U e1) (subst_tvt X U W)
with subst_tb_open_tb : forall e1 W X U,
  vtype U ->
  subst_tb X U (open_tb e1 W) =
    open_tb (subst_tb X U e1) (subst_tvt X U W)
with subst_ts_open_ts : forall e1 W X U,
  vtype U ->
  subst_ts X U (open_ts e1 W) =
    open_ts (subst_ts X U e1) (subst_tvt X U W).
Proof with eauto using subst_tvt_open_tvt_rec, subst_tbt_open_tbt_rec.
------
  intros * WU.
  apply subst_te_open_te_rec...
------
  intros * WU.
  apply subst_tb_open_tb_rec...
------
  intros * WU.
  apply subst_ts_open_ts_rec...
Qed.


Lemma open_te_rec_expr_aux : forall e j v T i,
  open_ee_rec j v e = open_te_rec i T (open_ee_rec j v e) ->
  e = open_te_rec i T e
with open_tb_rec_expr_aux : forall e j v T i,
  open_eb_rec j v e = open_tb_rec i T (open_eb_rec j v e) ->
  e = open_tb_rec i T e
with open_ts_rec_expr_aux : forall e j v T i,
  open_es_rec j v e = open_ts_rec i T (open_es_rec j v e) ->
  e = open_ts_rec i T e.
Proof with eauto*.
------
  intros * Eq.
  induction e; simpl in *; f_equal;
    inversion Eq; subst...
------
  intros * Eq.
  induction e; simpl in *; f_equal;
    inversion Eq; subst...
------
  intros * Eq.
  induction e; simpl in *; f_equal;
    inversion Eq; subst...
Qed.

Lemma open_te_rec_block_aux : forall e j v T i,
  open_be_rec j v e = open_te_rec i T (open_be_rec j v e) ->
  e = open_te_rec i T e
with open_tb_rec_block_aux : forall e j v T i,
  open_bb_rec j v e = open_tb_rec i T (open_bb_rec j v e) ->
  e = open_tb_rec i T e
with open_ts_rec_block_aux : forall e j v T i,
  open_bs_rec j v e = open_ts_rec i T (open_bs_rec j v e) ->
  e = open_ts_rec i T e.
Proof with eauto*.
------
  intros * Eq.
  induction e; simpl in *; f_equal;
    inversion Eq; subst...
------
  intros * Eq.
  induction e; simpl in *; f_equal;
    inversion Eq; subst...
------
  intros * Eq.
  induction e; simpl in *; f_equal;
    inversion Eq; subst...
Qed.

Lemma open_te_rec_capt_aux : forall e j C v T i,
  open_ce_rec j v C e = open_te_rec i T (open_ce_rec j v C e) ->
  e = open_te_rec i T e
with open_tb_rec_capt_aux : forall e j C v T i,
  open_cb_rec j v C e = open_tb_rec i T (open_cb_rec j v C e) ->
  e = open_tb_rec i T e
with open_ts_rec_capt_aux : forall e j C v T i,
  open_cs_rec j v C e = open_ts_rec i T (open_cs_rec j v C e) ->
  e = open_ts_rec i T e.
Proof with eauto using open_tvt_rec_capt_aux, open_tbt_rec_capt_aux.
------
  intros * Eq.
  induction e; simpl in *; f_equal;
    inversion Eq; subst...
------
  intros * Eq.
  induction e; simpl in *; f_equal;
    inversion Eq; subst; simpl in *...
------
  intros * Eq.
  induction e; simpl in *; f_equal;
    inversion Eq; subst...
Qed.

Lemma open_te_rec_type_aux : forall e j U T i,
  i <> j ->
  open_te_rec j U e = open_te_rec i T (open_te_rec j U e) ->
  e = open_te_rec i T e
with open_tb_rec_type_aux : forall e j U T i,
  i <> j ->
  open_tb_rec j U e = open_tb_rec i T (open_tb_rec j U e) ->
  e = open_tb_rec i T e
with open_ts_rec_type_aux : forall e j U T i,
  i <> j ->
  open_ts_rec j U e = open_ts_rec i T (open_ts_rec j U e) ->
  e = open_ts_rec i T e.
Proof with eauto using open_tvt_rec_type_aux, open_tbt_rec_type_aux.
------
  intros * Neq Eq.
  induction e; simpl in *; f_equal;
    inversion Eq; subst...
------
  intros * Neq Eq.
  induction e; simpl in *; f_equal;
    inversion Eq; subst...
------
  intros * Neq Eq.
  induction e; simpl in *; f_equal;
    inversion Eq; subst...
Qed.

Lemma open_te_rec_expr : forall k T e,
  expr e ->
  e = open_te_rec k T e
with open_ts_rec_stmt : forall k T e,
  stmt e ->
  e = open_ts_rec k T e
with open_tb_rec_block : forall k T e,
  block e ->
  e = open_tb_rec k T e.
Proof with eauto using open_tvt_rec_vtype, open_tbt_rec_btype.
------
  intros * H. revert k. induction H; intros k; simpl in *; f_equal;
    try solve [eauto using open_tvt_rec_vtype, open_tbt_rec_btype].
------
  intros * H. revert k. induction H; intros k; simpl in *; f_equal;
    try solve [eauto using open_tvt_rec_vtype, open_tbt_rec_btype].
  * pick fresh x.
    unfold open_es in *.
    eapply open_ts_rec_expr_aux with (j := 0) (v := x)...
  * pick fresh x.
    unfold open_bs in *.
    eapply open_ts_rec_block_aux with (j := 0) (v := x)...
  * pick fresh x.
    unfold open_cs in *.
    apply open_ts_rec_capt_aux with (j := 0) (v := x) (C := cset_fvar x)...
  * unfold open_bs, open_cs, open_es in *.
    pick fresh y. pick fresh kont.
    eapply open_ts_rec_expr_aux with (j := 0) (v := y); intuition.
    eapply open_ts_rec_block_aux with (j := 0) (v := kont); intuition.
    solve using assumption and notin_solve.
  * unfold open_bs, open_cs, open_es in *.
    pick fresh y. pick fresh kont.
    eapply open_ts_rec_expr_aux with (j := 0) (v := y); intuition.
    eapply open_ts_rec_block_aux with (j := 0) (v := kont); intuition.
    solve using assumption and notin_solve.
------
  intros * H; revert k; induction H; intros k; simpl in *; f_equal;
    try solve [eauto using open_tvt_rec_vtype, open_tbt_rec_btype].
  * pick fresh x.
    unfold open_es in *.
    eapply open_ts_rec_expr_aux with (j := 0) (v := x).
    solve using assumption and notin_solve.
  * pick fresh x.
    unfold open_cs in *.
    eapply open_ts_rec_capt_aux with (j := 0) (v := x) (C := cset_fvar x).
    solve using assumption and notin_solve.
  * pick fresh X.
    unfold open_tb in *.
    eapply open_tb_rec_type_aux with (j := 0) (U := X)...
Qed.

Lemma subst_ee_open_te_rec : forall e T x u k,
  expr u ->
  subst_ee x u (open_te_rec k T e) =
    open_te_rec k T (subst_ee x u e)
with subst_eb_open_tb_rec : forall e T x u k,
  expr u ->
  subst_eb x u (open_tb_rec k T e) =
    open_tb_rec k T (subst_eb x u e)
with subst_es_open_ts_rec : forall e T x u k,
  expr u ->
  subst_es x u (open_ts_rec k T e) =
    open_ts_rec k T (subst_es x u e).
Proof with auto*.
------
  intros * WP. revert k.
  induction e; intros k; simpl; f_equal...
  - Case "exp_fvar".
    destruct (a == x); subst... apply open_te_rec_expr...
------
  intros * WP. revert k.
  induction e; intros k; simpl; f_equal...
------
  intros * WP. revert k.
  induction e; intros k; simpl; f_equal...
Qed.

Lemma subst_ee_open_te: forall e T x u,
  expr u ->
  subst_ee x u (open_te e T) =
    open_te (subst_ee x u e) T
with subst_eb_open_tb : forall e T x u,
  expr u ->
  subst_eb x u (open_tb e T) =
    open_tb (subst_eb x u e) T
with subst_es_open_ts: forall e T x u,
  expr u ->
  subst_es x u (open_ts e T) =
    open_ts (subst_es x u e) T.
Proof with auto*.
------
  intros * WP.
  eapply subst_ee_open_te_rec...
------
  intros * WP.
  eapply subst_eb_open_tb_rec...
------
  intros * WP.
  eapply subst_es_open_ts_rec...
Qed.

Lemma subst_ee_open_te_var : forall (x y:atom) u e,
  y <> x ->
  expr u ->
  open_te (subst_ee x u e) y = subst_ee x u (open_te e y)
with subst_eb_open_tb_var : forall (x y:atom) u e,
  y <> x ->
  expr u ->
  open_tb (subst_eb x u e) y = subst_eb x u (open_tb e y)
with subst_es_open_ts_var : forall (x y:atom) u e,
  y <> x ->
  expr u ->
  open_ts (subst_es x u e) y = subst_es x u (open_ts e y).
Proof with auto*.
------
  intros * Neq Wu.
  unfold open_te.
  rewrite subst_ee_open_te_rec...
------
  intros * Neq Wu.
  unfold open_tb.
  rewrite subst_eb_open_tb_rec...
------
  intros x y u e Neq Wu.
  unfold open_ts.
  rewrite subst_es_open_ts_rec...
Qed.


Lemma subst_be_open_te_rec : forall e T x u k,
  block u ->
  subst_be x u (open_te_rec k T e) =
    open_te_rec k T (subst_be x u e)
with subst_bb_open_tb_rec : forall e T x u k,
  block u ->
  subst_bb x u (open_tb_rec k T e) =
    open_tb_rec k T (subst_bb x u e)
with subst_bs_open_ts_rec : forall e T x u k,
  block u ->
  subst_bs x u (open_ts_rec k T e) =
    open_ts_rec k T (subst_bs x u e).
Proof with auto*.
------
  intros * WP. revert k.
  induction e; intros k; simpl; f_equal...
------
  intros * WP. revert k.
  induction e; intros k; simpl; f_equal...
  - Case "block_fvar".
    destruct (a == x); subst... apply open_tb_rec_block...
------
  intros * WP. revert k.
  induction e; intros k; simpl; f_equal...
Qed.

Lemma subst_be_open_te: forall e T x u,
  block u ->
  subst_be x u (open_te e T) =
    open_te (subst_be x u e) T
with subst_bb_open_tb : forall e T x u,
  block u ->
  subst_bb x u (open_tb e T) =
    open_tb (subst_bb x u e) T
with subst_bs_open_ts: forall e T x u,
  block u ->
  subst_bs x u (open_ts e T) =
    open_ts (subst_bs x u e) T.
Proof with auto*.
------
  intros * WP.
  eapply subst_be_open_te_rec...
------
  intros * WP.
  eapply subst_bb_open_tb_rec...
------
  intros * WP.
  eapply subst_bs_open_ts_rec...
Qed.

Lemma subst_be_open_te_var : forall (x y:atom) u e,
  y <> x ->
  block u ->
  open_te (subst_be x u e) y = subst_be x u (open_te e y)
with subst_bb_open_tb_var : forall (x y:atom) u e,
  y <> x ->
  block u ->
  open_tb (subst_bb x u e) y = subst_bb x u (open_tb e y)
with subst_bs_open_ts_var : forall (x y:atom) u e,
  y <> x ->
  block u ->
  open_ts (subst_bs x u e) y = subst_bs x u (open_ts e y).
Proof with auto*.
------
  intros * Neq Wu.
  unfold open_te.
  rewrite subst_be_open_te_rec...
------
  intros * Neq Wu.
  unfold open_tb.
  rewrite subst_bb_open_tb_rec...
------
  intros x y u e Neq Wu.
  unfold open_ts.
  rewrite subst_bs_open_ts_rec...
Qed.


Lemma subst_ce_open_te_rec : forall e T x u C k,
  capt C ->
  block u ->
  subst_ce x u C (open_te_rec k T e) =
    open_te_rec k (subst_cvt x C T) (subst_ce x u C e)
with subst_cb_open_tb_rec : forall e T x u C k,
  capt C ->
  block u ->
  subst_cb x u C (open_tb_rec k T e) =
    open_tb_rec k (subst_cvt x C T) (subst_cb x u C e)
with subst_cs_open_ts_rec : forall e T x u C k,
  capt C ->
  block u ->
  subst_cs x u C (open_ts_rec k T e) =
    open_ts_rec k (subst_cvt x C T)  (subst_cs x u C e).
Proof with auto using subst_cvt_open_tvt_rec, subst_cbt_open_tbt_rec.
------
  intros * WC WP. revert k.
  induction e; intros k; simpl; f_equal...
------
  intros * WC WP. revert k.
  induction e; intros k; simpl; f_equal...
  - Case "block_fvar".
    destruct (a == x); subst... apply open_tb_rec_block...
------
  intros * WC WP. revert k.
  induction e; intros k; simpl; f_equal...
Qed.

Lemma subst_ce_open_te: forall e T x u C,
  capt C ->
  block u ->
  subst_ce x u C (open_te e T) =
    open_te (subst_ce x u C e) (subst_cvt x C T)
with subst_cb_open_tb : forall e T x u C,
  capt C ->
  block u ->
  subst_cb x u C (open_tb e T) =
    open_tb (subst_cb x u C e) (subst_cvt x C T)
with subst_cs_open_ts: forall e T x u C,
  capt C ->
  block u ->
  subst_cs x u C (open_ts e T) =
    open_ts (subst_cs x u C e) (subst_cvt x C T).
Proof with auto*.
------
  intros * WC WP.
  eapply subst_ce_open_te_rec...
------
  intros * WC WP.
  eapply subst_cb_open_tb_rec...
------
  intros * WC WP.
  eapply subst_cs_open_ts_rec...
Qed.

Lemma subst_ce_open_te_var : forall (x y:atom) u e C,
  y <> x ->
  capt C ->
  block u ->
  open_te (subst_ce x u C e) y = subst_ce x u C (open_te e y)
with subst_cb_open_tb_var : forall (x y:atom) u e C,
  y <> x ->
  capt C ->
  block u ->
  open_tb (subst_cb x u C e) y = subst_cb x u C (open_tb e y)
with subst_cs_open_ts_var : forall (x y:atom) u e C,
  y <> x ->
  capt C ->
  block u ->
  open_ts (subst_cs x u C e) y = subst_cs x u C (open_ts e y).
Proof with auto*.
------
  intros * Neq WC Wu.
  unfold open_te.
  rewrite subst_ce_open_te_rec...
------
  intros * Neq WC Wu.
  unfold open_tb.
  rewrite subst_cb_open_tb_rec...
------
  intros * Neq WC Wu.
  unfold open_ts.
  rewrite subst_cs_open_ts_rec...
Qed.