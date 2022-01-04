Require Export SystemC.Infrastructure.
Require Import Taktiks.
Require Import Signatures.
Require Import Coq.Program.Tactics.

(* ********************************************************************** *)
(** * #<a name="wft"></a># Properties of [wf_typ] *)

(** If a type is well-formed in an environment, then it is locally
    closed. *)

Lemma capt_from_wf_cap : forall E T,
  wf_cap E T -> capt T.
Proof.
  intros * H; induction H; eauto.
  unfold capt. unfold cset_bvars. fnsetdec.
Qed.

Lemma vtype_from_wf_vtyp : forall E T,
  wf_vtyp E T -> vtype T
with btype_from_wf_btyp : forall E T,
  wf_btyp E T -> btype T.
Proof with eauto using capt_from_wf_cap.
------
  intros * H; induction H; econstructor...
------
  intros * H; induction H; try solve [econstructor; eauto 2].
  - pick fresh X and apply type_bfun...
Qed.

(** The remaining properties are analogous to the properties that we
    need to show for the typing relations. *)

Lemma wf_cap_subset : forall E R R0,
  R |= R0 ->
  wf_cap E R ->
  wf_cap E R0.
Proof with eauto.
  intros * Sub Hwf_cap.
  inversion Hwf_cap; subst...
  inversion Sub as [Sub_F Sub_B].
  unfold cset_fvars, cset_bvars in *; destruct R0...
  assert (t0 = {}N) by fnsetdec; subst...
  constructor...
  unfold all_tracked in *.
  intros x xInT. specialize (H x ltac:(fsetdec))...
Qed.

Lemma wf_cap_weakening : forall T E F G,
  wf_cap (G ++ E) T ->
  ok (G ++ F ++ E) ->
  wf_cap (G ++ F ++ E) T.
Proof with simpl_env; eauto.
  intros * Hwf_cap Hk.
  dependent induction Hwf_cap...
  econstructor. unfold all_tracked; intros. destruct (H x H0) as [T Binds]...
Qed.

Lemma wf_cap_weaken_head : forall T E F,
  wf_cap E T ->
  ok (F ++ E) ->
  wf_cap (F ++ E) T.
Proof.
  intros.
  rewrite_env (empty ++ F++ E).
  auto using wf_cap_weakening.
Qed.

Lemma wf_cap_bind_head : forall E R x S1,
  ok ([(x, bind_blk S1 tracked)] ++ E) ->
  wf_cap E R ->
  wf_cap ([(x, bind_blk S1 tracked)] ++ E) (cset_union R (cset_fvar x)).
Proof with eauto.
  intros * Ok Wf.
  inversion Wf; subst; unfold all_tracked in *...
  unfold cset_union, cset_fvar in *; csetsimpl; simpl_env.
  constructor.
  intros x0 HIn.
  rewrite AtomSetFacts.union_iff in HIn.
  destruct HIn.
  - specialize (H x0 ltac:(assumption)) as [T H]...
  - rewrite AtomSetFacts.singleton_iff in H0; symmetry in H0; subst.
    exists S1...
Qed.

Lemma wf_cap_lvar : forall E l,
  wf_cap E (cset_lvar l).
Proof.
  intros.
  econstructor. intros x In. fsetdec.
Qed.

Lemma wf_cap_labels : forall E c,
  wf_cap E (from_labels (bound_labels c)).
Proof.
  intros.
  econstructor. intros x In. fsetdec.
Qed.

Hint Resolve wf_cap_lvar wf_cap_labels : core.

Lemma wf_vtyp_weakening : forall T E F G,
  wf_vtyp (G ++ E) T ->
  ok (G ++ F ++ E) ->
  wf_vtyp (G ++ F ++ E) T
with wf_btyp_weakening : forall T E F G,
  wf_btyp (G ++ E) T ->
  ok (G ++ F ++ E) ->
  wf_btyp (G ++ F ++ E) T.
Proof with simpl_env; eauto using wf_cap_weakening.
------
  intros * Hwf_typ Hk.
  dependent induction Hwf_typ; econstructor...
------
  intros * Hwf_typ Hk.
  dependent induction Hwf_typ; try solve [econstructor].
  - econstructor; eauto.
  - Case "typ_bfun".
    pick fresh X and apply wf_typ_bfun...
    rewrite <- concat_assoc.
    apply wf_vtyp_weakening...
  - pick fresh X and apply wf_typ_tfun.
    rewrite <- concat_assoc.
    apply wf_btyp_weakening...
  - econstructor; eauto.
Qed.

Lemma wf_vtyp_weaken_head : forall T E F,
  wf_vtyp E T ->
  ok (F ++ E) ->
  wf_vtyp (F ++ E) T
with wf_btyp_weaken_head : forall T E F,
  wf_btyp E T ->
  ok (F ++ E) ->
  wf_btyp (F ++ E) T.
Proof.
------
  intros.
  rewrite_env (empty ++ F++ E).
  auto using wf_vtyp_weakening.
------
  intros.
  rewrite_env (empty ++ F++ E).
  auto using wf_btyp_weakening.
Qed.


Lemma wf_cap_strengthening : forall E F x U T,
 wf_cap (F ++ [(x, bind_val U)] ++ E) T ->
 wf_cap (F ++ E) T.
Proof with simpl_env; eauto.
  intros * H.
  dependent induction H...
  constructor.
  unfold all_tracked; intros.
  destruct (H x0 H0) as [S0 Bind].
  binds_cases Bind.
  - exists S0. apply binds_tail...
  - exists S0. apply binds_head...
Qed.

Lemma wf_vtyp_strengthening : forall E F x U T,
 wf_vtyp (F ++ [(x, bind_val U)] ++ E) T ->
 wf_vtyp (F ++ E) T
with wf_btyp_strengthening : forall E F x U T,
  wf_btyp (F ++ [(x, bind_val U)] ++ E) T ->
  wf_btyp (F ++ E) T.
Proof with simpl_env; eauto using wf_cap_strengthening.
------
  intros * H.
  dependent induction H.
  - trivial.
  - econstructor...
  - econstructor...
    binds_cases H...
------
  intros * H.
  dependent induction H.
  - constructor...
  - pick fresh y and apply wf_typ_bfun...
    rewrite <- concat_assoc.
    eapply wf_vtyp_strengthening...
  - pick fresh y and apply wf_typ_tfun...
    rewrite <- concat_assoc.
    eapply wf_btyp_strengthening...
  - constructor...
Qed.

Lemma wf_cap_strengthening_blk : forall E F x U C T,
 wf_cap (F ++ [(x, bind_blk U (capture C))] ++ E) T ->
 wf_cap (F ++ E) T.
Proof with simpl_env; eauto.
  intros * H.
  dependent induction H...
  constructor.
  unfold all_tracked; intros.
  destruct (H x0 H0) as [S0 Bind].
  binds_cases Bind.
  - exists S0. apply binds_tail...
  - exists S0. apply binds_head...
Qed.

Lemma wf_cap_strengthening_typ : forall E F X T,
 wf_cap (F ++ [(X, bind_typ)] ++ E) T ->
 wf_cap (F ++ E) T.
Proof with simpl_env; eauto.
  intros * H.
  dependent induction H...
  constructor...
  unfold all_tracked in *; intros.
  destruct (H x H0) as [S0 Bind].
  binds_cases Bind.
  - exists S0. apply binds_tail...
  - exists S0. apply binds_head...
Qed.

Lemma wf_vtyp_strengthening_blk : forall E F x U C T,
 wf_vtyp (F ++ [(x, bind_blk U (capture C))] ++ E) T ->
 wf_vtyp (F ++ E) T
with wf_btyp_strengthening_blk : forall E F x U C T,
  wf_btyp (F ++ [(x, bind_blk U (capture C))] ++ E) T ->
  wf_btyp (F ++ E) T.
Proof with simpl_env; eauto using wf_cap_strengthening_blk.
------
  intros * H.
  dependent induction H.
  - trivial.
  - econstructor...
  - binds_cases H...
------
  intros * H.
  dependent induction H.
  - constructor...
  - pick fresh y and apply wf_typ_bfun...
    rewrite <- concat_assoc.
    eapply wf_vtyp_strengthening_blk...
  - pick fresh y and apply wf_typ_tfun...
    rewrite <- concat_assoc.
    eapply wf_btyp_strengthening_blk...
  - constructor...
Qed.

Lemma wf_cap_strengthening_blk_tracked : forall E F x U T,
  x `notin` cset_fvars T ->
  wf_cap (F ++ [(x, bind_blk U tracked)] ++ E) T ->
  wf_cap (F ++ E) T.
Proof with simpl_env; eauto.
  intros * Notin H.
  dependent induction H...
  constructor.
  unfold all_tracked; intros.
  destruct (H x0 H0) as [S0 Bind].
  binds_cases Bind.
  - exists S0. apply binds_tail...
  - simpl in Notin. fsetdec.
  - exists S0. apply binds_head...
Qed.

Lemma notin_fvars_open_cset : forall x k T C,
  x `notin` (cset_fvars T `union` cset_fvars C) ->
  x `notin` cset_fvars (open_cset k T C).
Proof.
  intros * H.
  destruct C. destruct T.
  unfold cset_fvars, open_cset, cset_references_bvar_dec, cset_bvars in *.
  destruct_set_mem k t0; csetsimpl. fsetdec.
Qed.

Lemma notin_fv_cvt_open_cvt : forall x k T C,
  x `notin` (fv_cvt T `union` cset_fvars C) ->
  x `notin` fv_cvt (open_cvt_rec k C T)
with notin_fv_cbt_open_cbt : forall x k T C,
  x `notin` (fv_cbt T `union` cset_fvars C) ->
  x `notin` fv_cbt (open_cbt_rec k C T).
Proof with auto; try notin_solve.
------
  intros * H.
  induction T; try solve [simpl in *; notin_solve].
  - simpl in *.
    pose proof (notin_fv_cbt_open_cbt x k b C ltac:(notin_solve)).
    pose proof (notin_fvars_open_cset x k C c ltac:(notin_solve))...
------
  intros * H.
  induction T; try solve [simpl in *; notin_solve].
  - simpl in *.
    pose proof (notin_fv_cvt_open_cvt x k v C ltac:(notin_solve)).
    pose proof (notin_fv_cvt_open_cvt x k v0 C ltac:(notin_solve))...
  - simpl in *.
    pose proof (notin_fv_cbt_open_cbt x k T C ltac:(notin_solve)).
    pose proof (notin_fv_cvt_open_cvt x (S k) v C ltac:(notin_solve))...
  - simpl in *.
    pose proof (notin_fv_cbt_open_cbt x k T C ltac:(notin_solve))...
  - simpl in *.
    pose proof (notin_fv_cvt_open_cvt x k v C ltac:(notin_solve))...
Qed.

Lemma notin_fv_cvt_open_tvt : forall x k T U,
  x `notin` (fv_cvt T `union` fv_cvt U) ->
  x `notin` (fv_cvt (open_tvt_rec k U T))
with notin_fv_cbt_open_tbt : forall x k T U,
  x `notin` (fv_cbt T `union` fv_cvt U) ->
  x `notin` (fv_cbt (open_tbt_rec k U T)).
Proof with auto; try notin_solve.
------
  intros * H.
  dependent induction T; try solve [simpl in *; notin_solve].
  - simpl in *.
    pose proof (notin_fv_cbt_open_tbt x k b U ltac:(notin_solve))...
  - simpl in *.
    destruct (k === n)...
------
  intros * H. generalize dependent k.
  dependent induction T; intros k; try solve [simpl in *; notin_solve].
  - simpl in *.
    pose proof (notin_fv_cvt_open_tvt x k v U ltac:(notin_solve)).
    pose proof (notin_fv_cvt_open_tvt x k v0 U ltac:(notin_solve))...
  - simpl in *.
    pose proof (notin_fv_cvt_open_tvt x k v U ltac:(notin_solve)).
    pose proof (notin_fv_cbt_open_tbt x k T U ltac:(notin_solve))...
  - simpl in *.
    specialize (IHT U ltac:(notin_solve) (S k))...
  - simpl in *.
    pose proof (notin_fv_cvt_open_tvt x k v U ltac:(notin_solve)).
    pose proof (notin_fv_cvt_open_tvt x k v0 U ltac:(notin_solve))...
Qed.

Lemma wf_vtyp_strengthening_blk_tracked : forall E F x U T,
 x `notin` fv_cvt T ->
 wf_vtyp (F ++ [(x, bind_blk U tracked)] ++ E) T ->
 wf_vtyp (F ++ E) T
with wf_btyp_strengthening_blk_tracked : forall E F x U T,
  x `notin` fv_cbt T ->
  wf_btyp (F ++ [(x, bind_blk U tracked)] ++ E) T ->
  wf_btyp (F ++ E) T.
Proof with simpl_env; eauto using wf_cap_strengthening_blk_tracked.
------
  intros * Notin H.
  dependent induction H.
  - trivial.
  - simpl in Notin.
    econstructor.
    eapply wf_btyp_strengthening_blk_tracked with (x := x)...
    eapply wf_cap_strengthening_blk_tracked...
  - binds_cases H...
------
  intros * Notin H.
  dependent induction H.
  - simpl in Notin.
    constructor.
    eapply wf_vtyp_strengthening_blk_tracked with (x := x)...
    eapply wf_vtyp_strengthening_blk_tracked with (x := x)...
  - simpl in Notin.
    pick fresh y and apply wf_typ_bfun.
    eapply (IHwf_btyp _ _ x)...
    rewrite <- concat_assoc.
    eapply wf_vtyp_strengthening_blk_tracked with (x := x)...
    apply notin_fv_cvt_open_cvt...
  - simpl in Notin.
    pick fresh y and apply wf_typ_tfun.
    rewrite <- concat_assoc.
    eapply wf_btyp_strengthening_blk_tracked with (x := x)...
    apply notin_fv_cbt_open_tbt...
  - constructor; eapply wf_vtyp_strengthening_blk_tracked with (x := x);
      simpl in Notin;
      try solve [notin_solve || eassumption].
Qed.

Lemma wf_cap_subst_tracked : forall F E U Z P T,
  wf_cap (F ++ [(Z, bind_blk U tracked)] ++ E) T ->
  wf_cap E P ->
  ok (map (subst_bbind Z P) F ++ E) ->
  wf_cap (map (subst_bbind Z P) F ++ E) (subst_cset Z P T).
Proof with simpl_env; eauto using wf_vtyp_weaken_head, wf_cap_weaken_head, vtype_from_wf_vtyp, capt_from_wf_cap.
  intros * WT WP Ok.
  dependent induction WT; unfold subst_cset; simpl...
  unfold subst_cset, cset_fvars, cset_references_fvar_dec; simpl.
  destruct_set_mem Z xs.
  - unfold cset_union, cset_remove_fvar.
    destruct P.
    inversion WP; subst.
    autorewrite with csets.
    simpl.
    constructor.
    intros x xIn.
    rewrite AtomSetFacts.union_iff in xIn.
    destruct xIn as [xIn | xIn].
    + specialize (H2 x xIn) as [T H2]...
    + assert (x <> Z) by fsetdec.
      specialize (H x ltac:(fsetdec)) as [T H]...
      binds_cases H...
      enough (binds x (subst_bbind Z (cset_set t {}N t1) (bind_blk T tracked))
                    (map (subst_bbind Z (cset_set t {}N t1)) F ++ E))...
  - constructor.
    unfold all_tracked in *.
    intros x xIn.
    assert (x <> Z) by fsetdec.
    specialize (H x xIn) as [T H].
    binds_cases H...
    enough (binds x (subst_bbind Z P (bind_blk T tracked)) (map (subst_bbind Z P) F ++ E))...
Qed.

Lemma wf_vtyp_subst_tracked : forall F E Z U C T,
  wf_vtyp (F ++ [(Z, bind_blk U tracked)] ++ E) T ->
  wf_cap E C ->
  ok (map (subst_bbind Z C) F ++ E) ->
  ok (F ++ [(Z, bind_blk U tracked)] ++ E) ->
  wf_vtyp (map (subst_bbind Z C) F ++ E) (subst_cvt Z C T)
with wf_btyp_subst_tracked : forall F E Z U C T,
  wf_btyp (F ++ [(Z, bind_blk U tracked)] ++ E) T ->
  wf_cap E C ->
  ok (map (subst_bbind Z C) F ++ E) ->
  ok (F ++ [(Z, bind_blk U tracked)] ++ E) ->
  wf_btyp (map (subst_bbind Z C) F ++ E) (subst_cbt Z C T).
Proof with simpl_env; eauto
    using
      wf_vtyp_weaken_head, wf_cap_weaken_head,
      vtype_from_wf_vtyp, capt_from_wf_cap, wf_cap_subst_tracked.
------
  intros * WT WP.
  dependent induction WT; simpl subst_cvt...
  econstructor...
  binds_cases H...
  apply binds_head...
  eapply binds_map in H3...
  rapply H3...
------
  intros * WT WP.
  dependent induction WT; simpl subst_cbt...
  + intros ?Ok ?Ok.
    pick fresh Y and apply wf_typ_bfun.
    - eapply IHWT with (U0 := U)...
    - rewrite <- subst_cvt_open_cvt_var; eauto.
      specialize (H Y ltac:(notin_solve)).
      rewrite_env (([(Y, bind_blk S1 tracked)] ++ F) ++ [(Z, bind_blk U tracked)] ++ E) in H.
      apply wf_vtyp_subst_tracked with (C := C) in H...
      eapply capt_from_wf_cap...
  + intros ?Ok ?Ok.
    pick fresh Y and apply wf_typ_tfun.
    - rewrite <- subst_cbt_open_tbt_var...
    specialize (H Y ltac:(notin_solve)).
    rewrite_env (([(Y, bind_typ)] ++ F) ++ [(Z, bind_blk U tracked)] ++ E) in H.
    apply wf_btyp_subst_tracked with (C := C) in H...
Qed.

(* ********************************************************************** *)
(** * #<a name="oktwft"></a># Properties of [wf_env] and [wf_typ] *)

Lemma ok_from_wf_env : forall E,
  wf_env E ->
  ok E.
Proof.
  intros E H; induction H; auto.
Qed.

(** We add [ok_from_wf_env] as a hint here since it helps blur the
    distinction between [wf_env] and [ok] in proofs.  The lemmas in
    the [Environment] library use [ok], whereas here we naturally have
    (or can easily show) the stronger [wf_env].  Thus,
    [ok_from_wf_env] serves as a bridge that allows us to use the
    environments library. *)

Hint Resolve ok_from_wf_env : core.

Lemma wf_vtyp_from_binds_typ : forall x U E,
  wf_env E ->
  binds x (bind_val U) E ->
  wf_vtyp E U.
Proof with auto using wf_vtyp_weaken_head.
  induction 1; intros J; binds_cases J...
  inversion H4; subst...
Qed.

Lemma wf_vtyp_from_wf_env_typ : forall x T E,
  wf_env ([(x, bind_val T)] ++ E) ->
  wf_vtyp E T.
Proof.
  intros * H. inversion H; auto.
Qed.

Lemma wf_btyp_from_binds_blk : forall x U Q E,
  wf_env E ->
  binds x (bind_blk U Q) E ->
  wf_btyp E U.
Proof with auto using wf_btyp_weaken_head.
  induction 1; intros J; binds_cases J...
  inversion H4; subst...
  inversion H5; subst...
Qed.

Lemma wf_btyp_from_wf_env_blk : forall x T Q E,
  wf_env ([(x, bind_blk T Q)] ++ E) ->
  wf_btyp E T.
Proof.
  intros * H. inversion H; auto.
Qed.

Lemma wf_vtyp_from_sig_binds : forall Q l T1 T,
  wf_sig Q ->
  Signatures.binds l (bind_sig T1 T) Q ->
  wf_vtyp empty T.
Proof with eauto*.
  intros * WfQ Hbinds.
  induction Q...
------
  inversion Hbinds.
------
  destruct a as [l' T'].
  unfold Signatures.binds, Signatures.get in Hbinds.
  destruct (l =l= l').
  - inversion WfQ; inversion Hbinds; subst.
    inversion select (bind_sig _ _= _ _ _); subst...
  - inversion WfQ; apply IHQ; auto.
Qed.

Lemma wf_vtyp_from_sig_binds_val : forall Q l T1 T,
  wf_sig Q ->
  Signatures.binds l (bind_sig T1 T) Q ->
  wf_vtyp empty T1.
Proof with eauto*.
  intros * WfQ Hbinds.
  induction Q...
------
  inversion Hbinds.
------
  destruct a as [l' T'].
  unfold Signatures.binds, Signatures.get in Hbinds.
  destruct (l =l= l').
  - inversion WfQ; inversion Hbinds; subst.
    inversion select (bind_sig _ _= _ _ _); subst...
  - inversion WfQ; apply IHQ; auto.
Qed.


(* ********************************************************************** *)
(** * #<a name="okt"></a># Properties of [wf_env] *)

(** These properties are analogous to the properties that we need to
    show for the typing relations. *)

Lemma wf_env_tail : forall E F,
  wf_env (F ++ E) ->
  wf_env E.
Proof with auto.
  induction F; intros Wf_env; inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma wf_env_strengthening : forall x T E F,
  wf_env (F ++ [(x, bind_val T)] ++ E) ->
  wf_env (F ++ E).
Proof with eauto using wf_vtyp_strengthening, wf_btyp_strengthening, wf_cap_strengthening.
  induction F; intros Wf_env; inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma wf_env_strengthening_blk : forall x S1 C E F,
  wf_env (F ++ [(x, bind_blk S1 (capture C))] ++ E) ->
  wf_env (F ++ E).
Proof with eauto using wf_vtyp_strengthening_blk, wf_btyp_strengthening_blk, wf_cap_strengthening_blk.
  induction F; intros Wf_env; inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma wf_env_subst_tracked : forall x U E F C,
  wf_env (F ++ [(x, bind_blk U tracked)] ++ E) ->
  wf_cap E C ->
  wf_env (map (subst_bbind x C) F ++ E).
Proof with eauto 6 using wf_vtyp_subst_tracked, wf_btyp_subst_tracked, wf_cap_subst_tracked.
  induction F; intros C Wf_env WP; simpl_env;
  inversion Wf_env; simpl_env in *; simpl subst_bbind...
  constructor...
  constructor...
  constructor...
Qed.

(* ********************************************************************** *)
(** * #<a name="subst"></a># Environment is unchanged by substitution for a fresh name *)


Lemma notin_fv_cap_wf : forall E (X : atom) C,
  wf_cap E C ->
  X `notin` dom E ->
  X `notin` cset_fvars C.
Proof.
  intros * Wf H.
  inversion Wf; subst. unfold all_tracked in H0.
  intros In. unfold cset_fvars in *.
  destruct (H0 X In) as [T Bind].
  eapply binds_In in Bind. contradiction.
Qed.

Lemma notin_cset_fvars_open_cset : forall (Y X : atom) k c,
  X `notin` cset_fvars (open_cset k (cset_fvar Y) c) ->
  X `notin` cset_fvars c.
Proof with auto.
  intros.
  unfold open_cset in *.
  destruct_set_mem k c; simpl in *; notin_solve.
Qed.

Lemma notin_fv_cvt_open_cvt_rec : forall (Y X : atom) k T,
  X `notin` fv_cvt (open_cvt_rec k (cset_fvar Y) T) ->
  X `notin` fv_cvt T
with notin_fv_cbt_open_cbt_rec : forall (Y X : atom) k T,
  X `notin` fv_cbt (open_cbt_rec k (cset_fvar Y) T) ->
  X `notin` fv_cbt T.
Proof with auto.
------
  intros Y X k T. generalize dependent k.
  induction T; simpl; intros k Fr; notin_simpl; try apply notin_union; eauto.
  eapply notin_cset_fvars_open_cset...
  apply H0.
------
  intros Y X k T. generalize dependent k.
  induction T; simpl; intros k Fr; notin_simpl; try apply notin_union; eauto.
Qed.

Lemma notin_fv_cvt_open_tvt_rec : forall (Y X : atom) k T,
  X `notin` fv_cvt (open_tvt_rec k Y T) ->
  X `notin` fv_cvt T
with notin_fv_cbt_open_tbt_rec : forall (Y X : atom) k T,
  X `notin` fv_cbt (open_tbt_rec k Y T) ->
  X `notin` fv_cbt T.
Proof with auto.
------
  intros Y X k T. generalize dependent k.
  induction T; simpl; intros k Fr; notin_simpl; try apply notin_union; eauto.
------
  intros Y X k T. generalize dependent k.
  induction T; simpl; intros k Fr; notin_simpl; try apply notin_union; eauto.
Qed.

Lemma notin_fv_cvt_wf : forall E (X : atom) T,
  wf_vtyp E T ->
  X `notin` dom E ->
  X `notin` fv_cvt T
with notin_fv_cbt_wf : forall E (X : atom) T,
  wf_btyp E T ->
  X `notin` dom E ->
  X `notin` fv_cbt T.
Proof with eauto using notin_fv_cap_wf.
------
  intros * Wf.
  induction Wf; intros Fr; simpl...
------
  intros * Wf.
  induction Wf; intros Fr; simpl...
  - rewrite AtomSetFacts.union_iff; intros N; destruct N.
    + destruct (notin_fv_cbt_wf _ _ _ Wf Fr)...
    + pick fresh Y.
      specialize (H Y ltac:(notin_solve)).
      revert H0.
      eapply notin_fv_cvt_open_cvt_rec...
  - pick fresh Y.
    specialize (H0 Y ltac:(notin_solve) ltac:(simpl_env; notin_solve)).
    eapply notin_fv_cbt_open_tbt_rec...
Qed.

Lemma subst_cvt_fresh_wf_vtyp : forall T x C,
  wf_vtyp empty T ->
  T = subst_cvt x C T.
Proof with eauto.
  intros * Wf.
  rewrite <- subst_cvt_fresh; trivial.
  eapply notin_fv_cvt_wf...
Qed.

Lemma wf_cset_in_dom : forall E C,
  wf_cap E C ->
  cset_fvars C `subset` dom E.
Proof with eauto.
  intros.
  inversion H; subst; simpl in *...
  unfold all_tracked in H0...
  intros elem Helem. specialize (H0 elem Helem)...
  inversion H0 as [T Hbinds].
  eapply binds_In...
Qed.

Lemma map_subst_cvt_id : forall G Z P,
  wf_env G ->
  Z `notin` dom G ->
  G = map (subst_bbind Z P) G.
 Proof with eauto.
  intros G Z P H.
  induction H; simpl; intros Fr; simpl_env;
    try solve [rewrite <- IHwf_env; eauto]...
  - rewrite <- IHwf_env...
    rewrite <- subst_cvt_fresh...
    eapply notin_fv_cvt_wf...
  - rewrite <- IHwf_env...
    rewrite <- subst_cbt_fresh...
    eapply notin_fv_cbt_wf...
  - rewrite <- IHwf_env...
    rewrite <- subst_cbt_fresh...
    repeat f_equal...
    apply subst_cset_fresh...
    * unshelve epose proof (wf_cset_in_dom E C _)...
    (* notin_fv_cbt lemma *)
    * eapply notin_fv_cbt_wf...
Qed.

Ltac convert_binds_to_in :=
  multimatch goal with
  | H : binds _ _ _ |- _ =>
    apply binds_In in H
  end.

Ltac pick_fresh_fill :=
  let Y := fresh "Y" in
  pick fresh Y;
  repeat match goal with
  | H : forall (y : atom), @?P y |- _ =>
    match P with
    | (fun (y : atom) => y `notin` _ -> _) => specialize (H Y ltac:(notin_solve))
    end
  end.

Ltac notin_clear :=
  repeat match goal with
  | H : _ `notin` _ -> _ |- _ => specialize (H ltac:(notin_solve))
  end.

Lemma notin_union_split : forall x a1 a2,
  x `notin` (a1 `union` a2) <-> x `notin` a1 /\ x `notin` a2.
Proof.
  intros; split; fsetdec.
Qed.

Ltac split_hyps :=
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.

Lemma notin_fv_ee_opened_ee : forall x k s1 s2,
  x `notin` fv_ee s1 ->
  x `notin` fv_ee s2 ->
  x `notin` fv_ee (open_ee_rec k s2 s1)
with notin_fv_es_opened_es : forall x k s1 s2,
  x `notin` fv_es s1 ->
  x `notin` fv_ee s2 ->
  x `notin` fv_es (open_es_rec k s2 s1)
with notin_fv_eb_opened_eb : forall x k s1 s2,
  x `notin` fv_eb s1 ->
  x `notin` fv_ee s2 ->
  x `notin` fv_eb (open_eb_rec k s2 s1).
Proof with eauto.
------
  intros * Frs1 Frs2. generalize dependent k.
  induction s1; intros k; simpl; f_equal...
  destruct (k === n)...
------
  intros * Frs1 Frs2. generalize dependent k.
  induction s1; intros k; simpl; f_equal; notin_clear; simpl in *...
------
  intros * Frs1 Frs2. generalize dependent k.
  induction s1; intros k; simpl; f_equal...
Qed.

Lemma notin_fv_be_opened_be : forall x k s1 s2,
  x `notin` fv_be s1 ->
  x `notin` fv_bb s2 ->
  x `notin` fv_be (open_be_rec k s2 s1)
with notin_fv_bs_opened_bs : forall x k s1 s2,
  x `notin` fv_bs s1 ->
  x `notin` fv_bb s2 ->
  x `notin` fv_bs (open_bs_rec k s2 s1)
with notin_fv_bb_opened_bb : forall x k s1 s2,
  x `notin` fv_bb s1 ->
  x `notin` fv_bb s2 ->
  x `notin` fv_bb (open_bb_rec k s2 s1).
Proof with eauto.
------
  intros * Frs1 Frs2. generalize dependent k.
  induction s1; intros k; simpl; f_equal...
------
  intros * Frs1 Frs2. generalize dependent k.
  induction s1; intros k; simpl; f_equal; notin_clear; simpl in *...
------
  intros * Frs1 Frs2. generalize dependent k.
  induction s1; intros k; simpl; f_equal...
  destruct (k === n)...
Qed.

Lemma notin_fv_be_opened_ee : forall x k s1 s2,
  x `notin` fv_be s1 ->
  x `notin` fv_be s2 ->
  x `notin` fv_be (open_ee_rec k s2 s1)
with notin_fv_bs_opened_es : forall x k s1 s2,
  x `notin` fv_bs s1 ->
  x `notin` fv_be s2 ->
  x `notin` fv_bs (open_es_rec k s2 s1)
with notin_fv_bb_opened_eb : forall x k s1 s2,
  x `notin` fv_bb s1 ->
  x `notin` fv_be s2 ->
  x `notin` fv_bb (open_eb_rec k s2 s1).
Proof with eauto.
------
  intros * Frs1 Frs2. generalize dependent k.
  induction s1; intros k; simpl; f_equal...
  destruct (k === n)...
------
  intros * Frs1 Frs2. generalize dependent k.
  induction s1; intros k; simpl; f_equal; notin_clear; simpl in *...
------
  intros * Frs1 Frs2. generalize dependent k.
  induction s1; intros k; simpl; f_equal...
Qed.

Lemma notin_fv_ee_open_ce : forall x k s1 C s2,
  x `notin` fv_ee (open_ce_rec k s2 C s1) ->
  x `notin` fv_ee s1
with notin_fv_es_open_cs : forall x k s1 C s2,
  x `notin` fv_es (open_cs_rec k s2 C s1) ->
  x `notin` fv_es s1
with notin_fv_eb_open_cb : forall x k s1 C s2,
  x `notin` fv_eb (open_cb_rec k s2 C s1) ->
  x `notin` fv_eb s1.
Proof with eauto.
------
  intros * Fr1. generalize dependent k.
  induction s1; simpl in *...
------
  intros * Fr1. generalize dependent k.
  induction s1; intros k Fr; simpl in *;
    try rewrite notin_union_split in *; split_hyps; try split...
------
  intros * Fr1. generalize dependent k.
  induction s1; simpl in *...
Qed.

Lemma notin_fv_be_open_ce : forall x k s1 C s2,
  x `notin` fv_be (open_ce_rec k s2 C s1) ->
  x `notin` fv_be s1
with notin_fv_bs_open_cs : forall x k s1 C s2,
  x `notin` fv_bs (open_cs_rec k s2 C s1) ->
  x `notin` fv_bs s1
with notin_fv_bb_open_cb : forall x k s1 C s2,
  x `notin` fv_bb (open_cb_rec k s2 C s1) ->
  x `notin` fv_bb s1.
Proof with eauto.
------
  intros * Fr1. generalize dependent k.
  induction s1; simpl in *...
------
  intros * Fr1. generalize dependent k.
  induction s1; intros k Fr; simpl in *;
    try rewrite notin_union_split in *; split_hyps; try split...
------
  intros * Fr1. generalize dependent k.
  induction s1; simpl in *...
Qed.


Lemma notin_fv_ee_open_ee : forall x k s1 s2,
  x `notin` fv_ee (open_ee_rec k s2 s1) ->
  x `notin` fv_ee s1
with notin_fv_es_open_es : forall x k s1 s2,
  x `notin` fv_es (open_es_rec k s2 s1) ->
  x `notin` fv_es s1
with  notin_fv_eb_open_eb : forall x k s1 s2,
  x `notin` fv_eb (open_eb_rec k s2 s1) ->
  x `notin` fv_eb s1.
Proof with eauto.
------
  intros * Fr1. generalize dependent k.
  induction s1; simpl in *...
------
  intros * Fr1. generalize dependent k.
  induction s1; intros k Fr; simpl in *;
    try rewrite notin_union_split in *; split_hyps; try split...
------
  intros * Fr1. generalize dependent k.
  induction s1; simpl in *...
Qed.

Lemma notin_fv_be_open_ee : forall x k s1 s2,
  x `notin` fv_be (open_ee_rec k s2 s1) ->
  x `notin` fv_be s1
with notin_fv_bs_open_es : forall x k s1 s2,
  x `notin` fv_bs (open_es_rec k s2 s1) ->
  x `notin` fv_bs s1
with  notin_fv_bb_open_eb : forall x k s1 s2,
  x `notin` fv_bb (open_eb_rec k s2 s1) ->
  x `notin` fv_bb s1.
Proof with eauto.
------
  intros * Fr1. generalize dependent k.
  induction s1; simpl in *...
------
  intros * Fr1. generalize dependent k.
  induction s1; intros k Fr; simpl in *;
    try rewrite notin_union_split in *; split_hyps; try split...
------
  intros * Fr1. generalize dependent k.
  induction s1; simpl in *...
Qed.


Lemma notin_fv_be_open_be : forall x k s1 s2,
  x `notin` fv_be (open_be_rec k s2 s1) ->
  x `notin` fv_be s1
with notin_fv_bs_open_bs : forall x k s1 s2,
  x `notin` fv_bs (open_bs_rec k s2 s1) ->
  x `notin` fv_bs s1
with  notin_fv_bb_open_bb : forall x k s1 s2,
  x `notin` fv_bb (open_bb_rec k s2 s1) ->
  x `notin` fv_bb s1.
Proof with eauto.
------
  intros * Fr1. generalize dependent k.
  induction s1; simpl in *...
------
  intros * Fr1. generalize dependent k.
  induction s1; intros k Fr; simpl in *;
    try rewrite notin_union_split in *; split_hyps; try split...
------
  intros * Fr1. generalize dependent k.
  induction s1; simpl in *...
Qed.

Lemma notin_fv_ee_open_be : forall x k s1 s2,
  x `notin` fv_ee (open_be_rec k s2 s1) ->
  x `notin` fv_ee s1
with notin_fv_es_open_bs : forall x k s1 s2,
  x `notin` fv_es (open_bs_rec k s2 s1) ->
  x `notin` fv_es s1
with  notin_fv_eb_open_bb : forall x k s1 s2,
  x `notin` fv_eb (open_bb_rec k s2 s1) ->
  x `notin` fv_eb s1.
Proof with eauto.
------
  intros * Fr1. generalize dependent k.
  induction s1; simpl in *...
------
  intros * Fr1. generalize dependent k.
  induction s1; intros k Fr; simpl in *;
    try rewrite notin_union_split in *; split_hyps; try split...
------
  intros * Fr1. generalize dependent k.
  induction s1; simpl in *...
Qed.

Lemma notin_fv_ee_open_te : forall x k T s,
  x `notin` fv_ee (open_te_rec k T s) ->
  x `notin` fv_ee s
with notin_fv_es_open_ts : forall x k T s,
  x `notin` fv_es (open_ts_rec k T s) ->
  x `notin` fv_es s
with  notin_fv_eb_open_tb : forall x k T s,
  x `notin` fv_eb (open_tb_rec k T s) ->
  x `notin` fv_eb s.
Proof with eauto.
------
  intros * Fr1. generalize dependent k.
  induction s; simpl in *...
------
  intros * Fr1. generalize dependent k.
  induction s; intros k Fr; simpl in *;
    try rewrite notin_union_split in *; split_hyps; try split...
------
  intros * Fr1. generalize dependent k.
  induction s; simpl in *...
Qed.

Lemma notin_fv_ee_etyping : forall E Q e T x,
  E ; Q |-exp e ~: T ->
  x `notin` dom E ->
  x `notin` fv_ee e
with notin_fv_es_styping : forall E R Q e T x,
  E @ R ; Q |-stm e ~: T ->
  x `notin` dom E ->
  x `notin` fv_es e
with notin_fv_eb_btyping : forall E R Q e T x,
  E @ R ; Q |-blk e ~: T ->
  x `notin` dom E ->
  x `notin` fv_eb e.
Proof with eauto.
------
  intros * Typing Fr.
  induction Typing; simpl in *...
  convert_binds_to_in. fsetdec.
------
  intros * Typing Fr.
  induction Typing; simpl in *; try notin_solve...
  * pick_fresh_fill; simpl_env in *.
    notin_clear. unfold open_es in *.
    eapply notin_fv_es_open_es in H0.
    notin_solve.
  * pick_fresh_fill; simpl_env in *.
    notin_clear. unfold open_bs in *.
    eapply notin_fv_es_open_bs in H2.
    eapply notin_fv_eb_btyping with (x := x) in H0; notin_solve.
  * pick_fresh_fill. pick_fresh_fill. simpl_env in *.
    notin_clear.
    eapply notin_fv_es_open_bs in H5.
    eapply notin_fv_es_open_es in H5.
    eapply notin_fv_es_open_cs in H3.
    notin_solve.
  * pick_fresh_fill. pick_fresh_fill. simpl_env in *.
    notin_clear.
    eapply notin_fv_es_open_bs in H4.
    eapply notin_fv_es_open_es in H4.
    notin_solve.
------
  intros * Typing Fr.
  induction Typing; simpl in *...
  * pick_fresh_fill; simpl_env in *.
    eapply notin_fv_es_styping with (x := x) in H.
    eapply notin_fv_es_open_es in H...
    simpl...
  * pick_fresh_fill; simpl_env in *.
    eapply notin_fv_es_styping with (x := x) in H...
    eapply notin_fv_es_open_cs in H...
  * pick_fresh_fill; simpl_env in *...
    notin_clear.
    eapply notin_fv_eb_open_tb in H0...
Qed.


Lemma notin_fv_be_open_te : forall x k T s,
  x `notin` fv_be (open_te_rec k T s) ->
  x `notin` fv_be s
with notin_fv_bs_open_ts : forall x k T s,
  x `notin` fv_bs (open_ts_rec k T s) ->
  x `notin` fv_bs s
with  notin_fv_bb_open_tb : forall x k T s,
  x `notin` fv_bb (open_tb_rec k T s) ->
  x `notin` fv_bb s.
Proof with eauto.
------
  intros * Fr1. generalize dependent k.
  induction s; simpl in *...
------
  intros * Fr1. generalize dependent k.
  induction s; intros k Fr; simpl in *;
    try rewrite notin_union_split in *; split_hyps; try split...
------
  intros * Fr1. generalize dependent k.
  induction s; simpl in *...
Qed.


Lemma notin_fv_be_etyping : forall E Q e T x,
  E ; Q |-exp e ~: T ->
  x `notin` dom E ->
  x `notin` fv_be e
with notin_fv_bs_styping : forall E R Q e T x,
  E @ R ; Q |-stm e ~: T ->
  x `notin` dom E ->
  x `notin` fv_bs e
with notin_fv_bb_btyping : forall E R Q e T x,
  E @ R ; Q |-blk e ~: T ->
  x `notin` dom E ->
  x `notin` fv_bb e.
Proof with eauto.
------
  intros * Typing Fr.
  induction Typing; simpl in *...
------
  intros * Typing Fr.
  induction Typing; simpl in *; try notin_solve...
  * pick_fresh_fill; simpl_env in *.
    notin_clear. unfold open_es in *.
    eapply notin_fv_bs_open_es in H0.
    notin_solve.
  * pick_fresh_fill; simpl_env in *.
    notin_clear. unfold open_bs in *.
    eapply notin_fv_bs_open_bs in H2.
    eapply notin_fv_bb_btyping with (x := x) in H0; notin_solve.
  * pick_fresh_fill. pick_fresh_fill. simpl_env in *.
    notin_clear.
    eapply notin_fv_bs_open_bs in H5.
    eapply notin_fv_bs_open_es in H5.
    eapply notin_fv_bs_open_cs in H3.
    notin_solve.
  * pick_fresh_fill. pick_fresh_fill. simpl_env in *.
    notin_clear.
    eapply notin_fv_bs_open_bs in H4.
    eapply notin_fv_bs_open_es in H4.
    notin_solve.
------
  intros * Typing Fr.
  induction Typing; simpl in *...
  * pick_fresh_fill; simpl_env in *.
    convert_binds_to_in...
  * pick_fresh_fill; simpl_env in *.
    convert_binds_to_in...
  * pick_fresh_fill; simpl_env in *.
    eapply notin_fv_bs_styping with (x := x) in H; try notin_solve.
    apply notin_fv_bs_open_es in H...
  * pick_fresh_fill; simpl_env in *.
    eapply notin_fv_bs_styping with (x := x) in H; try notin_solve.
    apply notin_fv_bs_open_cs in H...
  * pick_fresh_fill; simpl_env in *.
    notin_clear.
    eapply notin_fv_bb_open_tb in H0...
Qed.


Lemma notin_fv_tvt_open_cvt_rec : forall (Y X : atom) k T,
  X `notin` fv_tvt (open_cvt_rec k (cset_fvar Y) T) ->
  X `notin` fv_tvt T
with notin_fv_tbt_open_cbt_rec : forall (Y X : atom) k T,
  X `notin` fv_tbt (open_cbt_rec k (cset_fvar Y) T) ->
  X `notin` fv_tbt T.
Proof with auto.
------
  intros Y X k T. generalize dependent k.
  induction T; simpl; intros k Fr; notin_simpl; try apply notin_union; eauto.
------
  intros Y X k T. generalize dependent k.
  induction T; simpl; intros k Fr; notin_simpl; try apply notin_union; eauto.
Qed.

Lemma notin_fv_tvt_open_tvt_rec : forall (Y X : atom) k T,
  X `notin` fv_tvt (open_tvt_rec k Y T) ->
  X `notin` fv_tvt T
with notin_fv_tbt_open_tbt_rec : forall (Y X : atom) k T,
  X `notin` fv_tbt (open_tbt_rec k Y T) ->
  X `notin` fv_tbt T.
Proof with auto.
------
  intros Y X k T. generalize dependent k.
  induction T; simpl; intros k Fr; notin_simpl; try apply notin_union; eauto.
------
  intros Y X k T. generalize dependent k.
  induction T; simpl; intros k Fr; notin_simpl; try apply notin_union; eauto.
Qed.

Lemma notin_fv_tvt_wf : forall E (X : atom) T,
  wf_vtyp E T ->
  X `notin` dom E ->
  X `notin` fv_tvt T
with notin_fv_tbt_wf : forall E (X : atom) T,
  wf_btyp E T ->
  X `notin` dom E ->
  X `notin` fv_tbt T.
Proof with eauto.
------
  intros * Wf.
  induction Wf; intros Fr; simpl...
    convert_binds_to_in...
------
  intros * Wf.
  induction Wf; intros Fr; simpl; eauto.
  - rewrite AtomSetFacts.union_iff; intros N; destruct N.
    + notin_clear...
    + pick fresh Y.
      specialize (H Y ltac:(notin_solve)).
      revert H0.
      eapply notin_fv_tvt_open_cvt_rec...
  - pick fresh Y.
    specialize (H0 Y ltac:(notin_solve) ltac:(simpl_env; notin_solve)).
    eapply notin_fv_tbt_open_tbt_rec...
Qed.

Lemma map_subst_tbind_id : forall G Z P,
  wf_env G ->
  Z `notin` dom G ->
  G = map (subst_tbind Z P) G.
Proof with eauto using notin_fv_tvt_wf, notin_fv_tbt_wf; try notin_solve.
  intros G Z P H.
  induction H; simpl; intros Fr; simpl_env...
  rewrite <- IHwf_env...
    rewrite <- subst_tvt_fresh...
    rewrite <- IHwf_env...
  rewrite <- IHwf_env...
    rewrite <- subst_tbt_fresh...
  rewrite <- IHwf_env...
    rewrite <- subst_tbt_fresh...
Qed.

Lemma wf_cap_subst_tbind : forall F E Z P C,
  wf_cap (F ++ [(Z, bind_typ)] ++ E) C ->
  wf_vtyp E P ->
  ok (F ++ E) ->
  wf_cap (map (subst_tbind Z P) F ++ E) C.
Proof with simpl_env; eauto.
  intros * WfC WfP Ok.
  inversion WfC; econstructor; subst...
  intros x xIn.
  specialize (H x xIn) as [T Binds].
  binds_cases Binds...
  * exists (subst_tbt Z P T)...
    eapply (binds_map _ _ _ _ (subst_tbind Z P)) in H0...
Qed.

Lemma wf_vtyp_subst_tbind : forall F E Z P T,
  wf_vtyp (F ++ [(Z, bind_typ)] ++ E) T ->
  wf_vtyp E P ->
  ok (F ++ E) ->
  wf_vtyp (map (subst_tbind Z P) F ++ E) (subst_tvt Z P T)
with wf_btyp_subst_tbind : forall F E Z P T,
  wf_btyp (F ++ [(Z, bind_typ)] ++ E) T ->
  wf_vtyp E P ->
  ok (F ++ E) ->
  wf_btyp (map (subst_tbind Z P) F ++ E) (subst_tbt Z P T).
Proof with simpl_env; eauto using wf_btyp_weaken_head, wf_vtyp_weaken_head,
  vtype_from_wf_vtyp, btype_from_wf_btyp, wf_cap_subst_tbind.
------
  intros *.
  intros WfT WfP Ok.
  dependent induction WfT; subst; simpl subst_tvt; f_equal...
  + Case "typ_var".
    destruct (X == Z)...
    binds_cases H...
    apply wf_typ_var...
    eapply (binds_map _ _ _ _ (subst_tbind Z P)) in H1...
------
  intros *.
  intros WfT WfP Ok.
  dependent induction WfT; subst; simpl subst_tvt; simpl subst_tbt; f_equal...
  + Case "wf_typ_bfun".
    pick fresh Y and apply wf_typ_bfun...
    rewrite subst_tvt_open_cvt_var...
    rewrite_env (
      (map (subst_tbind Z P) ([(Y, bind_blk S1 tracked)] ++ F)) ++ E).
    apply wf_vtyp_subst_tbind...
  + Case "wf_typ_tfun".
    pick fresh Y and apply wf_typ_tfun...
    rewrite subst_tbt_open_tbt_var...
    rewrite_env (
      (map (subst_tbind Z P) ([(Y, bind_typ)] ++ F)) ++ E).
    apply H0...
Qed.

Lemma wf_env_subst_tbind : forall X U E F,
  wf_env (F ++ [(X, bind_typ)] ++ E) ->
  wf_vtyp E U ->
  wf_env (map (subst_tbind X U) F ++ E).
Proof with eauto 6 using wf_vtyp_subst_tbind, wf_btyp_subst_tbind, wf_cap_subst_tbind.
  induction F; intros Wf_env WU; simpl_env;
  inversion Wf_env; simpl_env in *; simpl subst_tbind...
  all: constructor...
  all: apply ok_from_wf_env in H1...
Qed.


Lemma wf_typ_open : forall E U T,
  ok E ->
  wf_btyp E (typ_tfun T) ->
  wf_vtyp E U ->
  wf_btyp E (open_tbt T U).
Proof with simpl_env; eauto*.
  intros * Ok WfT WfU. inversion WfT; subst...
  pick fresh X.
  rewrite (subst_tbt_intro X)...
  rewrite_env (map (subst_tbind X U) empty ++ E).
  eapply wf_btyp_subst_tbind...
Qed.

(* ********************************************************************** *)
(** * #<a name="regularity"></a># Regularity of relations *)

Ltac solve_regular := simpl_env; eauto using
  wf_vtyp_from_binds_typ,
  wf_vtyp_from_sig_binds_val,
  wf_vtyp_from_sig_binds,
  wf_btyp_from_binds_blk,
  capt_from_wf_cap,
  wf_cap_subset.

Lemma etyping_regular : forall E Q e T,
  E ; Q |-exp e ~: T ->
  wf_env E /\ expr e /\ wf_vtyp E T /\ wf_sig Q
with btyping_regular : forall E R Q (b : blk) S,
  E @ R ; Q |-blk b ~: S ->
  wf_env E /\ block b /\ wf_btyp E S /\ wf_cap E R /\ wf_sig Q
with styping_regular : forall E R Q s T,
  E @ R ; Q |-stm s ~: T ->
  wf_env E /\ stmt s /\ wf_vtyp E T /\ wf_cap E R /\ wf_sig Q.
Proof with solve_regular.
------
  intros * H; induction H; try solve [repeat split; solve_regular].
  - Case "box".
    destruct (btyping_regular _ _ _ _ _ H0) as [WfEnv [Block [WfS1 [WfRes WfSig]]]].
    repeat split...
------
  intros * H; induction H; try solve [repeat split; solve_regular].
  - Case "unbox".
    destruct (etyping_regular _ _ _ _ H) as [WfEnv [Block [WfS1 WfSig]]].
    repeat split...
    inversion WfS1...
  - Case "vfun".
    pick fresh y.
    destruct (styping_regular _ _ _ _ _ (H y ltac:(notin_solve))) as [WfEnv [Block [WfS1 [WfRes WfSig]]]].
    inversion WfEnv; subst...
    repeat split...
    + pick fresh z and apply block_vabs.
      eauto using vtype_from_wf_vtyp.
      destruct (styping_regular _ _ _ _ _ (H z ltac:(notin_solve))) as [_ [SBlock [_ _]]]...
    + apply wf_typ_vfun...
      rewrite_env (empty ++ E).
      eapply wf_vtyp_strengthening...
    + rewrite_env (empty ++ E).
      eapply wf_cap_strengthening...
  - Case "bfun".
    pick fresh y.
    destruct (styping_regular _ _ _ _ _ (H y ltac:(notin_solve))) as [WfEnv [Block [WfS1 [WfRes WfSig]]]].
    inversion WfEnv; subst...
    repeat split; try assumption.
    + pick fresh z and apply block_babs.
      eauto using btype_from_wf_btyp.
      destruct (styping_regular _ _ _ _ _ (H z ltac:(notin_solve))) as [_ [SBlock [_ _]]]...
    + pick fresh z and apply wf_typ_bfun; trivial.
      destruct (styping_regular _ _ _ _ _ (H z ltac:(notin_solve))) as [_ [_ [Typ _]]]...
    + inversion WfRes; subst; unfold cset_union, cset_fvar, all_tracked in *; destruct R;
        subst; simpl in *; autorewrite with csets in *; subst...
      constructor; intros x xInT.
      pick fresh z.
      destruct (styping_regular _ _ _ _ _ (H z ltac:(notin_solve))) as [_ [_ [_ [Res _]]]].
      assert (z <> x) by fsetdec.
      clear Fr.
      inversion Res; subst...
      destruct (H7 x ltac:(fsetdec)) as [T Binds].
      simpl_env in *. binds_cases Binds...
  - Case "tfun".
    pick fresh y.
    destruct (btyping_regular _ _ _ _ _ (H y ltac:(notin_solve))) as [WfEnv [Block [WfS1 [WfRes WfSig]]]].
    inversion WfEnv; subst...
    repeat split; try assumption.
    + pick fresh z and apply block_tabs...
      destruct (btyping_regular _ _ _ _ _ (H z ltac:(notin_solve))) as [_ [SBlock [_ _]]]...
    + pick fresh z and apply wf_typ_tfun...
      destruct (btyping_regular _ _ _ _ _ (H z ltac:(notin_solve))) as [_ [_ [STyp _]]]...
    + rewrite_env (empty ++ [(y, bind_typ)] ++ E) in WfRes.
      apply wf_cap_strengthening_typ in WfRes...
  - Case "tapp".
    repeat split; try intuition.
    * econstructor...
      eauto using vtype_from_wf_vtyp.
    * apply wf_typ_open...
  - repeat split...
    constructor;
    rewrite_env (empty ++ E ++ empty); apply wf_vtyp_weakening...
------
  intros * H; induction H; try solve [repeat split; solve_regular].
  - destruct (etyping_regular _ _ _ _ H) as [WfEnv [Block [WfS1 WfSig]]].
    repeat split...
  - destruct IHstyping as [WfEnv [Block [WfS1 [WfRes WfSig]]]].
    pick fresh z.
    destruct (H1 z ltac:(notin_solve)) as [_ [Block2 [WfS12 [WfRes2 WfSig2]]]].
    repeat split...
    pick fresh x and apply stmt_val...
    eauto using vtype_from_wf_vtyp.
    destruct (H1 x ltac:(notin_solve)) as [_ [Stmt [_ _]]]...
    (* by z notin T2 *)
    rewrite_env (empty ++ E).
    eapply wf_vtyp_strengthening...
  - destruct (btyping_regular _ _ _ _ _ H0) as [WfEnv [Block [WfS1 [WfRes WfSig]]]]...
    pick fresh z.
    destruct (H2 z ltac:(notin_solve)) as [_ [Block2 [WfS12 [WfRes2 WfSig2]]]].
    repeat split...
    + pick fresh y and apply stmt_def...
      eauto using btype_from_wf_btyp.
      destruct (H2 y ltac:(notin_solve)) as [_ [Stmt [_ _]]]...
    + rewrite_env (empty ++ E).
      eapply wf_vtyp_strengthening_blk...
    + rewrite_env (empty ++ E). (* by WfRes2 and z notin R *)
      eapply wf_cap_strengthening_blk...
  - destruct (btyping_regular _ _ _ _ _ H) as [WfEnv [Block [WfS1 [WfRes WfSig]]]].
    destruct (etyping_regular _ _ _ _ H0) as [_ [Expr [WfT1 WfSigT1]]].
    repeat split...
    inversion WfS1...
  - Case "bapp".
    (* this is the only interesting case... *)
    destruct (btyping_regular _ _ _ _ _ H1) as [WfEnv [Block [WfFun [WfRes WfSig]]]].
    destruct (btyping_regular _ _ _ _ _ H2) as [WfEnv2_ [Block2 [WfS1 _]]].
    repeat split...
    + inversion WfFun; subst.
      pick fresh x.
      specialize (H7 x ltac:(notin_solve)).
      (* like wf_typ_open_rt this needs a combi of subst_rt_fresh and wf_typ_subst_rb *)
      rewrite_env (map (subst_bbind x C) empty ++ E).
      replace (open_cvt T2 C) with (subst_cvt x C (open_cvt T2 (cset_fvar x))).
      eapply wf_vtyp_subst_tracked...
      symmetry.
      eapply subst_cvt_intro...
  - Case "try".
    pick fresh y.
    destruct (styping_regular _ _ _ _ _ (H2 y ltac:(notin_solve))) as [WfEnv [Block [WfS1 [WfRes WfSig]]]].
    inversion WfEnv; subst.
    repeat split; trivial...
    + pick fresh x and apply stmt_try...
      * eapply wf_btyp_from_binds_blk with (x := y) in WfEnv...
        apply btype_from_wf_btyp in WfEnv...
        inversion WfEnv...
      * eapply wf_btyp_from_binds_blk with (x := y) in WfEnv...
        apply btype_from_wf_btyp in WfEnv...
        inversion WfEnv...
      * destruct (H3 x ltac:(notin_solve)) as [Wf [StmtH [TypT CapR]]]...
      * intros kont Hfr.
        destruct (H5 x ltac:(notin_solve) kont ltac:(notin_solve)) as [Wf [StmtH [TypT CapR]]]...
    + pick fresh kont.
      destruct (H5 y ltac:(notin_solve) kont ltac:(notin_solve)) as [Wf [StmtH [TypT CapR]]]...
      rewrite_env (empty ++ ([(kont, bind_blk (typ_vfun T1 T) (capture C))] ++
        [(y, bind_val T2)]) ++ E) in TypT.
      eapply wf_vtyp_strengthening_blk in TypT...
      rewrite_env (empty ++ [(y, bind_val T2)] ++ E) in TypT.
      eapply wf_vtyp_strengthening in TypT...
  - Case "reset".
    pick fresh y.
    destruct IHstyping as [Wf [StmtB [TypT [CapRL WfSig]]]].
    repeat split...
    pick fresh x and apply stmt_reset...
    intros kont kontFr.
    solve using assumption and notin_solve.
  - destruct (btyping_regular _ _ _ _ _ H) as [WfEnv [Block [WfS1 [WfCap WfSig]]]].
    destruct (etyping_regular _ _ _ _ H0) as [WfEnvE [BlockE [WfsE]]].
    repeat split...
    inversion WfS1...
Qed.

Lemma typing_ctx_regular : forall R Q c T,
  (R ; Q |-ctx c ~: T) ->
  wf_cap empty R /\ wf_sig Q.
Proof with eauto*.
  intros * H.
  induction H...
  - split...
    constructor.
    intros ? ?.
    exfalso; fsetdec.
  - split...
    inversion H1; subst.
    unfold cset_union; csetsimpl.
    constructor...
Qed.

Lemma typing_cnt_regular : forall C Q c S T,
  (C ; Q |-cnt c ~: S ~> T) ->
  wf_cap empty C /\ wf_sig Q.
Proof with eauto.
  intros * H.
  induction H...
  - split...
    intuition.
Qed.

(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** The lemma [ok_from_wf_env] was already added above as a hint since it
    helps blur the distinction between [wf_env] and [ok] in proofs.

    As currently stated, the regularity lemmas are ill-suited to be
    used with [auto] and [eauto] since they end in conjunctions.  Even
    if we were, for example, to split [sub_regularity] into three
    separate lemmas, the resulting lemmas would be usable only by
    [eauto] and there is no guarantee that [eauto] would be able to
    find proofs effectively.  Thus, the hints below apply the
    regularity lemmas and [type_from_wf_typ] to discharge goals about
    local closure and well-formedness, but in such a way as to
    minimize proof search.

    The first hint introduces an [wf_env] fact into the context.  It
    works well when combined with the lemmas relating [wf_env] and
    [wf_typ].  We choose to use those lemmas explicitly via [(auto
    using ...)] tactics rather than add them as hints.  When used this
    way, the explicitness makes the proof more informative rather than
    more cluttered (with useless details).

    The other three hints try outright to solve their respective
    goals. *)

Hint Extern 1 (wf_env ?E) =>
  match goal with
  | H: etyping _ _ _ _ |- _ => apply (proj1 (etyping_regular _ _ _ _ H))
  | H: btyping _ _ _ _ _ |- _ => apply (proj1 (btyping_regular _ _ _ _ _ H))
  | H: styping _ _ _ _ _ |- _ => apply (proj1 (styping_regular _ _ _ _ _ H))
  end
: core.

Hint Extern 1 (wf_sig ?Q) =>
  match goal with
  | H: etyping _ _ _ _ |- _ => apply (proj2 (proj2 (proj2 (etyping_regular _ _ _ _ H))))
  | H: btyping _ _ _ _ _ |- _ => apply (proj2 (proj2 (proj2 (proj2 (btyping_regular _ _ _ _ _ H)))))
  | H: styping _ _ _ _ _ |- _ => apply (proj2 (proj2 (proj2 (proj2 (styping_regular _ _ _ _ _ H)))))
  | H: typing_ctx _ Q _ _ |- _ => apply (proj2 (typing_ctx_regular _ Q _ _ H))
  | H: typing_cnt _ Q _ _ _ |- _ => apply (proj2 (typing_cnt_regular _ Q _ _ _ H))
  end
: core.

Hint Extern 1 (wf_vtyp ?E ?T) =>
  match goal with
  | H: etyping E _ _ T |- _ => apply (proj2 (proj2 (etyping_regular _ _ _ _ H)))
  | H: styping E _ _ _ T |- _ => apply (proj2 (proj2 (styping_regular _ _ _ _ _ H)))
  end
: core.

Hint Extern 1 (wf_btyp ?E ?T) =>
  match goal with
  | H: btyping E _ _ _ T |- _ => apply (proj1 (proj2 (proj2 (btyping_regular _ _ _ _ _ H))))
  end
: core.

Hint Extern 1 (wf_cap ?E ?C) =>
  match goal with
  | H: btyping E C _ _ _ |- _ => apply (proj1 (proj2 (proj2 (proj2 (btyping_regular _ _ _ _ _ H)))))
  | H: styping E C _ _ _ |- _ => apply (proj1 (proj2 (proj2 (proj2 (styping_regular _ _ _ _ _ H)))))
  | H: typing_ctx C _ _ _ |- _ => apply (proj1 (typing_ctx_regular C _ _ _ H))
  | H: typing_cnt C _ _ _ _ |- _ => apply (proj1 (typing_cnt_regular C _ _ _ _ H))
  end
: core.

Hint Extern 1 (vtype ?T) =>
  let go E := apply (vtype_from_wf_vtyp E); auto in
  match goal with
  | H: etyping ?E _ _ T |- _ => go E
  | H: styping ?E _ _ _ T |- _ => go E
  end
: core.

Hint Extern 1 (btype ?T) =>
  let go E := apply (btype_from_wf_btyp E); auto in
  match goal with
  | H: btyping ?E _ _ _ T |- _ => go E
  end
: core.

Hint Extern 1 (expr ?e) =>
  match goal with
  | H: etyping _ _ ?e _ |- _ => apply (proj1 (proj2 (etyping_regular _ _ _ _ H)))
  end
: core.

Hint Extern 1 (block ?e) =>
  match goal with
  | H: btyping _ _ _ ?e _ |- _ => apply (proj1 (proj2 (btyping_regular _ _ _ _ _ H)))
  (* | H: bred ?e _ |- _ => apply (proj1 (bred_regular _ _ H))
  | H: bred _ ?e |- _ => apply (proj2 (bred_regular _ _ H)) *)
  end
: core.

Hint Extern 1 (stmt ?e) =>
  match goal with
  | H: styping _ _ _ ?e _ |- _ => apply (proj1 (proj2 (styping_regular _ _ _ _ _ H)))
  end
: core.


Local Lemma expr_regular_automation : forall E Q e T,
  E ; Q |-exp e ~: T ->
  wf_env E /\ expr e /\ wf_vtyp E T /\ wf_sig Q.
Proof with eauto.
  intros * lkH. repeat split...
Qed.

Local Lemma block_regular_automation : forall E R Q b S,
  E @ R ; Q |-blk b ~: S ->
  wf_env E /\ block b /\ wf_btyp E S /\ wf_cap E R /\ wf_sig Q.
Proof with eauto.
  intros * H. repeat split...
Qed.

Local Lemma stmt_regular_automation : forall E R Q s T,
  E @ R ; Q |-stm s ~: T ->
  wf_env E /\ stmt s /\ wf_vtyp E T /\ wf_cap E R /\ wf_sig Q.
Proof with eauto.
  intros * H. repeat split...
Qed.

Local Lemma typing_ctx_regular_automation : forall R Q c T,
  (R ; Q |-ctx c ~: T) ->
  wf_cap empty R /\ wf_sig Q.
Proof with eauto.
  intros * H. repeat split...
Qed.

Local Lemma typing_cnt_regular_automation : forall C S Q c T,
  (C ; Q |-cnt c ~: S ~> T) ->
  wf_cap empty C /\ wf_sig Q.
Proof with eauto.
  intros * H. repeat split...
Qed.

(** Extra Lemmas using automation concerning plug *)

Lemma notin_fv_es_plug : forall k e R C T1 T2 x,
  R ; C |-cnt k ~: T1 ~> T2 ->
  x `notin` fv_ee e ->
  x `notin` fv_es (plug k e).
Proof with eauto.
  intros * Typ Fr.
  dependent induction k; inversion Typ; simpl; subst...
  - pose proof (typing_cnt_regular _ _ _ _ _ Typ).
    epose proof (IHk e _ _ _ _ _ H3 Fr) as Hyp.
    assert (x `notin` fv_es s).
    {
      pick_fresh_fill; simpl_env in *.
      eapply notin_fv_es_open_es.
      eapply notin_fv_es_styping...
    }
    fsetdec.
  - epose proof (IHk e _ _ _ _ _ H2 Fr) as Hyp.
    assert (x `notin` fv_es h).
    {
      pick_fresh_fill; pick_fresh_fill; simpl_env in *.
      eapply notin_fv_es_open_es.
      eapply notin_fv_es_open_bs.
      eapply notin_fv_es_styping...
    }
    fsetdec.
Qed.

Lemma notin_fv_bs_plug : forall k e R C T1 T2 x,
  R ; C |-cnt k ~: T1 ~> T2 ->
  x `notin` fv_be e ->
  x `notin` fv_bs (plug k e).
Proof with eauto.
  intros * Typ Fr.
  dependent induction k; inversion Typ; simpl; subst...
  - pose proof (typing_cnt_regular _ _ _ _ _ Typ).
    epose proof (IHk e _ _ _ _ _ H3 Fr) as Hyp.
    assert (x `notin` fv_bs s).
    {
      pick_fresh_fill; simpl_env in *.
      eapply notin_fv_bs_open_es.
      eapply notin_fv_bs_styping...
    }
    fsetdec.
  - epose proof (IHk e _ _ _ _ _ H2 Fr) as Hyp.
    assert (x `notin` fv_bs h).
    {
      pick_fresh_fill; pick_fresh_fill; simpl_env in *.
      eapply notin_fv_bs_open_es.
      eapply notin_fv_bs_open_bs.
      eapply notin_fv_bs_styping...
    }
    fsetdec.
Qed.