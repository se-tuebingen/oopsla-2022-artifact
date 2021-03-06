(** #
<div class="source">
  The source of this file can be found on
  <a href="{{site.github}}/blob/main/coq/SystemC/Substitution.v">Github</a>.
</div>
# *)

Require Export Taktiks.
Require Export SystemC.Lemmas.

(**
 * Weakening
 ****************************************)

(** The standard lemmas for weakening the environment in typing. *)

Ltac solve_weakening := simpl_env;
  eauto 5 using wf_cap_weakening,
              wf_vtyp_weakening,
              wf_btyp_weakening,
              wf_cap_weaken_head,
              wf_vtyp_from_wf_env_typ,
              wf_btyp_from_wf_env_blk,
              wf_cap_subset,
              wf_cap_bind_head.

Lemma etyping_weakening : forall E F G Q e T,
  etyping (G ++ E) Q e T ->
  wf_env (G ++ F ++ E) ->
  etyping (G ++ F ++ E) Q e T
with btyping_weakening : forall E F G R Q e T,
  btyping (G ++ E) R Q e T ->
  wf_env (G ++ F ++ E) ->
  btyping (G ++ F ++ E) R Q e T
with styping_weakening : forall E F G R Q e T,
  styping (G ++ E) R Q e T ->
  wf_env (G ++ F ++ E) ->
  styping (G ++ F ++ E) R Q e T.
Proof with solve_weakening.
------
  intros * Typ Wf.
  dependent induction Typ ; try solve [ econstructor; solve_weakening ].
------
  intros * Typ Wf.
  dependent induction Typ.
  - try solve [ econstructor; solve_weakening ].
  - try solve [ econstructor; solve_weakening ].
  - try solve [ econstructor; solve_weakening ].
  (* try solve [ econstructor; solve_weakening ]. *)
  - Case "typing_vabs".
    pick fresh x and apply typing_vabs.
    lapply (H x); [intros K | auto].
    rewrite <- concat_assoc.
    eapply styping_weakening...
  - Case "typing_babs".
    pick fresh x and apply typing_babs.
    lapply (H x); [intros K | auto].
    rewrite <- concat_assoc.
    eapply styping_weakening...
  - Case "typing_tabs".
    pick fresh x and apply typing_tabs.
    lapply (H x); [intros K | auto].
    rewrite <- concat_assoc.
    eapply btyping_weakening...
  - Case "typing_tapp".
    (* This also takes too long to resolve with eauto, somehow. *)
    econstructor; trivial.
    apply wf_vtyp_weakening...
    apply btyping_weakening...
    (* Strangely this case causes a loop *)
  - constructor; trivial.
    apply wf_cap_weakening...
    apply wf_vtyp_weakening...
------
  intros * Typ Wf.
  dependent induction Typ.
  - econstructor...
  - pick fresh x and apply typing_val...
    rewrite <- concat_assoc.
    apply (H0 x)...
  - pick fresh x and apply typing_def...
    rewrite <- concat_assoc.
    apply (H2 x); try notin_solve; simpl_env.
    econstructor...
  - econstructor...
  - econstructor...
  - assert (wf_vtyp (G ++ F ++ E) T2) as WfT2. {
      pick fresh g.
      specialize (H2 g ltac:(notin_solve)).
      apply styping_regular in H2 as (? & _).
      inversion H2; subst.
      inversion select (wf_btyp _ (typ_eff T2 T1)).
      apply wf_vtyp_weakening...
    }
    assert (wf_vtyp (G ++ E) T) as WfT. {
      pick fresh g.
      specialize (H2 g ltac:(notin_solve)).
      apply styping_regular in H2 as (_ & _ & ? & _).
      rewrite_env (empty ++ (G ++ E)).
      (* since g notin fv T, from H2 *)
      eapply wf_vtyp_strengthening_blk_tracked with (x := g).
      (* fsetdec is really slow here *)
      * notin_solve.
      * trivial...
    }
    assert (wf_vtyp (G ++ E) T1) as WfT1. {
      pick fresh g.
      specialize (H2 g ltac:(notin_solve)).
      apply styping_regular in H2 as (WfEnv & _ & _ & _).
      apply wf_btyp_from_wf_env_blk in WfEnv...
      inversion WfEnv; subst...
    }
    pick fresh v and apply typing_try.
    1, 2, 3 : trivial...
    * rewrite <- concat_assoc.
      apply (H3 v)...
    * intros kont kontFr.
      rewrite <- concat_assoc.
      rewrite <- concat_assoc.
      eapply H5; try notin_solve; simpl_env.
      repeat (econstructor; simpl_env in *; try notin_solve).
      + apply wf_vtyp_weaken_head.
        apply wf_vtyp_weakening...
        econstructor; simpl_env in *; try notin_solve.
      + apply wf_vtyp_weaken_head.
        apply wf_vtyp_weakening...
        econstructor; simpl_env in *; try notin_solve.
      + apply wf_cap_weaken_head...
  - pick fresh handler and apply typing_reset...
    intros kont kontFr.
    rewrite_env (([(kont, bind_blk (typ_vfun T1 T) (capture C))] ++
                  [(handler, bind_val T2)] ++ G) ++ F ++ E).
    eapply H4...
    pose proof (styping_regular _ _ _ _ _ (H3 handler ltac:(notin_solve) kont ltac:(notin_solve))) as [Wf2 _]...
    assert (wf_vtyp (G ++ F ++ E) T2) as WfT2. {
      pick fresh g. pick fresh f.
      specialize (H3 g ltac:(notin_solve) f ltac:(notin_solve)).
      apply styping_regular in H3 as (WfEnv & _ & _ & _).
      inversion WfEnv...
    }
    assert (wf_vtyp ([(handler, bind_val T2)] ++ G ++ F ++ E) T1) as WfT1. {
      pick fresh f.
      specialize (H3 handler ltac:(notin_solve) f ltac:(notin_solve)).
      apply styping_regular in H3 as (WfEnv & _ & _ & _).
      apply wf_btyp_from_wf_env_blk in WfEnv...
      inversion WfEnv; subst.
      rewrite_env (([(handler, bind_val T2)] ++ G) ++ F ++ E).
      apply wf_vtyp_weakening...
    }
    assert (wf_vtyp ([(handler, bind_val T2)] ++ G ++ F ++ E) T) as WfT. {
      pick fresh f.
      specialize (H3 handler ltac:(notin_solve) f ltac:(notin_solve)).
      apply styping_regular in H3 as (WfEnv & _ & _ & _).
      apply wf_btyp_from_wf_env_blk in WfEnv...
      inversion WfEnv; subst.
      rewrite_env (([(handler, bind_val T2)] ++ G) ++ F ++ E).
      apply wf_vtyp_weakening...
    }
    assert (wf_cap ([(handler, bind_val T2)] ++ G ++ F ++ E) C) as WfC. {
      pick fresh f.
      specialize (H3 handler ltac:(notin_solve) f ltac:(notin_solve)).
      apply styping_regular in H3 as (WfEnv & _ & _ & _).
      inversion WfEnv; subst. simpl_env in *.
      rewrite_env (([(handler, bind_val T2)] ++ G) ++ F ++ E).
      apply wf_cap_weakening...
    }
    repeat (econstructor)...
  - econstructor...
Qed.

Lemma restriction_transitive : forall C1 C2 C3,
  C1 |= C2 ->
  C2 |= C3 ->
  C1 |= C3.
Proof.
  intros * Sub1 Sub2.
  unfold cset_subset_prop in *.
  repeat split; try fsetdec; try fnsetdec; try lsetdec.
Qed.

(**
 * Capture Subsumption
 ****************************************)

(** Here we show that capture subsumption on blocks and statements is admissible. *)
Lemma btyping_weaken_restriction : forall C E R Q b S1,
  R |= C ->
  wf_cap E R ->
  E @ C ; Q |-blk b ~: S1 ->
  E @ R ; Q |-blk b ~: S1
with styping_weaken_restriction : forall C E R Q s T,
  R |= C ->
  wf_cap E R ->
  E @ C ; Q |-stm s ~: T ->
  E @ R ; Q |-stm s ~: T.
Proof with solve_weakening; eauto using restriction_transitive.
------
  intros * Sub Wf Typ.
  assert (ok E) as Ok by auto.
  dependent induction Typ.
  - eapply typing_bvar_tracked...
  - eapply typing_bvar_capture with (C := C)...
  - eapply typing_unbox...
  - pick fresh x and apply typing_vabs...
  - pick fresh x and apply typing_babs...
    eapply styping_weaken_restriction with (C := cset_union R0 (cset_fvar x))...
  - pick fresh x and apply typing_tabs...
  - econstructor...
  - eapply typing_handler...
------
  intros * Sub Wf Typ.
  dependent induction Typ.
  - econstructor...
  - pick fresh x and apply typing_val...
  - pick fresh x and apply typing_def...
  - econstructor...
  - econstructor...
  - pick fresh x and apply typing_try...
  - econstructor...
  - econstructor...
Qed.


(**
 * #<a name="substitution"></a># Substitution
 ****************************************)

(** We show the standard property that substitution preserves typing. *)

Ltac solve_substitution := simpl_env; eauto 4 using
  wf_vtyp_strengthening,
  wf_btyp_strengthening,
  wf_env_strengthening,
  wf_cap_strengthening.

(** *** Substitution of expressions into terms *)

Lemma etyping_through_subst_ee : forall U E F Q x T e u,
  etyping (F ++ [(x, bind_val U)] ++ E) Q e T ->
  etyping E Q u U ->
  etyping (F ++ E) Q (subst_ee x u e) T
with btyping_through_subst_eb : forall U E F R Q x T e u,
  btyping (F ++ [(x, bind_val U)] ++ E) R Q e T ->
  etyping E Q u U ->
  btyping (F ++ E) R Q (subst_eb x u e) T
with styping_through_subst_es : forall U E F R Q x T e u,
  styping (F ++ [(x, bind_val U)] ++ E) R Q e T ->
  etyping E Q u U ->
  styping (F ++ E) R Q (subst_es x u e) T.
Proof with solve_substitution.
------
  intros * TypT TypU.
  dependent induction TypT.
  - econstructor...
  - simpl. destruct (x0 == x); subst.
    + select (binds x _ _) (fun H => binds_get H)...
      inversion select (bind_val _ = bind_val _); subst.
      rewrite_env (empty ++ F ++ E).
      apply etyping_weakening...
    + econstructor; try assumption.
      * eapply wf_env_strengthening; eassumption.
      * select (binds _ _ _) (fun H => binds_cases H)...
  - econstructor...
------
  intros * TypT TypU.
  dependent induction TypT.
  - simpl. destruct (f == x); subst.
    + select (binds _ _ _) (fun H => binds_get H).
    + econstructor...
  - simpl. destruct (f == x); subst.
    + select (binds _ _ _) (fun H => binds_get H).
    + eapply typing_bvar_capture...
  - econstructor...
  - pick fresh y and apply typing_vabs. fold subst_es.
    rewrite subst_es_open_es_var...
    rewrite <- concat_assoc.
    eapply styping_through_subst_es...
  - pick fresh y and apply typing_babs. fold subst_es.
    rewrite subst_es_open_cs_var...
    rewrite <- concat_assoc.
    eapply styping_through_subst_es...
  - pick fresh y and apply typing_tabs. fold subst_eb.
    erewrite subst_eb_open_tb_var...
    rewrite <- concat_assoc.
    eapply btyping_through_subst_eb...
  - simpl. econstructor...
  - simpl. econstructor...
------
  intros * TypT TypU.
  dependent induction TypT.
  - econstructor...
  - pick fresh y and apply typing_val; fold subst_es...
    rewrite subst_es_open_es_var...
    rewrite <- concat_assoc.
    eapply styping_through_subst_es...
  - pick fresh y and apply typing_def; fold subst_es...
    rewrite subst_es_open_bs_var...
    rewrite <- concat_assoc.
    eapply styping_through_subst_es...
  - econstructor...
  - econstructor...
  - pick fresh y and apply typing_try; fold subst_es...
    * rewrite subst_es_open_cs_var...
      rewrite <- concat_assoc.
      eapply styping_through_subst_es...
    * intros kont kontFr.
      rewrite <- concat_assoc.
      rewrite subst_es_open_es_var...
      rewrite <- concat_assoc.
      rewrite subst_es_open_bs_var...
      rewrite <- concat_assoc.
      rewrite <- concat_assoc.
      eapply styping_through_subst_es...
  - pick fresh y and apply typing_reset; fold subst_es...
    intros kont kontFr.
    rewrite subst_es_open_es_var...
    rewrite subst_es_open_bs_var...
    rewrite <- concat_assoc.
    rewrite <- concat_assoc.
    eapply styping_through_subst_es...
  - econstructor...
Qed.

Ltac solve_substitution_blk := simpl_env; eauto 4 using
  wf_vtyp_strengthening_blk,
  wf_btyp_strengthening_blk,
  wf_env_strengthening_blk,
  wf_cap_strengthening_blk.

(** *** Substitution of monomorphic blocks into terms *)
Lemma etyping_through_subst_be : forall U C E F Q x T e u,
  etyping (F ++ [(x, bind_blk U (capture C))] ++ E) Q e T ->
  btyping E C Q u U ->
  etyping (F ++ E) Q (subst_be x u e) T
with btyping_through_subst_bb : forall U C E F R Q x T e u,
  btyping (F ++ [(x, bind_blk U (capture C))] ++ E) R Q e T ->
  btyping E C Q u U ->
  btyping (F ++ E) R Q (subst_bb x u e) T
with styping_through_subst_bs : forall U C E F R Q x T e u,
  styping (F ++ [(x, bind_blk U (capture C))] ++ E) R Q e T ->
  btyping E C Q u U ->
  styping (F ++ E) R Q (subst_bs x u e) T.
Proof with solve_substitution_blk.
------
  intros * TypT TypU.
  dependent induction TypT.
  - econstructor...
  - simpl. destruct (x0 == x); subst.
    + select (binds _ _ _) (fun H => binds_get H)...
    + select (binds _ _ _) (fun H => binds_cases H); econstructor...
  - econstructor...
------
  intros * TypT TypU.
  dependent induction TypT.
  - simpl. destruct (f == x); subst.
    + select (binds _ _ _) (fun H => binds_get H)...
    + econstructor...
  - simpl. destruct (f == x); subst.
    + select (binds _ _ _) (fun H => binds_get H)...
      inversion select (bind_blk _ _ = bind_blk _ _); subst.
      eapply btyping_weaken_restriction...
      rewrite_env (empty ++ F ++ E).
      apply btyping_weakening...
    + eapply typing_bvar_capture...
  - econstructor...
  - pick fresh y and apply typing_vabs. fold subst_bs.
    rewrite subst_bs_open_es_var...
    rewrite <- concat_assoc.
    eapply styping_through_subst_bs...
  - pick fresh y and apply typing_babs. fold subst_bs.
    rewrite subst_bs_open_cs_var...
    rewrite <- concat_assoc.
    eapply styping_through_subst_bs...
  - pick fresh y and apply typing_tabs. fold subst_bb.
    rewrite subst_bb_open_tb_var...
    rewrite <- concat_assoc.
    eapply btyping_through_subst_bb...
  - econstructor...
  - econstructor...
------
  intros * TypT TypU.
  dependent induction TypT.
  - econstructor...
  - pick fresh y and apply typing_val; fold subst_es...
    rewrite subst_bs_open_es_var...
    rewrite <- concat_assoc.
    eapply styping_through_subst_bs...
  - pick fresh y and apply typing_def; fold subst_es...
    rewrite subst_bs_open_bs_var...
    rewrite <- concat_assoc.
    eapply styping_through_subst_bs...
  - econstructor...
  - econstructor...
  - pick fresh y and apply typing_try...
    rewrite subst_bs_open_cs_var...
    rewrite <- concat_assoc.
    eapply styping_through_subst_bs...
    intros kont kontFr.
    fold subst_bs.
    rewrite subst_bs_open_es_var...
    rewrite subst_bs_open_bs_var; try notin_solve.
    rewrite <- concat_assoc.
    rewrite <- concat_assoc.
    eapply styping_through_subst_bs...
  - pick fresh y and apply typing_reset...
    intros kont kontFr. fold subst_bs.
    rewrite subst_bs_open_es_var...
    rewrite subst_bs_open_bs_var; try notin_solve.
    rewrite <- concat_assoc.
    rewrite <- concat_assoc.
    eapply styping_through_subst_bs...
  - econstructor...
Qed.

Ltac solve_subst_tracked := simpl_env; eauto 4 using
  wf_env_subst_tracked,
  wf_cap_subst_tracked,
  subst_over_subset,
  subst_subset_intro,
  capt_from_wf_cap,
  wf_vtyp_from_sig_binds,
  wf_vtyp_from_sig_binds_val.

(** *** Substitution of polymorphic blocks into terms *)
Lemma etyping_through_subst_ce : forall (C : cap) U E F Q x T e u,
  etyping (F ++ [(x, bind_blk U tracked)] ++ E) Q e T ->
  wf_cap E C ->
  btyping E C Q u U ->
  etyping (map (subst_bbind x C) F ++ E) Q (subst_ce x u C e) (subst_cvt x C T)
with btyping_through_subst_cb : forall (C : cap) U E F R Q x T e u,
  btyping (F ++ [(x, bind_blk U tracked)] ++ E) R Q e T ->
  wf_cap E C ->
  btyping E C Q u U ->
  btyping (map (subst_bbind x C) F ++ E) (subst_cset x C R) Q (subst_cb x u C e) (subst_cbt x C T)
with styping_through_subst_cs : forall (C : cap) U E F R Q x T e u,
  styping (F ++ [(x, bind_blk U tracked)] ++ E) R Q e T ->
  wf_cap E C ->
  btyping E C Q u U ->
  styping (map (subst_bbind x C) F ++ E) (subst_cset x C R) Q (subst_cs x u C e) (subst_cvt x C T).
Proof with solve_subst_tracked.
------
  intros * TypT WfCap TypU.
  dependent induction TypT.
  - econstructor...
  - eapply typing_evar...
    binds_cases H1.
    + apply binds_tail...
      assert (x `notin` dom E). { eapply fresh_mid_tail... }
      assert (wf_vtyp E T). { eapply wf_vtyp_from_binds_typ... }
      rewrite <- subst_cvt_fresh; trivial.
      eapply notin_fv_cvt_wf...
    + replace (bind_val (subst_cvt x C T)) with (subst_bbind x C (bind_val T))...
  - apply typing_box; fold subst_cb subst_cbt...
------
  intros * TypT WfCap TypU.
  dependent induction TypT.
  - Case "poly vars".
    simpl subst_cb.
    destruct (f == x); subst.
    + SCase "it is the block var".
      assert (x `notin` dom E) as NotIn. { eapply fresh_mid_tail... }
      select (binds x _ _) (fun H => binds_cases H).
      * exfalso. eauto...
        select (binds x _ _) (fun H => apply binds_In in H). fsetdec.
      * inversion H3; subst.
        assert (wf_btyp E U). { eapply wf_btyp_from_wf_env_blk. eapply wf_env_tail... }
        select (wf_btyp _ _) (fun H => pose proof (notin_fv_cbt_wf _ _ _ H NotIn)).
        rewrite <- subst_cbt_fresh...
        apply btyping_weaken_restriction with (C := C)...
        rewrite_env (empty ++ map (subst_bbind x C) F ++ E).
        apply btyping_weakening...
        inversion select (bind_blk _ _ = _ _ _); subst...
      * exfalso. select (binds x _ _) (fun H => apply binds_In in H).
        assert (x `notin` dom F). { eapply fresh_mid_head... }
        fsetdec.
    + SCase "wrong variable".
      select (_ |= _) (fun H => pose proof (subst_over_subset _ _ C x H)).
      select (subst_cset _ _ _ |= subst_cset _ _ _)
        (fun H => rewrite subst_cset_fresh_id in H)...
      select (binds _ _ _) (fun H => binds_cases H).
      * eapply typing_bvar_tracked...
        apply binds_tail.
        assert (wf_btyp E S1). { eapply wf_btyp_from_binds_blk... }
        assert (x `notin` dom E) as NotIn. { eapply fresh_mid_tail... }
        assert (x `notin` fv_cbt S1). { eapply notin_fv_cbt_wf... }
        rewrite <- subst_cbt_fresh...
        rewrite dom_map...
      * eapply typing_bvar_tracked...
        replace
          (bind_blk (subst_cbt x C S1) tracked)
        with
          (subst_bbind x C (bind_blk S1 tracked))...
  - Case "mono vars".
      simpl subst_cb.
      destruct (f == x); subst.
      + SCase "it is the block var".
        select (binds x _ _) (fun H => binds_get H).
      + SCase "it is the block var".
        select (binds f _ _) (fun H => binds_cases H).
        * apply typing_bvar_capture with (C := (subst_cset x C C0))...
          apply binds_tail...
          assert (x `notin` dom E) as NotIn. { eapply fresh_mid_tail... }
          rewrite map_subst_cvt_id with (Z := x) (P := C)...
          replace (bind_blk (subst_cbt x C S1) (capture (subst_cset x C C0)))
          with (subst_bbind x C (bind_blk S1 (capture C0)))...
        * eapply typing_bvar_capture with (C := (subst_cset x C C0))...
          replace (bind_blk (subst_cbt x C S1) (capture (subst_cset x C C0)))
          with (subst_bbind x C (bind_blk S1 (capture C0)))...
  - Case "unbox". simpl subst_cb; simpl subst_ce.
    eapply typing_unbox with (C := subst_cset x C C0)...
    replace (typ_capt (subst_cbt x C S1) (subst_cset x C C0)) with (subst_cvt x C (typ_capt S1 C0)) by auto.
    eapply etyping_through_subst_ce...
  - Case "vabs".
    pick fresh y and apply typing_vabs.
    fold subst_cbt subst_cvt subst_cb subst_cs.
    rewrite subst_cs_open_es_var...
    rewrite_env (map (subst_bbind x C) ([(y, bind_val T1)] ++ F) ++ E).
    eapply styping_through_subst_cs...
  - Case "babs".
    pick fresh y and apply typing_babs.
    fold subst_cbt subst_cvt subst_cb subst_cs.
    rewrite subst_cs_open_cs_var...
    rewrite_env (map (subst_bbind x C) ([(y, bind_blk S1 tracked)] ++ F) ++ E).
    rewrite <- subst_cvt_open_cvt_var; eauto.
    rewrite <- subst_cset_union_id.
    eapply styping_through_subst_cs...
    trivial...
    trivial...
  - Case "tabs".
    pick fresh Y and apply typing_tabs.
    fold subst_cbt subst_cvt subst_cb subst_cs.
    rewrite subst_cb_open_tb_var...
    rewrite <- subst_cbt_open_tbt_var...
    rewrite_env (map (subst_bbind x C) ([(Y, bind_typ)] ++ F) ++ E).
    eapply btyping_through_subst_cb...
  - Case "tapp".
    simpl subst_cb; simpl subst_cbt.
    rewrite subst_cbt_open_tbt; try notin_solve...
    econstructor...
    eapply wf_vtyp_subst_tracked...
  - Case "handler".
    simpl.
    econstructor...
    eapply wf_vtyp_subst_tracked...
    select (wf_sig _) (fun H => eapply wf_vtyp_from_sig_binds in H as ?)...
    rewrite <- subst_cvt_fresh.
    rewrite <- subst_cvt_fresh.
    assumption.
    eapply notin_fv_cvt_wf...
    eapply notin_fv_cvt_wf with (E := empty)...
------
  intros * TypT WfCap TypU.
  dependent induction TypT.
  - econstructor...
  - pick fresh y and apply typing_val...
    fold subst_cbt subst_cvt subst_cb subst_cs.
    rewrite subst_cs_open_es_var...
    rewrite_env (map (subst_bbind x C) ([(y, bind_val T1)] ++ F) ++ E).
    eapply styping_through_subst_cs...
  - pick fresh y and apply typing_def; fold subst_cbt subst_cvt subst_cb subst_cs...
    + rewrite subst_cs_open_bs_var...
      rewrite_env (map (subst_bbind x C) ([(y, bind_blk S1 (capture C0))] ++ F) ++ E).
      eapply styping_through_subst_cs...
  - econstructor... fold subst_cbt subst_cvt subst_cb subst_cs.
    replace
      (typ_vfun (subst_cvt x C T1) (subst_cvt x C T2))
    with
      (subst_cbt x C (typ_vfun T1 T2))...
  - simpl.
    rewrite subst_cvt_open_cvt...
    eapply typing_bapp with (S1 := (subst_cbt x C S1))...
    replace
      (typ_bfun (subst_cbt x C S1) (subst_cvt x C T2))
    with
      (subst_cbt x C (typ_bfun S1 T2))...
  - Case "try".
    assert (wf_env (F ++ [(x, bind_blk U tracked)] ++ E)). {
      pick fresh g.
      specialize (H2 g ltac:(notin_solve)).
      apply styping_regular in H2 as (HWf & _).
      inversion HWf...
    }
    pick fresh y and apply typing_try...
    + fold subst_cbt subst_cvt subst_cb subst_cs.
      rewrite subst_cs_open_cs_var...
      rewrite_env (map (subst_bbind x C) ([(y, bind_blk (typ_eff T2 T1) tracked)] ++ F) ++ E).
      rewrite <- subst_cset_union_id.
      eapply styping_through_subst_cs...
      trivial...
    + fold subst_cbt subst_cvt subst_cb subst_cs.
      intros kont kontFr.
      rewrite subst_cs_open_es_var...
      rewrite subst_cs_open_bs_var; try notin_solve.
      rewrite_env (map (subst_bbind x C)
        ([(kont, bind_blk (typ_vfun T1 T) (capture C0))] ++
         [(y, bind_val T2) ]++ F) ++ E).
      eapply styping_through_subst_cs...
  - Case "reset".
    pick fresh y and apply typing_reset...

    + fold subst_cbt subst_cvt subst_cb subst_cs.
      replace
        (cset_union (subst_cset x C C0) (cset_lvar l))
      with
        (subst_cset x C (cset_union C0 (cset_lvar l))).
      eapply styping_through_subst_cs...
      csetsimpl.
    + intros kont kontFr.
      fold subst_cbt subst_cvt subst_cb subst_cs.
      rewrite subst_cs_open_es_var...
      rewrite subst_cs_open_bs_var; try notin_solve.

      replace ([(kont, bind_blk (typ_vfun T1 (subst_cvt x C T)) (capture (subst_cset x C C0)))] ++
        [(y, bind_val T2)] ++
        map (subst_bbind x C) F ++ E)
      with (map (subst_bbind x C) (([(kont, bind_blk (typ_vfun T1 T) (capture C0))] ++ [(y, bind_val T2)]) ++ F) ++ E).
      eapply styping_through_subst_cs...
      simpl; trivial.
      rewrite <- (subst_cvt_fresh_wf_vtyp T1)...
      rewrite <- (subst_cvt_fresh_wf_vtyp T2)...
  - Case "throw".
    econstructor...
    fold subst_cbt subst_cvt subst_cb subst_cs.
    replace (typ_eff (subst_cvt x C T1) (subst_cvt x C T)) with (subst_cbt x C (typ_eff T1 T))...
Qed.


Ltac solve_subst_type := simpl_env; eauto 4 using wf_env_subst_tbind, wf_vtyp_subst_tbind,
  wf_btyp_subst_tbind, wf_vtyp_from_binds_typ, wf_cap_subst_tbind,
  vtype_from_wf_vtyp, btype_from_wf_btyp.

(** *** Substitution of types into terms
    We use our own induction principle to speed up termination checking. *)
Lemma typing_through_subst_t_ : forall U E Q X,
(forall E_ Q_ e T,
  etyping E_ Q_ e T ->
  (forall F, E_ = F ++ [(X, bind_typ)] ++ E ->
   Q_ = Q ->
   wf_vtyp E U ->
   etyping ((map (subst_tbind X U) F) ++ E) Q (subst_te X U e) (subst_tvt X U T)))
/\
(forall E_ R Q_ e T,
  styping E_ R Q_ e T ->
  (forall F, E_ = F ++ [(X, bind_typ)] ++ E ->
   Q_ = Q ->
   wf_vtyp E U ->
   styping ((map (subst_tbind X U) F) ++ E) R Q (subst_ts X U e) (subst_tvt X U T)))
/\
(forall E_ R Q_ e T,
  btyping E_ R Q_ e T ->
  (forall F, E_ = F ++ [(X, bind_typ)] ++ E ->
   Q_ = Q ->
   wf_vtyp E U ->
   btyping ((map (subst_tbind X U) F) ++ E) R Q (subst_tb X U e) (subst_tbt X U T))).
Proof with solve_subst_type.
  intros.
  apply typing_ind; intros; subst;
    try rename select (etyping (F ++ _ ++ E) _ _ _) into ETyping;
    try rename select (btyping (F ++ _ ++ E) _ _ _ _) into BTyping;
    try rename select (styping (F ++ _ ++ E) _ _ _ _) into STyping;
    try rename select (wf_cap _ _) into WfCap;
    try rename select (wf_sig _) into WfSig;
    try pose proof (etyping_regular _ _ _ _ ETyping) as [WfEnv _];
    try pose proof (btyping_regular _ _ _ _ _ BTyping) as [WfEnv _];
    try pose proof (styping_regular _ _ _ _ _ STyping) as [WfEnv _];
    try rename select (wf_env _) into WfEnv;
    try rename select (binds _ _ _) into HBinds;
    try rename select (wf_vtyp _ _) into WfVTyp;
    try apply ok_from_wf_env in WfEnv as OkEnv.
  (* etyping *)
  - econstructor...
  - econstructor...
    binds_cases HBinds...
    * rewrite <- subst_tvt_fresh with (X := X) (U := U) (T := T).
      apply binds_tail...
      apply notin_fv_tvt_wf with (E := E).
      eapply wf_vtyp_from_binds_typ...
      eapply wf_env_tail...
      eapply fresh_mid_tail...
    * apply binds_head...
      eapply binds_map with (f := (subst_tbind X U)) in H0...
  - econstructor...
  (* styping *)
  - econstructor...
  - pick fresh x and apply typing_val...
    assert (exp_fvar x = subst_te X U x) as Xsubst...
    rewrite Xsubst...
    rewrite <- subst_ts_open_es...
    rewrite_env ((map (subst_tbind X U) ([(x, bind_val T1)] ++ F)) ++ E).
    solve using assumption and solve_subst_type.
  - pick fresh x and apply typing_def...
    assert (blk_fvar x = subst_tb X U x) as Xsubst...
    rewrite Xsubst...
    rewrite <- subst_ts_open_bs...
    rewrite_env ((map (subst_tbind X U) ([(x, bind_blk S1 (capture C))] ++ F)) ++ E).
    solve using assumption and solve_subst_type.
  - apply typing_vapp with (T1 := subst_tvt X U T1)...
  - rewrite subst_tvt_open_cvt...
    eapply typing_bapp...
  - assert (wf_env (F ++ [(X, bind_typ)] ++ E)) as WfEnv. {
      pick fresh f; specialize (s f ltac:(notin_solve))...
      apply styping_regular in s as [WfEnv _].
      inversion WfEnv; simpl_env...
    }
    apply ok_from_wf_env in WfEnv as OkEnv.
    pick fresh f and apply typing_try; trivial.
    * apply wf_cap_subst_tbind...
    * apply wf_cap_subst_tbind...
    * assert (blk_fvar f = subst_tb X U f) as Fsubst...
      rewrite Fsubst...
      rewrite <- subst_ts_open_cs...
      rewrite_env ((map (subst_tbind X U) ([(f, bind_blk (typ_eff T2 T1) tracked)] ++ F)) ++ E).
      pose proof (styping_regular _ _ _ _ _ (s f ltac:(notin_solve))) as [WfEnv1 _].
      solve using assumption and solve_subst_type.
    * intros kont kontFr.
      assert (blk_fvar kont = subst_tb X U kont) as Kontsubst...
      assert (exp_fvar f = subst_te X U f) as Fsubst...
      rewrite Fsubst...
      rewrite Kontsubst...
      rewrite <- subst_ts_open_es.
      rewrite <- subst_ts_open_bs.
      rewrite_env ((map (subst_tbind X U)
                        ([(kont, bind_blk (typ_vfun T1 T) (capture C))] ++
                         [(f, bind_val T2)] ++ F)) ++ E).
      pose proof (styping_regular _ _ _ _ _ (s0 f ltac:(notin_solve) kont ltac:(notin_solve))) as [WfEnv1 _].
      solve using assumption and solve_subst_type.
  - pick fresh f and apply typing_reset...
    intros kont kontFr.
    assert (blk_fvar kont = subst_tb X U kont) as Kontsubst...
    assert (exp_fvar f = subst_te X U f) as Fsubst...
    assert (T1 = subst_tvt X U T1) as T1subst. {
      apply subst_tvt_fresh.
      eapply notin_fv_tvt_wf with (E := empty)...
      eapply wf_vtyp_from_sig_binds...
    }
    assert (T2 = subst_tvt X U T2) as T2subst. {
      apply subst_tvt_fresh.
      eapply notin_fv_tvt_wf with (E := empty)...
      eapply wf_vtyp_from_sig_binds_val...
    }
    rewrite T1subst...
    rewrite T2subst...
    rewrite Fsubst...
    rewrite Kontsubst...
    rewrite <- subst_ts_open_es.
    rewrite <- subst_ts_open_bs.
    rewrite_env ((map (subst_tbind X U)
                      ([(kont, bind_blk (typ_vfun T1 T) (capture C))] ++
                       [(f, bind_val T2)] ++ F)) ++ E).
    pose proof (styping_regular _ _ _ _ _ (s0 f ltac:(notin_solve) kont ltac:(notin_solve))) as [WfEnv1 _].
    solve using assumption and solve_subst_type.
  - econstructor...
  (* btyping *)
  - eapply typing_bvar_tracked...
    binds_cases HBinds...
    * replace (subst_tbt X U S1) with S1...
      apply subst_tbt_fresh.
      eapply notin_fv_tbt_wf with (E := E).
      eapply wf_btyp_from_binds_blk...
      repeat apply wf_env_tail in WfEnv...
      eapply fresh_mid_tail...
    * apply binds_head...
      eapply binds_map with (f := subst_tbind X U) in H0...
  - eapply typing_bvar_capture...
    binds_cases HBinds...
    * replace (subst_tbt X U S1) with S1...
      apply subst_tbt_fresh.
      eapply notin_fv_tbt_wf with (E := E).
      eapply wf_btyp_from_binds_blk...
      repeat apply wf_env_tail in WfEnv...
      eapply fresh_mid_tail...
    * apply binds_head...
      eapply binds_map with (f := subst_tbind X U) in H0...
  - econstructor...
  - pick fresh x and apply typing_vabs... fold subst_tvt. fold subst_ts.
    replace (exp_fvar x) with (subst_te X U x)...
    rewrite <- subst_ts_open_es...
    specialize (s0 x ltac:(notin_solve)).
    rewrite_env ((map (subst_tbind X U) ([(x, bind_val T1)] ++ F)) ++ E).
    rewrite_env (([(x, bind_val T1)] ++ F) ++ [(X, bind_typ)] ++ E) in s0.
    solve using assumption and solve_subst_tracked.
  - pick fresh x and apply typing_babs... fold subst_tvt. fold subst_ts. fold subst_tbt.
    replace (blk_fvar x) with (subst_tb X U x)...
    rewrite <- subst_ts_open_cs...
    rewrite <- subst_tvt_open_cvt...
    specialize (s0 x ltac:(notin_solve)).
    rewrite_env ((map (subst_tbind X U) ([(x, bind_blk S1 tracked)] ++ F)) ++ E).
    rewrite_env (([(x, bind_blk S1 tracked)] ++ F) ++ [(X, bind_typ)] ++ E) in s0.
    solve using assumption and solve_subst_tracked.
  - pick fresh Y and apply typing_tabs... fold subst_tb; fold subst_tvt; fold subst_tbt.
    replace (typ_fvar Y) with (subst_tvt X U Y)...
    * rewrite <- subst_tbt_open_tbt...
      rewrite <- subst_tb_open_tb...
      rewrite_env ((map (subst_tbind X U) ([(Y, bind_typ)] ++ F)) ++ E).
      solve using assumption and solve_subst_tracked.
    * simpl subst_tvt...
      destruct (Y == X)... exfalso. notin_solve.
  - rewrite subst_tbt_open_tbt...
    econstructor...
  - simpl.
    assert (wf_vtyp empty T). eapply wf_vtyp_from_sig_binds...
    assert (wf_vtyp empty T1). eapply wf_vtyp_from_sig_binds_val...
    replace (subst_tvt X U T1) with T1...
    replace (subst_tvt X U T) with T...
    apply typing_handler...
    apply wf_vtyp_weaken_head...
    rewrite_env (E ++ empty). apply wf_vtyp_weaken_head...
    apply ok_from_wf_env. repeat apply wf_env_tail in WfEnv...
    apply subst_tvt_fresh. eapply notin_fv_tvt_wf...
    apply subst_tvt_fresh. eapply notin_fv_tvt_wf...
Qed.

(** We now can state the lemmas as it is more common, using the helper above *)
Lemma etyping_through_subst_te: forall U E F Q X e T,
  wf_vtyp E U ->
  etyping (F ++ [(X, bind_typ)] ++ E) Q e T ->
  etyping ((map (subst_tbind X U) F) ++ E) Q (subst_te X U e) (subst_tvt X U T).
Proof with solve_subst_type.
------
  intros.
  pose proof (typing_through_subst_t_ U E Q X) as [etyping_ [_ _]].
  unshelve epose proof (etyping_ _ Q e T H0 F)...
Qed.

Lemma styping_through_subst_ts : forall U E F R Q X e T,
  wf_vtyp E U ->
  styping (F ++ [(X, bind_typ)] ++ E) R Q e T ->
  styping ((map (subst_tbind X U) F) ++ E) R Q (subst_ts X U e) (subst_tvt X U T).
Proof with solve_subst_type.
------
  intros.
  pose proof (typing_through_subst_t_ U E Q X) as [_ [styping_ _]].
  unshelve epose proof (styping_ _ R Q e T H0 F _)...
Qed.

Lemma btyping_through_subst_tb : forall U E F R Q X e T,
  wf_vtyp E U ->
  btyping (F ++ [(X, bind_typ)] ++ E) R Q e T ->
  btyping ((map (subst_tbind X U) F) ++ E) R Q (subst_tb X U e) (subst_tbt X U T).
Proof with solve_subst_type.
------
  intros.
  pose proof (typing_through_subst_t_ U E Q X) as [_ [_ btyping_]].
  unshelve epose proof (btyping_ _ R Q e T H0 F _)...
Qed.
