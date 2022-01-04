Require Import Taktiks.
Require Export SystemC_Substitution.
Require Import Signatures.


(* ********************************************************************** *)
(** * #<a name="preservation"></a># Preservation *)


(* ********************************************************************** *)
(** ** Preservation (20) *)

Require Import Coq.Program.Tactics.

Lemma preservation_block : forall E R Q b b' S1,
  btyping E R Q b S1 ->
  bred b b' ->
  btyping E R Q b' S1.
Proof with simpl_env; eauto using btyping_weaken_restriction.
  intros * Typ.
  generalize dependent b'.
  induction Typ; intros b' Red; try solve [ inversion Red; subst; eauto ].
  - inversion Red; subst...
    inversion H; subst...
  - inversion Red; subst...
    * econstructor...
    * inversion Typ; subst...
      pick fresh X.
      rewrite (subst_tb_intro X)...
      rewrite (subst_tbt_intro X)...
      rewrite_env (map (subst_tbind X T1) empty ++ E).
      eapply btyping_through_subst_tb...
Qed.

Lemma preservation_expr : forall E Q b b' S1,
  etyping E Q b S1 ->
  ered b b' ->
  etyping E Q b' S1.
Proof with simpl_env; eauto using btyping_weaken_restriction.
  intros * Typ.
  generalize dependent b'.
  induction Typ; intros b' Red; try solve [ inversion Red; subst; eauto ].
  - inversion Red; subst...
    econstructor... eapply preservation_block...
Qed.

Lemma preservation_stmt : forall E R Q s s' T,
  styping E R Q s T ->
  sred s s' ->
  styping E R Q s' T.
Proof with simpl_env; eauto using btyping_weaken_restriction, preservation_block, preservation_expr.
  intros * Typ.
  generalize dependent s'.
  induction Typ; intros s' Red; try solve [ inversion Red; subst; eauto ].
  - Case "typing_ret".
    inversion Red; subst...
  - Case "typing_def".
    inversion Red; subst...
    + econstructor...
    + pick fresh x.
      rewrite (subst_bs_intro x); auto;
      rewrite_env (empty ++ E);
      apply (styping_through_subst_bs S1 C); eauto;
      eapply (btyping_weaken_restriction C); eauto.
  - Case "typing_vapp".
    inversion Red; subst...
    inversion H; subst.
    pick fresh x.
    rewrite (subst_es_intro x); auto;
    rewrite_env (empty ++ E);
    apply (styping_through_subst_es T1); eauto.
  (* this is the only interesting case! *)
  - Case "typing_bapp".
    inversion Red; subst...
    inversion H1; subst.
    pick fresh x.
    specialize (H8 x ltac:(notin_solve)).
    rewrite (subst_cs_intro x); auto.
    rewrite (subst_cvt_intro x); auto.
    rewrite_env (map (subst_bbind x C) empty ++ E).
    replace R with (subst_cset x C (cset_union R (cset_fvar x))).
    
    eapply (styping_through_subst_cs C S1); eauto.
    csetsimpl.
    rewrite <- subst_cset_fresh...
  - Case "typing_throw".
    inversion Red; subst...
Qed.



(* ********************************************************************** *)
(** * #<a name="progress"></a># Progress *)


(* ********************************************************************** *)
(** ** Canonical forms (14) *)


Lemma canonical_form_tabs : forall e T R Q,
  bvalue e ->
  btyping empty R Q e (typ_tfun T) ->
  exists e1, e = blk_tabs e1.
Proof.
  intros * Val Typ.
  remember empty.
  remember (typ_tfun T).
  revert T Heqb Heql.
  induction Typ; intros T' EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
Qed.

Lemma canonical_form_vabs : forall e U1 U2 R Q,
  bvalue e ->
  btyping empty R Q e (typ_vfun U1 U2) ->
  exists V, exists e1, e = blk_vabs V e1.
Proof.
  intros * Val Typ.
  remember empty.
  remember (typ_vfun U1 U2).
  revert U1 U2 Heqb Heql.
  induction Typ; intros U1 U2 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
Qed.

Lemma canonical_form_babs : forall e U1 U2 R Q,
  bvalue e ->
  btyping empty R Q e (typ_bfun U1 U2) ->
  exists V, exists e1, e = blk_babs V e1.
Proof.
  intros * Val Typ.
  remember empty.
  remember (typ_bfun U1 U2).
  revert U1 U2 Heqb Heql.
  induction Typ; intros U1 U2 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
Qed.

Lemma canonical_form_box : forall e R Q C,
  evalue e ->
  etyping empty Q e (typ_capt R C) ->
  exists s, e = exp_box C s.
Proof.
  intros * Val Typ.
  remember empty.
  remember (typ_capt R C).
  revert R Heqv Heql.
  induction Typ; intros R4 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  inversion EQT; subst.
  exists b. trivial.
Qed.

Lemma canonical_form_exc : forall b R Q T1 T,
  bvalue b ->
  empty @ R ; Q |-blk b ~: (typ_exc T1 T) ->
  exists l, b = blk_handler l /\ Signatures.binds l (bind_sig T1 T) Q.
Proof.
  intros * Val Typ.
  dependent induction Typ; try solve [inversion Val; eauto].
Qed.

(* ********************************************************************** *)
(** ** Progress (16) *)

Lemma progress_block : forall b S1 R Q,
  empty @ R ; Q |-blk b ~: S1 ->
  bvalue b \/ exists b', b -->b b'.
Proof with eauto.
  intros * Typ.
  remember empty. generalize dependent Heql.
  assert (Typ' : l @ R ; Q |-blk b ~: S1)...
  induction Typ; intros EQ; subst...
  - Case "typing_var_mono".
    inversion select (binds _ _ empty).
  - Case "typing_var_poly".
    inversion select (binds _ _ empty).
  - inversion H; subst.
    + inversion select (binds _ _ empty).
    + right. exists b...
  - Case "typing_tapp".
    destruct (IHTyp Typ ltac:(trivial)); right...
    * destruct (canonical_form_tabs _ _ _ _ H0 Typ); subst.
      eexists.
      apply bred_tapp.
    * destruct H0 as [b Red].
      exists (blk_tapp b T1).
      apply bred_tapp_cong...
Qed.

Lemma empty_cset_closed : capt {}C.
Proof.
  unfold capt; simpl; fnsetdec.
Qed.

Lemma cset_in_empty_env : forall C,
  wf_cap empty C -> 
    exists ls, C = cset_set {} {}N ls.
Proof with eauto.
  intros * Wf.
  inversion Wf.
  destruct (AtomSet.F.choose xs) as [x |] eqn:Eq.
  - apply AtomSet.F.choose_1 in Eq. 
    destruct (H x Eq) as [S0 Binds].
    inversion Binds.
  - apply AtomSet.F.choose_2 in Eq.
    assert (xs = {}) by fsetdec; subst...
Qed.

Lemma progress_expr : forall Q e T,
  empty ; Q |-exp e ~: T ->
  evalue e \/ exists e', e -->e e'.
Proof with eauto using empty_cset_closed.
  intros * Typ.
  remember empty. generalize dependent Heql.
  assert (Typ' : l ; Q |-exp e ~: T)...
  induction Typ; intros EQ; subst...
  - Case "typing_var".
    inversion select (binds _ _ empty).
  - destruct (cset_in_empty_env C H) as [ls EQ]; subst...
    destruct (progress_block _ _ _ _ H0) as [Val | [b' Step]].
    left. constructor...
    right. exists (exp_box (cset_set {} {}N ls) b'). constructor... 
Qed.

Lemma progress_stmt : forall s T R Q,
  empty @ R ; Q |-stm s ~: T ->
  machine_redex s \/ exists s', s -->s s'.
Proof with eauto using vtype_from_wf_vtyp, btype_from_wf_btyp, empty_cset_closed.
  intros * Typ.
  remember empty. remember R. generalize dependent Heql.
  assert (Typ' : l @ c ; Q |-stm s ~: T)...
  dependent induction Typ; intros EQ; subst...
  - Case "typing_ret".
    destruct (progress_expr _ _ _ H) as [Val | [e' Step]]...
  - Case "typing_def".
    right.
    destruct (progress_block _ _ _ _ H1) as [Val | [b' Step]]...
  - Case "typing_vapp".
    right.
    destruct (progress_block _ _ _ _ H) as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct (progress_expr _ _ _ H0) as [Val2 | [e2' Rede2']]...
      SSCase "Val2".
        destruct (canonical_form_vabs _ _ _ _ _ Val1 H) as [S [e3 EQ]].
        subst.
        exists (open_es e3 e)...
  - Case "typing_bapp".
    right.
    destruct C.
    destruct (progress_block _ _ _ _ H1) as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct (progress_block _ _ _ _ H2) as [Val2 | [e2' Rede2']]...
      SSCase "Val2".
        destruct (canonical_form_babs _ _ _ _ _ Val1 H1) as [S [e3 EQ]].
        subst. 
        exists (open_cs e3 b2 (cset_set t t0 t1))...
  - Case "typing_throw".
    destruct (progress_block _ _ _ _ H) as [Val1 | [e1' Rede1']]...
    destruct (canonical_form_exc _ _ _ _ _ Val1 H) as [l [EQ Binds]]; subst.
    destruct (progress_expr _ _ _ H0) as [Val2 | [e2' Rede2']]...
Qed.

Lemma cnt_typing_weaken_restriction : forall C1 C2 Q k T1 T2,
  wf_cap empty C2 ->
  C1; Q |-cnt k ~: T1 ~> T2 ->
  C2 |= C1 ->
  C2; Q |-cnt k ~: T1 ~> T2.
Proof with eauto using styping_weaken_restriction, wf_cap_weaken_head.
  intros * WfC2 C1TypingQ Subsumption.
  generalize dependent C2.
  dependent induction C1TypingQ; intros C2 WfC2 Subsumption...
  - pick fresh X and apply typing_cnt_frame...
    pose proof (styping_regular _ _ _ _ _ (H X ltac:(notin_solve)))...
    eapply styping_weaken_restriction...
    rewrite_env ([(X, bind_val T2)] ++ empty)...
  - pick fresh f and apply typing_cnt_handler...
    eapply subset_trans...
Qed.

Lemma unwind_step : forall L Q x C T1 T2 k,
  wf_vtyp empty T1 ->
  wf_cap empty C ->
  C ; Q |-cnt k ~: T1 ~> T2 ->
  x `notin` L ->
  [(x, bind_val T1)] @ C ; Q |-stm (plug k x) ~: T2.
Proof with eauto using 
  wf_cap_weaken_head, wf_btyp_weaken_head, wf_vtyp_weaken_head, wf_btyp_weakening.
  intros * WfT WfC Cnt Fr.
  generalize dependent C.
  generalize dependent T2.
  dependent induction k; intros T2 C WfC Cnt...
  - inversion Cnt; subst... repeat (simpl; try econstructor)...
    rewrite_env ([(x, bind_val T2)] ++ empty)...
  - inversion Cnt; subst...
    * assert (wf_vtyp empty T3). {
        pick fresh y.
        specialize (H6 y ltac:(notin_solve)).
        apply styping_regular in H6 as (Wf & _).
        inversion Wf; subst...
      }
      simpl.
      pick fresh y and apply typing_val...
      rewrite_env ([(y, bind_val T3)] ++ [(x, bind_val T1)] ++ empty).
      apply styping_weakening; simpl_env...
      econstructor...
      econstructor...
      rewrite_env ([(x, bind_val T1)] ++ empty)...
    * simpl.
      pick fresh y and apply typing_reset...      
      apply wf_cap_subset with (R := C)...
      rewrite_env ([(x, bind_val T1)] ++ empty)...
      rewrite_env ([(x, bind_val T1)] ++ empty)...
      specialize (H9 y ltac:(notin_solve)).
      intros kont kontFr.
      rewrite_env ([(kont, bind_blk (typ_vfun T T2) (capture C0))] ++ [(y, bind_val T4)] ++ [(x, bind_val T1)] ++ empty).
      assert (wf_env ([(kont, bind_blk (typ_vfun T T2) (capture C0))] ++ [(y, bind_val T4)] ++ [(x, bind_val T1)])). {
        assert (wf_env [(x, bind_val T1)]). {
          econstructor...
        }
        assert (wf_env ([(y, bind_val T4)] ++ [(x, bind_val T1)])). {
          econstructor...
          rewrite_env ([(x, bind_val T1)] ++ empty)...
          apply wf_vtyp_weaken_head...
          eapply wf_vtyp_from_sig_binds_val...
          pose proof (typing_cnt_regular _ _ _ _ _ Cnt)...
        }
        econstructor...
        * econstructor...
          + eapply wf_vtyp_weaken_head...
            rewrite_env ([(x, bind_val T1)] ++ empty)...
            eapply wf_vtyp_weaken_head...
            eapply wf_vtyp_from_sig_binds...
            pose proof (typing_cnt_regular _ _ _ _ _ Cnt)...
          + eapply wf_vtyp_weaken_head...
            pose proof (styping_regular _ _ _ _ _ (IHk WfT Fr T2 (cset_union C0 (cset_lvar l)) 
              (proj1 (typing_cnt_regular _ _ _ _ _ H2)) H2)) as [_ [_ [WfT2 _]]]...
        * rewrite_env (([(y, bind_val T4)] ++ [(x, bind_val T1)]) ++ empty).
          eapply wf_cap_weaken_head...
          eapply wf_cap_subset... 
      }
      rewrite <- concat_assoc.
      apply styping_weakening; simpl_env...
Qed.

(** show that plug doesn't introduce binders *)
Lemma plugging : forall (x : atom) k C Q T1 T2,
  C ; Q |-cnt k ~: T1 ~> T2 ->
  open_es (plug k 0) x = plug k x.
Proof with eauto*.
  intros * Cnt.
  unfold open_es.
  dependent induction k...
  cbv [plug].
  fold plug. simpl.
  destruct a;
  cbv [open_es_rec]; fold open_es_rec; subst...
  (** s is closed *)
  * inversion Cnt; subst...
    pick fresh X. specialize (H7 X ltac:(fsetdec)).
    pose proof (styping_regular _ _ _  _ _ H7) as [_ [Closed [_ _]]].
    unfold open_es in Closed.
    assert ((open_es_rec 0 X s) = (open_es_rec 1 x (open_es_rec 0 X s))).
    { apply open_es_rec_stmt... }
    eapply open_es_rec_expr_aux in H... rewrite <- H; erewrite IHk...
  * inversion Cnt; subst...
    pick fresh v. pick fresh kont.
    specialize (H11 v ltac:(notin_solve) kont ltac:(notin_solve)).
    pose proof (styping_regular _ _ _  _ _ H11) as [_ [Closed [_ _]]].
    unfold open_bs, open_es in Closed.
    assert ((open_bs_rec 0 kont (open_es_rec 0 v s)) = (open_es_rec 1 x (open_bs_rec 0 kont (open_es_rec 0 v s)))).
    { eapply open_es_rec_stmt... }
    eapply open_es_rec_block_aux in H.
    eapply open_es_rec_expr_aux in H...
    rewrite <- H; erewrite IHk...
Qed.

Lemma signature_binds_weaken : forall Q M N l (T1 T : vtyp),
  Signatures.ok (Q ++ M ++ N) ->
  Signatures.binds l (bind_sig T1 T) (Q ++ N) ->
  Signatures.binds l (bind_sig T1 T) (Q ++ M ++ N).
Proof with eauto.
  intros * Ok SgnBinds.
  Signatures.binds_cases SgnBinds...
  * rewrite_env ((Q ++ M) ++ N). eapply Signatures.binds_concat_ok... 
    Signatures.simpl_env...
Qed.

Lemma signatures_ok_from_wf_sig : forall S,
  wf_sig S -> Signatures.ok S.
Proof with eauto.
  intros S Wf.
  induction Wf...
Qed.

Ltac solve_weakening := simpl_env;
  eauto 5 using wf_cap_weakening,
              wf_vtyp_weakening,
              wf_btyp_weakening,
              wf_cap_weaken_head,
              wf_vtyp_from_wf_env_typ,
              wf_btyp_from_wf_env_blk,
              wf_cap_subset,
              wf_cap_bind_head,
              signature_binds_weaken,
              signatures_ok_from_wf_sig.

Lemma etyping_weaken_signature : forall Q M N E e T,
  wf_sig (Q ++ M ++ N) ->
  E ; Q ++ N |-exp e ~: T ->
  E ; Q ++ M ++ N |-exp e ~: T
with btyping_weaken_signature : forall Q M N E R b S1,
  wf_sig (Q ++ M ++ N) ->
  E @ R ; Q ++ N |-blk b ~: S1 ->
  E @ R ; Q ++ M ++ N |-blk b ~: S1
with styping_weaken_signature : forall Q M N E R s T,
  wf_sig (Q ++ M ++ N) ->
  E @ R ; Q ++ N |-stm s ~: T ->
  E @ R ; Q ++ M ++ N |-stm s ~: T.
Proof with solve_weakening.
------
  intros * Wf Typ.
  dependent induction Typ; try solve [ econstructor; solve_weakening ].
------
  intros * Wf Typ.
  dependent induction Typ.
  - try solve [ clear btyping_weaken_signature styping_weaken_signature; econstructor; solve_weakening ].
  - try solve [ clear btyping_weaken_signature styping_weaken_signature; econstructor; solve_weakening ].
  - try solve [ clear btyping_weaken_signature styping_weaken_signature; econstructor; solve_weakening ].
  - pick fresh x and apply typing_vabs...
  - pick fresh x and apply typing_babs...
  - pick fresh x and apply typing_tabs...
  - try solve [ clear btyping_weaken_signature styping_weaken_signature; econstructor; solve_weakening ].
  - try solve [ clear btyping_weaken_signature styping_weaken_signature; econstructor; solve_weakening ].
------
  intros * Wf Typ.
  dependent induction Typ.
  - try solve [ econstructor; solve_weakening ].
  - pick fresh x and apply typing_val...
  - pick fresh x and apply typing_def...
  - try solve [ econstructor; solve_weakening ].
  - try solve [ econstructor; solve_weakening ].
  - pick fresh x and apply typing_try...
  - pick fresh x and apply typing_reset...
  - try solve [ econstructor; solve_weakening ].
Qed.

Lemma ctx_typing_weaken_signature : forall Q M N R c T,
  wf_sig (Q ++ M ++ N) ->
  R ; Q ++ N |-ctx c ~: T ->
  R ; Q ++ M ++ N |-ctx c ~: T.
Proof with eauto using etyping_weaken_signature, btyping_weaken_signature, styping_weaken_signature,
  signatures_ok_from_wf_sig.
  intros * WfS H.
  dependent induction H...
  - pick fresh x and apply typing_ctx_frame...
  - pick fresh x and apply typing_ctx_try...
    eapply signature_binds_weaken...
Qed.

Lemma signature_binds_unique : forall l T1 T2 Q,
  Signatures.binds l T1 Q ->
  Signatures.binds l T2 Q ->
  wf_sig Q ->
  T1 = T2.
Proof.
  intros * Bind1 Bind2 Wf.
  unfold Signatures.binds in *.
  rewrite Bind1 in Bind2.
  inversion Bind2.
  trivial.
Qed.

Lemma notin_fv_be_substed_ee : forall x y s1 s2,
  x <> y ->
  x `notin` fv_be s1 ->
  x `notin` fv_be s2 ->
  x `notin` fv_be (subst_ee y s2 s1)
with notin_fv_bs_substed_es : forall x y s1 s2,
  x <> y ->
  x `notin` fv_bs s1 ->
  x `notin` fv_be s2 ->
  x `notin` fv_bs (subst_es y s2 s1)
with notin_fv_bb_substed_eb : forall x y s1 s2,
  x <> y ->
  x `notin` fv_bb s1 ->
  x `notin` fv_be s2 ->
  x `notin` fv_bb (subst_eb y s2 s1).
Proof with eauto.
------
  intros * Fry Frs1 Frs2.
  induction s1; simpl; f_equal...
  destruct (a == y)...
------
  intros * Fry Frs1 Frs2.
  induction s1; simpl in *; f_equal...
------
  intros * Fry Frs1 Frs2.
  induction s1; simpl in *; f_equal...
Qed.

Lemma preservation_step : forall s1 s2,
  typing_state s1 -> 
  s1 --> s2 ->
  typing_state s2.
Proof with eauto 5 using styping_weaken_restriction, wf_vtyp_from_sig_binds.
  intros * Typ Step.
  inversion Typ; subst.
  -- Case "Step".
    inversion Step; subst.
    - SCase "Cong". 
      econstructor...
      epose proof (preservation_stmt _ _ _ _ _ _ H0 H5)...
    - SCase "Pop".
      inversion H; subst.
      inversion H0; subst.
      eapply typ_step with (T := T2)...
      pick fresh x.
      rewrite (subst_es_intro x); auto;
      rewrite_env (empty ++ empty);
      apply (styping_through_subst_es T); simpl_env; eauto.
    - SCase "Ret". 
      inversion H; subst.
      assert (wf_cap empty R0). {
        rename select (typing_ctx R0 _ _ _) into HT.
        apply typing_ctx_regular in HT as (? & _)...
      }
      inversion H0; subst.
      econstructor...
    - SCase "Push".
      inversion H0; subst.
      eapply typ_step with (T := T0)...
      econstructor...
    - SCase "Try".
      assert (wf_vtyp empty T1). {
        inversion H0; subst.
        pick fresh x.
        select (forall f,  _ -> _ @ (cset_union _ _); _ |-stm _ ~: _)
         (fun H => specialize (H x ltac:(notin_solve)) as StmOpenCs).
        apply styping_regular in StmOpenCs as (Wf & _).
        inversion Wf; subst.
        inversion select (wf_btyp _ (typ_exc _ _)); subst...
      }
      assert (wf_vtyp empty T2). {
        inversion H0; subst.
        pick fresh x.
        select (forall f,  _ -> _ @ (cset_union _ _); _ |-stm _ ~: _)
         (fun H => specialize (H x ltac:(notin_solve)) as StmOpenCs).
        apply styping_regular in StmOpenCs as (Wf & _).
        inversion Wf; subst.
        inversion select (wf_btyp _ (typ_exc _ _)); subst...
      }
      inversion H0; subst...
      apply typ_step with (T := T) (R := cset_union C (cset_lvar l))...
      econstructor...
      + srewrite_env (nil ++ [(l, bind_sig T2 T1)] ++ Q). 
        apply ctx_typing_weaken_signature...
        Signatures.simpl_env. econstructor...
      + intros v Notinv kont Notinkont.
        srewrite_env (nil ++ [(l, bind_sig T2 T1)] ++ Q). 
        eapply styping_weaken_signature.
        Signatures.simpl_env...
        constructor...
        solve using assumption and (try eassumption; notin_solve).
      + simpl.
        pick fresh x.
        rewrite (subst_cs_intro x); auto;
        rewrite_env (map (subst_bbind x (cset_lvar l)) empty ++ empty).
        replace T with (subst_cvt x (cset_lvar l) T).
        replace (cset_union C (cset_lvar l)) with (subst_cset x (cset_lvar l) (cset_union C (cset_fvar x))).
        eapply styping_through_subst_cs with (U := typ_exc T2 T1) (R := cset_union C (cset_fvar x))...
        rewrite_env ([(x, bind_blk (typ_exc T2 T1) tracked)] ++ empty).
        srewrite_env (nil ++ [(l, bind_sig T2 T1)] ++ Q).
        eapply styping_weaken_signature...
        econstructor...
        econstructor...
        econstructor...
        (* Connect (bound_labels c) and Q by R : Q |-ctx c ~: T. *)
        {          
          simpl_env.
          apply Signatures.binds_head. apply Signatures.binds_singleton.
        }
        {
          csetsimpl.
          rewrite <- subst_cset_fresh...
        }
        rewrite <- subst_cvt_fresh...
    - SCase "reset".
      assert (wf_vtyp empty T0). {
        apply typing_ctx_regular in H as (_ & ?).
        rename select (Signatures.binds _ (bind_sig _ _) Q) into HB.
        apply wf_vtyp_from_sig_binds in HB...
      }
      inversion H0; subst.
      econstructor...
    - SCase "throw".
      inversion H0; subst...
      inversion H7; subst...
      assert (wf_sig Q). {
        apply typing_ctx_regular in H.
        eauto*.
      }
      econstructor...
  -- Case "Wind".
    inversion Step; subst.
    - SCase "throw frame". 
      inversion H0; subst.
      inversion H1; subst...
      econstructor...
      econstructor...
    - SCase "throw wrong handler". 
      inversion H1; subst.
      eapply typ_wind with (R := R0)...
      {
        unshelve epose proof (union_lvar_1 _ _ _ _ _ _ H) as [InC | InL2]...
        exfalso. unfold cset_references_lvar, cset_lvars, cset_lvar in InL2. lsetdec.
      }
      eapply typing_cnt_handler with (T1 := T1)...
    - SCase "throw".
      inversion H1; subst.
      pose proof (signature_binds_unique _ _ _ _ H0 H10 ltac:(eauto*)) as HT1T0;
        symmetry in HT1T0; inversion HT1T0; subst...
      pose proof (signature_binds_unique _ _ _ _ H10 H15 ltac:(eauto*)) as HT1T3;
        symmetry in HT1T3; inversion HT1T3; subst...
      econstructor...
      eapply styping_weaken_restriction...
      pick fresh f. pick fresh val.
      
      rewrite (subst_es_intro val); try notin_solve.
      rewrite (subst_bs_intro f); try notin_solve.
      rewrite subst_es_open_bs_var...
      rewrite_env (empty ++ empty).

      (* substitution commutes, assuming some wellformedness conditions that we need
          to prove. *)
      rewrite subst_es_through_subst_bs.
      2 : {
        simpl. repeat rewrite notin_union_split; repeat split; try notin_solve.
        eapply notin_fv_es_plug...
        eapply notin_fv_bs_plug...
      }
      2 : {
        simpl.
        repeat rewrite notin_union_split; repeat split; try notin_solve.
        eapply notin_fv_es_plug...
        eapply notin_fv_bs_plug...
      }
      2 : {
        apply notin_fv_bs_substed_es; try trivial.
        * notin_solve.
        * apply notin_fv_bs_opened_es...
        * notin_solve.
      }

      (* now the proof works. *)
      eapply styping_through_subst_es with (U := T3)...
      eapply (styping_through_subst_bs (typ_vfun T1 T2) C)...
      * pick fresh X and apply typing_vabs...
        replace (open_es (plug (SystemC_Definitions.H l C h :: k) 0) X) with
          (plug (SystemC_Definitions.H l C h :: k) X)...
        {
          apply styping_weakening...
          apply unwind_step with (L := L)...
          econstructor...
          repeat econstructor...
          apply wf_vtyp_weaken_head...
        }
        erewrite <- plugging; eauto*.
        econstructor...
Qed.

Lemma progress_step : forall s1,
  typing_state s1 -> 
  done s1 \/ exists s2, s1 --> s2.
Proof with eauto.
  intros * Typ.
  inversion Typ; subst.
  -- Case "Step".
    destruct (progress_stmt _ _ _ _ H0) as [Done|[s' Red]].
    - SCase "Redex".
      inversion Done; subst...
      + destruct c.
        * left...
        * right. destruct f...
      + right.
        pick fresh label l for (LabelSet.F.union (Signatures.dom Q) (bound_labels c)).
        (* Here we will have to show that T0 is wellformed in the empty env *)
        eexists 〈 open_cs b (blk_handler l) (cset_lvar l) |
            SystemC_Definitions.H l C s0 :: c | _ ++ Q 〉...
        econstructor...
        all : lsetdec.
      + (* Here we have to learn that l is bound at type T0 *)
        inversion H0; subst...
    - SCase "Cong".
      destruct (progress_stmt _ _ _ _ H0) as [M|[e' Red1]]...
  -- Case "Wind".
    destruct c.
    * exfalso. 
      inversion Typ; subst.
      inversion H1; subst.
      exfalso. unfold cset_references_lvar, from_labels, cset_lvars, bound_labels in H.
      lsetdec.
    * destruct f.
      ** right...
      ** destruct (l =l= l0); subst...
Qed.
