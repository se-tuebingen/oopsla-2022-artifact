(** #
<div class="source">
  The source of this file can be found on
  <a href="{{site.github}}/blob/main/coq/SystemC/Examples.v">Github</a>.
</div>
# *)

Require Import SystemC.Definitions.
Require Import Coq.Program.Tactics.
Require Import SystemC.Lemmas.
Require Import Signatures.

(**
  * #<a name="examples"></a>#  Examples
  **********************************************************)
(** This file contains some worked examples in Coq for System C. *)

(** As System C is concerned with tracking _effectful_ computation,
    represented by a block type, we define a base block type [S0]
    that is used to represent some ambient, global effectful operation
    -- perhaps for performing I/O.
    
    In System C, we could define [S0] using the following:
#
<pre><code class="language-effekt">
interface S0 {
  def doSomething(): Int
}
</code></pre>
#
*)
Parameter S0 : btyp.
Parameter S0Wf : wf_btyp empty S0.
Parameter S0Type : btype S0.
(* begin hide *)
Ltac destruct_if :=
  match goal with
  | |- context[if ?t then _ else _] =>
    destruct t eqn:?
  end.
Ltac binds_dec :=
  cbv [binds get]; simpl;
    repeat first [ reflexivity | destruct_if; try congruence].
Lemma substZeroInSingleton (x : atom): (open_cset 0 (cset_fvar x) (cset_bvar 0)) = (cset_fvar x).
Proof with eauto*.
  cbv [open_cset cset_references_bvar_dec cset_bvar cset_bvars cset_union cset_fvar
       cset_fvars cset_remove_bvar cset_lvars cset_lvar].
  destruct_set_mem 0 (NatSet.F.singleton 0); f_equal;
    try fsetdec; try lsetdec; try fnsetdec...
Qed.
Lemma substitutionS0 (x : atom) : open_cbt_rec 0 (cset_fvar x) S0 = S0.
Proof with eauto.
  assert (btype S0). {
    eapply btype_from_wf_btyp.
    apply S0Wf.
  }
  symmetry. apply open_cbt_rec_btype...
Qed.
Lemma wf_cap_empty: forall E,
  wf_cap E {}C.
Proof.
  intros.
  constructor.
  eexists (typ_eff typ_base typ_base). exfalso; fsetdec.
Qed.
Lemma cset_references_bvar_evidently : forall A (t s : A) i,
  (if cset_references_bvar_dec i (cset_bvar i) then t else s) = t.
Proof.
  intros.
  cbv.
  destruct_if; [reflexivity |].
  rewrite_set_facts_in Heqb.
  fnsetdec.
Qed.
Lemma cset_references_bvar_evidently_empty : forall A (t s : A) i,
  (if cset_references_bvar_dec i {}C then t else s) = s.
Proof.
  intros.
  cbv.
  destruct_if; [|reflexivity].
  rewrite_set_facts_in Heqb.
  fnsetdec.
Qed.
Lemma cset_references_bvar_evidently_not : forall A (t s : A) i j,
  i <> j ->
  (if cset_references_bvar_dec i (cset_bvar j) then t else s) = s.
Proof.
  intros.
  cbv.
  destruct_if; [|reflexivity].
  rewrite_set_facts_in Heqb.
  fnsetdec.
Qed.
Lemma cset_references_bvar_evidently_fvar : forall A (t s : A) i x,
  (if cset_references_bvar_dec i (cset_fvar x) then t else s) = s.
Proof.
  intros.
  cbv.
  destruct_if; [|reflexivity].
  rewrite_set_facts_in Heqb.
  fnsetdec.
Qed.
Lemma cset_references_bvar_evidently_lvar : forall A (t s : A) i l,
  (if cset_references_bvar_dec i (cset_lvar l) then t else s) = s.
Proof.
  intros.
  cbv.
  destruct_if; [|reflexivity].
  rewrite_set_facts_in Heqb.
  fnsetdec.
Qed.
Lemma cset_remove_bvar_evidently : forall i, cset_remove_bvar i (cset_bvar i) = {}C.
Proof. intro. cbv. f_equal. csetdec. Qed.
Lemma cset_union_empty : forall C, cset_union C {}C = C.
Proof. intro. cbv. destruct C. csetdec. Qed.
Hint Rewrite cset_references_bvar_evidently : csets.
Hint Rewrite cset_references_bvar_evidently_empty : csets.
Hint Rewrite cset_references_bvar_evidently_fvar : csets.
Hint Rewrite cset_references_bvar_evidently_lvar : csets.
Hint Rewrite cset_references_bvar_evidently_not using congruence : csets.
Hint Rewrite cset_remove_bvar_evidently : csets.
Hint Rewrite cset_union_empty : csets.
Ltac cleanup :=
  cbv [
      open_es open_es_rec open_bs open_bs_rec
      open_cvt open_cvt_rec open_cbt open_cbt_rec open_cs open_cs_rec open_cset]; csetsimpl.
Ltac sig_binds_dec :=
  cbv [Signatures.binds Signatures.get]; simpl;
    repeat first [ reflexivity | destruct_if; try congruence].
Lemma wf_sig_nil : wf_sig nil. constructor. Qed.
Lemma wf_cap_union : forall E C D,
  wf_cap E C ->
  wf_cap E D ->
  wf_cap E (cset_union C D).
Proof.
  intros * WfC WfD.
  destruct C; destruct D.
  cbv.
  inversion WfC; inversion WfD; subst.
  csetsimpl.
  constructor.
  intros ? ?.
  rewrite AtomSetFacts.union_iff in H.
  eauto*.
Qed.
Ltac solve_wf_cap_cset_fvar :=
    constructor;
    intros ? ?;
    match goal with
    | H : ?x `in` singleton ?y |- _ =>
      assert (x = y) by fsetdec; subst
    end;
    eexists; binds_dec.
(* end hide *)

(**
  ** #<a name="examples-id"></a>#  Identity on blocks
  **********************************************************)
(** Here is an example of a function which takes a block argument f of type [S0] and boxes it.
    In System C, we could define this using the following:
#
<pre><code class="language-effekt">
def id {f : S0} {
  box f
}
</code></pre>
# *)
Definition id : blk :=
  blk_babs S0 (stm_ret (exp_box (cset_bvar 0) (blk_bvar 0))).

(** Naturally, it would have the type <<{f : S0} => S0 at {f}>>.  You can see this by hovering over
    <<id_typ>> in the following code block.
#
<pre><code class="language-effekt">
def show_typ() { val id_typ = id; () }
</code></pre>
#
*)
Definition id_typ : btyp :=
  typ_bfun S0 (typ_capt S0 (cset_bvar 0)).

Ltac crush :=
  eauto; simpl_env; simpl;
    try fsetdec;
    unfold open_bs, open_bs_rec, open_cvt, open_cvt_rec, open_cbt, open_cbt_rec, open_cs, open_cs_rec;
    destruct (0 === 0); try contradiction;
    fold open_bs open_bs_rec open_cvt open_cvt_rec open_cbt_rec open_cs open_cs_rec.


Lemma id_typing : empty @ {}C ; nil |-blk id ~: id_typ.
Proof with crush.
  eapply (typing_babs {}).
  intros...
  rewrite substZeroInSingleton.
  rewrite substitutionS0.
  econstructor.
  econstructor...
  econstructor; intros; exists S0.
  assert (x = x0) by fsetdec; subst...

  econstructor...
  econstructor...
  apply S0Wf...
  econstructor...
  econstructor...
  econstructor...
  csetsimpl.
  econstructor...
  intros y In...
  destruct (x == y); subst...
Qed.


(**
  ** #<a name="examples-try"></a>#  Effectful Handlers
  **********************************************************)
(** Next, we model a simple try-catch expression which simply returns a value.
    This, written in our language, looks like:
#
<pre><code class="language-effekt">
def try_return_immediate() {
  try {
    0
  } with cap : S0 {
    def doSomething() {
      1
    }
  }
}
</code></pre>
#
    As our formalism in Coq lacks integers (and other expression values), we model
    our expressions and expression values in Coq using a base expression type [typ_base]
    and a singular inhabitant of that type, namely [exp_const].


*)
Definition try_return_immediate_typ :=
  typ_base.
Definition try_return_param_type :=
  typ_base.
Definition try_return_immediate :=
  stm_try {}C try_return_param_type try_return_immediate_typ
     (stm_ret exp_const) (* 0 *)
     (stm_ret exp_const) (* 1 *).

(** As expected, that try statement returns an <<Int>> (in our formalism, a [typ_base]). *)
Lemma try_return_immediate_typing : empty @ {}C ; nil |-stm try_return_immediate ~: try_return_immediate_typ.
Proof with crush; try autorewrite with csets.
  eapply (typing_try {}).
  intros...
  * repeat (try constructor; try fsetdec).
    econstructor. instantiate (1 := typ_eff typ_base typ_base). fsetdec.
  * repeat (try constructor; try fsetdec).
    econstructor. instantiate (1 := typ_eff typ_base typ_base). fsetdec.
  * repeat (constructor; try fsetdec).
    csetsimpl.
    constructor.
    eexists.
    assert (x = f) by fsetdec.
    subst.
    binds_dec.
  * repeat (constructor; try fsetdec).
    + econstructor. instantiate (1 := typ_eff typ_base typ_base). fsetdec.
    + simpl_env.  fsetdec.
    + econstructor. instantiate (1 := typ_eff typ_base typ_base). fsetdec.
Qed.

(** And naturally, reduces to 0 ([exp_const]) as the effect is never invoked.
    As an aside, we assume the existance of three unique, fresh labels, which
    are used by our reduction semantics to uniquely identify frames on the stack. *)

Parameter l1 l2 l3 : label.
Axiom l1l2 : l1 <> l2.
Axiom l1l3 : l1 <> l3.
Axiom l2l3 : l2 <> l3.

(** Now, the try expression then reduces to returning a value directly out of a handler frame. *)
Lemma try_return_immediate_s1 :
  〈 try_return_immediate | top | nil 〉-->
  〈 (stm_ret exp_const) (* 0 *) |
     (H l1 {}C (stm_ret exp_const) (* 1 *)) :: top |
     (l1, bind_sig try_return_param_type try_return_immediate_typ) :: nil 〉.
Proof with crush.
  unfold try_return_immediate.
  rapply step_try...
Qed.
(** ...which, by our reduction rules, eliminates the handler frame from the top of the stack. *)
Lemma try_return_immediate_s2 : forall Q,
  〈 (stm_ret exp_const) (* 0 *) | (H l1 {}C (stm_ret exp_const) (* 1 *)) :: top | Q 〉-->
  〈 (stm_ret exp_const) (* 0 *) | top | Q 〉.
Proof with crush.
  intro.
  apply step_pop_2...
Qed.

(**
  ** #<a name="examples-try-invoke"></a>#  Invoking a handler
  **********************************************************)
(**
  Similarly, next we model a try statement which actually throws something.  In System C, this can be
  expressed using the following fragment:
#
<pre><code class="language-effekt">
def try_return_throw() {
  try {
    cap.doSomething()
  } with cap : S0 {
    def doSomething() {
      0
    }
  }
}
</code></pre>
#
*)
Definition try_return_throw_typ :=
  typ_base.
Definition try_return_throw_param_typ :=
  typ_base.
Definition try_return_throw :=
  stm_try {}C try_return_throw_param_typ try_return_throw_typ 
  (stm_perform (blk_bvar 0) exp_const (* () *)) 
  (stm_ret exp_const (* 0 *)).

(** Naturally, it still returns an Int/[typ_base] though. *)
Lemma try_return_throw_typing : empty @ {}C ; nil |-stm try_return_throw ~: try_return_throw_typ.
Proof with crush; try autorewrite with csets.
  eapply (typing_try {}).
  intros...
  * repeat (constructor; try fsetdec).
    econstructor. instantiate (1 := typ_eff typ_base typ_base). fsetdec.
  * repeat (constructor; try fsetdec).
    econstructor. instantiate (1 := typ_eff typ_base typ_base). fsetdec.
  * repeat (constructor; try fsetdec).
    csetsimpl.
    apply typing_throw with (T1 := try_return_throw_param_typ);
    repeat (constructor; try fsetdec)...
    eexists.
    assert (x = f) by fsetdec.
    subst.
    binds_dec.
  * repeat (constructor; try fsetdec).
    - eexists (typ_eff typ_base typ_base). fsetdec.
    - simpl_env. fsetdec.
    - econstructor. instantiate (1 := typ_eff typ_base typ_base). fsetdec.
Qed.

(** The reduction steps for this expression are a bit more complicated.  First, a throw
    statement is reduced in the presence of a matching handler, which shifts evaluation
    to that handler and unwinds from there. *)
Lemma try_return_throw_s1 :
  〈 try_return_throw | top | nil 〉-->
  〈 (stm_perform (blk_handler l1) exp_const (* () *)) |
     (H l1 {}C (stm_ret exp_const (* 0 *))) :: top |
     [(l1, bind_sig try_return_throw_param_typ try_return_throw_typ)] 〉.
Proof with crush.
  unfold try_return_immediate.
  rapply step_try...
Qed.

Lemma try_return_throw_s2 : forall Q,
  〈 (stm_perform (blk_handler l1) exp_const (* () *)) | (H l1 {}C (stm_ret exp_const (* 0 *))) :: top | Q 〉-->
  〈throw l1 # exp_const (* () *) | (H l1 {}C (stm_ret exp_const (* 0 *))) :: top • top | Q〉.
Proof with crush.
  intro.
  apply step_throw...
Qed.

Lemma try_return_throw_s3 :
  〈throw l1 # exp_const (* () *) | (H l1 {}C (stm_ret exp_const (* 0 *))) :: top • top |
     [(l1, bind_sig try_return_throw_param_typ try_return_throw_typ)]〉-->
  〈 (stm_ret exp_const (* 0 *)) | top | [(l1, bind_sig try_return_throw_param_typ try_return_throw_typ)] 〉 .
Proof with crush.
  rapply step_handle...
Qed.

(**
  ** #<a name="examples-try-invoke-2"></a>#  Invoking a handler, redux
  **********************************************************)
(** This example is a little more complicated.  Here, we throw while evaluating a value-binder
    under the handler block.
#
<pre><code class="language-effekt">
def try_apply_throw() {
  try {
    val x = cap.doSomething();
    x
  } with cap : S0 {
    def doSomething() {
      1
    }
  }
}
</code></pre>
#    
*)
Definition try_apply_throw_param_typ := typ_base.
Definition try_apply_throw_typ := typ_base.
Definition try_apply_throw :=
  stm_try {}C try_apply_throw_param_typ try_apply_throw_typ 
    (stm_val typ_base 
      (stm_perform (blk_bvar 0) exp_const (* () *)) 
      (stm_ret (exp_bvar 0) (* x *)))
    (stm_ret (exp_const) (* 1 *)).

(** Naturally, it returns an Int/[typ_base] again. *)
Lemma try_apply_throw_typing :
  empty @ {}C ; nil |-stm try_apply_throw ~: try_apply_throw_typ.
Proof with crush; try autorewrite with csets; simpl_env in *.
  eapply (typing_try {}); try apply wf_cap_empty.
  - trivial...
  - intros; cbv in *...
    eapply (typing_val (singleton f)).
    + econstructor.
      apply typing_bvar_tracked; eauto.
      * constructor...          (* wf_env *)
      * constructor.            (* wf_sig nil *)
      * constructor.            (* wf_cap singleton *)
        intros ? ?.
        assert (x = f) by fsetdec; subst.
        eexists; binds_dec.
      * constructor...
        repeat (constructor; try fsetdec)...
        econstructor.
    + intros.
      cbn...
      constructor.
      * apply typing_evar.
        -- constructor...
           constructor...
        -- constructor.
        -- binds_dec.
      * constructor.            (* wf_cap singleton *)
        intros x0 Hx0.
        assert (x0 = f) by fsetdec; subst.
        eexists; binds_dec.
  - intros.
    cbn...
    constructor.
    + cbv. constructor.
      2: constructor.           (* wf_sig nil *)
      constructor...
      econstructor...
      apply wf_cap_empty.       (* wf_cap empty (variant) *)
    + apply wf_cap_empty.       (* wf_cap empty *)
Qed.

(** The reduction steps for this statement are a little more complicated.  First,
    as before, we shift the try statement onto the stack as a handler frame. *)
Lemma try_apply_throw_s1 :
  〈 try_apply_throw | top | nil 〉-->
  〈 (stm_val typ_base 
      (stm_perform (blk_handler l1) exp_const (* () *)) 
      (stm_ret (exp_bvar 0) (* x *)))
    | (H l1 {}C (stm_ret exp_const (* 1 *))) :: top
    | [(l1, bind_sig try_apply_throw_param_typ try_apply_throw_typ)]
   〉.
Proof with crush.
  unfold try_apply_throw.
  rapply step_try...
Qed.

(** Next, we mark that we are evaluating a binding with a K frame.  *)
Lemma try_apply_throw_s2 :
  〈 (stm_val typ_base (stm_perform (blk_handler l1) exp_const (* () *)) (stm_ret (exp_bvar 0) (* x *)))
    | (H l1 {}C (stm_ret exp_const (* 1 *))) :: top
    | [(l1, bind_sig try_apply_throw_param_typ try_apply_throw_typ)]
  〉-->
  〈 (stm_perform (blk_handler l1) exp_const (* () *))
    | (K typ_base (stm_ret (exp_bvar 0) (* x *))) :: ((H l1 {}C (stm_ret exp_const (* 1 *))) :: top)
    | [(l1, bind_sig try_apply_throw_param_typ try_apply_throw_typ)]
  〉.
Proof with crush.
  rapply step_push.
  apply stmt_val with (L := {})...
Qed.

(** We throw in the presence of a K frame and a matching H (handler) frame,
    which causes the K frame to be unwound... *)
Lemma try_apply_throw_s3 :
  〈 (stm_perform (blk_handler l1) exp_const (* () *))
    | (K typ_base (stm_ret (exp_bvar 0) (* x *))) :: ((H l1 {}C (stm_ret exp_const (* 1 *))) :: top)
    | [(l1, bind_sig try_apply_throw_param_typ try_apply_throw_typ)]
  〉-->
  〈throw l1 # exp_const (* () *)
    | (K typ_base (stm_ret (exp_bvar 0) (* x *))) :: ((H l1 {}C (stm_ret exp_const (* 1 *))) :: top)
    • top
    | [(l1, bind_sig try_apply_throw_param_typ try_apply_throw_typ)]
  〉.
Proof with crush.
  apply step_throw...
Qed.

(** We unwind the stack, building the resumption continuation as we go, denoted by • ...*)
Lemma try_apply_throw_s4 :
  〈throw l1 # exp_const (* () *)
    | (K typ_base (stm_ret (exp_bvar 0) (* x *))) :: ((H l1 {}C (stm_ret exp_const (* 1 *))) :: top)
    • top
    | [(l1, bind_sig try_apply_throw_param_typ try_apply_throw_typ)]
  〉-->
  〈throw l1 # exp_const (* () *)
    | ((H l1 {}C (stm_ret exp_const (* 1 *))) :: top)
    • (K typ_base (stm_ret (exp_bvar 0) (* x *))) :: top
    | [(l1, bind_sig try_apply_throw_param_typ try_apply_throw_typ)]
  〉.
Proof with crush.
  apply step_unwind_1.
Qed.

(** ... and when we get to the matching H frame, we shift it off to evaluate the corresponding
    handler. *)
Lemma try_apply_throw_s5 :
  〈throw l1 # exp_const (* () *)
    | ((H l1 {}C (stm_ret exp_const (* 1 *))) :: top)
    • (K typ_base (stm_ret (exp_bvar 0) (* x *))) :: top
    | [(l1, bind_sig try_apply_throw_param_typ try_apply_throw_typ)]
  〉-->
  〈 (stm_ret exp_const (* 1 *))
    | top
    | [(l1, bind_sig try_apply_throw_param_typ try_apply_throw_typ)]
  〉.
Proof with crush.
  rapply step_handle...
Qed.

(**
  ** #<a name="examples-capability-thread"></a>#  Capability threading
  **********************************************************)
(** Here is a more complicated example, which threads and returns a capability
    through try/handle frames.
#
<pre><code class="language-effekt">
def cap_return() {
  try {
    interface S1 {
      def doSomethingElse(): Unit => Int at {cap}
    }

    val thunk = 
      try {
        def f() {
          cap.doSomething()
        }
        f
      } with cap2 : S1 {
        def doSomethingElse() {
          def g() {
            0
          }
          box {cap} g
        }
      };
    thunk()
  } with cap : S0 {
    def doSomething() {
      0
    }
  }
}
</code></pre>
#    
*)
Definition cap_return_tm :=
  (* try { ... *)
  (stm_try {}C typ_base typ_base
          (* val thunk = ... *)
          (stm_val (typ_capt (typ_vfun typ_base typ_base) (cset_bvar 0))
                    (* try { ... *)
                    (stm_try (cset_bvar 0) typ_base typ_base
                             (* def f() { ... *)
                             (stm_def (cset_bvar 1) (typ_vfun typ_base typ_base)
                                      (* cap.doSomething() *)
                                      (blk_vabs typ_base (stm_perform (blk_bvar 1) exp_const))
                             (*} f *)
                                      (stm_ret (exp_box (cset_bvar 2)
                                                        (blk_bvar 0))))
                    (*} with cap2 : S1 { *)  
                             (stm_ret (exp_box (cset_bvar 1)
                                               (blk_vabs typ_base (stm_ret exp_const)))))
                    (*}; thunk() *)
                    (stm_vapp (blk_unbox (exp_bvar 0)) exp_const))
  (*} with cap : S0 { ... *) 
           (stm_ret exp_const)).
  (*}*)

(* begin hide *)
Lemma cap_return_typing1 :
  (nil @ (cset_lvar l1) ; (l2, bind_sig typ_base typ_base) :: (l1, bind_sig typ_base typ_base) :: nil
                          |-blk (blk_vabs typ_base (stm_perform (blk_handler l1) exp_const))
                               ~: (typ_vfun typ_base typ_base)).
Proof with crush.
  Require Import SystemC.Soundness.
  pick fresh x and apply typing_vabs.
  cbv [open_es open_es_rec].
  pose proof (l1l2).
  econstructor; try instantiate (1 := typ_base); repeat (constructor; try fsetdec; try lsetdec)...
  sig_binds_dec.
Qed.

Lemma cap_return_typing2 : forall x,
  (styping
     ((x, bind_blk (typ_vfun typ_base typ_base) (capture (cset_lvar l1))) :: nil)
     (cset_lvar l1)
     ((l2, bind_sig typ_base typ_base) :: (l1, bind_sig typ_base typ_base) :: nil)
     (stm_ret (exp_box (cset_lvar l1) (blk_fvar x)))
     (typ_capt (typ_vfun typ_base typ_base) (cset_lvar l1))).
Proof with crush.
  intro x.
  assert (wf_sig nil) by constructor.
  assert
    (wf_cap [(x, bind_blk (typ_vfun typ_base typ_base) (capture (cset_lvar l1)))] (cset_lvar l1)). {
    constructor.
    intros ? ?.
    fsetdec.
  }
  rapply typing_ret...
  constructor...
  eapply typing_bvar_capture...
  - constructor...
  - constructor...
    + constructor...
    + (pose proof l1l2); lsetdec.
Qed.
(* end hide *)
(** Naturally, it is also well-typed. *)
Lemma cap_return_typing0 : exists T,
  (styping nil {}C nil
           cap_return_tm
           T).
Proof with crush.
  eexists.
  unfold cap_return_tm.
  pose proof wf_cap_empty.
  pose proof wf_sig_nil.
  pick fresh x and apply typing_try... {
    cleanup.
    pick fresh y and apply typing_val... {
      pick fresh z and apply typing_try.
      1: crush.
      1: {
        solve_wf_cap_cset_fvar.
      }
      1: solve_wf_cap_cset_fvar.
      1: {
        cleanup.
        pick fresh xx and apply typing_def.
        1: crush.
        1: solve_wf_cap_cset_fvar.
        1: {
          assert (z <> x) by fsetdec.
          pick fresh yx and apply typing_vabs;
            assert (yx <> z) by fsetdec;
            assert (yx <> x) by fsetdec.
          cleanup.
          eapply typing_throw; try instantiate (1 := typ_base)...
          apply typing_bvar_tracked.
          2: trivial.
          2: solve_wf_cap_cset_fvar.
          2: binds_dec.
          2: crush.
          1: {
            constructor...
            constructor...
            constructor...
          }
          econstructor...
          repeat (constructor; simpl_env; try fsetdec).
        }
        cleanup.
        assert (z <> x) by fsetdec.
        assert (xx <> z) by fsetdec.
        assert (xx <> x) by fsetdec.
        constructor.

        1: {
          constructor.
          1: solve_wf_cap_cset_fvar.
          eapply typing_bvar_capture.
          5: binds_dec.
          4: crush.
          2: trivial.
          2: solve_wf_cap_cset_fvar.
          1: {
            constructor...
            2: solve_wf_cap_cset_fvar.
            constructor...
            constructor...
          }
        }

        1: apply wf_cap_union; solve_wf_cap_cset_fvar.
      }
      1: {
        cleanup.
        constructor.
        2: solve_wf_cap_cset_fvar...
        constructor.
        1: solve_wf_cap_cset_fvar...
        pick fresh zx and apply typing_vabs.
        cleanup.
        assert (z <> x) by fsetdec.
        assert (zx <> z) by fsetdec.
        assert (zx <> x) by fsetdec.
        constructor.
        2: solve_wf_cap_cset_fvar...
        constructor.
        2: trivial.
        {
          constructor...
          constructor...
          3: solve_wf_cap_cset_fvar.
          2: {
            constructor...
            constructor...
            solve_wf_cap_cset_fvar.
          }
          constructor...
          constructor...
        }
      }
    }
    cleanup.
    eapply typing_vapp...
    1: {
      assert (y <> x) by fsetdec.
      econstructor.
      1: {
        apply typing_evar.
        3: binds_dec.
        2: trivial.
        1: {
          constructor...
          2: {
            constructor...
            solve_wf_cap_cset_fvar.
          }
          constructor...
        }
      }
      2: crush.
      1: solve_wf_cap_cset_fvar.
    }
    1: {
      assert (y <> x) by fsetdec.
      constructor...
      constructor...
      2: {
        constructor...
        solve_wf_cap_cset_fvar.
      }
      constructor...
    }
  }
  constructor...
  constructor...
  constructor...
  constructor...
Qed.

(**
  ** #<a name="examples-sugar"></a>#  Desugaring block definitions
  **********************************************************)
(** Definitions can be desugared at some cost into block applications
    and boxes.  Note that we insert an <<unbox>> to work around
    System C's automatic box inferencing.
#
<pre><code class="language-effekt">
def using_def {c : S0} {
  def C() {
    c.doSomething();
    0
  }
  // body here...
  0
}

def sugar_def {c : S0} {
  (unbox {(C : () => Int at {c}) => 
    // body here
    0})
  (box {() => c.doSomething(); 0})
}
</code></pre>
#        
*)
  
Definition sugar_def (C : cap) (S1 : btyp) (b : blk) (s : stm) : stm :=
  (stm_vapp (blk_vabs (typ_capt S1 C) s) (exp_box C b)).

Definition sugar_var (x : atom) : blk :=
    (blk_unbox (exp_fvar x)).

Lemma sugar_def_typing : forall L E R b s (C : cap) Q S1 T2,
  R |= C ->
  wf_cap E C ->
  wf_cap E R ->
  E @ C ; Q |-blk b ~: S1 ->
  (forall x : atom, x `notin` L ->
    ([(x, bind_val (typ_capt S1 C))] ++ E) @ R ; Q |-stm (open_es s x) ~: T2) ->
  E @ R ; Q |-stm (sugar_def C S1 b s) ~: T2.
Proof with crush.
  intros. unfold sugar_def.
  econstructor.
  econstructor...
  econstructor...
Qed.

Lemma sugar_var_typing : forall E R f S1 C,
  wf_env E ->
  wf_cap E R ->
  R |= C ->
  binds f (bind_val (typ_capt S1 C)) E ->
  E @ R ; nil |-blk (sugar_var f) ~: S1.
Proof with crush.
  intros.
  assert (wf_sig nil) by constructor.
  econstructor...
Qed.

(**
  ** #<a name="examples-mutable-state"></a>#  Local Mutable State
  **********************************************************)
(** Finally, we formalize an example which models local, bounded mutable
    state.
#
<pre><code class="language-effekt">
interface ExampleCounter {
  def tick() : Int
}

def handleTick {prog : {() => Int} => Int} : Int {
  val stateFun = try {
    val res = prog {() => counter.tick()};
    box { prog } {(s : Int) => res}
  } with counter : ExampleCounter {
    def tick() {
      box { prog } {(s : Int) => (unbox resume(s))(s + 1)}
    }
  };
  (unbox stateFun)(0)
}
</code></pre>
#
*)
Definition handle_tick_term :=
  blk_babs (typ_bfun (typ_eff typ_base typ_base) typ_base)
    (stm_val
      (typ_capt (typ_vfun typ_base typ_base) (cset_bvar 0))
      (stm_try (cset_bvar 0) typ_base typ_base
        (stm_val typ_base (stm_bapp (blk_bvar 1) (cset_bvar 0) (blk_bvar 0))
          (stm_ret (exp_box (cset_bvar 1) (blk_vabs typ_base (stm_ret (exp_bvar 1))))))
        (stm_val
          (typ_capt (typ_vfun typ_base typ_base) (cset_bvar 1))
          (stm_vapp (blk_bvar 0) (exp_bvar 0))
          (stm_ret
            (exp_box (cset_bvar 1)
              (blk_vabs typ_base (stm_vapp (blk_unbox (exp_bvar 1))
                (exp_bvar 0)))))))
      (stm_vapp (blk_unbox (exp_bvar 0)) exp_const)).
Lemma handle_tick_term_typing :
  exists T, empty @ {}C ; nil |-blk handle_tick_term ~: T.
Proof.
Admitted.

(* begin hide *)
(*
Proof with notin_simpl; crush; try fsetdec; try fnsetdec; try lsetdec.
  eexists.
  econstructor.
  instantiate (2 := {}).
  intros prog progFresh.
  econstructor.
  {
    crush.
    econstructor.
    * autorewrite with csets.
      cbv [cset_fvar open_cset cset_bvar cset_references_bvar_dec cset_bvars
            cset_fvars cset_union cset_remove_bvar cset_lvars cset_subset_prop].
      destruct_set_mem 0 (NatSet.F.singleton 0); try nnotin_solve...
      repeat split; try fnsetdec; try lsetdec...
    * cbv [cset_fvar open_cset cset_bvar cset_references_bvar_dec cset_bvars
      cset_fvars cset_union cset_remove_bvar cset_lvars cset_subset_prop]...
      destruct_set_mem 0 (NatSet.F.singleton 0); try nnotin_solve...
      replace ((NatSet.F.union {}N (NatSet.F.remove 0 (NatSet.F.singleton 0))))
        with ({}N)...
      repeat econstructor...
      replace (x) with (prog).
      unfold binds. simpl. destruct (prog == prog)...
      crush.
    * cbv [cset_fvar open_cset cset_bvar cset_references_bvar_dec cset_bvars
      cset_fvars cset_union cset_remove_bvar cset_lvars cset_subset_prop]...
      destruct_set_mem 0 (NatSet.F.singleton 0); try nnotin_solve...
      replace ((NatSet.F.union {}N (NatSet.F.remove 0 (NatSet.F.singleton 0))))
        with ({}N)...
      autorewrite with csets.
      repeat econstructor...
    * intros tick. instantiate (1 := singleton prog). intros tickFr.
      crush.
      econstructor.
      {
        replace (open_cset 0 (cset_fvar tick)
        (open_cset 1 (cset_fvar prog) (cset_bvar 0))) with (cset_fvar tick).
        replace (open_cvt_rec 0 (cset_fvar tick) typ_base) with
          (open_cvt typ_base (cset_fvar tick)).
        eapply typing_bapp with (S1 := (typ_eff typ_base typ_base))...
        * econstructor. intros t tisTick.
          replace t with tick.
          exists (typ_eff typ_base typ_base).
          binds_dec.
          fsetdec.
        * econstructor...
          econstructor...
          econstructor...
          econstructor...
          { cbv [cset_union cset_fvar cset_fvars open_cset cset_lvars
                 cset_remove_bvar cset_references_bvar_dec cset_bvars
                 cset_bvar].
            destruct_set_mem 0 (NatSet.F.singleton 0); try nnotin_solve.
            autorewrite with csets.
            replace (NatSet.F.remove 0 (NatSet.F.singleton 0)) with ({}N)...
            econstructor.
            intros progOrTick progOrTickCond.
            rewrite AtomSetFacts.union_iff in *.
            destruct progOrTickCond...
            * replace progOrTick with prog...
              exists (typ_bfun (typ_eff typ_base typ_base) typ_base).
              binds_dec...
            * replace progOrTick with tick...
              exists (typ_eff typ_base typ_base)...
              binds_dec.
          }
          binds_dec; notin_solve.
          cbv [cset_union cset_fvar open_cset cset_bvar cset_bvars cset_fvars
            cset_lvars cset_lvar cset_references_bvar_dec cset_remove_bvar].
          destruct_set_mem 0 (NatSet.F.singleton 0); try nnotin_solve...
          autorewrite with csets. unfold cset_subset_prop; repeat split...
        * econstructor...
          econstructor...
          econstructor...
          econstructor...
          econstructor...
          { intros t tIsTick.
            replace t with tick...
            eexists.
            binds_dec.
          }
          binds_dec.
        * crush.
        * cbv [cset_union cset_fvar open_cset cset_bvar cset_bvars cset_fvars
              cset_lvars cset_lvar cset_references_bvar_dec cset_remove_bvar
          ].
          replace (NatSet.F.mem 1 (NatSet.F.singleton 0)) with false...
          destruct_set_mem 0 (NatSet.F.singleton 0); try nnotin_solve.
          f_equal...
          symmetry. rewrite <- NatSetFacts.not_mem_iff...
      }
      cbv [open_cvt_rec].
      intros s. instantiate (1 := singleton tick `union` singleton prog).
      intros sFr.
      cbv [open_es open_es_rec].
      destruct (1 === 1)...
      econstructor...
      replace (open_cset 0 (cset_fvar tick)
        (open_cset 1 (cset_fvar prog) (cset_bvar 1))) with (cset_fvar prog)...
      replace (open_cset 0 (cset_fvar prog) (cset_bvar 0)) with (cset_fvar prog)...
      econstructor...
      econstructor...
      intros p pIsProg. replace p with prog...
        exists (typ_bfun (typ_eff typ_base typ_base) typ_base). binds_dec...
      econstructor.
      instantiate (1 := singleton s `union` singleton tick `union` singleton prog).
      intros unused unusedFr.
      cbv [open_es open_es_rec].
      econstructor...
      econstructor...
      econstructor...
      econstructor...
      econstructor...
      econstructor...
      econstructor...
      binds_dec.
      econstructor...
      intros p pIsProg. replace p with prog...
      exists (typ_bfun (typ_eff typ_base typ_base) typ_base).
      binds_dec...
      cbv [cset_fvar cset_bvar open_cset cset_fvars cset_bvars cset_lvars
            cset_references_bvar_dec cset_union cset_remove_bvar].
      destruct_set_mem 0 (NatSet.F.singleton 0)...
      autorewrite with csets.
      f_equal...
      cbv [cset_fvar cset_bvar open_cset cset_fvars cset_bvars cset_lvars
      cset_references_bvar_dec cset_union cset_remove_bvar].
      destruct_set_mem 0 (NatSet.F.singleton 0)...
      replace (NatSet.F.mem 1 (NatSet.F.singleton 1)) with true...
      replace (NatSet.F.mem 0
      (NatSet.F.union {}N (NatSet.F.remove 1 (NatSet.F.singleton 1)))) with false...
      f_equal...
      symmetry; rewrite <- NatSetFacts.not_mem_iff...
      symmetry; rewrite <- NatSetFacts.mem_iff...
      replace
      (cset_union (open_cset 0 (cset_fvar prog) (cset_bvar 0)) (cset_fvar tick))
      with (cset_set (singleton tick `union` singleton prog) {}N {}L)...
      econstructor.
      intros progOrTick progOrTickCond.
      rewrite AtomSetFacts.union_iff in *.
      destruct progOrTickCond...
      { replace progOrTick with tick...
        exists (typ_eff typ_base typ_base).
        binds_dec... }
      { replace progOrTick with prog...
        exists (typ_bfun (typ_eff typ_base typ_base) typ_base)...
        binds_dec... }
      cbv [cset_union open_cset cset_fvar cset_fvars
           cset_references_bvar_dec cset_bvars cset_bvar
           cset_remove_bvar cset_lvars cset_lvar].
      destruct_set_mem 0 (NatSet.F.singleton 0)...
      f_equal...
    * intros unused unusedFr resume resumeFr.
      cbv [open_bs open_bs_rec open_es open_es_rec].
      destruct (0 === 0)...
      econstructor.
      econstructor...
      instantiate (1 := typ_base).
      eapply typing_bvar_capture...
      econstructor...
      econstructor...
      econstructor...
      econstructor...
      econstructor...
      replace (open_cset 0 (cset_fvar prog) (cset_bvar 0)) with (cset_fvar prog)...
      econstructor...
      intros p pIsProg; replace p with prog...
      exists (typ_bfun (typ_eff typ_base typ_base) typ_base).
      binds_dec...
      cbv [cset_fvar cset_fvar cset_bvar cset_bvars open_cset cset_union
            cset_references_bvar_dec cset_lvar cset_lvars]...
      destruct_set_mem 0 (NatSet.F.singleton 0)...
      f_equal...
      replace (open_cset 0 (cset_fvar prog) (cset_bvar 0)) with (cset_fvar prog)...
      econstructor...
      intros p pIsProg; replace p with prog...
      exists (typ_bfun (typ_eff typ_base typ_base) typ_base).
      binds_dec...
      cbv [cset_fvar cset_fvar cset_bvar cset_bvars open_cset cset_union
            cset_references_bvar_dec cset_lvar cset_lvars]...
      destruct_set_mem 0 (NatSet.F.singleton 0)...
      f_equal...
      econstructor...
      replace (open_cset 0 (cset_fvar prog) (cset_bvar 0)) with (cset_fvar prog)...
      econstructor...
      intros p pIsProg; replace p with prog...
      exists (typ_bfun (typ_eff typ_base typ_base) typ_base).
      binds_dec...
      cbv [cset_fvar cset_fvar cset_bvar cset_bvars open_cset cset_union
            cset_references_bvar_dec cset_lvar cset_lvars]...
      destruct_set_mem 0 (NatSet.F.singleton 0)...
      f_equal...
      binds_dec...
      replace (open_cset 0 (cset_fvar prog) (cset_bvar 0)) with (cset_fvar prog)...
      replace (open_cset 1 (cset_fvar prog) (cset_bvar 1)) with (cset_fvar prog)...
      cbv [cset_fvar cset_fvar cset_bvar cset_bvars open_cset cset_union
            cset_references_bvar_dec cset_lvar cset_lvars]...
      replace (NatSet.F.mem 1 (NatSet.F.singleton 1)) with true...
      f_equal...
      symmetry. rewrite <- NatSetFacts.mem_iff. fnsetdec.
      cbv [cset_fvar cset_fvar cset_bvar cset_bvars open_cset cset_union
            cset_references_bvar_dec cset_lvar cset_lvars]...
      destruct_set_mem 0 (NatSet.F.singleton 0)...
      f_equal...
      econstructor...
      econstructor...
      econstructor...
      econstructor...
      econstructor...
      replace (open_cset 0 (cset_fvar prog) (cset_bvar 0)) with (cset_fvar prog)...
      econstructor...
      econstructor...
      intros p pIsProg; replace p with prog...
      exists (typ_bfun (typ_eff typ_base typ_base) typ_base).
      binds_dec...
      cbv [cset_fvar cset_fvar cset_bvar cset_bvars open_cset cset_union
            cset_references_bvar_dec cset_lvar cset_lvars]...
      destruct_set_mem 0 (NatSet.F.singleton 0)...
      f_equal...
      replace (open_cset 0 (cset_fvar prog) (cset_bvar 0)) with (cset_fvar prog)...
      econstructor...
      intros p pIsProg; replace p with prog...
      exists (typ_bfun (typ_eff typ_base typ_base) typ_base).
      binds_dec...
      cbv [cset_fvar cset_fvar cset_bvar cset_bvars open_cset cset_union
            cset_references_bvar_dec cset_lvar cset_lvars]...
      destruct_set_mem 0 (NatSet.F.singleton 0)...
      f_equal...
      econstructor...
      binds_dec...
      instantiate (1 := singleton resume `union` singleton prog `union` singleton unused).
      intros s sFr.
      cbv [open_es open_es_rec].
      destruct (1 === 0); try nnotin_solve...
      econstructor...
      replace (open_cset 0 (cset_fvar prog) (cset_bvar 0)) with (cset_fvar prog)...
      replace (open_cset 1 (cset_fvar prog) (cset_bvar 1)) with (cset_fvar prog)...
      econstructor...
      econstructor...
      intros p pIsProg; replace p with prog...
      exists (typ_bfun (typ_eff typ_base typ_base) typ_base).
      binds_dec...
      econstructor.
      instantiate (1 := singleton s `union` singleton resume `union` singleton prog `union` singleton unused).
      intros unboxResume unboxResumeFr.
      econstructor.
      instantiate (1 := typ_base).
      econstructor.
      instantiate (1 := (cset_fvar prog)).
      econstructor...
      econstructor...
      econstructor...
      econstructor...
      econstructor...
      econstructor...
      econstructor...
      econstructor...
      econstructor...
      intros p pIsProg; replace p with prog...
      exists (typ_bfun (typ_eff typ_base typ_base) typ_base).
      binds_dec...
      econstructor...
      intros p pIsProg; replace p with prog...
      exists (typ_bfun (typ_eff typ_base typ_base) typ_base).
      binds_dec...
      econstructor...
      econstructor...
      intros p pIsProg; replace p with prog...
      exists (typ_bfun (typ_eff typ_base typ_base) typ_base).
      binds_dec...
      econstructor...
      binds_dec...
      econstructor...
      intros p pIsProg; replace p with prog...
      exists (typ_bfun (typ_eff typ_base typ_base) typ_base).
      binds_dec...
      unfold cset_subset_prop; repeat split...
      destruct (0 === 0)...
      econstructor...
      econstructor...
      econstructor...
      econstructor...
      econstructor...
      econstructor...
      econstructor...
      econstructor...
      econstructor...
      intros p pIsProg; replace p with prog...
      exists (typ_bfun (typ_eff typ_base typ_base) typ_base).
      binds_dec...
      econstructor...
      intros p pIsProg; replace p with prog...
      exists (typ_bfun (typ_eff typ_base typ_base) typ_base).
      binds_dec...
      econstructor...
      econstructor...
      intros p pIsProg; replace p with prog...
      exists (typ_bfun (typ_eff typ_base typ_base) typ_base).
      binds_dec...
      econstructor...
      binds_dec...
      cbv [cset_fvar cset_fvar cset_bvar cset_bvars open_cset cset_union
            cset_references_bvar_dec cset_lvar cset_lvars]...
      replace (NatSet.F.mem 1 (NatSet.F.singleton 1)) with true; f_equal...
      symmetry ;rewrite <- NatSetFacts.mem_iff...
      cbv [cset_fvar cset_fvar cset_bvar cset_bvars open_cset cset_union
            cset_references_bvar_dec cset_lvar cset_lvars]...
      replace (NatSet.F.mem 0 (NatSet.F.singleton 0)) with true; f_equal...
      symmetry ;rewrite <- NatSetFacts.mem_iff...
      replace   (open_cset 0 (cset_fvar prog) (cset_bvar 0)) with (cset_fvar prog).
      econstructor...
      intros p pIsProg; replace p with prog...
      exists (typ_bfun (typ_eff typ_base typ_base) typ_base).
      binds_dec...
      cbv [cset_fvar cset_fvar cset_bvar cset_bvars open_cset cset_union
      cset_references_bvar_dec cset_lvar cset_lvars]...
      replace (NatSet.F.mem 0 (NatSet.F.singleton 0)) with true; f_equal...
      symmetry ;rewrite <- NatSetFacts.mem_iff...
  }
  instantiate (2 := singleton prog).
  intros stateFun stateFunFr.
  econstructor.
  destruct (0 === 0)...
  econstructor...
  instantiate (2 := typ_base).
  instantiate (1 := typ_base).
  econstructor...
  econstructor...
  econstructor...
  econstructor...
  replace   (open_cset 0 (cset_fvar prog) (cset_bvar 0)) with (cset_fvar prog).
  econstructor...
  intros p pIsProg; replace p with prog...
  cbv [cset_fvar cset_fvar cset_bvar cset_bvars open_cset cset_union
  cset_references_bvar_dec cset_lvar cset_lvars]...
  replace (NatSet.F.mem 0 (NatSet.F.singleton 0)) with true; f_equal...
  symmetry ;rewrite <- NatSetFacts.mem_iff...
  econstructor...
  binds_dec.
  autorewrite with csets.
  replace   (open_cset 0 (cset_fvar prog) (cset_bvar 0)) with (cset_fvar prog)...
  cbv [cset_fvar cset_fvar cset_bvar cset_bvars open_cset cset_union
  cset_references_bvar_dec cset_lvar cset_lvars]...
  replace (NatSet.F.mem 0 (NatSet.F.singleton 0)) with true; f_equal...
  symmetry ;rewrite <- NatSetFacts.mem_iff...
  autorewrite with csets.
  econstructor...
  intros p pIsProg; replace p with prog...
  exists  (typ_bfun (typ_eff typ_base typ_base) typ_base)...
  binds_dec...
  econstructor...
  econstructor...
  econstructor...
  econstructor...
  replace   (open_cset 0 (cset_fvar prog) (cset_bvar 0)) with (cset_fvar prog)...
  econstructor...
  intros p pIsProg; replace p with prog...
  cbv [cset_fvar cset_fvar cset_bvar cset_bvars open_cset cset_union
  cset_references_bvar_dec cset_lvar cset_lvars]...
  replace (NatSet.F.mem 0 (NatSet.F.singleton 0)) with true; f_equal...
  symmetry ;rewrite <- NatSetFacts.mem_iff...
  econstructor...
  Unshelve.
  all: repeat exact {}.
Qed.
*)
(* end hide *)