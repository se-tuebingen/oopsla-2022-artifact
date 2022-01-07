(** #
<div class="source">
  The source of this file can be found on
  <a href="{{site.github}}/blob/main/coq/SystemC/Definitions.v">Github</a>.
</div>
# *)

Require Export Metatheory.
Require Export CaptureSets.
Require Import Signatures.
Require Export Coq.Program.Equality.

(** This file contains the definitions for System C. We include snippets of the paper
    as images to facilitate comparison.

    ** Table of Contents

    #<a href="##syntax">Syntax</a>#
    - #<a href="##syntax-types">Syntax of Types</a>#
    - #<a href="##syntax-terms">Syntax of Terms</a>#

    #<a href="##env">Environments and Signatures</a>#

    #<a href="##typing">Typing</a>#
    - #<a href="##typing-expression">Expression Typing</a>#
    - #<a href="##typing-block">Block Typing</a>#
    - #<a href="##typing-statement">Statement Typing</a>#

    #<a href="##semantics">Operational Semantics</a>#
    - #<a href="##values">Values</a>#
    - #<a href="##redexes">Machine Redexes</a>#
    - #<a href="##semantics-trivial">Trivial Reduction</a>#
    - #<a href="##stacks">Stacks, Contexts, and their Typing</a>#
    - #<a href="##abstract-machine">Abstract Machine</a>#
    - #<a href="##machine-reduction">Machine Reduction</a>#
    - #<a href="##machine-typing">Abstract Machine Typing</a>#
*)


(**
  * #<a name="syntax"></a>#  Syntax
  **********************************************************)

(** The definitions here reflect the definitions in Figure 1 from the paper.

    Please note that we base our proofs on a
    #<a href="https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/coqdoc/Fsub_Definitions.html">locally nameless representation</a>#.

    Consequently there are always two kinds of variables, free variables
    (such as [typ_fvar]) and locally bound variables (such as [typ_bvar]).

    Capture sets [cap] are records, containing sets of free variables, sets of bound variables, and sets of labels.
    *)


(**
 ** #<a name="syntax-types"></a># Syntax of Types
 *************************************************************)

(** Here, we define the syntax of types, as defined in Figure 1 in the paper.

  #<img src="img/syntax-types.png" alt="Syntax of types" class="fig" />#  *)

(** *** Value Types *)
Inductive vtyp : Type :=
  | typ_base : vtyp                 (* base types *)
  | typ_capt : btyp -> cap -> vtyp  (* boxed block types *)
  | typ_fvar : atom -> vtyp         (* (free) value-type variables *)
  | typ_bvar : nat -> vtyp          (* (bound) value-type variables *)

(** **** Differences from the paper:
    In the mechanization, we also additionally support
    value-type polymorphism, inherited from System F.
    This requires additional constructors for type variables ([typ_bvar] and [typ_fvar]),
    which are not present in the paper. 
    
    Finally, for simplicity, we only include one base type [typ_base] instead
    of multiple separate base types (as in the paper). *)

(** *** Block Types *)
with btyp : Type :=
  | typ_vfun : vtyp -> vtyp -> btyp    (* function types with value arguments *)
  | typ_bfun : btyp -> vtyp -> btyp    (* function types with tracked block arguments *)
  | typ_tfun : btyp -> btyp            (* type abstractions *)
  | typ_eff  : vtyp -> vtyp -> btyp    (* capability types *)
.

(** **** Differences from the paper:
    In the paper, we formalize multi-arity function types.
    This is awkward to work with in Coq so here we only mechanize single arity
    function types.

    We include two type constructors, [typ_vfun] for function types with value arguments
    (e.g. [Int -> Int]), and [typ_bfun] for function types with block arguments that
    are always tracked (e.g. [(f : Int -> Int) -> Int]).

    Since in the calculus function arguments are independent of each other, we do not
    expect any theoretical complications in the setting of a full multi-arity representation.

    Finally, type constructor [typ_eff T1 T2] is a block type that represents capabilities with an effect
    signature from [T1] to [T2]. To simplify the presentation, in the paper, this is represented
    as a function type [T1 -> T2]; this can be seen in rule TRY in Figure 2. *)



(**
 ** #<a name="syntax-terms"></a># Syntax of Terms
 **********************************************************)

(** In the following, we define the syntax of expressions, statements, and blocks.

    #<img src="img/syntax-terms.png" alt="Syntax of terms" class="fig" /># *)

(** *** Expressions *)
Inductive exp : Type :=
  | exp_bvar : nat -> exp         (* (bound) expression variables *)
  | exp_fvar : atom -> exp        (* (free) expression variables *)
  | exp_const : exp               (* primitives *)
  | exp_box : cap -> blk -> exp   (* box introduction *)

(** **** Differences from the paper:
    Expressions are formalized with only one primitive value, [exp_const]. *)

(** *** Statements *)
with stm : Type :=
  | stm_ret : exp -> stm                                (* returning *)
  | stm_val : vtyp -> stm -> stm -> stm                 (* sequencing *)
  | stm_def : cap -> btyp -> blk -> stm -> stm          (* block definition *)
  | stm_vapp : blk -> exp -> stm                        (* block application (to value arguments) *)
  | stm_bapp : blk -> cap -> blk -> stm                 (* block application (to block arguments) *)
  | stm_try : cap -> vtyp -> vtyp -> stm -> stm -> stm  (* handlers *)
  | stm_perform : blk -> exp -> stm                       (* performing an effect *)
  | stm_reset : label -> cap -> stm -> stm -> stm       (* runtime delimiter *)

(** **** Differences from the paper:
    Similar to the syntax of types, in the mechanization we have two different
    forms of application (instead of multi-arity). [stm_vapp] takes the block to call
    and an expression (value argument), while [stm_bapp] takes the block to call,
    a capture annotation (to avoid implementing capture inference in the mechanization),
    and a block argument.

    Similar to block application for blocks the handler construct [stm_try C T1 T2 s1 s2] models statements
    of the form
    <<
      try { f : Exc T1 T2 => s1 } with { (x: T1, k: (T2 => R @ C)) => s2 }
    >>

    That is, the capture annotion [C] corresponds to the capture set on the continuation [k].
    This can also be seen in Figure 2, rule TRY, but without an explicit annotation on the [stm_try].
    Types [T1] and [T2] are also explicitly annotated, which is not the case in the paper.

    Like in Figure 3 of the paper, we also include the syntax for runtime delimiters [stm_reset C T1 T2] that model
    statements of the form
    <<
      #_l { s1 } with { (x: T1, k: (T2 => R @ C)) => s2 }
    >>
  *)

(** *** Blocks *)
with blk : Type :=
  | blk_bvar : nat -> blk           (* (bound) block variables *)
  | blk_fvar : atom -> blk          (* (free) block variables *)
  | blk_vabs : vtyp -> stm -> blk   (* block implementation (with value argument) *)
  | blk_babs : btyp -> stm -> blk   (* block implementation (with block argument) *)
  | blk_unbox : exp -> blk          (* box elimination *)
  | blk_tabs : blk -> blk           (* value type abstraction *)
  | blk_tapp : blk -> vtyp -> blk   (* value type application *)
  | blk_handler : label -> blk      (* runtime capability *)
.
(** **** Differences from the paper:
    Again, as for statements and block types, we have two different forms
    of abstraction. [blk_vabs] to abstract over values and [blk_babs] to abstract
    over (tracked) blocks.

    In addition to the paper, we also include term-level syntax to abstract over
    value types [blk_tabs] and instantiate polymorphic blocks with value types [blk_tapp].

    The constructor [blk_handler] corresponds to the <<cap_l>> form in the paper and
    represents runtime capabilities.
  *)

(* begin hide *)

(** We declare the constructors for indices and variables to be
    coercions.  For example, if Coq sees a [nat] where it expects an
    [exp], it will implicitly insert an application of [exp_bvar];
    similar behavior happens for [atom]s.  Thus, we may write
    [(exp_abs typ_top (exp_app 0 x))] instead of [(exp_abs typ_top
    (exp_app (exp_bvar 0) (exp_fvar x)))]. *)

Coercion blk_bvar : nat >-> blk.
Coercion blk_fvar : atom >-> blk.
Coercion exp_bvar : nat >-> exp.
Coercion exp_fvar : atom >-> exp.
Coercion typ_bvar : nat >-> vtyp.
Coercion typ_fvar : atom >-> vtyp.


(** * Opening terms *)

(*  Opening expressions in expressions  *)
Fixpoint open_ee_rec (k : nat) (f : exp) (e : exp)  {struct e} : exp :=
  match e with
  | exp_bvar i => if k === i then f else (exp_bvar i)
  | exp_fvar x => exp_fvar x
  | exp_const => exp_const
  | exp_box C b => exp_box C (open_eb_rec k f b)
  end
with open_es_rec (k : nat) (f : exp) (s : stm) {struct s} : stm :=
  match s with
  | stm_ret e => stm_ret (open_ee_rec k f e)
  | stm_val T s1 s2 => stm_val T (open_es_rec k f s1) (open_es_rec (S k) f s2)
  | stm_def C S1 b s => stm_def C S1 (open_eb_rec k f b) (open_es_rec k f s)
  | stm_vapp b e => stm_vapp (open_eb_rec k f b) (open_ee_rec k f e)
  | stm_bapp b C g => stm_bapp (open_eb_rec k f b) C (open_eb_rec k f g)
  | stm_try C T1 T b h => stm_try C T1 T (open_es_rec k f b) (open_es_rec (S k) f h)
  | stm_reset l C b h => stm_reset l C (open_es_rec k f b) (open_es_rec (S k) f h)
  | stm_perform b e => stm_perform (open_eb_rec k f b) (open_ee_rec k f e)
  end
with open_eb_rec (k : nat) (f : exp) (b : blk) {struct b} : blk :=
  match b with
  | blk_bvar i => blk_bvar i
  | blk_fvar x => blk_fvar x
  | blk_vabs T s => blk_vabs T (open_es_rec (S k) f s)
  | blk_babs S1 s => blk_babs S1 (open_es_rec k f s)
  | blk_unbox e => blk_unbox (open_ee_rec k f e)
  | blk_tabs s => blk_tabs (open_eb_rec k f s)
  | blk_tapp s T => blk_tapp (open_eb_rec k f s) T
  | blk_handler l => blk_handler l
end.

(* Opening blocks in types *)
Fixpoint open_cvt_rec (k : nat) (C : cap) (T : vtyp)  {struct T} : vtyp :=
  match T with
  | typ_base => typ_base
  | typ_capt S1 C1 => typ_capt (open_cbt_rec k C S1) (open_cset k C C1)
  | typ_fvar a => typ_fvar a
  | typ_bvar n => typ_bvar n
  end
with open_cbt_rec (k : nat) (C : cap) (S1 : btyp)  {struct S1} : btyp :=
  match S1 with
  | typ_vfun T1 T2 => typ_vfun (open_cvt_rec k C T1) (open_cvt_rec k C T2)
  | typ_bfun S1 T => typ_bfun (open_cbt_rec k C S1) (open_cvt_rec (S k) C T)
  | typ_tfun T => typ_tfun (open_cbt_rec k C T)
  | typ_eff T1 T => typ_eff (open_cvt_rec k C T1) (open_cvt_rec k C T)
  end.


(*  Opening of term-level blocks in expression *)
Fixpoint open_be_rec (k : nat) (f : blk) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_const => exp_const
  | exp_box C1 b => exp_box C1 (open_bb_rec k f b)
  end
with open_bs_rec (k : nat) (f : blk) (s : stm) {struct s} : stm :=
  match s with
  | stm_ret e => stm_ret (open_be_rec k f e)
  | stm_val T s1 s2 => stm_val T (open_bs_rec k f s1) (open_bs_rec k f s2)
  | stm_def C1 S1 b s => stm_def C1 S1 (open_bb_rec k f b) (open_bs_rec (S k) f s)
  | stm_vapp b e => stm_vapp (open_bb_rec k f b) (open_be_rec k f e)
  | stm_bapp b C1 g => stm_bapp (open_bb_rec k f b) C1 (open_bb_rec k f g)
  | stm_try C1 T1 T b h => stm_try C1 T1 T (open_bs_rec (S k) f b) (open_bs_rec (S k) f h)
  | stm_reset l C1 b h => stm_reset l C1 (open_bs_rec k f b) (open_bs_rec (S k) f h)
  | stm_perform b e => stm_perform (open_bb_rec k f b) (open_be_rec k f e)
  end
with open_bb_rec (k : nat) (f : blk) (b : blk) {struct b} : blk :=
  match b with
  | blk_bvar i => if k === i then f else (blk_bvar i)
  | blk_fvar x => blk_fvar x
  | blk_vabs T s => blk_vabs T (open_bs_rec k f s)
  | blk_babs S1 s => blk_babs S1 (open_bs_rec (S k) f s)
  | blk_unbox e => blk_unbox (open_be_rec k f e)
  | blk_tabs s => blk_tabs (open_bb_rec k f s)
  | blk_tapp s T => blk_tapp (open_bb_rec k f s) T
  | blk_handler l => blk_handler l
  end.

(* Type level opening with capture sets *)
Fixpoint open_ce_rec (k : nat) (f : blk) (C : cap) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_const => exp_const
  | exp_box C1 b => exp_box (open_cset k C C1) (open_cb_rec k f C b)
  end

with open_cs_rec (k : nat) (f : blk) (C : cap) (s : stm) {struct s} : stm :=
  match s with
  | stm_ret e => stm_ret (open_ce_rec k f C e)
  | stm_val T s1 s2 => stm_val (open_cvt_rec k C T) (open_cs_rec k f C s1) (open_cs_rec k f C s2)
  | stm_def C1 S1 b s => stm_def (open_cset k C C1) (open_cbt_rec k C S1) (open_cb_rec k f C b) (open_cs_rec (S k) f C s)
  | stm_vapp b e => stm_vapp (open_cb_rec k f C b) (open_ce_rec k f C e)
  | stm_bapp b C1 g => stm_bapp (open_cb_rec k f C b) (open_cset k C C1) (open_cb_rec k f C g)
  | stm_try C1 T1 T b h => stm_try (open_cset k C C1) (open_cvt_rec k C T1) (open_cvt_rec k C T) (open_cs_rec (S k) f C b) (open_cs_rec (S k) f C h)
  | stm_reset l C1 b h => stm_reset l (open_cset k C C1) (open_cs_rec k f C b) (open_cs_rec (S k) f C h)
  | stm_perform b e => stm_perform (open_cb_rec k f C b) (open_ce_rec k f C e)
  end

with open_cb_rec (k : nat) (f : blk) (C : cap) (b : blk) {struct b} : blk :=
  match b with
  | blk_bvar i => if k === i then f else (blk_bvar i)
  | blk_fvar x => blk_fvar x
  | blk_vabs T s => blk_vabs (open_cvt_rec k C T) (open_cs_rec k f C s)
  | blk_babs S1 s => blk_babs  (open_cbt_rec k C S1) (open_cs_rec (S k) f C s)
  | blk_unbox e => blk_unbox (open_ce_rec k f C e)
  | blk_tabs s => blk_tabs (open_cb_rec k f C s)
  | blk_tapp s T => blk_tapp (open_cb_rec k f C s) (open_cvt_rec k C T)
  | blk_handler l => blk_handler l
  end.

(* Opening types in types *)
Fixpoint open_tvt_rec (k : nat) (U : vtyp) (T : vtyp) {struct T} : vtyp :=
  match T with
  | typ_base => typ_base
  | typ_capt S1 C1 => typ_capt (open_tbt_rec k U S1) C1
  | typ_fvar a => typ_fvar a
  | typ_bvar n => if (k === n) then U else typ_bvar n
  end
with open_tbt_rec (k : nat) (U : vtyp) (S1 : btyp) {struct S1} : btyp :=
  match S1 with
  | typ_vfun T1 T2 => typ_vfun (open_tvt_rec k U T1) (open_tvt_rec k U T2)
  | typ_bfun S1 T => typ_bfun (open_tbt_rec k U S1) (open_tvt_rec k U T)
  | typ_tfun T => typ_tfun (open_tbt_rec (S k) U T)
  | typ_eff T1 T => typ_eff (open_tvt_rec k U T1) (open_tvt_rec k U T)
  end.

(* Opening types in terms *)
Fixpoint open_te_rec (k : nat) (U : vtyp) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_const => exp_const
  | exp_box C1 b => exp_box C1 (open_tb_rec k U b)
  end
with open_ts_rec (k : nat) (U : vtyp) (s : stm) {struct s} : stm :=
  match s with
  | stm_ret e => stm_ret (open_te_rec k U e)
  | stm_val T s1 s2 => stm_val (open_tvt_rec k U T) (open_ts_rec k U s1) (open_ts_rec k U s2)
  | stm_def C1 S1 b s => stm_def C1 (open_tbt_rec k U S1) (open_tb_rec k U b) (open_ts_rec k U s)
  | stm_vapp b e => stm_vapp (open_tb_rec k U b) (open_te_rec k U e)
  | stm_bapp b C1 g => stm_bapp (open_tb_rec k U b) C1 (open_tb_rec k U g)
  | stm_try C1 T1 T b h => stm_try C1 (open_tvt_rec k U T1) (open_tvt_rec k U T)
                                      (open_ts_rec k U b) (open_ts_rec k U h)
  | stm_reset l C1 b h => stm_reset l C1 (open_ts_rec k U b) (open_ts_rec k U h)
  | stm_perform b e => stm_perform (open_tb_rec k U b) (open_te_rec k U e)
  end
with open_tb_rec (k : nat) (U : vtyp) (b : blk) {struct b} : blk :=
  match b with
  | blk_bvar i => blk_bvar i
  | blk_fvar x => blk_fvar x
  | blk_vabs T s => blk_vabs (open_tvt_rec k U T) (open_ts_rec k U s)
  | blk_babs S1 s => blk_babs (open_tbt_rec k U S1) (open_ts_rec k U s)
  | blk_unbox e => blk_unbox (open_te_rec k U e)
  | blk_tabs s => blk_tabs (open_tb_rec (S k) U s)
  | blk_tapp s T => blk_tapp (open_tb_rec k U s) (open_tvt_rec k U T)
  | blk_handler l => blk_handler l
  end.

(** Many common applications of opening replace index zero with an
    expression or variable.  The following definitions provide
    convenient shorthands for such uses.  Note that the order of
    arguments is switched relative to the definitions above.  For
    example, [(open_tt T X)] can be read as "substitute the variable
    [X] for index [0] in [T]" and "open [T] with the variable [X]."
    Recall that the coercions above let us write [X] in place of
    [(typ_fvar X)], assuming that [X] is an [atom]. *)

Definition open_ee T U := open_ee_rec 0 U T.
Definition open_es T U := open_es_rec 0 U T.
Definition open_eb T U := open_eb_rec 0 U T.
Definition open_cvt C U := open_cvt_rec 0 U C.
Definition open_cbt C U := open_cbt_rec 0 U C.
Definition open_be e U := open_be_rec 0 U e.
Definition open_bs e U := open_bs_rec 0 U e.
Definition open_bb e1 e2 := open_bb_rec 0 e2 e1.
Definition open_ce e f C := open_ce_rec 0 f C e.
Definition open_cs e f C := open_cs_rec 0 f C e.
Definition open_cb e f C := open_cb_rec 0 f C e.
Definition open_tvt T U := open_tvt_rec 0 U T.
Definition open_tbt T U := open_tbt_rec 0 U T.
Definition open_ts e U := open_ts_rec 0 U e.
Definition open_tb e U := open_tb_rec 0 U e.
Definition open_te e U := open_te_rec 0 U e.


(** ************************************************************ *)
(* Closed Terms *)

Inductive vtype : vtyp -> Prop :=
  | type_base :
      vtype typ_base
  | type_capt : forall S1 C1,
      btype S1 ->
      capt C1 ->
      vtype (typ_capt S1 C1)
  | type_fvar : forall a,
      vtype (typ_fvar a)
with btype : btyp -> Prop :=
  | type_vfun : forall T1 T2,
    vtype T1 ->
    vtype T2 ->
    btype (typ_vfun T1 T2)
  | type_bfun : forall L S1 T,
      btype S1 ->
      (forall X : atom, X `notin` L -> vtype (open_cvt T (cset_fvar X))) ->
      btype (typ_bfun S1 T)
  | type_tfun : forall L T,
      (forall X : atom, X `notin` L -> btype (open_tbt T X)) ->
      btype (typ_tfun T)
  | type_exc : forall T1 T,
      vtype T1 ->
      vtype T ->
      btype (typ_eff T1 T)
.

Inductive expr : exp -> Prop :=
  | expr_var : forall x,
      expr (exp_fvar x)
  | expr_const :
      expr exp_const
  | expr_box : forall C b,
      capt C ->
      block b ->
      expr (exp_box C b)

with stmt : stm -> Prop :=
  | stmt_ret : forall e,
      expr e ->
      stmt (stm_ret e)
  | stmt_val : forall L T b s,
      vtype T ->
      stmt b ->
      (forall X : atom, X `notin` L -> stmt (open_es s X)) ->
      stmt (stm_val T b s)
  | stmt_def : forall L C S1 b s,
      capt C ->
      btype S1 ->
      block b ->
      (* here we really only want to open with a block, but not the capture set, since it
         does not introduce a tracked binding! *)
      (forall X : atom, X `notin` L -> stmt (open_bs s X)) ->
      stmt (stm_def C S1 b s)
  | stmt_vapp : forall b e,
      block b ->
      expr e ->
      stmt (stm_vapp b e)
  | stmt_bapp : forall b1 C b2,
      block b1 ->
      capt C ->
      block b2 ->
      stmt (stm_bapp b1 C b2)
  | stmt_try : forall L C T1 T b h,
      capt C ->
      vtype T1 ->
      vtype T ->
      (forall X : atom, X `notin` L -> stmt (open_cs b X (cset_fvar X))) ->
      (forall v : atom, v `notin` L ->
        (forall k : atom, k `notin` (L `union` singleton v) ->
        stmt (open_bs (open_es h v) k))) ->
      stmt (stm_try C T1 T b h)
  | stmt_reset : forall L l C b h,
      capt C ->
      stmt b ->
      (forall v : atom, v `notin` L ->
       forall k : atom, k `notin` (L `union` singleton v) ->
       stmt (open_bs (open_es h v) k)) ->
      stmt (stm_reset l C b h)
  | stmt_throw : forall b e,
      block b ->
      expr e ->
      stmt (stm_perform b e)

with block : blk -> Prop :=
  | block_var : forall x,
      block (blk_fvar x)
  | block_vabs : forall L T s,
      vtype T ->
      (forall X : atom, X `notin` L -> stmt (open_es s X)) ->
      block (blk_vabs T s)
  | block_babs : forall L S1 s,
      btype S1 ->
      (* Here we open simultanously with X as block and captureset at the SAME index *)
      (forall X : atom, X `notin` L -> stmt (open_cs s X (cset_fvar X))) ->
      block (blk_babs S1 s)
  | block_unbox : forall e,
      expr e ->
      block (blk_unbox e)
  | block_tabs : forall L s,
      (forall X : atom, X `notin` L -> block (open_tb s X)) ->
      block (blk_tabs s)
  | block_tapp : forall b T,
      block b ->
      vtype T ->
      block (blk_tapp b T)
  | block_handler : forall l,
      block (blk_handler l)
.

(* end hide *)



(**
 * #<a name="env"></a># Environments and Signatures
 **********************************************************)

(** ** Environments
    Like in the paper, we use a single environment for value, block, and type abstraction.
    We formalize environments by representing them as association lists
    (lists of pairs of keys and values) whose keys are atoms.

    #<img src="img/environments.png" alt="Syntax of environments" class="fig" />#

    Instead of having two forms of block bindings, we index them by a coeffect defined below: *)

Inductive coeffect : Type :=
  | tracked : coeffect
  | capture : cap -> coeffect.

(** Basing our mechanization on an existing locally nameless proof, we
    reuse the infrastructure for environments.

    [Util.Metatheory], [Util.Environment], and [Util.Signatures] libraries provide functions,
    predicates, tactics, notations and lemmas that simplify working
    with environments.  The [Util.Environment] library treats environments
    as lists of type [list (atom * A)].

    Since environments map [atom]s, the type [A] should encode whether
    a particular binding is a typing or region assumption.  Thus,
    we instantiate [A] with the type [binding], defined below *)

Inductive binding : Type :=
  (*  x : T   *)
  | bind_val : vtyp -> binding
  | bind_blk : btyp -> coeffect -> binding
  (* X *)
  | bind_typ : binding.

Notation env := (list (atom * binding)).
Notation empty := (@nil (atom * binding)).

(** ** Signatures
    As a proof device, each runtime label (Figure 3 in the paper) is associated with a
    signature (that is the argument type and the result type of an effect operation).

    #<img src="img/signatures.png" alt="Syntax of signatures" class="fig" />#

    The tooling in [Util.Signatures] is a plain copy of [Util.Environment]. *)

Inductive signature : Type :=
  (* label : T1 (param type) T (result type)*)
  | bind_sig : vtyp -> vtyp -> signature.

Notation sig := (list (label * signature)).


(* begin hide *)

(** We also define a notation that makes it convenient to write one
    element lists.  This notation is useful because of our convention
    for building environments; see the examples below. *)

Notation "[ x ]" := (x :: nil).


(** ************************************************************ *)
(* Substitution *)

Fixpoint subst_ee (z : atom) (f : exp) (e : exp)  {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => if x == z then f else e
  | exp_const => exp_const
  | exp_box C b => exp_box C (subst_eb z f b)
  end
with subst_es (z : atom) (f : exp) (s : stm) {struct s} : stm :=
  match s with
  | stm_ret e => stm_ret (subst_ee z f e)
  | stm_val T s1 s2 => stm_val T (subst_es z f s1) (subst_es z f s2)
  | stm_def C S1 b s => stm_def C S1 (subst_eb z f b) (subst_es z f s)
  | stm_vapp b e => stm_vapp (subst_eb z f b) (subst_ee z f e)
  | stm_bapp b C g => stm_bapp (subst_eb z f b) C (subst_eb z f g)
  | stm_try C T1 T b h => stm_try C T1 T (subst_es z f b) (subst_es z f h)
  | stm_reset l C b h => stm_reset l C (subst_es z f b) (subst_es z f h)
  | stm_perform b e => stm_perform (subst_eb z f b) (subst_ee z f e)
  end
with subst_eb (z : atom) (f : exp) (b : blk) {struct b} : blk :=
  match b with
  | blk_bvar i => blk_bvar i
  | blk_fvar x => blk_fvar x
  | blk_vabs T s => blk_vabs T (subst_es z f s)
  | blk_babs S1 s => blk_babs S1 (subst_es z f s)
  | blk_unbox e => blk_unbox (subst_ee z f e)
  | blk_tabs e => blk_tabs (subst_eb z f e)
  | blk_tapp e T => blk_tapp (subst_eb z f e) T
  | blk_handler l => blk_handler l
  end.

Fixpoint subst_be (z : atom) (f : blk) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_const => exp_const
  | exp_box C1 b => exp_box C1 (subst_bb z f b)
  end
with subst_bs (z : atom) (f : blk) (s : stm) {struct s} : stm :=
  match s with
  | stm_ret e => stm_ret (subst_be z f e)
  | stm_val T s1 s2 => stm_val T (subst_bs z f s1) (subst_bs z f s2)
  | stm_def C1 S1 b s => stm_def C1 S1 (subst_bb z f b) (subst_bs z f s)
  | stm_vapp b e => stm_vapp (subst_bb z f b) (subst_be z f e)
  | stm_bapp b C1 g => stm_bapp (subst_bb z f b) C1 (subst_bb z f g)
  | stm_try C T1 T b h => stm_try C T1 T (subst_bs z f b) (subst_bs z f h)
  | stm_reset l C b h => stm_reset l C (subst_bs z f b) (subst_bs z f h)
  | stm_perform b e => stm_perform (subst_bb z f b) (subst_be z f e)
  end
with subst_bb (z : atom) (f : blk) (b : blk) {struct b} : blk :=
  match b with
  | blk_bvar i => blk_bvar i
  | blk_fvar x => if x == z then f else (blk_fvar x)
  | blk_vabs T s => blk_vabs T (subst_bs z f s)
  | blk_babs S1 s => blk_babs S1 (subst_bs z f s)
  | blk_unbox e => blk_unbox (subst_be z f e)
  | blk_tabs e => blk_tabs (subst_bb z f e)
  | blk_tapp e T => blk_tapp (subst_bb z f e) T
  | blk_handler l => blk_handler l
  end.

Fixpoint subst_cvt (z : atom) (C : cap) (T : vtyp) {struct T} : vtyp :=
  match T with
  | typ_base => typ_base
  | typ_capt S1 C1 => typ_capt (subst_cbt z C S1) (subst_cset z C C1)
  | typ_bvar n => typ_bvar n
  | typ_fvar a => typ_fvar a
  end
with subst_cbt (z : atom) (C : cap) (S1 : btyp) {struct S1} : btyp :=
  match S1 with
  | typ_vfun T1 T2 => typ_vfun (subst_cvt z C T1) (subst_cvt z C T2)
  | typ_bfun S1 T => typ_bfun (subst_cbt z C S1) (subst_cvt z C T)
  | typ_tfun T => typ_tfun (subst_cbt z C T)
  | typ_eff T1 T => typ_eff (subst_cvt z C T1) (subst_cvt z C T)
  end.

Fixpoint subst_ce (z : atom) (f : blk) (C : cap) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_const => exp_const
  | exp_box C1 b => exp_box (subst_cset z C C1) (subst_cb z f C b)
  end

with subst_cs (z : atom) (f : blk) (C : cap) (s : stm) {struct s} : stm :=
  match s with
  | stm_ret e => stm_ret (subst_ce z f C e)
  | stm_val T s1 s2 => stm_val (subst_cvt z C T) (subst_cs z f C s1) (subst_cs z f C s2)
  | stm_def C1 S1 b s => stm_def (subst_cset z C C1) (subst_cbt z C S1) (subst_cb z f C b) (subst_cs z f C s)
  | stm_vapp b e => stm_vapp (subst_cb z f C b) (subst_ce z f C e)
  | stm_bapp b C1 g => stm_bapp (subst_cb z f C b) (subst_cset z C C1) (subst_cb z f C g)
  | stm_try C1 T1 T b h => stm_try (subst_cset z C C1) (subst_cvt z C T1) (subst_cvt z C T) (subst_cs z f C b) (subst_cs z f C h)
  | stm_reset l C1 b h => stm_reset l (subst_cset z C C1) (subst_cs z f C b) (subst_cs z f C h)
  | stm_perform b e => stm_perform (subst_cb z f C b) (subst_ce z f C e)
  end

with subst_cb (z : atom) (f : blk) (C : cap) (b : blk) {struct b} : blk :=
  match b with
  | blk_bvar i => blk_bvar i
  | blk_fvar x => if x == z then f else (blk_fvar x)
  | blk_vabs T s => blk_vabs (subst_cvt z C T) (subst_cs z f C s)
  | blk_babs S1 s => blk_babs (subst_cbt z C S1) (subst_cs z f C s)
  | blk_unbox e => blk_unbox (subst_ce z f C e)
  | blk_tabs e => blk_tabs (subst_cb z f C e)
  | blk_tapp e T => blk_tapp (subst_cb z f C e) (subst_cvt z C T)
  | blk_handler l => blk_handler l
  end.

Fixpoint subst_tvt (z : atom) (U : vtyp) (T : vtyp) {struct T} : vtyp :=
  match T with
  | typ_base => typ_base
  | typ_capt S1 C1 => typ_capt (subst_tbt z U S1) C1
  | typ_bvar n => typ_bvar n
  | typ_fvar a => if (a == z) then U else typ_fvar a
  end
with subst_tbt (z : atom) (U : vtyp) (S1 : btyp) {struct S1} : btyp :=
  match S1 with
  | typ_vfun T1 T2 => typ_vfun (subst_tvt z U T1) (subst_tvt z U T2)
  | typ_bfun S1 T => typ_bfun (subst_tbt z U S1) (subst_tvt z U T)
  | typ_tfun T => typ_tfun (subst_tbt z U T)
  | typ_eff T1 T => typ_eff (subst_tvt z U T1) (subst_tvt z U T)
  end.


Fixpoint subst_te (Z : atom) (U : vtyp) (e : exp)  {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_const => exp_const
  | exp_box C b => exp_box C (subst_tb Z U b)
  end
with subst_ts (Z : atom) (U : vtyp) (s : stm) {struct s} : stm :=
  match s with
  | stm_ret e => stm_ret (subst_te Z U e)
  | stm_val T s1 s2 => stm_val (subst_tvt Z U T)
                                (subst_ts Z U s1)
                                (subst_ts Z U s2)
  | stm_def C S1 b s => stm_def C (subst_tbt Z U S1)
                                (subst_tb Z U b)
                                (subst_ts Z U s)
  | stm_vapp b e => stm_vapp (subst_tb Z U b) (subst_te Z U e)
  | stm_bapp b C g => stm_bapp (subst_tb Z U b) C (subst_tb Z U g)
  | stm_try C T1 T b h => stm_try C (subst_tvt Z U T1)
                                    (subst_tvt Z U T)
                                    (subst_ts Z U b)
                                    (subst_ts Z U h)
  | stm_reset l C b h => stm_reset l C (subst_ts Z U b) (subst_ts Z U h)
  | stm_perform b e => stm_perform (subst_tb Z U b) (subst_te Z U e)
  end
with subst_tb (Z : atom) (U : vtyp) (b : blk) {struct b} : blk :=
  match b with
  | blk_bvar i => blk_bvar i
  | blk_fvar x => blk_fvar x
  | blk_vabs T s => blk_vabs (subst_tvt Z U T) (subst_ts Z U s)
  | blk_babs S1 s => blk_babs (subst_tbt Z U S1) (subst_ts Z U s)
  | blk_unbox e => blk_unbox (subst_te Z U e)
  | blk_tabs e => blk_tabs (subst_tb Z U e)
  | blk_tapp e T => blk_tapp (subst_tb Z U e) (subst_tvt Z U T)
  | blk_handler l => blk_handler l
    end.

Definition subst_tbind (z : atom) (U : vtyp) (b : binding) : binding :=
  match b with
  | bind_val T => bind_val (subst_tvt z U T)
  | bind_blk s tracked => bind_blk (subst_tbt z U s) tracked
  | bind_blk s (capture C2) => bind_blk (subst_tbt z U s) (capture C2)
  | bind_typ => bind_typ
  end.

Definition subst_bbind (z : atom) (C : cap) (b : binding) : binding :=
  match b with
  | bind_val T => bind_val (subst_cvt z C T)
  | bind_blk s tracked => bind_blk (subst_cbt z C s) tracked
  | bind_blk s (capture C2) => bind_blk (subst_cbt z C s) (capture (subst_cset z C C2))
  | bind_typ => bind_typ
  end.


(* ********************************************************************** *)
(** * #<a name="wf"></a># Well-formedness *)

(* A capture set is wellformed if each entry is bound in the environment and tracked *)
Definition is_tracked (E : env) (xs : atoms) (x : atom) : Prop :=
  AtomSet.F.In x xs -> exists T, binds x (bind_blk T tracked) E.

Definition all_tracked (E : env) (xs : atoms) : Prop :=
  forall x, (AtomSet.F.In x xs -> exists T, binds x (bind_blk T tracked) E).

Inductive wf_cap : env -> cap -> Prop :=
  | wf_concret_cset : forall E xs ls,
      all_tracked E xs ->
      wf_cap E (cset_set xs {}N ls).

Inductive wf_vtyp : env -> vtyp -> Prop :=
  | wf_typ_base : forall E,
      wf_vtyp E typ_base
  | wf_typ_capt : forall E S1 C1,
      wf_btyp E S1 ->
      wf_cap E C1 ->
      wf_vtyp E (typ_capt S1 C1)
  | wf_typ_var : forall E (X : atom),
      binds X (bind_typ) E ->
      wf_vtyp E X
with  wf_btyp : env -> btyp -> Prop :=
  | wf_typ_vfun : forall E T1 T2,
      wf_vtyp E T1 ->
      wf_vtyp E T2 ->
      wf_btyp E (typ_vfun T1 T2)
  | wf_typ_bfun : forall L E S1 T2,
      wf_btyp E S1 ->
      (forall X : atom, X `notin` L ->
        wf_vtyp ([(X, bind_blk S1 tracked)] ++ E) (open_cvt T2 (cset_fvar X))) ->
      wf_btyp E (typ_bfun S1 T2)
  | wf_typ_tfun : forall L E T,
      (forall X : atom, X `notin` L ->
        wf_btyp ([(X, bind_typ)] ++ E) (open_tbt T X)) ->
      wf_btyp E (typ_tfun T)
  | wf_typ_eff : forall E T1 T,
      wf_vtyp E T1 ->
      wf_vtyp E T ->
      wf_btyp E (typ_eff T1 T).


(** An environment E is well-formed, denoted [(wf_env E)], if each
    atom is bound at most at once and if each binding is to a
    well-formed type.  This is a stronger relation than the [ok]
    relation defined in the [Environment] library.  We need this
    relation in order to restrict the typing relations,
    defined below, to contain only well-formed environments. *)

Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_tvar : forall (E : env) (X : atom),
      wf_env E ->
      X `notin` dom E ->
      wf_env ([(X, bind_typ)] ++ E)
  | wf_env_typ : forall (E : env) (x : atom) (T : vtyp),
      wf_env E ->
      wf_vtyp E T ->
      x `notin` dom E ->
      wf_env ([(x, bind_val T)] ++ E)
  | wf_env_blk_tracked : forall (E : env) (x : atom) (S1 : btyp),
      wf_env E ->
      wf_btyp E S1 ->
      x `notin` dom E ->
      wf_env ([(x, bind_blk S1 tracked)] ++ E)
  | wf_env_blk_transparent : forall (E : env) (x : atom) (S1 : btyp) (C : cap),
      wf_env E ->
      wf_btyp E S1 ->
      wf_cap E C ->
      x `notin` dom E ->
      wf_env ([(x, bind_blk S1 (capture C))] ++ E).

Inductive wf_sig : sig -> Prop :=
  | wf_sig_empty :
      wf_sig nil
  | wf_sig_typ : forall (E : sig) (x : label) (T1 T : vtyp),
      wf_sig E ->
      wf_vtyp empty T1 ->
      wf_vtyp empty T ->
      ~ LabelSet.F.In x (Signatures.dom E) ->
      wf_sig ([(x, bind_sig T1 T)] ++ E).


(* end hide *)


(**
 * #<a name="typing"></a># Typing
 **********************************************************)

(** Like in the paper, we model typing as three mutually inductive relations.

    Note that we use notation [C |= D] (pronounced "C admits D") instead
    of subset inclusion [D <= C] as it is used in the paper. *)
Notation "C |= D" := (cset_subset_prop D C) (at level 68).

Reserved Notation "E ; Q |-exp e ~: T" (at level 70, Q at next level).
Reserved Notation "E @ R ; Q |-blk b ~: S" (at level 70, R at next level, Q at next level).
Reserved Notation "E @ R ; Q |-stm s ~: T" (at level 70, R at next level, Q at next level).

(** Note on presentation: we use Gamma for E, and Xi for Q, both in the paper and in coqdoc. *)

(**
 ** #<a name="typing-expression"></a># Expression Typing
 **********************************************************)

(** #<img src="img/typing-expressions.png" alt="Typing of expressions" class="fig" /># *)
Inductive etyping : env -> sig -> exp -> vtyp -> Prop :=
  | typing_base : forall E Q,
      wf_env E ->
      wf_sig Q ->
      E ; Q |-exp exp_const ~: typ_base

  | typing_evar : forall E Q x T,
      wf_env E ->
      wf_sig Q ->
      binds x (bind_val T) E ->
      E ; Q |-exp (exp_fvar x) ~: T

  | typing_box : forall E Q (C : cap) S1 b,
      wf_cap E C ->
      (E @ C ; Q |-blk b ~: S1) ->
      E ; Q |-exp (exp_box C b) ~: (typ_capt S1 C)

where "E ; Q |-exp e ~: T" := (etyping E Q e T)

(** **** Differences from the paper:
    The three rules directly correspond to rules LIT, VAR, and BOXINTRO in
    the paper. As can be seen (all) typing judgements in Coq make wellformedness
    conditions explicit, which are left implicit in the paper. *)


(**
 ** #<a name="typing-block"></a># Block Typing
 **********************************************************)

(** #<img src="img/typing-blocks.png" alt="Typing of blocks" class="fig" /># *)
with btyping : env -> cap -> sig -> blk -> btyp -> Prop :=

  | typing_bvar_tracked : forall E R Q f S1,
      wf_env E ->
      wf_sig Q ->
      wf_cap E R ->
      binds f (bind_blk S1 tracked) E ->
      R |= cset_fvar f ->
      E @ R ; Q |-blk (blk_fvar f) ~: S1

  | typing_bvar_capture : forall E R Q f S1 (C : cap),
      wf_env E ->
      wf_sig Q ->
      wf_cap E R ->
      R |= C ->
      binds f (bind_blk S1 (capture C)) E ->
      E @ R ; Q |-blk (blk_fvar f) ~: S1

  | typing_unbox : forall E R Q e S1 C,
      E ; Q |-exp e ~: (typ_capt S1 C) ->
      wf_cap E R ->

      R |= C ->
      E @ R ; Q |-blk (blk_unbox e) ~: S1

  | typing_vabs : forall L E R Q T1 s T2,
      (forall x : atom, x `notin` L ->
        ([(x, bind_val T1)] ++ E) @ R ; Q |-stm (open_es s x) ~: T2) ->
      E @ R ; Q |-blk (blk_vabs T1 s) ~: (typ_vfun T1 T2)

  | typing_babs : forall L E R Q S1 s T2,
      (forall x : atom, x `notin` L ->
        ([(x, bind_blk S1 tracked)] ++ E) @ cset_union R (cset_fvar x) ; Q |-stm (open_cs s x (cset_fvar x)) ~: (open_cvt T2 (cset_fvar x))) ->
      E @ R ; Q |-blk (blk_babs S1 s) ~: (typ_bfun S1 T2)


(** **** Differences from the paper:
    Note that we build in subsumption on blocks (rule BSUB in the paper)
    into the rules as additional premises, instead of having one additional
    rule. This allows us to omit having to prove inversion of subeffecting.

    Instead, in [SystemC.Substitution.btyping_weaken_restriction] we show
    that rule SUB is admissible (and similar for subsumption on statements).

    In the paper, we use [C] for capture sets, but in the mechanization we
    speak of restrictions and use the metavariable [R]

    Rules from the paper map in the following way to the mechanization:
    - <<TRACKED>> maps to [typing_bvar_tracked]
    - <<TRANSPARENT>> maps to [typing_bvar_capture]
    - <<BLOCK>> maps to [typing_vabs] and [typing_babs]
    - <<BOXELIM>> maps to [typing_unbox]

    *** Additional Rules for Type Polymorphism *)


  | typing_tabs : forall L E R Q s T,
      (forall X : atom, X `notin` L ->
        ([(X, bind_typ)] ++ E) @ R ; Q |-blk (open_tb s X) ~: (open_tbt T X)) ->
      E @ R ; Q |-blk (blk_tabs s) ~: (typ_tfun T)

  | typing_tapp : forall E R Q s T T1,
      wf_vtyp E T1 ->
      E @ R ; Q |-blk s ~: (typ_tfun T) ->
      E @ R ; Q |-blk (blk_tapp s T1) ~: (open_tbt T T1)

(** *** Typing Effect Handlers
    #<img src="img/typing-cap.png" alt="Typing of handlers" class="fig" />#
    Like in the other rules, we bake subsumption into this rule. *)

  | typing_handler : forall E R Q l T1 T,
      wf_env E ->
      wf_sig Q ->
      wf_cap E R ->
      wf_vtyp E T ->
      (* We are allowed to use l: *)
      cset_references_lvar l R ->
      (* It has the correct type *)
      Signatures.binds l (bind_sig T1 T) Q ->
      E @ R ; Q |-blk blk_handler l ~: (typ_eff T1 T)

where "E @ R ; Q |-blk b ~: S" := (btyping E R Q b S)

(**
 ** #<a name="typing-statement"></a># Statement Typing
 **********************************************************)

(** #<img src="img/typing-statements.png" alt="Typing of statements" class="fig" /># *)
with styping : env -> cap -> sig -> stm -> vtyp -> Prop :=

  | typing_ret : forall E R Q e T,
      E ; Q |-exp e ~: T ->
      wf_cap E R ->
      E @ R ; Q |-stm (stm_ret e) ~: T

  | typing_val : forall L E R Q b s T1 T2,
      E @ R ; Q |-stm b ~: T1 ->
      (forall x : atom, x `notin` L ->
        ([(x, bind_val T1)] ++ E) @ R ; Q |-stm (open_es s x) ~: T2) ->
      E @ R ; Q |-stm (stm_val T1 b s) ~: T2

  | typing_def : forall L E R Q b s (C : cap) S1 T2,
      wf_cap E C ->
      E @ C ; Q |-blk b ~: S1 ->
      (* This is a transparent binding (not tracked), we do not open types. *)
      (forall x : atom, x `notin` L ->
        ([(x, bind_blk S1 (capture C))] ++ E) @ R ; Q |-stm (open_bs s x) ~: T2) ->
      E @ R ; Q |-stm (stm_def C S1 b s) ~: T2

  | typing_vapp : forall E R Q b e T1 T2,
      E @ R ; Q |-blk b ~: (typ_vfun T1 T2) ->
      E ; Q |-exp e ~: T1 ->
      E @ R ; Q |-stm (stm_vapp b e) ~: T2

  | typing_bapp : forall E R Q b1 b2 (C : cap) S1 T2,
      R |= C ->
      wf_cap E C ->
      E @ R ; Q |-blk b1 ~: (typ_bfun S1 T2) ->
      E @ C ; Q |-blk b2 ~: S1 ->
      E @ R ; Q |-stm (stm_bapp b1 C b2) ~: (open_cvt T2 C)

(** **** Differences from the paper:
    The rules correspond to the paper with the following mapping:
    - <<RET>> maps to [typing_ret]
    - <<VAL>> maps to [typing_val]
    - <<DEF>> maps to [typing_def]
    - <<APP>> maps to [typing_vapp] and [typing_bapp]

    In rule [typing_val], for simplicity we do not compute the union, but
    instead require both restrictions to be the same. This does not affect
    expressivity, since we can always use subsumption. *)


(** *** Typing Handling of Effects
    #<img src="img/typing-try.png" alt="Typing of handlers" class="fig" />#  *)
  | typing_try : forall L E R Q C b h T T1 T2,
      R |= C ->
      wf_cap E C ->
      wf_cap E R ->

      (* E, f : (Exc @ {*}) @ C union f |- h : T *)
      (forall f : atom, f `notin` L ->
        ([(f, bind_blk (typ_eff T2 T1) tracked)] ++ E) @ (cset_union C (cset_fvar f)) ; Q
          |-stm (open_cs b f (cset_fvar f)) ~: T) ->

      (* E, x : T1, k : (T2 -> T @ C) @ C |- h : T *)
      (forall (v : atom), v `notin` L ->
      (forall (f : atom), f `notin` (L `union` singleton v) ->
        ([(f, bind_blk (typ_vfun T1 T) (capture C))] ++
         [(v, bind_val T2)] ++ E) @ C ; Q
          |-stm (open_bs (open_es h v) f) ~: T)) ->

      E @ R ; Q |-stm (stm_try C T2 T1 b h) ~: T

(** **** Differences from the paper:
    As mentioned above, handling statements are annotated with a capture set [C].
    Also, we use the special type constructor [typ_eff] instead of a function type.
    Otherwise, the definition is a straightforward translation to Coq in locally nameless. *)

(** The following rule for [typing_reset] is a variation of [typing_try], not binding the capability
    anymore and with a singleton set [{l}] instead of [C]. *)

  | typing_reset : forall L E R Q C l b h T T1 T2,
      R |= C ->
      wf_cap E C ->
      wf_cap E R ->

      (* We require that the signature of l matches the type at the reset. *)
      Signatures.binds l (bind_sig T2 T1) Q ->

      E @ (cset_union C (cset_lvar l)) ; Q |-stm b ~: T ->
      (forall v : atom, v `notin` L ->
      (forall f : atom, f `notin` (L `union` singleton v) ->
        ([(f, bind_blk (typ_vfun T1 T) (capture C))] ++
          [(v, bind_val T2)] ++ E) @ C ; Q
          |-stm (open_bs (open_es h v) f) ~: T)) ->
      E @ R ; Q |-stm (stm_reset l C b h) ~: T

  | typing_throw : forall E R Q b e T T1,
      E @ R ; Q |-blk b ~: (typ_eff T1 T) ->
      E ; Q |-exp e ~: T1 ->
      E @ R ; Q |-stm (stm_perform b e) ~: T

where "E @ R ; Q |-stm s ~: T" := (styping E R Q s T).

(** Since we use locally nameless, the definition of typing uses the [binds] relation
    from the [Environment] library (in the [typing_var] case) and cofinite quantification
    in the cases involving binders (e.g., [typing_vabs], [typing_tabs], ...). *)

(** We have to define our own induction scheme to convince the termination checker *)

Scheme etyping_mutind := Induction for etyping Sort Prop
  with styping_mutind := Induction for styping Sort Prop
  with btyping_mutind := Induction for btyping Sort Prop.

Combined Scheme typing_ind from etyping_mutind, styping_mutind, btyping_mutind.

(**
 * #<a name="semantics"></a># Operational Semantics
 **********************************************************)

(** As described in the appendix of the paper, we mechanize the operational semantics
    in form of an abstract machine.

    However, the operational semantics is of a hybrid form: We _only_ use the abstract
    machine semantics for _statements_ and only if they affect the evaluation context / stack.

    For all other "trivial" reductions, we use a substitution based semantics with congruence rules.

    This separation makes it easier in the soundness proof to separate the "interesting" cases from
    the trivial ones. *)


(**
 ** #<a name="values"></a># Values
 **********************************************************)

(** Values are defined in the paper in the appendix.

    #<img src="img/values.png" alt="Values" class="fig" /># *)

Inductive evalue : exp -> Prop :=
  | value_const :
      evalue exp_const
  | value_box : forall C b,
      bvalue b ->
      capt C ->
      evalue (exp_box C b)

with bvalue : blk -> Prop :=
  | value_vfun : forall T s,
      block (blk_vabs T s) ->
      bvalue (blk_vabs T s)
  | value_bfun : forall S1 s,
      block (blk_babs S1 s) ->
      bvalue (blk_babs S1 s)
  | value_tfun : forall s,
      block (blk_tabs s) ->
      bvalue (blk_tabs s)
  | value_handler : forall l,
      bvalue (blk_handler l).

(**
 ** #<a name="redexes"></a># Machine Redexes
 **********************************************************)

(** Since we mechanize the operational semantics in terms of an abstract machine, we also
    define a predicate that describes when a statement can only be reduced in a larger context. *)

Inductive machine_redex : stm -> Prop :=
  | redex_ret : forall e,
      evalue e ->
      machine_redex (stm_ret e)
  | redex_val : forall T b s,
      machine_redex (stm_val T b s)
  | redex_try : forall C T1 T b s,
      machine_redex (stm_try C T1 T b s)
  | redex_reset : forall l C b s,
      machine_redex (stm_reset l C b s)
  | redex_throw : forall l e,
      evalue e ->
      machine_redex (stm_perform (blk_handler l) e).

(**
 ** #<a name="semantics-trivial"></a># Trivial Reduction
 **********************************************************)

(** #<img src="img/machine-semantics-trivial.png" alt="Semantics" class="fig" /># *)


Reserved Notation "e1 -->b e2" (at level 69).
Reserved Notation "e1 -->e e2" (at level 69).
Reserved Notation "e1 -->s e2" (at level 69).

(** *** #<a name="semantics-blocks"></a># Reduction of Blocks
    Blocks can always be reduced regardless of the context. In fact,
    the only reduction is box-unbox elimination ([bred_box]) and block substitution ([bred_box]).
  *)
Inductive bred : blk -> blk -> Prop :=
  | bred_box  : forall C b,
     blk_unbox (exp_box C b) -->b b

  | bred_tapp_cong : forall b b' T,
     b -->b b' ->
     blk_tapp b T -->b blk_tapp b' T

  | bred_tapp : forall s T,
     blk_tapp (blk_tabs s) T -->b (open_tb s T)
where "b1 -->b b2" := (bred b1 b2).

(** *** #<a name="semantics-blocks"></a># Reduction of Expressions
    Reduction on expressions is even simpler. Only boxed blocks can be reduced at all.
  *)
Inductive ered : exp -> exp -> Prop :=
  | ered_box : forall C b b',
      b -->b b' ->
      (exp_box C b) -->e (exp_box C b')
where "e1 -->e e2" := (ered e1 e2).


(** *** #<a name="semantics-statements"></a># Reduction of Statements  *)
Inductive sred : stm -> stm -> Prop :=
  | sred_ret : forall e e',
     e -->e e' ->
     stm_ret e -->s stm_ret e'

  | sred_vapp_3 : forall T s e,
      evalue e ->
      stm_vapp (blk_vabs T s) e -->s (open_es s e)

(** The remaining rules are congruences, omitted in the appendix of the paper. *)
  | sred_def_1 : forall C S1 b b' s,
      b -->b b' ->
      stm_def C S1 b s -->s stm_def C S1 b' s

  | sred_def_2 : forall C S1 b s,
      bvalue b ->
      stm_def C S1 b s -->s (open_bs s b)

  | sred_vapp_1 : forall b b' e,
      b -->b b' ->
      stm_vapp b e -->s stm_vapp b' e

  | sred_vapp_2 : forall b e e',
      e -->e e' ->
      stm_vapp b e -->s stm_vapp b e'

  | sred_bapp_1 : forall b1 b1' C b2,
      b1 -->b b1' ->
      stm_bapp b1 C b2 -->s stm_bapp b1' C b2

  | sred_bapp_2 : forall b1 C b2 b2',
      b2 -->b b2' ->
      stm_bapp b1 C b2 -->s stm_bapp b1 C b2'

  | sred_bapp_3 : forall S1 s C b2,
      bvalue b2 ->
      stm_bapp (blk_babs S1 s) C b2 -->s (open_cs s b2 C)

  | sred_throw_1 : forall b b' e,
      b -->b b' ->
      stm_perform b e -->s stm_perform b' e

  | sred_throw_2 : forall b e e',
      bvalue b ->
      e -->e e' ->
      stm_perform b e -->s stm_perform b e'

where "b1 -->s b2" := (sred b1 b2)
.



(**
 ** #<a name="stacks"></a># Stacks / Contexts
 **********************************************************)

(** #<img src="img/contexts.png" alt="contexts" class="fig" />#  *)

Inductive frame : Type :=
  (* val _ : T = []; s  *)
  | K : vtyp -> stm -> frame
  (* invariant: all elements in cap are bound in the tail of the ctx *)
  | H : label -> cap -> stm -> frame
.

(** We use the following abbreviation to denote runtime stacks *)
Notation ctx := (list frame).

(** The toplevel / empty runtime stack.  *)
Notation top := (@nil frame).

(** The following definition extracts labels, bound by the context. *)
Fixpoint bound_labels (c : ctx) : labels :=
  match c with
  | nil => {}L
  | K T s :: c => bound_labels c
  | H l C h :: c => LabelSet.F.union (bound_labels c) (LabelSet.F.singleton l)
  end.

(** We need to be able to plug an expression into a context. *)
Fixpoint plug (c : ctx) (e : exp) {struct c} : stm :=
  match c with
  | nil => stm_ret e
  | K T s :: c => stm_val T (plug c e) s
  | H l C h :: c => stm_reset l C (plug c e) h
  end.

Reserved Notation "R ; Q |-cnt k ~: T1 ~> T2" (at level 70, Q at next level).
Reserved Notation "R ; Q |-ctx c ~: T" (at level 70, Q at next level).

(** *** Context typing
    The following definition models the context typing from Appendix A.3 in the paper.

    #<img src="img/context-typing.png" alt="context typing" class="fig" />#

    It can be thought of as a variant of statement typing, flipped inside-out.
    [typing_ctx C Q K T] is parametrized by a set [C] of capabilities _bound_ in the
    context, global signatures [Q], the context [K] itself, and the type [T] at the hole. *)
Inductive typing_ctx : cap -> sig -> ctx -> vtyp -> Prop :=
  | typing_ctx_empty : forall Q T,
      wf_sig Q ->
      empty_cset ; Q |-ctx top ~: T
  | typing_ctx_frame : forall L R Q c T1 T2 s,
      R ; Q |-ctx c ~: T2 ->
      (forall X : atom, X `notin` L ->
        [(X, bind_val T1)] @ R ; Q |-stm (open_es s X) ~: T2) ->
      R ; Q |-ctx K T1 s :: c ~: T1
  | typing_ctx_try : forall L R Q l C c T T1 T2 s,
      R ; Q |-ctx c ~: T ->
      R |= C ->
      wf_cap empty C ->
      Signatures.binds l (bind_sig T1 T2) Q ->
      (forall v : atom, v `notin` L ->
      (forall f : atom, f `notin` (L `union` singleton v) ->
        [(f, bind_blk (typ_vfun T2 T) (capture C))] ++
        [(v, bind_val T1)] @ C ; Q
        |-stm (open_bs (open_es s v) f) ~: T)) ->
      cset_union C (cset_lvar l) ; Q |-ctx H l C s :: c ~: T

where "R ; Q |-ctx K ~: T" := (typing_ctx R Q K T).

(** *** Continuation typing
    Continuations are reversed contexts, so the typing rules are very similar.
    The rendering [R ; Q |-cnt K ~: T1 ~> T2] shows that continuations [K]
    have a function-like type. The hole has type [T1] and they are delimited at [T2].
    *)
Inductive typing_cnt : cap -> sig -> ctx -> vtyp -> vtyp -> Prop :=
  | typing_cnt_empty : forall R Q T,
      wf_cap empty R ->
      wf_sig Q ->
      R ; Q |-cnt top ~: T ~> T

  | typing_cnt_frame : forall L R Q c T1 T2 T3 s,
      R ; Q |-cnt c ~: T1 ~> T2 ->
      (forall X : atom, X `notin` L ->
        [(X, bind_val T2)] @ R ; Q |-stm (open_es s X) ~: T3) ->
      R ; Q |-cnt K T2 s :: c ~: T1 ~> T3

  | typing_cnt_handler : forall L R Q c l C T T1 T2 T3 h,
      wf_cap empty R ->
      cset_union C (cset_lvar l) ; Q |-cnt c ~: T1 ~> T2 ->
      R |= C ->
      Signatures.binds l (bind_sig T3 T) Q ->
      (forall v : atom, v `notin` L ->
      (forall f : atom, f `notin` (L `union` singleton v) ->
        [(f, bind_blk (typ_vfun T T2) (capture C))] ++
        [(v, bind_val T3)] @ C ; Q |-stm (open_bs (open_es h v) f) ~: T2)) ->
      R ; Q |-cnt (H l C h :: c) ~: T1 ~> T2

where "R ; Q |-cnt K ~: T1 ~> T2" := (typing_cnt R Q K T1 T2).


(**
 ** #<a name="abstract-machine"></a># Abstract Machine
 **********************************************************)

(** The abstract machine can be in one of two states.
    - either we simply step within a context [state_step],
    - or we unwind the stack to search for a delimiter [state_wind]. *)
Inductive state : Type :=
  | state_step (s : stm) (c : ctx) (Q : sig) : state
  | state_wind (l : label) (v : exp) (c : ctx) (k : ctx) (Q : sig) : state
.

Notation "〈throw l # v | c • k | Q 〉" := (state_wind l v c k Q).
Notation "〈 s | c | Q 〉" := (state_step s c Q).
Notation "〈 e | Q 〉" := (state_step (stm_ret e) top Q).

Reserved Notation "st1 --> st2" (at level 69).

(** The following predicate corresponds to values, but for machine states. *)
Inductive done : state -> Prop :=
  | done_ret : forall Q e,
      evalue e ->
      done 〈 e | Q 〉
.

(** *** #<a name="machine-reduction"></a># Reduction Steps
    For better comparison, we label the rules with the names from the paper.

    #<img src="img/machine-semantics-serious.png" alt="Semantics" class="fig" /># *)

Inductive step : state -> state -> Prop :=

(** (cong) *)
  | step_cong : forall Q s s' c,
      s -->s s' ->
      〈 s | c | Q 〉 --> 〈 s' | c | Q 〉

(** (pop) *)
  | step_pop_1 : forall Q v T s c,
      evalue v ->
      〈 stm_ret v | K T s :: c | Q 〉 --> 〈 open_es s v | c | Q 〉

(** (ret) *)
  | step_pop_2 : forall Q v l C s c,
      evalue v ->
      〈 stm_ret v | H l C s :: c | Q 〉 --> 〈 stm_ret v | c | Q 〉

(** (push) *)
  | step_push : forall Q s T b c,
      stmt (stm_val T b s) ->
      〈 stm_val T b s | c | Q 〉 --> 〈 b | K T s :: c | Q 〉

(** (try) *)
  | step_try : forall Q s h l C T2 T1 c,
      ~ LabelSet.F.In l (bound_labels c) ->
      ~ LabelSet.F.In l (Signatures.dom Q) ->
      〈 stm_try C T2 T1 s h | c | Q 〉-->
      〈 open_cs s (blk_handler l) (cset_lvar l) | H l C h :: c | [(l , bind_sig T2 T1)] ++ Q 〉

(** (reset) *)
  | step_reset : forall Q s h l C T1 T c,
      Signatures.binds l (bind_sig T1 T) Q ->
      〈 stm_reset l C s h | c | Q 〉--> 〈 s | H l C h :: c | Q 〉

(** (try), switch to search mode *)
  | step_throw : forall Q l v c,
       evalue v ->
      〈 stm_perform (blk_handler l) v | c | Q 〉-->
      〈throw l # v | c • top | Q 〉

(** (unwind) *)
  | step_unwind_1 : forall Q l v T s c k,
      〈throw l # v | K T s :: c • k | Q 〉--> 〈throw l # v | c • K T s :: k | Q 〉

(** (forward) *)
  | step_unwind_2 : forall Q l v l2 C h c k,
      l <> l2 ->
      〈throw l # v | H l2 C h :: c • k | Q 〉--> 〈throw l # v | c • H l2 C h :: k | Q 〉

(** (handle), switch back to step mode *)
  | step_handle : forall Q l v T T1 C h c k,
    (* the continuation: (y : T1) => reset l c h E[y]  *)
    Signatures.binds l (bind_sig T T1) Q ->
    〈throw l # v | H l C h :: c • k | Q 〉-->
    〈 open_bs (open_es h v)
      (blk_vabs T1 (plug (H l C h :: k) (exp_bvar 0))) | c | Q 〉

where "st1 --> st2" := (step st1 st2).

(** *** #<a name="machine-typing"></a># Abstract Machine Typing
    A machine state is simply by composing the previously defined typing judgements.

    For [typ_state], a the statement has to have the same type [T] that is expected
    by the context. *)

Inductive typing_state : state -> Prop :=
  | typ_step : forall R Q s c T,
      R ; Q |-ctx c ~: T ->
      nil @ R ; Q |-stm s ~: T ->
      typing_state〈 s | c | Q 〉

(** For [typ_wind] the signature bound at label [l] has to be [T3 -> T1],
    the value has to have the expected type [T3], and the types of the
    continuation and stack have to align at [T2].  *)
  | typ_wind : forall R Q l v c k T1 T2 T3,
      cset_references_lvar l R ->
      Signatures.binds l (bind_sig T3 T1) Q ->
      R ; Q |-ctx c ~: T2 ->
      R ; Q |-cnt k ~: T1 ~> T2 ->
      nil ; Q |-exp v ~: T3 ->
      typing_state〈throw l # v | c • k | Q 〉
.

Hint Constructors
  vtype btype block expr stmt
  wf_cap wf_vtyp wf_btyp wf_env
  evalue bvalue machine_redex
  bred sred done step state
: core.

Hint Resolve
  typing_evar typing_vapp typing_bapp typing_ret typing_val typing_handler typing_try typing_throw
  typing_cnt_empty typing_ctx_empty typing_ctx_try
: core.
