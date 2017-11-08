

(** Anthony Bordg ************************************************

Contents:

- The ring of endomorphisms of an abelian group ([rngofendabgr])
- (left) modules over a ring ([module]) and module homomorphisms ([modulefun])
- Submodules of a module ([submodule])
- Univalence for modules over a ring ([modules_univalence])
- Precategory of modules over a ring ([Mod])
- Category of modules over a ring ([category_Mod])
- Mod is a univalent category ([Mod_is_univalent])

***************************************************)

Require Import UniMath.Algebra.Rigs_and_Rings.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Algebra.Domains_and_Fields.
Require Import UniMath.Foundations.PartD.
Require Import Types_and_groups_with_operators.v
Require Import UniMath.CategoryTheory.Categories.


Local Open Scope addmonoid_scope.

(** * The ring of endomorphisms of an abelian group *)

(** Two binary operations on the set of endomorphisms of an abelian group *)

Definition monoidfun_to_isbinopfun {G : abgr} (f : monoidfun G G) : isbinopfun f := pr1 (pr2 f).

Definition rngofendabgr_op1 {G: abgr} : binop (monoidfun G G).
Proof.
  intros f g.
  apply (@monoidfunconstr _ _ (λ x : G, f x + g x)).
  apply tpair.
  - intros x x'.
    rewrite (monoidfun_to_isbinopfun f).
    rewrite (monoidfun_to_isbinopfun g).
    apply (abmonoidrer G).
  - rewrite (monoidfununel f).
    rewrite (monoidfununel g).
    rewrite (lunax G).
    reflexivity.
Defined.

Definition rngofendabgr_op2 {G : abgr} : binop (monoidfun G G).
Proof.
  intros f g.
  apply (monoidfuncomp f g).
Defined.

Notation "f + g" := (rngofendabgr_op1 f g) : abgr_scope.

(** the composition below uses the diagrammatic order following the general convention used in UniMath *)

Notation "f ∘ g" := (rngofendabgr_op2 f g) : abgr_scope.

(** The underlying set of the ring of endomorphisms of an abelian group *)

Definition setofendabgr (G : abgr) : hSet :=
   hSetpair (monoidfun G G) (isasetmonoidfun G G).

(** A few access functions *)

Definition pr1setofendabgr {G : abgr} (f : setofendabgr G) : G -> G := pr1 f.

Definition pr2setofendabgr {G : abgr} (f : setofendabgr G) : ismonoidfun (pr1 f) := pr2 f.

Definition setofendabgr_to_isbinopfun {G : abgr} (f : setofendabgr G) : isbinopfun (pr1setofendabgr f) := pr1 (pr2 f).

Definition setofendabgr_to_unel {G : abgr} (f : setofendabgr G) : pr1setofendabgr f 0 = 0 := pr2 (pr2setofendabgr f).

(** We endow setofendabgr with the two binary operations defined above *)

Definition setwith2binopofendabgr (G : abgr) : setwith2binop :=
   setwith2binoppair (setofendabgr G) (dirprodpair (rngofendabgr_op1) (rngofendabgr_op2)).

(** rngofendabgr_op1 G and rngofendabgr_op2 G are ring operations *)

(** rngofendabgr_op1 is a monoid operation *)

Local Open Scope abgr_scope.

Definition isassoc_rngofendabgr_op1 {G : abgr} : isassoc (@rngofendabgr_op1 G).
Proof.
   intros f g h.
   use total2_paths_f.
   - apply funextfun.
     intro.
     apply (pr2 G).
   - apply isapropismonoidfun.
Defined.

Definition setofendabgr_un0 {G: abgr} : monoidfun G G.
Proof.
   apply (@monoidfunconstr _ _ (λ x : G, 0)).
   apply dirprodpair.
     - intros x x'.
       rewrite (lunax G).
       reflexivity.
     - reflexivity.
Defined.

Definition islunit_setofendabgr_un0 {G : abgr} : islunit (@rngofendabgr_op1 G) setofendabgr_un0.
Proof.
   intro f.
   use total2_paths_f.
   - apply funextfun. intro x.
     apply (lunax G (pr1setofendabgr f x)).
   - apply isapropismonoidfun.
Defined.

Definition isrunit_setofendabgr_un0 {G : abgr} : isrunit (@rngofendabgr_op1 G) setofendabgr_un0.
Proof.
   intros f.
   use total2_paths_f.
   - apply funextfun. intro x.
     apply (runax G (pr1setofendabgr f x)).
   - apply isapropismonoidfun.
Defined.

Definition isunit_setofendabgr_un0 {G : abgr} : isunit (@rngofendabgr_op1 G) setofendabgr_un0 :=
  isunitpair islunit_setofendabgr_un0 isrunit_setofendabgr_un0.

Definition isunital_rngofendabgr_op1 {G : abgr} : isunital (@rngofendabgr_op1 G) :=
  isunitalpair setofendabgr_un0 isunit_setofendabgr_un0.

Definition ismonoidop_rngofendabgr_op1 {G : abgr} : ismonoidop (@rngofendabgr_op1 G) :=
   mk_ismonoidop isassoc_rngofendabgr_op1 isunital_rngofendabgr_op1.

Local Close Scope abgr_scope.

(** rngofendabgr_op1 is a group operation *)

Definition setofendabgr_inv {G : abgr} : monoidfun G G -> monoidfun G G.
Proof.
   intro f.
   apply (@monoidfunconstr G G (λ x : G, grinv G (pr1setofendabgr f x))).
   apply dirprodpair.
   - intros x x'.
     rewrite (setofendabgr_to_isbinopfun f).
     rewrite (grinvop G).
     apply (commax G).
   - rewrite (setofendabgr_to_unel f).
     apply (grinvunel G).
Defined.

Local Open Scope abgr_scope.

Definition islinv_setofendabgr_inv {G : abgr} : islinv (@rngofendabgr_op1 G) setofendabgr_un0 setofendabgr_inv.
Proof.
   intro f.
   use total2_paths_f.
   - apply funextfun. intro x.
     apply (grlinvax G).
   - apply isapropismonoidfun.
Defined.

Definition isrinv_setofendabgr_inv {G : abgr} : isrinv (@rngofendabgr_op1 G) setofendabgr_un0 setofendabgr_inv.
Proof.
   intro f.
   use total2_paths_f.
   - apply funextfun. intro x.
     apply (grrinvax G).
   - apply isapropismonoidfun.
Defined.

Definition isinv_setofendabgr_inv {G : abgr} : isinv (@rngofendabgr_op1 G) (unel_is (@ismonoidop_rngofendabgr_op1 G)) setofendabgr_inv :=
  mk_isinv islinv_setofendabgr_inv isrinv_setofendabgr_inv.

Definition invstruct_setofendabgr_inv {G : abgr} : invstruct (@rngofendabgr_op1 G) ismonoidop_rngofendabgr_op1 :=
   mk_invstruct (@setofendabgr_inv G) (@isinv_setofendabgr_inv G).

Definition isgrop_rngofendabgr_op1 {G : abgr} : isgrop (@rngofendabgr_op1 G) :=
   isgroppair ismonoidop_rngofendabgr_op1 invstruct_setofendabgr_inv.

Definition iscomm_rngofendabgr_op1 {G : abgr} : iscomm (@rngofendabgr_op1 G).
Proof.
   intros f g.
   use total2_paths_f.
   - apply funextfun. intro x.
     apply (commax G).
   - apply (isapropismonoidfun).
Defined.

Definition isabgrop_rngofendabgr_op1 {G : abgr} : isabgrop (@rngofendabgr_op1 G) :=
  mk_isabgrop isgrop_rngofendabgr_op1 iscomm_rngofendabgr_op1.

(** rngofendabgr_op2 is a monoid operation *)

Definition isassoc_rngofendabgr_op2 {G : abgr} : isassoc (@rngofendabgr_op2 G).
Proof.
  intros f g h.
  use total2_paths_f.
  - apply funcomp_assoc.
  - apply isapropismonoidfun.
Defined.

Definition setofendabgr_un1 {G: abgr} : monoidfun G G.
Proof.
   apply (@monoidfunconstr _ _ (idfun G)).
   apply dirprodpair.
   - intros x x'. reflexivity.
   - reflexivity.
Defined.

Definition islunit_setofendabgr_un1 {G : abgr} : islunit (@rngofendabgr_op2 G) setofendabgr_un1.
Proof.
   intro f.
   use total2_paths_f.
   - apply funextfun. intro x. reflexivity.
   - apply isapropismonoidfun.
Defined.

Definition isrunit_setofendabgr_un1 {G : abgr} : isrunit (@rngofendabgr_op2 G) setofendabgr_un1.
Proof.
   intros f.
   use total2_paths_f.
   - apply funextfun. intro x. reflexivity.
   - apply isapropismonoidfun.
Defined.

Definition isunit_setofendabgr_un1 {G : abgr} : isunit (@rngofendabgr_op2 G) setofendabgr_un1 :=
  isunitpair islunit_setofendabgr_un1 isrunit_setofendabgr_un1.

Definition isunital_rngofendabgr_op2 {G : abgr} : isunital (@rngofendabgr_op2 G) :=
  isunitalpair setofendabgr_un1 isunit_setofendabgr_un1.

Definition ismonoidop_rngofendabgr_op2 {G : abgr} : ismonoidop (@rngofendabgr_op2 G) :=
   mk_ismonoidop isassoc_rngofendabgr_op2 isunital_rngofendabgr_op2.

(** rngofendabgr_op2 is distributive over rngofendabgr_op1 *)

Definition isldistr_setofendabgr_op {G : abgr} : isldistr (@rngofendabgr_op1 G) (@rngofendabgr_op2 G).
Proof.
   intros f g h.
   use total2_paths_f.
   - apply funextfun. intro x. reflexivity.
   - apply isapropismonoidfun.
Defined.

Definition isrdistr_setofendabgr_op {G : abgr} : isrdistr (@rngofendabgr_op1 G) (@rngofendabgr_op2 G).
Proof.
   intros f g h.
   use total2_paths_f.
   - apply funextfun. intro x.
     apply (setofendabgr_to_isbinopfun h).
   - apply isapropismonoidfun.
Defined.

Definition isdistr_setofendabgr_op {G : abgr} : isdistr (@rngofendabgr_op1 G) (@rngofendabgr_op2 G) :=
   dirprodpair isldistr_setofendabgr_op isrdistr_setofendabgr_op.

Definition isrngops_setofendabgr_op {G : abgr} : isrngops (@rngofendabgr_op1 G) (@rngofendabgr_op2 G) :=
   mk_isrngops isabgrop_rngofendabgr_op1 ismonoidop_rngofendabgr_op2 isdistr_setofendabgr_op.

(** The set of endomorphisms of an abelian group is a ring *)

Definition rngofendabgr (G : abgr) : rng :=
   @rngpair (setwith2binopofendabgr G) (@isrngops_setofendabgr_op G).


(** * The definition of the small type of (left) R-modules over a ring R *)

Definition module_struct (R : rng) (G : abgr) : UU := rngfun R (rngofendabgr G).

Definition module (R : rng) : UU := ∑ G, module_struct R G.

Definition pr1module {R : rng} (M : module R) : abgr := pr1 M.

Coercion pr1module : module >-> abgr.

Definition pr2module {R : rng} (M : module R) : module_struct R (pr1module M) := pr2 M.

Identity Coercion id_module_struct : module_struct >-> rngfun.

Definition modulepair {R : rng} (G : abgr) (f : module_struct R G) : module R := tpair _ G f.

(** The multiplication defined from a module *)

Definition module_mult {R : rng} (M : module R) : R -> M -> M := λ r : R, λ x : M, (pr1setofendabgr (pr2module M r) x).

Notation "r * x" := (module_mult _ r x) : module_scope.

Delimit Scope module_scope with module.

Local Open Scope rig_scope.

Definition rigfun_to_unel_rigaddmonoid {X Y : rig} (f : rigfun X Y) : f 0 = 0 := pr2 (pr1 (pr2 f)).

Local Close Scope rig_scope.

Local Open Scope module.

Definition module_mult_0_to_0 {R : rng} {M : module R} (x : M) : rngunel1 * x = @unel M.
Proof.
   unfold module_mult. cbn.
   assert (pr2module M rngunel1 = @rngunel1 (rngofendabgr M)).
   - exact (rigfun_to_unel_rigaddmonoid (pr2module M)).
   - rewrite X.
     reflexivity.
Defined.

(** To construct a module from a left action satisfying four axioms *)

Local Open Scope addmonoid.

Definition mult_isldistr_wrt_grop {R : rng} {G : abgr} (m : R -> G -> G) : UU := ∏ r : R, ∏ x y : G, m r (x + y) = (m r x) + (m r y).

Definition mult_isrdistr_wrt_rngop1 {R : rng} {G : abgr} (m : R -> G -> G) : UU := ∏ r s : R, ∏ x : G, m (op1 r s) x = (m r x) + (m s x).

Definition mult_isrdistr_wrt_rngop2 {R : rng} {G : abgr} (m : R -> G -> G) : UU := ∏ r s : R, ∏ x : G, m (op2 r s) x = m s (m r x).

Definition mult_unel {R : rng} {G : abgr} (m : R -> G -> G) : UU := ∏ x : G, m rngunel2 x = x.

Local Close Scope addmonoid.

Definition mult_to_rngofendabgr {R : rng} {G : abgr} {m : R -> G -> G} (ax1 : mult_isldistr_wrt_grop m) (r : R) : rngofendabgr G.
Proof.
    use monoidfunconstr.
    intro x. exact (m r x).
    apply dirprodpair.
    + intros x y. apply ax1.
    + apply (grlcan G (m r (unel G))).
      rewrite runax.
      rewrite <- (ax1 r (unel G) (unel G)).
      rewrite runax.
      apply idpath.
Defined.

Definition mult_to_module_struct {R : rng} {G : abgr} {m : R -> G -> G} (ax1 : mult_isldistr_wrt_grop m) (ax2 : mult_isrdistr_wrt_rngop1 m)
  (ax3 : mult_isrdistr_wrt_rngop2 m) (ax4 : mult_unel m) : module_struct R G.
Proof.
  split with (λ r : R, mult_to_rngofendabgr ax1 r).
  apply dirprodpair.
  - apply dirprodpair.
    + intros r s.
      use total2_paths2_f.
      * apply funextfun. intro x. apply ax2.
      * apply isapropismonoidfun.
    + use total2_paths2_f.
      * apply funextfun. intro x. change (m rngunel1 x = unel G). apply (grlcan G (m (rngunel1) x)). rewrite runax.
        rewrite <- (ax2 rngunel1 rngunel1 x). rewrite rngrunax1. apply idpath.
      * apply isapropismonoidfun.
  -  apply dirprodpair.
     + intros r s.
       use total2_paths2_f.
       * apply funextfun. intro x. apply ax3.
       * apply isapropismonoidfun.
     + use total2_paths2_f.
       * apply funextfun. intro x. apply ax4.
       * apply isapropismonoidfun.
Defined.

Definition mult_to_module {R : rng} {G : abgr} {m : R -> G -> G} (ax1 : mult_isldistr_wrt_grop m) (ax2 : mult_isrdistr_wrt_rngop1 m)
  (ax3 : mult_isrdistr_wrt_rngop2 m) (ax4 : mult_unel m) : module R := modulepair G (mult_to_module_struct ax1 ax2 ax3 ax4).

(** (left) R-module homomorphism *)

Definition islinear {R : rng} {M N : module R} (f : M -> N) :=
  ∏ r : R, ∏ x : M, f (r * x) = r * (f x).

Definition isaprop_islinear {R : rng} {M N : module R} (f : M -> N) : isaprop (islinear f).
Proof.
   use impred. intro r.
   use impred. intro x.
   apply setproperty.
Defined.

Definition islinear_id {R : rng} (M : module R) : islinear (idfun M).
Proof.
  intros r x.
  unfold idfun. apply idpath.
Defined.

Definition linearfun {R : rng} (M N : module R) : UU := ∑ f : M -> N, islinear f.

Definition linearfunpair {R : rng} {M N : module R} (f : M -> N) (is : islinear f) : linearfun M N := tpair _ f is.

Definition pr1linearfun {R : rng} {M N : module R} (f : linearfun M N) : M -> N := pr1 f.

Coercion pr1linearfun : linearfun >-> Funclass.

Definition islinearfuncomp {R : rng} {M N P : module R} (f : linearfun M N) (g : linearfun N P) : islinear (funcomp (pr1 f) (pr1 g)).
Proof.
  intros r x.
  unfold funcomp.
  rewrite (pr2 f).
  rewrite (pr2 g).
  apply idpath.
Defined.

Definition linearfuncomp {R : rng} {M N P : module R} (f : linearfun M N) (g : linearfun N P) : linearfun M P :=
  tpair _ (funcomp f g) (islinearfuncomp f g).

Definition ismodulefun {R : rng} {M N : module R} (f : M -> N) : UU :=
   (isbinopfun f) × (islinear f).

Lemma isapropismodulefun {R : rng} {M N : module R} (f : M -> N) : isaprop (ismodulefun f).
Proof.
   refine (@isofhleveldirprod 1 (isbinopfun f) (islinear f) _ _).
   exact (isapropisbinopfun f).
   exact (isaprop_islinear f).
Defined.

Definition ismodulefun_id {R : rng} (M : module R) : ismodulefun (idfun M).
Proof.
  apply dirprodpair.
  - intros x y. apply idpath.
  - intros. apply  islinear_id.
Defined.

Definition modulefun {R : rng} (M N : module R) : UU := ∑ f : M -> N, ismodulefun f.

Definition modulefunpair {R : rng} {M N : module R} (f : M -> N) (is : ismodulefun f) : modulefun M N :=
   tpair _ f is.

Definition pr1modulefun {R : rng} {M N : module R} (f : modulefun M N) : M -> N := pr1 f.

Coercion pr1modulefun : modulefun >-> Funclass.

Definition modulefun_to_isbinopfun {R : rng} {M N : module R} (f : modulefun M N) : isbinopfun (pr1modulefun f) := pr1 (pr2 f).

Definition modulefun_to_binopfun {R : rng} {M N : module R} (f : modulefun M N) : binopfun M N :=
  binopfunpair (pr1modulefun f) (modulefun_to_isbinopfun f).

Definition modulefun_to_islinear {R : rng} {M N : module R} (f : modulefun M N): islinear (pr1modulefun f) := pr2 (pr2 f).

Definition modulefun_to_linearfun {R : rng} {M N : module R} (f : modulefun M N) : linearfun M N :=
  linearfunpair f (modulefun_to_islinear f).

Definition modulefun_unel {R : rng} {M N : module R} (f : modulefun M N) : f (unel M) = unel N.
Proof.
   rewrite <- (module_mult_0_to_0 (unel M)).
   rewrite ((modulefun_to_islinear f) rngunel1 (unel M)).
   rewrite (module_mult_0_to_0 _).
   reflexivity.
Defined.

(** From modules to abelian groups with operators *)

Definition module_to_grwithaction {R : rng} (M : module R) : grwithaction R := tpair (λ G : gr, action R G) (pr1module M) (module_mult M).

Definition module_to_ishdistr_action {R : rng} (M : module R) :
  ishdistr_action (@op (gr_to_typewithbinop M)) (module_mult M).
Proof.
  intros r x y.
  apply (pr1 (pr2 (pr2 M r))).
Defined.

Definition module_to_grwithoperators {R : rng} (M : module R) : grwithoperators R :=
  tpair _ (module_to_grwithaction M) (module_to_ishdistr_action M).

Coercion module_to_grwithoperators : module >-> grwithoperators .


(** Submodules of a module *)

Definition submodule {R : rng} (M : module R) : UU := stable_subgr M.

Definition submodule_to_gr {R : rng} {M : module R} (N : submodule M) : gr := stable_subgr_to_gr N.

Definition submodule_to_abgr {R : rng} {M : module R} (N : submodule M) : abgr.
Proof.
  use abgrpair.
  - exact (pr1 (submodule_to_gr N)).
  - apply dirprodpair.
    + exact (pr2 (submodule_to_gr N)).
    + intros x y. use total2_paths_f.
      * apply (dirprod_pr2 (pr2 (pr1module M))).
      * apply propproperty.
Defined.

Definition submodule_to_module_struct {R : rng} {M : module R} (N : submodule M) : module_struct R (submodule_to_abgr N).
Proof.
  use rngfunconstr.
  - intro r.
    use monoidfunconstr.
    + intro x.
      split with (module_mult M r (pr1 x)).
      apply (pr2 (pr2 N) r (pr1 x)).
      apply (pr2 x).
    + apply dirprodpair.
      * intros x y.
        use total2_paths2_f.
        apply (pr1 (pr2 (pr2 M r))).
        apply propproperty.
      * use total2_paths2_f.
        apply (pr2 (pr2 (pr2 M r))).
        apply propproperty.
  - apply dirprodpair.
    + apply dirprodpair.
      * intros r s.
        use total2_paths2_f.
        apply funextfun. intro x.
        use total2_paths2_f.
        assert (p : pr1 (pr1 (pr2 M) (@op1 R r s)) ~ pr1 (@op1 (rngofendabgr (pr1 M)) (pr1 (pr2 M) r) (pr1 (pr2 M) s))).
        use eqtohomot. apply (base_paths _ _ (dirprod_pr1 (dirprod_pr1 (pr2 (pr2 M))) r s)).
        apply (p (pr1 x)).
        apply propproperty.
        apply isapropismonoidfun.
      * use total2_paths2_f.
        apply funextfun. intro x.
        use total2_paths2_f.
        assert (p : pr1 (pr1 (pr2 M) (@rngunel1 R)) ~ pr1 (@rngunel1 (rngofendabgr (pr1 M)))).
        use eqtohomot. apply (base_paths _ _ (dirprod_pr2 (dirprod_pr1 (pr2 (pr2 M))))).
        apply (p (pr1 x)).
        apply propproperty.
        apply isapropismonoidfun.
    + apply dirprodpair.
      * intros r s.
        use total2_paths2_f.
        apply funextfun. intro x.
        use total2_paths2_f.
        assert (p : pr1 (pr1 (pr2 M) (@op2 R r s)) ~ pr1 (@op2 (rngofendabgr (pr1 M)) (pr1 (pr2 M) r) (pr1 (pr2 M) s))).
        use eqtohomot. apply (base_paths _ _ (dirprod_pr1 (dirprod_pr2 (pr2 (pr2 M))) r s)).
        apply (p (pr1 x)).
        apply propproperty.
        apply isapropismonoidfun.
      * use total2_paths2_f.
        apply funextfun. intro x.
        use total2_paths2_f.
        assert (p : pr1 (pr1 (pr2 M) (@rngunel2 R)) ~ pr1 (@rngunel2 (rngofendabgr (pr1 M)))).
        use eqtohomot. apply (base_paths _ _ (dirprod_pr2 (dirprod_pr2 (pr2 (pr2 M))))).
        apply (p (pr1 x)).
        apply propproperty.
        apply isapropismonoidfun.
Defined.

Definition submodule_to_module {R : rng} {M : module R} (N : submodule M) : module R :=
  modulepair (submodule_to_abgr N) (submodule_to_module_struct N).

(** * Univalence for R-modules *)

Definition moduleiso {R : rng} (M N : module R) : UU := ∑ w : M ≃ N, ismodulefun w.

Definition moduleiso_to_modulefun {R : rng} (M N : module R) : moduleiso M N -> modulefun M N.
Proof.
   intro f.
   exact (tpair _ (pr1weq (pr1 f)) (pr2 f)).
Defined.

Coercion moduleiso_to_modulefun : moduleiso >-> modulefun.

Definition pr1moduleiso {R : rng} {M N : module R} (f : moduleiso M N) : M ≃ N := pr1 f.

Coercion pr1moduleiso : moduleiso >-> weq.

Definition moduleisopair {R : rng} {M N : module R} (f : M ≃ N) (is : ismodulefun f) : moduleiso M N :=
   tpair _ f is.

Definition idmoduleiso {R : rng} (M : module R) : moduleiso M M.
Proof.
   use moduleisopair.
   - exact (idweq (pr1module M)).
   - apply dirprodpair.
     + intros x y. apply idpath.
     + intros r x. apply idpath.
Defined.

Definition isbinopfuninvmap {R : rng} {M N : module R} (f : moduleiso M N) : isbinopfun (invmap f).
Proof.
   intros x y.
   apply (invmaponpathsweq f).
   rewrite (homotweqinvweq f (op x y)).
   symmetry.
   transitivity (op ((pr1moduleiso f) (invmap f x)) ((pr1moduleiso f) (invmap f y))).
   apply (modulefun_to_isbinopfun f (invmap f x) (invmap f y)).
   rewrite 2 (homotweqinvweq f).
   apply idpath.
Defined.

Definition islinearinvmap {R : rng} {M N : module R} (f : moduleiso M N) : islinear (invmap f).
Proof.
   intros r x.
   apply (invmaponpathsweq f).
   transitivity (module_mult N r x).
   exact (homotweqinvweq f (module_mult N r x)).
   transitivity (module_mult N r (pr1 f (invmap (pr1 f) x))).
   rewrite (homotweqinvweq (pr1 f) x).
   apply idpath.
   symmetry.
   apply (pr2 (pr2 f) r (invmap f x)).
Defined.

Definition invmoduleiso {R : rng} {M N : module R} (f : moduleiso M N) : moduleiso N M.
Proof.
   use moduleisopair.
   - exact (invweq f).
   - apply dirprodpair.
     + exact (isbinopfuninvmap f).
     + exact (islinearinvmap f).
Defined.

Definition moduleiso' {R : rng} (M N : module R) : UU := ∑ w : monoidiso (pr1module M) (pr1module N), islinear w.

Definition moduleiso_to_moduleiso' {R : rng} (M N : module R) : moduleiso M N -> moduleiso' M N.
Proof.
   intro w.
   use tpair.
   - use tpair.
     + exact w.
     + use tpair.
       * exact (modulefun_to_isbinopfun w).
       * apply (modulefun_unel w).
   - exact (modulefun_to_islinear w).
Defined.

Definition moduleiso'_to_moduleiso {R : rng} (M N : module R) : moduleiso' M N -> moduleiso M N.
Proof.
   intro w.
   use tpair.
   - exact (pr1 w).
   - apply dirprodpair.
     + exact (pr1 (pr2 (pr1 w))).
     + exact (pr2 w).
Defined.

Lemma modulefun_unel_uniqueness {R : rng} {M N : module R} {f : pr1module M -> pr1module N} {is: ismodulefun f}
       (p : f (@unel (pr1module M)) = @unel (pr1module N)) : modulefun_unel (f,,is) = p.
Proof.
   apply (setproperty (pr1module N)).
Defined.

Definition moduleiso'_to_moduleiso_isweq {R : rng} (M N : module R) : isweq (moduleiso'_to_moduleiso M N).
Proof.
   use (gradth _ (moduleiso_to_moduleiso' M N)). intro w.
   unfold moduleiso'_to_moduleiso, moduleiso_to_moduleiso'. cbn.
   rewrite (modulefun_unel_uniqueness (dirprod_pr2 (pr2 (pr1 w)))).
   apply idpath.
   intro w. apply idpath.
Defined.

Definition moduleiso'_to_moduleiso_weq {R : rng} (M N : module R) : (moduleiso' M N) ≃ (moduleiso M N) :=
   weqpair (moduleiso'_to_moduleiso M N) (moduleiso'_to_moduleiso_isweq M N).

(* The next lemma below should be moved to Rigs_and_Rings.v *)

Lemma isaset_rngfun (X Y : rng) : isaset (rngfun X Y).
Proof.
   apply (isofhleveltotal2 2).
   - use impred_isaset. intro x.
     apply setproperty.
   - intro f.
     apply (isasetaprop (isapropisrigfun f)).
Defined.

Definition modules_univalence_weq {R : rng} (M N : module R) : (M ╝ N) ≃ (moduleiso' M N).
Proof.
   use weqbandf.
   - apply abgr_univalence.
   - intro e.
     use invweq.
     induction M. induction N. cbn in e. induction e.
     use weqimplimpl.
     + intro i.
       use total2_paths2_f.
       * use funextfun. intro r.
         use total2_paths2_f.
           apply funextfun. intro x. exact (i r x).
           apply isapropismonoidfun.
       * apply isapropisrigfun.
     + intro i. cbn.
       intros r x.
       unfold idmonoidiso. cbn in i.
       induction i.
       apply idpath.
     + apply isaprop_islinear.
     + apply isaset_rngfun.
Defined.

Definition modules_univalence_map {R : rng} (M N : module R) : (M = N) -> (moduleiso M N).
Proof.
   intro p.
   induction p.
   exact (idmoduleiso M).
Defined.

Definition modules_univalence_map_isweq {R : rng} (M N : module R) : isweq (modules_univalence_map M N).
Proof.
   use isweqhomot.
   - exact (weqcomp (weqcomp (total2_paths_equiv _ M N) (modules_univalence_weq M N)) (moduleiso'_to_moduleiso_weq M N)).
   - intro p.
     induction p.
     apply (pathscomp0 weqcomp_to_funcomp_app).
     apply idpath.
   - apply weqproperty.
Defined.

Definition modules_univalence {R : rng} (M N : module R) : (M = N) ≃ (moduleiso M N).
Proof.
   use weqpair.
   - exact (modules_univalence_map M N).
   - exact (modules_univalence_map_isweq M N).
Defined.


Section univalent_category_modules.

(** * The precategory of (left) R-modules and R-modules homomorphisms *)


Variable R : rng.

Definition precategory_ob_mor_module : precategory_ob_mor :=
   precategory_ob_mor_pair (module R) (λ M N, modulefun M N).

Local Open Scope Cat.

Definition modulefun_id : ∏ M : precategory_ob_mor_module, M --> M.
Proof.
  intro M.
  exists (idfun (pr1module M)).
  exact (ismodulefun_id M).
Defined.

Definition ismodulefun_comp {M N P : precategory_ob_mor_module} (f : M --> N) (g : N --> P) :
  ismodulefun (funcomp (pr1modulefun f) (pr1modulefun g)) :=
    dirprodpair (isbinopfuncomp (modulefun_to_binopfun f) (modulefun_to_binopfun g))
                (islinearfuncomp (modulefun_to_linearfun f) (modulefun_to_linearfun g)).

Definition modulefun_comp : ∏ M N P : precategory_ob_mor_module, M --> N → N --> P → M --> P.
Proof.
    intros  M N P f g.
    exists (funcomp (pr1modulefun f) (pr1modulefun g)).
    exact (ismodulefun_comp f g).
Defined.

Definition precategory_id_comp_module : precategory_id_comp (precategory_ob_mor_module) :=
  dirprodpair (modulefun_id) (modulefun_comp).

Definition precategory_data_module : precategory_data :=
   tpair _ (precategory_ob_mor_module) (precategory_id_comp_module).

Definition is_precategory_precategory_data_module : is_precategory (precategory_data_module).
Proof.
   apply dirprodpair.
   - apply dirprodpair.
     + intros M N f.
       use total2_paths_f.
       * apply funextfun. intro x. apply idpath.
       * apply isapropismodulefun.
     + intros M N f.
       use total2_paths_f.
       * apply funextfun. intro x. apply idpath.
       * apply isapropismodulefun.
   - intros M N P Q f g h.
     use total2_paths_f.
     + apply funextfun. intro x.
       unfold compose. cbn.
       rewrite funcomp_assoc.
       apply idpath.
     + apply isapropismodulefun.
Defined.

Definition Mod : precategory :=
   mk_precategory (precategory_data_module) (is_precategory_precategory_data_module).


(** * The category of (left) R-modules and R-modules homomorphisms *)

(** The precategory of R-modules has homsets *)

Definition has_homsets_Mod : has_homsets Mod.
Proof.
   intros M N. unfold isaset. intros f g. unfold isaprop.
   apply (isofhlevelweqb 1 (total2_paths_equiv (λ x :  pr1module M ->  pr1module N, ismodulefun x) f g)).
   refine (isofhleveltotal2 1 _ _ _).
   - assert (p : isofhlevel 2 (pr1module M ->  pr1module N)).
     + apply impred. intro.
       exact (setproperty (pr1module N)).
     + exact (p (pr1 f) (pr1 g)).
   - intro p.
     assert (q : isaset (ismodulefun (pr1 g))).
     + exact (isasetaprop (isapropismodulefun (pr1 g))).
     + apply q.
Defined.

Definition category_Mod : category := category_pair Mod has_homsets_Mod.


(** * The univalent category of (left) R-modules and R-modules homomorphisms *)

(** Equivalence between isomorphisms and moduleiso in Mod R *)

Lemma iso_isweq {M N : ob Mod} (f : iso M N) : isweq (pr1 (pr1 f)).
Proof.
   use (gradth (pr1 (pr1 f))).
   - exact (pr1 (inv_from_iso f)).
   - intro x.
     set (T:= iso_inv_after_iso f).
     apply subtypeInjectivity in T.
     + set (T':= toforallpaths _ _ _ T).
       apply T'.
     + intro g.
       apply isapropismodulefun.
   - intro y.
     set (T:= iso_after_iso_inv f).
     apply subtypeInjectivity in T.
     + set (T':= toforallpaths _ _ _ T).
       apply T'.
     + intro g.
       apply isapropismodulefun.
Defined.

Lemma iso_moduleiso (M N : ob Mod) : iso M N -> moduleiso M N.
Proof.
   intro f.
   use moduleisopair.
   - use weqpair.
     + exact (pr1 (pr1 f)).
     + exact (iso_isweq f).
   - exact (pr2 (pr1 f)).
Defined.

Lemma moduleiso_is_iso {M N : ob Mod} (f : moduleiso M N) : @is_iso Mod M N (modulefunpair f (pr2 f)).
Proof.
   apply (is_iso_qinv (C:= Mod) _ (modulefunpair (invmoduleiso f) (pr2 (invmoduleiso f)))).
   split.
   - use total2_paths_f.
     + apply funextfun. intro x.
       unfold funcomp, idfun.
       apply homotinvweqweq.
     + apply isapropismodulefun.
   - use total2_paths_f.
     + apply funextfun. intro y.
       apply homotweqinvweq.
     + apply isapropismodulefun.
Defined.

Lemma moduleiso_iso (M N : ob Mod) : moduleiso M N -> iso M N.
Proof.
   intro f.
   use isopair.
   - use tpair.
     + exact f.
     + exact (pr2 f).
   - exact (moduleiso_is_iso f).
Defined.

Lemma moduleiso_iso_isweq (M N : ob Mod) : isweq (@moduleiso_iso M N).
Proof.
   apply (gradth _ (iso_moduleiso M N)).
   - intro f.
     apply subtypeEquality.
     + intro w.
       apply isapropismodulefun.
     + unfold moduleiso_iso, iso_moduleiso.
       use total2_paths_f.
       * apply idpath.
       * apply isapropisweq.
   - intro f.
     unfold iso_moduleiso, moduleiso_iso.
     use total2_paths_f.
     + apply idpath.
     + apply isaprop_is_iso.
Defined.

Definition moduleiso_iso_weq (M N : Mod) : (moduleiso M N) ≃ (iso M N) :=
   weqpair (moduleiso_iso M N) (moduleiso_iso_isweq M N).

Definition Mod_idtoiso_isweq : ∏ M N : ob Mod, isweq (fun p : M = N => idtoiso p).
Proof.
   intros M N.
   use (isweqhomot (weqcomp (modules_univalence M N) (moduleiso_iso_weq M N)) _).
   - intro p.
     induction p.
     use (pathscomp0 weqcomp_to_funcomp_app). cbn.
     use total2_paths_f.
     + apply idpath.
     + apply isaprop_is_iso.
   - apply weqproperty.
Defined.

Definition Mod_is_univalent : is_univalent Mod :=
  mk_is_univalent Mod_idtoiso_isweq has_homsets_Mod.

Definition univalent_category_Mod : univalent_category := mk_category Mod Mod_is_univalent.

End univalent_category_modules.