

(** Anthony Bordg ********************************************

Contents:

- Bilinear morphisms between modules over a ring ([bilinearfun])
- Algebras over a commutative ring ([algebra]) and associative, commutative, unital algebras ([assoc_comm_unital_algebra]), see Serge Lang,
Algebra, III.1, p.121 in the revised third edition.
- Morphisms between (non-associative) algebras aver a commutative ring ([algebrafun])
- The opposite algebra ([algebra_opp])
- Subalgebras of an algebra ([subalgebra])

***********************************************)


(** * Bilinear morphims between modules over a ring *)

Definition isbilinear {R : rng} {M N P : module R} (f : M -> N -> P) : UU :=
  (∏ x : M, ismodulefun (λ y : N, f x y) ) × (∏ y : N, ismodulefun (λ x : M, f x y)).

Definition bilinearfun {R : rng} (M N P : module R) : UU := ∑ f : M -> N -> P, isbilinear f.

Definition pr1bilinearfun {R : rng} {M N P : module R} (f : bilinearfun M N P) : M -> N -> P := pr1 f.

Coercion pr1bilinearfun : bilinearfun >-> Funclass.


(** * Algebras over a commutative ring *)

Section algebras.
Variable R : commrng.

(** Non-associative algebras over a commutative ring *)


Definition algebra : UU := ∑ M : module R, bilinearfun M M M.

Definition pr1algebra (A : algebra) : module R := pr1 A.

Coercion pr1algebra : algebra >-> module.

Definition algebra_pair (M : module R) (f : bilinearfun M M M) : algebra := tpair (λ X : module R, bilinearfun X X X) M f.

Definition mult_algebra (A : algebra) : binop A := pr1 (pr2 A).

Definition isbilinear_mult_algebra (A : algebra) : isbilinear (mult_algebra A) := pr2 (pr2 A).

Notation "x * y" := (mult_algebra _ x y) : algebras_scope.

Delimit Scope algebras_scope with algebras.

(** Commutative algebras over a commutative ring *)

Definition iscomm_algebra (A : algebra) : UU := iscomm (mult_algebra A).

Definition commalgebra : UU := ∑ A : algebra, iscomm_algebra A.

Definition commalgebra_pair (A : algebra) (is : iscomm_algebra A) : commalgebra := tpair _ A is.

Definition commalgebra_to_algebra (A : commalgebra) : algebra := pr1 A.

Coercion commalgebra_to_algebra : commalgebra >-> algebra.

(** Associative  algebras over a commutative ring *)

Definition isassoc_algebra (A : algebra) : UU := isassoc (mult_algebra A).

Definition assocalgebra : UU := ∑ A : algebra, isassoc_algebra A.

Definition assocalgebra_pair (A : algebra) (is : isassoc_algebra A) : assocalgebra := tpair _ A is.

Definition assocalgebra_to_algebra (A : assocalgebra) : algebra := pr1 A.

Coercion assocalgebra_to_algebra : assocalgebra >-> algebra.

(** Unital algebras over a commutative ring *)

Definition isunital_algebra (A : algebra) : UU := isunital (mult_algebra A).

Definition unitalalgebra : UU := ∑ A : algebra, isunital_algebra A.

Definition unitalalgebra_pair (A : algebra) (is : isunital_algebra A) : unitalalgebra := tpair _ A is.

Definition unitalalgebra_to_algebra (A : unitalalgebra) : algebra := pr1 A.

Coercion unitalalgebra_to_algebra : unitalalgebra >-> algebra.

(** Unital associative algebras over a commutative ring *)

Definition unital_assoc_algebra : UU := ∑ A : algebra, (isassoc_algebra A) × (isunital_algebra A).

Definition unital_assoc_algebra_to_algebra (A : unital_assoc_algebra) : algebra := pr1 A.

Coercion unital_assoc_algebra_to_algebra : unital_assoc_algebra >-> algebra.

(** Associative, commutative, unital algebras over a ring *)

Definition assoc_comm_unital_algebra : UU := ∑ A : unital_assoc_algebra, iscomm_algebra A.

(** Morphisms between (non-associative) algebras over a commutative ring *)

Local Open Scope algebras.

Definition algebrafun (A B : algebra) : UU := ∑ f : modulefun A B, ∏ x y : A, f (x * y) = f x * f y.

(** * The opposite algebra  *)

Definition mult_opp (A : algebra) : A -> A -> A := λ x y : A, y * x.

Definition isbilinear_mult_opp (A : algebra) : isbilinear (mult_opp A).
Proof.
  apply dirprodpair.
  - intro a. apply dirprodpair.
    + intros x x'. apply (pr1 (pr2 (isbilinear_mult_algebra A) a) x x').
    + intros r b. apply (pr2 (pr2  (isbilinear_mult_algebra A) a) r b).
  - intro a. apply dirprodpair.
    + intros x x'. apply (pr1 (pr1 (isbilinear_mult_algebra A) a) x x').
    + intros r b. apply (pr2 (pr1  (isbilinear_mult_algebra A) a) r b).
Defined.

Definition bilinear_mult_opp (A : algebra) : bilinearfun A A A := tpair _ (mult_opp A) (isbilinear_mult_opp A).

Definition algebra_opp (A : algebra) : algebra := tpair (λ X : module R, bilinearfun X X X) A (bilinear_mult_opp A).

(** * Subalgebras of an algebra *)

Definition subalgebra (A : algebra) : UU := ∑ B : submodule (pr1 A), isstable_by_action (mult_algebra A) (pr1 B).

Definition subalgebra_to_module {A : algebra} (B : subalgebra A) : module R := submodule_to_module (pr1 B).

Definition subalgebra_to_mult {A : algebra} (B : subalgebra A) : binop (subalgebra_to_module B).
Proof.
  intros x y.
  split with (mult_algebra A (pr1 x) (pr1 y)).
  exact (pr2 B (pr1 x) (pr1 y) (pr2 y)).
Defined.

Definition isbilinear_subalgebra_to_mult {A : algebra } (B : subalgebra A) : isbilinear (subalgebra_to_mult B).
Proof.
  apply dirprodpair.
  - intro x. unfold ismodulefun.
    apply dirprodpair.
    +  unfold isbinopfun. intros x0 x'.
       use total2_paths2_f.
       apply (dirprod_pr1 (pr2 (pr2 A))).
       apply propproperty.
    +  intros r y.
       use total2_paths2_f.
       apply (dirprod_pr1 (pr2 (pr2 A))).
       apply propproperty.
  - intro y. apply dirprodpair.
    + intros x x'.
      use total2_paths2_f.
      apply (dirprod_pr2 (pr2 (pr2 A))).
      apply propproperty.
    + intros r x.
      use total2_paths2_f.
      apply (dirprod_pr2 (pr2 (pr2 A))).
      apply propproperty.
Defined.

Definition subalgebra_to_bilinearfun {A : algebra} (B : subalgebra A) :
  bilinearfun (subalgebra_to_module B) (subalgebra_to_module B) (subalgebra_to_module B) :=
    tpair _ (subalgebra_to_mult B) (isbilinear_subalgebra_to_mult B).

Definition subalgebra_to_algebra {A : algebra} (B : subalgebra A) : algebra :=
  algebra_pair (subalgebra_to_module B) (subalgebra_to_bilinearfun B).

End algebras.