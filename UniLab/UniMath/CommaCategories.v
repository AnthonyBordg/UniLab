(** **********************************************************

Anthony Bordg (May 2017)


************************************************************)


(** **********************************************************

Contents :

        - Comma precategories [comma_precategory]

************************************************************)


Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.


(** * Comma precategories *)

Section comma_precategories.

Local Open Scope cat.

(* We require that the target category C below has homsets *)

Context {C : category}.
Context {D E : precategory}.
Variable S : D ⟶ C.
Variable T : E ⟶ C.

Local Open Scope type_scope.
Local Open Scope cat.

Definition comma_cat_ob : UU := ∑ ed : ob E × ob D, C⟦T (pr1 ed), S (pr2 ed)⟧.

Definition comma_cat_mor : comma_cat_ob -> comma_cat_ob -> UU :=
  λ abf : comma_cat_ob,
    (λ cdg : comma_cat_ob,
             ∑ kh : E⟦pr1 (pr1 abf), pr1 (pr1 cdg)⟧ × D⟦pr2 (pr1 abf), pr2 (pr1 cdg)⟧, pr2 (abf) · #S(pr2 kh) = #T(pr1 kh) · pr2 (cdg)).

Definition comma_cat_ob_mor : precategory_ob_mor := precategory_ob_mor_pair comma_cat_ob comma_cat_mor.

Definition comma_cat_id : ∏ edf : comma_cat_ob_mor, comma_cat_ob_mor ⟦ edf, edf ⟧.
Proof.
  intro edf. cbn.
  exists (dirprodpair (identity (pr1 (pr1 edf))) (identity (pr2 (pr1 edf)))). cbn.
  abstract (
    rewrite 2 functor_id;
    rewrite id_right;
    rewrite id_left;
    apply idpath
    ).
Defined.

Definition comma_cat_comp : ∏ uvf xyg zwh : comma_cat_ob, comma_cat_mor uvf xyg → comma_cat_mor xyg zwh → comma_cat_mor uvf zwh.
Proof.
  intros uvf xyg zwh ijp klq.
  exists (dirprodpair (pr1 (pr1 ijp) · pr1 (pr1 klq)) (pr2 (pr1 ijp) · pr2 (pr1 klq))). cbn.
  abstract (
    rewrite 2 functor_comp;
    rewrite assoc;
    rewrite (pr2 ijp);
    rewrite <- assoc;
    rewrite (pr2 klq);
    rewrite assoc;
    apply idpath
    ).
Defined.

Definition comma_cat_id_comp : precategory_id_comp comma_cat_ob_mor := dirprodpair comma_cat_id comma_cat_comp.

Definition comma_cat_data : precategory_data := tpair _ comma_cat_ob_mor comma_cat_id_comp.

Definition comma_cat_data_id_left :  ∏ (abf cdg : comma_cat_data) (hkp : abf --> cdg), identity abf · hkp = hkp .
Proof.
  intros abf cdg hkp.
  use total2_paths2_f.
  - use total2_paths2.
    + cbn. apply id_left.
    + cbn. apply id_left.
  - cbn. apply (homset_property C).
Qed.

Definition comma_cat_data_id_right :  ∏ (abf cdg : comma_cat_data) (hkp : abf --> cdg), hkp · identity cdg = hkp .
Proof.
  intros abf cdg hkp.
  use total2_paths2_f.
  - use total2_paths2.
    + cbn. apply id_right.
    + cbn. apply id_right.
  - cbn. apply (homset_property C).
Qed.

Definition comma_cat_data_assoc :
  ∏ (stf uvg xyh zwi : comma_cat_data) (jkp : stf --> uvg) (lmq : uvg --> xyh) (nor : xyh --> zwi), jkp · (lmq · nor) = (jkp · lmq) · nor .
Proof.
  intros stf uvg xyh zwi jkp lmq nor.
  use total2_paths2_f.
  - use total2_paths2.
    + cbn. apply assoc.
    + cbn. apply assoc.
  - apply (homset_property C).
Qed.

Definition is_precategory_comma_cat_data : is_precategory comma_cat_data :=
  mk_is_precategory comma_cat_data_id_left comma_cat_data_id_right comma_cat_data_assoc.

Definition comma_precategory : precategory := mk_precategory comma_cat_data is_precategory_comma_cat_data.


End comma_precategories.
