import NLAlib.Probability.Free.WordWickBasis
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Exact normal ordering of concrete finite-word Wick operators

Each cut keeps the prefix as creation and turns the reversed suffix into
the adjoint creation product. The reversal is part of the literal identity.
This is an algebraic prerequisite for the homogeneous estimate in Lemma 4.5
of arXiv:2406.11453v2; no norm comparison is assumed.
-/

noncomputable section
set_option autoImplicit false

open scoped Classical

namespace NLAlib

variable {ι : Type*}
local notation "B" => WordHilbertSpace ι →L[ℂ] WordHilbertSpace ι

/-- The actual ordered creation product prepends the letters of a word. -/
def wordCreationProduct (w : List ι) : B :=
  (w.map fun i => (wordCreation i).toContinuousLinearMap).prod

/-- The creation product of the empty word is the identity operator. -/
@[simp]
theorem wordCreationProduct_nil : wordCreationProduct ([] : List ι) = 1 := rfl

/-- Prepending a letter composes its creation operator on the left. -/
@[simp]
theorem wordCreationProduct_cons (i : ι) (w : List ι) :
    wordCreationProduct (i :: w) =
      (wordCreation i).toContinuousLinearMap * wordCreationProduct w := rfl

/-- Concatenating two words multiplies their ordered creation products. -/
@[simp]
theorem wordCreationProduct_append (u v : List ι) :
    wordCreationProduct (u ++ v) = wordCreationProduct u * wordCreationProduct v := by
  simp [wordCreationProduct]

/-- Ordered creation products act by actual list concatenation on basis vectors. -/
@[simp]
theorem wordCreationProduct_apply_single (u v : List ι) (z : ℂ) :
    wordCreationProduct u (lp.single 2 v z) = lp.single 2 (u ++ v) z := by
  induction u with
  | nil => simp
  | cons i u hu =>
    simp only [wordCreationProduct_cons, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_apply, hu, LinearIsometry.coe_toContinuousLinearMap,
      wordCreation_apply_single, List.cons_append]

private def wordWickNormalOrder : List ι → B
  | [] => 1
  | i :: w => (wordCreation i).toContinuousLinearMap * wordWickNormalOrder w +
      star (wordCreationProduct (i :: w).reverse)

private theorem wordWickNormalOrder_cons (i : ι) (w : List ι) :
    wordWickNormalOrder (i :: w) =
      (wordCreation i).toContinuousLinearMap * wordWickNormalOrder w +
        wordAnnihilation i * star (wordCreationProduct w.reverse) := by
  rw [wordWickNormalOrder, List.reverse_cons, wordCreationProduct_append, star_mul]
  simp [wordAnnihilation, ContinuousLinearMap.star_eq_adjoint]

private theorem wordWickOperator_eq_normalOrder (w : List ι) :
    wordWickOperator w = wordWickNormalOrder w := by
  induction w using List.twoStepInduction with
  | nil => rfl
  | singleton i =>
    simp [wordWickOperator, wordWickNormalOrder,
      wordField, wordAnnihilation, ContinuousLinearMap.star_eq_adjoint]
  | cons_cons i j w hw hcons =>
    simp only [wordWickOperator, hw, hcons j]
    rw [wordWickNormalOrder_cons j w]
    rw [wordWickNormalOrder_cons i (j :: w)]
    rw [wordWickNormalOrder_cons j w]
    have hrel : wordAnnihilation i * (wordCreation j).toContinuousLinearMap =
        if i = j then 1 else 0 := by
      simpa only [ContinuousLinearMap.mul_def] using wordAnnihilation_comp_wordCreation i j
    have hrev : star (wordCreationProduct (j :: w).reverse) =
        wordAnnihilation j * star (wordCreationProduct w.reverse) := by
      rw [List.reverse_cons, wordCreationProduct_append, star_mul]
      simp [wordAnnihilation, ContinuousLinearMap.star_eq_adjoint]
    rw [hrev]
    change (((wordCreation i).toContinuousLinearMap + wordAnnihilation i) *
      ((wordCreation j).toContinuousLinearMap * wordWickNormalOrder w +
        wordAnnihilation j * star (wordCreationProduct w.reverse)) -
      (if i = j then wordWickNormalOrder w else 0)) = _
    simp only [add_mul, mul_add, ← mul_assoc, hrel]
    by_cases hij : i = j <;> simp only [hij, if_true, if_false, one_mul, zero_mul]
    · noncomm_ring
    · noncomm_ring

/-- Exact Wick normal ordering: the prefix is a creation product and the
suffix is reversed before taking its adjoint. All cuts, including the two
empty ends, are present. -/
theorem wordWickOperator_eq_sum_cuts (w : List ι) :
    wordWickOperator w = ∑ j ∈ Finset.range (w.length + 1),
      wordCreationProduct (w.take j) *
        star (wordCreationProduct (w.drop j).reverse) := by
  rw [wordWickOperator_eq_normalOrder]
  induction w with
  | nil => simp [wordWickNormalOrder]
  | cons i w hw =>
    change (wordCreation i).toContinuousLinearMap * wordWickNormalOrder w +
      star (wordCreationProduct (i :: w).reverse) =
        ∑ j ∈ Finset.range (w.length + 1 + 1),
          wordCreationProduct ((i :: w).take j) *
            star (wordCreationProduct ((i :: w).drop j).reverse)
    rw [Finset.sum_range_succ']
    simp only [List.take_zero, List.drop_zero, wordCreationProduct_nil,
      one_mul, List.take_succ_cons, List.drop_succ_cons, wordCreationProduct_cons]
    rw [hw, Finset.mul_sum]
    congr 1

end NLAlib
