import NLAlib.Probability.Free.WordVacuumSeparation
import Mathlib.Data.List.Induction

/-!
# Actual finite-word Wick polynomials on the concrete word Hilbert space

The recursion removes the single possible adjacent contraction at the first
letter. Its values are actual polynomials in the self-adjoint fields, and
their vacuum vectors are precisely the native orthonormal word vectors.
No distribution, Wick orthogonality or norm comparison is assumed.

This is a finite algebraic prerequisite for the homogeneous Wick estimate
used in Lemma 4.5 of arXiv:2406.11453v2. It does not yet prove that estimate.
-/

noncomputable section
set_option autoImplicit false

open scoped Classical lp InnerProduct

namespace NLAlib

variable {ι : Type*}
local notation "B" => WordHilbertSpace ι →L[ℂ] WordHilbertSpace ι

/-- The actual finite-word Wick polynomial, with its adjacent contraction
removed recursively. The definition remains valid for arbitrary alphabets. -/
def wordWickOperator : List ι → B
  | [] => 1
  | [i] => wordField i
  | i :: j :: w => wordField i * wordWickOperator (j :: w) -
      if i = j then wordWickOperator w else 0

private theorem wordField_apply_single_cons (i j : ι) (w : List ι) (z : ℂ) :
    wordField i (lp.single 2 (j :: w) z) =
      lp.single 2 (i :: j :: w) z + if i = j then lp.single 2 w z else 0 := by
  simp only [wordField, add_apply, LinearIsometry.coe_toContinuousLinearMap,
    wordCreation_apply_single, wordAnnihilation_apply_single_cons]

/-- Applying an actual Wick polynomial to the actual vacuum creates exactly
its word basis vector. There is no law or moment premise. -/
@[simp]
theorem wordWickOperator_wordVacuum (w : List ι) :
    wordWickOperator w (wordVacuum ι) = lp.single 2 w 1 := by
  induction w using List.twoStepInduction with
  | nil => simp [wordWickOperator, wordVacuum]
  | singleton i => simpa only [wordWickOperator] using wordField_wordVacuum i
  | cons_cons i j w hw hcons =>
    change (wordField i * wordWickOperator (j :: w) -
      if i = j then wordWickOperator w else 0) (wordVacuum ι) = _
    rw [sub_apply, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      hcons j, wordField_apply_single_cons]
    by_cases hij : i = j <;> simp [hij, hw]

private theorem wordField_mem_wordFieldAlgebra (i : ι) :
    wordField i ∈ wordFieldAlgebra ι :=
  StarSubalgebra.le_topologicalClosure _
    (StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self i))

/-- Every Wick polynomial belongs to the genuine closed algebra generated
only by the self-adjoint fields. -/
theorem wordWickOperator_mem_wordFieldAlgebra (w : List ι) :
    wordWickOperator w ∈ wordFieldAlgebra ι := by
  induction w using List.twoStepInduction with
  | nil => exact one_mem _
  | singleton i => exact wordField_mem_wordFieldAlgebra i
  | cons_cons i j w hw hcons =>
    apply sub_mem (mul_mem (wordField_mem_wordFieldAlgebra i) (hcons j))
    by_cases hij : i = j <;> simp only [hij, if_true, if_false]
    · exact hw
    · exact zero_mem _

/-- The exact Wick Gram matrix for the actual vacuum is the Kronecker delta,
derived from the actual word-basis action and the native Hilbert adjoint. -/
theorem wordVacuumExpectation_star_wordWickOperator_mul (w v : List ι) :
    wordVacuumExpectation ι (star (wordWickOperator w) * wordWickOperator v) =
      if w = v then 1 else 0 := by
  rw [wordVacuumExpectation_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right,
    wordWickOperator_wordVacuum, wordWickOperator_wordVacuum]
  simp [lp.inner_single_left, lp.single_apply, Pi.single_apply]

end NLAlib
