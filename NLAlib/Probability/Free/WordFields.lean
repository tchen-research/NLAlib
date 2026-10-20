import NLAlib.Probability.Free.WordCreation
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Concrete self-adjoint fields on finite-word Hilbert space

The actual prefix creation and its native adjoint give bounded self-adjoint
operators. Their vacuum expectations have mean zero and covariance identity.
These are construction prerequisites for a free semicircular model; no
semicircular distribution, freeness, or faithful state is claimed here.

Source: Nica--Speicher, Lectures on the Combinatorics of Free Probability,
Definitions 7.13 and the full-Fock operators of Proposition 7.16.
-/

noncomputable section
set_option autoImplicit false

open scoped Classical lp InnerProduct

namespace NLAlib

variable {ι : Type*}

/-- The actual self-adjoint field is prefix creation plus its Hilbert adjoint. -/
def wordField (i : ι) : WordHilbertSpace ι →L[ℂ] WordHilbertSpace ι :=
  (wordCreation i).toContinuousLinearMap + wordAnnihilation i

/-- The actual complex-linear vacuum functional. Mathlib's inner product is
linear in the second argument, so the vacuum occurs in the first slot. -/
def wordVacuumExpectation (ι : Type*) :
    (WordHilbertSpace ι →L[ℂ] WordHilbertSpace ι) →L[ℂ] ℂ :=
  (innerSL ℂ (wordVacuum ι)).comp
    (ContinuousLinearMap.apply ℂ (WordHilbertSpace ι) (wordVacuum ι))

/-- Evaluating the vacuum functional is the actual vacuum matrix coefficient. -/
@[simp]
theorem wordVacuumExpectation_apply
    (T : WordHilbertSpace ι →L[ℂ] WordHilbertSpace ι) :
    wordVacuumExpectation ι T = inner ℂ (wordVacuum ι) (T (wordVacuum ι)) := rfl

/-- Creation plus its native adjoint is self-adjoint. -/
theorem isSelfAdjoint_wordField (i : ι) : IsSelfAdjoint (wordField i) := by
  simpa only [wordField, wordAnnihilation, ← ContinuousLinearMap.star_eq_adjoint] using
    IsSelfAdjoint.add_star_self (wordCreation i).toContinuousLinearMap

/-- The concrete fields have operator norm at most two, uniformly over the alphabet. -/
theorem norm_wordField_le_two (i : ι) : ‖wordField i‖ ≤ 2 := by
  have hC : ‖(wordCreation i).toContinuousLinearMap‖ ≤ 1 :=
    (wordCreation i).norm_toContinuousLinearMap_le
  have hA : ‖wordAnnihilation i‖ ≤ 1 := by
    change ‖ContinuousLinearMap.adjoint (wordCreation i).toContinuousLinearMap‖ ≤ 1
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hC
  exact (norm_add_le _ _).trans (by linarith)

/-- A field creates its one-letter unit vector from the concrete vacuum. -/
@[simp]
theorem wordField_wordVacuum (i : ι) :
    wordField i (wordVacuum ι) = lp.single 2 [i] 1 := by
  simp [wordField, wordVacuum, LinearIsometry.coe_toContinuousLinearMap]

/-- The vacuum functional is normalized, including an empty alphabet. -/
@[simp]
theorem wordVacuumExpectation_one :
    wordVacuumExpectation ι (1 : WordHilbertSpace ι →L[ℂ] WordHilbertSpace ι) = 1 := by
  simp [wordVacuumExpectation_apply, wordVacuum]

/-- Every concrete field has vacuum mean zero. -/
@[simp]
theorem wordVacuumExpectation_wordField (i : ι) :
    wordVacuumExpectation ι (wordField i) = 0 := by
  rw [wordVacuumExpectation_apply, wordField_wordVacuum]
  simp [wordVacuum, lp.inner_single_left, lp.single_apply]

open scoped Classical in
/-- The raw second vacuum moments of the actual self-adjoint fields are
the Kronecker delta, hence each field has variance one. -/
@[simp]
theorem wordVacuumExpectation_wordField_mul_wordField (i j : ι) :
    wordVacuumExpectation ι (wordField i * wordField j) = if i = j then 1 else 0 := by
  rw [wordVacuumExpectation_apply, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  have hi : (wordField i).adjoint = wordField i := (isSelfAdjoint_wordField i).adjoint_eq
  have h := ContinuousLinearMap.adjoint_inner_right (wordField i)
    (wordVacuum ι) (wordField j (wordVacuum ι))
  rw [hi] at h
  rw [h, wordField_wordVacuum, wordField_wordVacuum]
  simp [lp.inner_single_left, lp.single_apply, Pi.single_apply]

end NLAlib
