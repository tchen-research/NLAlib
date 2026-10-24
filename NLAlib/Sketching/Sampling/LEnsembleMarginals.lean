import NLAlib.Sketching.Sampling.LEnsembleLaw
import NLAlib.ForMathlib.LinearAlgebra.Matrix.PrincipalMinorInclusions
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Inclusion probabilities of an L-ensemble

The marginal kernel is defined using the invertible regularized matrix
`I + L`, even when `L` is singular. The principal-minor inclusion identity
then gives every inclusion probability. Source: Dereziński–Mahoney 2020, §3.
Atlas: `l-ensemble-marginals`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The marginal kernel `L (I + L)⁻¹` of an L-ensemble. The total inverse
formula is used outside the PSD domain; the L-ensemble results require PSD.
Dereziński–Mahoney 2020, §3.
atlas: l-ensemble-marginals (partial) -/
def lEnsembleKernel (L : Matrix n n ℝ) : Matrix n n ℝ := L * (1 + L)⁻¹

private theorem isUnit_det_one_add {L : Matrix n n ℝ} (hL : L.PosSemidef) :
    IsUnit (1 + L).det :=
  isUnit_iff_ne_zero.mpr (ne_of_gt (zero_lt_one.trans_le
    (one_le_det_one_add_of_posSemidef hL)))

/-- The marginal kernel solves the regularized linear equation without
requiring an inverse of the kernel `L` itself. -/
theorem lEnsembleKernel_mul_one_add {L : Matrix n n ℝ} (hL : L.PosSemidef) :
    lEnsembleKernel L * (1 + L) = L := by
  rw [lEnsembleKernel, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_det_one_add hL), Matrix.mul_one]

/-- The L-ensemble kernel is the identity minus the inverse regularized
matrix. This identity is valid for every PSD kernel, including zero. -/
theorem lEnsembleKernel_eq_one_sub_inv {L : Matrix n n ℝ} (hL : L.PosSemidef) :
    lEnsembleKernel L = 1 - (1 + L)⁻¹ := by
  have h := Matrix.mul_nonsing_inv (1 + L) (isUnit_det_one_add hL)
  rw [Matrix.add_mul, Matrix.one_mul] at h
  change (1 + L)⁻¹ + lEnsembleKernel L = 1 at h
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_comm] using h

/-- A real PSD L-ensemble has a symmetric marginal kernel. -/
theorem lEnsembleKernel_isHermitian {L : Matrix n n ℝ} (hL : L.PosSemidef) :
    (lEnsembleKernel L).IsHermitian := by
  rw [lEnsembleKernel_eq_one_sub_inv hL]
  exact Matrix.isHermitian_one.sub ((Matrix.isHermitian_one.add hL.isHermitian).inv)

/-- Integrating the indicator that a fixed set is included gives the
corresponding principal minor of the marginal kernel. This keeps the finite
indicator as an ordinary real function. Dereziński–Mahoney 2020, §3.
atlas: l-ensemble-marginals (partial) -/
theorem integral_subset_indicator_lEnsembleLaw (L : Matrix n n ℝ)
    (hL : L.PosSemidef) (J : Finset n) :
    ∫ S, (if J ⊆ S then (1 : ℝ) else 0) ∂lEnsembleLaw L hL =
      principalMinor (lEnsembleKernel L) J := by
  classical
  rw [integral_lEnsembleLaw]
  have hsum : (∑ S : Finset n, if J ⊆ S then principalMinor L S else 0) =
      (1 + L).det * principalMinor (lEnsembleKernel L) J := by
    exact Matrix.sum_det_principal_minors_superset L (lEnsembleKernel L)
      (lEnsembleKernel_mul_one_add hL) J
  have he : (∑ S : Finset n, lEnsembleProbability L S *
      if J ⊆ S then (1 : ℝ) else 0) =
      (∑ S : Finset n, if J ⊆ S then principalMinor L S else 0) / (1 + L).det := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro S _
    by_cases h : J ⊆ S <;> simp [h, lEnsembleProbability]
  rw [he, hsum, mul_div_cancel_left₀ _ (isUnit_det_one_add hL).ne_zero]

/-- Every prescribed inclusion event has the determinant of the matching
principal marginal-kernel block as its probability. The empty event and
singular kernels are included. Dereziński–Mahoney 2020, §3.
atlas: l-ensemble-marginals (partial)-/
theorem measureReal_subset_lEnsembleLaw (L : Matrix n n ℝ)
    (hL : L.PosSemidef) (J : Finset n) :
    (lEnsembleLaw L hL).real {S | J ⊆ S} = principalMinor (lEnsembleKernel L) J := by
  classical
  have hm : MeasurableSet {S : Finset n | J ⊆ S} := (Set.toFinite _).measurableSet
  have hi := integral_indicator_one (μ := lEnsembleLaw L hL) hm
  have he : (∫ S, (if J ⊆ S then (1 : ℝ) else 0) ∂lEnsembleLaw L hL) =
      (lEnsembleLaw L hL).real {S | J ⊆ S} := by
    simpa only [Set.indicator_apply, Pi.one_apply, Set.mem_ofPred_eq] using hi
  rw [← he]
  exact integral_subset_indicator_lEnsembleLaw L hL J

/-- Inclusion probabilities transport to any random subset with the
L-ensemble law. -/
theorem measureReal_subset_lEnsembleLaw_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (L : Matrix n n ℝ) (hL : L.PosSemidef)
    {S : Ω → Finset n} (hS : HasLaw S (lEnsembleLaw L hL) μ) (J : Finset n) :
    μ.real {ω | J ⊆ S ω} = principalMinor (lEnsembleKernel L) J := by
  have hm : MeasurableSet {T : Finset n | J ⊆ T} := (Set.toFinite _).measurableSet
  have he := hS.measureReal_eq hm
  exact he.trans (measureReal_subset_lEnsembleLaw L hL J)

end NLAlib
