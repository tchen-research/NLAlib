import NLAlib.Probability.Gaussian.Comparison.MatrixCoordinateLaws
import NLAlib.Probability.Concentration.Matrix.IndependentSquareSum

/-! # Expected square mass in actual full matrix coordinates

The full product coordinate law has exactly the original aggregate squared
matrix mass after almost-everywhere Hermitian reconstruction. Applying the
actual PSD Chernoff expectation theorem before transporting the product law
retains the genuine sum of second-moment matrices.

This is the coordinate-law input for Brailovskaya--van Handel,
*Universality and sharp matrix concentration inequalities*,
arXiv:2201.05142v3 (2024), §6.4, Lemma 6.12.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "J" => (n × n) ⊕ (n × n)
local notation "E" => J → ℝ
local notation "L" => (hermitianMatrixFromRealCoordinates : E →L[ℝ] M)

open scoped Matrix.Norms.L2Operator in
/-- The independent full-coordinate law of bounded Hermitian matrix
increments has integrable reconstructed squared-sum spectral norm, bounded
by the actual original summed second moments with Chernoff coefficient
`exp 1 - 1`. All integrability is derived from the original support bound;
no zero-mean, Gaussian or positive-dimension premise is needed.

Source: Brailovskaya--van Handel, arXiv:2201.05142v3 (2024), §6.4,
Lemma 6.12, using the explicit PSD Chernoff bound at parameter one.
atlas: matrix-resolvent-gaussian-universality (partial) -/
theorem integrable_and_integral_specNorm_sum_coordinate_sq_le_chernoff
    (ν : ι → Measure M) [∀ i, IsProbabilityMeasure (ν i)]
    {R : ℝ} (hR : 0 ≤ R) (hHerm : ∀ i, ∀ᵐ A ∂ν i, A.IsHermitian)
    (hBound : ∀ i, ∀ᵐ A ∂ν i, specNorm A ≤ R) :
    Integrable (fun x : ι → E => specNorm (∑ i, (L (x i)) ^ 2))
      (Measure.pi fun i => (ν i).map matrixRealCoordinates) ∧
      (∫ x : ι → E, specNorm (∑ i, (L (x i)) ^ 2)
        ∂Measure.pi fun i => (ν i).map matrixRealCoordinates) ≤
      (Real.exp 1 - 1) * specNorm (∑ i, ∫ A : M, A ^ 2 ∂ν i) +
        R ^ 2 * Real.log (Fintype.card n) := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn =>
    let := hn
    have hz : ∀ A : M, specNorm A = 0 := by
      intro A
      rw [Subsingleton.elim A 0, specNorm_zero]
    constructor
    · simpa only [hz] using!
        (integrable_zero (ι → E) ℝ (Measure.pi fun i => (ν i).map matrixRealCoordinates))
    · simp only [hz, integral_zero, mul_zero, Fintype.card_eq_zero, Nat.cast_zero,
        Real.log_zero, add_zero, le_refl]
  | inr hn =>
    let := hn
    let κ : ι → Measure E := fun i => (ν i).map matrixRealCoordinates
    have (i : ι) : IsProbabilityMeasure (κ i) :=
      (ν i).isProbabilityMeasure_map measurable_matrixRealCoordinates.aemeasurable
    let T : (ι → M) → ι → E := fun x i => matrixRealCoordinates (x i)
    let F : (ι → E) → ℝ := fun x => specNorm (∑ i, (L (x i)) ^ 2)
    have hFc : Continuous F := by
      simp only [F, specNorm_eq_norm]
      fun_prop
    have hπHerm : ∀ i, ∀ᵐ x : ι → M ∂Measure.pi ν, (x i).IsHermitian :=
      fun i => (measurePreserving_eval ν i).quasiMeasurePreserving.ae (hHerm i)
    have hπBound : ∀ i, ∀ᵐ x : ι → M ∂Measure.pi ν, specNorm (x i) ≤ R :=
      fun i => (measurePreserving_eval ν i).quasiMeasurePreserving.ae (hBound i)
    have h := integrable_and_integral_specNorm_sum_sq_le_chernoff (Measure.pi ν)
      (fun i (x : ι → M) => x i) hR (fun i => measurable_pi_apply i)
      (iIndepFun_pi (fun _ => aemeasurable_id)) hπHerm hπBound
    have hsqc : Continuous (fun A : M => A ^ 2) := by fun_prop
    have hSqInt (i : ι) : Integrable (fun A : M => A ^ 2) (ν i) := by
      apply Integrable.of_bound hsqc.measurable.aestronglyMeasurable (R ^ 2)
      filter_upwards [hBound i] with A hA
      exact (norm_pow_le A 2).trans (pow_le_pow_left₀ (norm_nonneg A) hA 2)
    have hmoment (i : ι) : (∫ x : ι → M, (x i) ^ 2 ∂Measure.pi ν) =
        ∫ A : M, A ^ 2 ∂ν i := by
      exact (measurePreserving_eval ν i).hasLaw.integral_comp
        (hSqInt i).aestronglyMeasurable
    have hLaw : HasLaw T (Measure.pi κ) (Measure.pi ν) := hasLaw_matrixRealCoordinates_pi ν
    have hAE : ∀ᵐ x : ι → M ∂Measure.pi ν, F (T x) = specNorm (∑ i, (x i) ^ 2) := by
      filter_upwards [ae_all_iff.mpr hπHerm] with x hx
      dsimp only [F, T]
      apply congrArg specNorm
      apply Finset.sum_congr rfl
      intro i hi
      rw [hermitianMatrixFromRealCoordinates_matrixRealCoordinates (hx i)]
    have hCompInt : Integrable (fun x : ι → M => F (T x)) (Measure.pi ν) := h.1.congr (hAE.mono fun x hx => hx.symm)
    have hFint : Integrable F (Measure.pi κ) := by
      rw [← hLaw.map_eq]
      exact (integrable_map_measure hFc.measurable.aestronglyMeasurable hLaw.aemeasurable).mpr hCompInt
    have htransport := hLaw.integral_comp hFc.measurable.aestronglyMeasurable
    change (∫ x : ι → M, F (T x) ∂Measure.pi ν) = ∫ x : ι → E, F x ∂Measure.pi κ at htransport
    have he : (∫ x : ι → E, F x ∂Measure.pi κ) =
        ∫ x : ι → M, specNorm (∑ i, (x i) ^ 2) ∂Measure.pi ν :=
      htransport.symm.trans (integral_congr_ae hAE)
    refine ⟨hFint, ?_⟩
    have hb := h.2
    simp_rw [hmoment] at hb
    exact he.trans_le hb

end NLAlib
