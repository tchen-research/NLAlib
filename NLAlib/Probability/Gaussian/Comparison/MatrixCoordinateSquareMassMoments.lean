import NLAlib.Probability.Gaussian.Comparison.MatrixCoordinateLaws
import NLAlib.Probability.Concentration.Matrix.IndependentSquareSumMoments

/-!
# Chernoff moments of actual reconstructed independent matrix squares

Full-coordinate product transport retains the actual raw second-moment matrix
sum. The matrix Chernoff tail derives every positive integer square-mass
moment without a centering premise. Empty dimensions and zero radius are included.

Source: Brailovskaya--van Handel, arXiv:2201.05142v3, Lemma 6.12.
Prerequisite for independent-sum-spectrum-universality.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace NLAlib
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "E" => ((n × n) ⊕ (n × n)) → ℝ
local notation "L" => (hermitianMatrixFromRealCoordinates : E →L[ℝ] M)

open scoped Matrix.Norms.L2Operator in
/-- The actual full-coordinate law of independent bounded Hermitian matrix
increments has every positive integer square-mass moment. Its Lq norm is
controlled by the original summed raw second moments and the explicit
Chernoff term. No mean, Gaussian or positive-dimension premise is needed. -/
theorem memLp_and_lpNorm_specNorm_sum_coordinate_sq_le_chernoff
    (ν : ι → Measure M) [∀ i, IsProbabilityMeasure (ν i)]
    {R : ℝ} (hR : 0 ≤ R) (hHerm : ∀ i, ∀ᵐ A ∂ν i, A.IsHermitian)
    (hBound : ∀ i, ∀ᵐ A ∂ν i, specNorm A ≤ R) {q : ℕ} (hq : 0 < q) :
    MemLp (fun x : ι → E => specNorm (∑ i, L (x i) ^ 2)) (q : ℝ≥0∞)
      (Measure.pi fun i => (ν i).map matrixRealCoordinates) ∧
      lpNorm (fun x : ι → E => specNorm (∑ i, L (x i) ^ 2)) (q : ℝ≥0∞)
        (Measure.pi fun i => (ν i).map matrixRealCoordinates) ≤
      (Real.exp 1 - 1) * specNorm (∑ i, ∫ A : M, A ^ 2 ∂ν i) +
        R ^ 2 * (Real.log (Fintype.card n) + q) := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn =>
    have hz (A : M) : specNorm A = 0 := by
      rw [Subsingleton.elim A 0, specNorm_zero]
    have hMzero : (fun x : ι → E => specNorm (∑ i, L (x i) ^ 2)) = 0 := by
      funext x
      exact hz _
    rw [hMzero]
    constructor
    · exact MemLp.zero
    · simp only [lpNorm_zero, hz, mul_zero, Fintype.card_eq_zero, Nat.cast_zero,
        Real.log_zero, zero_add]
      positivity
  | inr hn =>
    let κ : ι → Measure E := fun i => (ν i).map matrixRealCoordinates
    have (i : ι) : IsProbabilityMeasure (κ i) :=
      (ν i).isProbabilityMeasure_map measurable_matrixRealCoordinates.aemeasurable
    have hκBound (i : ι) : ∀ᵐ x ∂κ i, specNorm (L x) ≤ R := by
      have hm : MeasurableSet {x : E | specNorm (L x) ≤ R} :=
        (isClosed_le (by simpa only [specNorm_eq_norm] using (L).continuous.norm)
          continuous_const).measurableSet
      apply (ae_map_iff measurable_matrixRealCoordinates.aemeasurable hm).mpr
      filter_upwards [hHerm i, hBound i] with A hA hb
      simpa only [hermitianMatrixFromRealCoordinates_matrixRealCoordinates hA] using hb
    let Z : ι → (ι → E) → M := fun i x => L (x i)
    have hZm (i : ι) : Measurable (Z i) :=
      (L).continuous.measurable.comp (measurable_pi_apply i)
    have hZi : iIndepFun Z (Measure.pi κ) :=
      (iIndepFun_pi (fun _ => aemeasurable_id)).comp
        (fun _ => L) (fun _ => (L).continuous.measurable)
    have hZH (i : ι) : ∀ᵐ x ∂Measure.pi κ, (Z i x).IsHermitian :=
      Filter.Eventually.of_forall fun x => isHermitian_hermitianMatrixFromRealCoordinates (x i)
    have hZB (i : ι) : ∀ᵐ x ∂Measure.pi κ, specNorm (Z i x) ≤ R :=
      (measurePreserving_eval κ i).quasiMeasurePreserving.ae (hκBound i)
    have h := memLp_and_lpNorm_specNorm_sum_sq_le_chernoff (Measure.pi κ)
      Z hR hZm hZi hZH hZB q hq
    have hSq : Measurable (fun x : E => L x ^ 2) := by
      simpa only [pow_two] using (L).continuous.measurable.matrix_mul (L).continuous.measurable
    have hMoment (i : ι) : (∫ x : ι → E, Z i x ^ 2 ∂Measure.pi κ) =
        ∫ A : M, A ^ 2 ∂ν i := by
      calc
        _ = ∫ x : E, L x ^ 2 ∂κ i :=
          (measurePreserving_eval κ i).hasLaw.integral_comp hSq.aestronglyMeasurable
        _ = ∫ A : M, (L (matrixRealCoordinates A)) ^ 2 ∂ν i :=
          ((show HasLaw (matrixRealCoordinates : M → E) (κ i) (ν i) from
            ⟨measurable_matrixRealCoordinates.aemeasurable, rfl⟩).integral_comp
              hSq.aestronglyMeasurable).symm
        _ = _ := integral_congr_ae ((hHerm i).mono fun A hA => by
          change (L (matrixRealCoordinates A)) ^ 2 = A ^ 2
          rw [hermitianMatrixFromRealCoordinates_matrixRealCoordinates hA])
    simp_rw [hMoment] at h
    exact h

end NLAlib
