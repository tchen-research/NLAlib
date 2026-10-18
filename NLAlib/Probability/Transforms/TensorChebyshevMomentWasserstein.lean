import NLAlib.Polynomial.FunctionApproximation.JacksonTensorApproximation
import NLAlib.Polynomial.FunctionApproximation.ChebyshevCube
import NLAlib.ForMathlib.MeasureTheory.CompactKantorovich

/-!
# Tensor Chebyshev moments control genuine Wasserstein distance

The finite positive Jackson polynomial is paired directly against actual laws.
The normalized tensor coefficient energy gives precisely the source's constant.
Source: MMRS, arXiv:2408.12385v3, Appendix A.1, Theorem 32.
Atlas: `chebyshev-moment-wasserstein` (tensor clause).
-/

noncomputable section

open Real MeasureTheory Set Finset

namespace NLAlib

/-- The squared Euclidean degree of an actual tensor multi-index. -/
def tensorChebyshevIndexNormSq {d : ℕ} (α : Fin d → ℕ) : ℝ := ∑ i, (α i : ℝ) ^ 2

/-- Retained tensor indices with the constant mode removed. -/
def tensorChebyshevMomentIndices (d k : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset (fun _ : Fin d => range (k + 1))).erase 0

/-- Difference of actual normalized tensor moments of two Euclidean laws. -/
def tensorChebyshevMomentDiscrepancy {d : ℕ}
    (μ ν : Measure (EuclideanSpace ℝ (Fin d))) (α : Fin d → ℕ) : ℝ :=
  (∫ x, tensorNormalizedChebyshev α (WithLp.ofLp x) ∂μ) -
    ∫ x, tensorNormalizedChebyshev α (WithLp.ofLp x) ∂ν

/-- The source's weighted tensor moment error, with squared multi-index norm
in the denominator after squaring. -/
def tensorChebyshevMomentError {d : ℕ}
    (μ ν : Measure (EuclideanSpace ℝ (Fin d))) (k : ℕ) : ℝ :=
  sqrt (∑ α ∈ tensorChebyshevMomentIndices d k,
    (tensorChebyshevMomentDiscrepancy μ ν α / sqrt (tensorChebyshevIndexNormSq α)) ^ 2)

theorem tensorChebyshevIndexNormSq_pos {d : ℕ} {α : Fin d → ℕ} (hα : α ≠ 0) :
    0 < tensorChebyshevIndexNormSq α := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hα
  apply sum_pos' (fun j _ => sq_nonneg (α j : ℝ))
  exact ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero (by exact_mod_cast hi)⟩

/-- Damping does not increase the actual tensor coefficient energy. -/
theorem sum_tensor_damping_coeff_mul_discrepancy_le {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {L : NNReal}
    (hf : LipschitzOnWith L f (chebyshevCube (Fin d)))
    (μ ν : Measure (EuclideanSpace ℝ (Fin d))) (k : ℕ) :
    (∑ α ∈ tensorChebyshevMomentIndices d k, tensorChebyshevJacksonDamping k α *
      tensorChebyshevCoeff f α * tensorChebyshevMomentDiscrepancy μ ν α) ≤
      sqrt ((d : ℝ) * π ^ d / 2) * (L : ℝ) * tensorChebyshevMomentError μ ν k := by
  let s := tensorChebyshevMomentIndices d k
  let a := fun α : Fin d → ℕ => sqrt (tensorChebyshevIndexNormSq α) *
    (tensorChebyshevJacksonDamping k α * tensorChebyshevCoeff f α)
  let b := fun α : Fin d → ℕ => tensorChebyshevMomentDiscrepancy μ ν α /
    sqrt (tensorChebyshevIndexNormSq α)
  have heq (α : Fin d → ℕ) (hα : α ∈ s) : a α * b α =
      tensorChebyshevJacksonDamping k α * tensorChebyshevCoeff f α *
        tensorChebyshevMomentDiscrepancy μ ν α := by
    have hq := sqrt_pos.2 (tensorChebyshevIndexNormSq_pos (mem_erase.mp hα).1)
    dsimp [a, b]
    field_simp
  have henergy0 : (∑ α ∈ s, tensorChebyshevIndexNormSq α * tensorChebyshevCoeff f α ^ 2) ≤
      (d : ℝ) * π ^ d * (L : ℝ) ^ 2 / 2 := by
    obtain ⟨g, hg, hfg⟩ := hf.extend_real
    simp_rw [tensorChebyshevCoeff_congr hfg]
    exact sum_norm_sq_mul_tensorChebyshevCoeff_sq_le_of_lipschitzWith hg s
  have henergy : (∑ α ∈ s, a α ^ 2) ≤ (d : ℝ) * π ^ d * (L : ℝ) ^ 2 / 2 := by
    apply le_trans _ henergy0
    apply sum_le_sum
    intro α hα
    have hρ := tensorChebyshevJacksonDamping_mem_Icc (M := k) (α := α) (fun i => by
      have h := Fintype.mem_piFinset.mp (mem_erase.mp hα).2 i
      have := mem_range.mp h
      omega)
    dsimp [a]
    rw [mul_pow, sq_sqrt (by unfold tensorChebyshevIndexNormSq; positivity)]
    calc
      _ = tensorChebyshevJacksonDamping k α ^ 2 *
          (tensorChebyshevIndexNormSq α * tensorChebyshevCoeff f α ^ 2) := by ring
      _ ≤ 1 * (tensorChebyshevIndexNormSq α * tensorChebyshevCoeff f α ^ 2) :=
        mul_le_mul_of_nonneg_right (by nlinarith [hρ.1, hρ.2]) (by
          unfold tensorChebyshevIndexNormSq
          positivity)
      _ = _ := one_mul _
  have hroot : sqrt (∑ α ∈ s, a α ^ 2) ≤ sqrt ((d : ℝ) * π ^ d / 2) * (L : ℝ) := by
    refine (sqrt_le_sqrt henergy).trans_eq ?_
    rw [show (d : ℝ) * π ^ d * (L : ℝ) ^ 2 / 2 =
      ((d : ℝ) * π ^ d / 2) * (L : ℝ) ^ 2 by ring,
      sqrt_mul (by positivity), sqrt_sq L.coe_nonneg]
  calc
    _ = ∑ α ∈ s, a α * b α := sum_congr rfl (fun α hα => (heq α hα).symm)
    _ ≤ sqrt (∑ α ∈ s, a α ^ 2) * sqrt (∑ α ∈ s, b α ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt s a b
    _ ≤ _ := mul_le_mul_of_nonneg_right hroot (sqrt_nonneg _)

/-- The displayed finite weighted squared-error formula, with no coefficient
or density surrogate in place of the actual moments. -/
theorem tensorChebyshevMomentError_sq {d : ℕ}
    (μ ν : Measure (EuclideanSpace ℝ (Fin d))) (k : ℕ) :
    tensorChebyshevMomentError μ ν k ^ 2 =
      ∑ α ∈ tensorChebyshevMomentIndices d k,
        tensorChebyshevMomentDiscrepancy μ ν α ^ 2 / tensorChebyshevIndexNormSq α := by
  rw [tensorChebyshevMomentError, sq_sqrt (sum_nonneg (fun _ _ => sq_nonneg _))]
  apply sum_congr rfl
  intro α _
  rw [div_pow, sq_sqrt (by unfold tensorChebyshevIndexNormSq; positivity)]

/-- Direct pairing of the actual finite tensor polynomial cancels the
constant mode because the two input laws both have mass one. -/
theorem integral_tensorChebyshevJacksonApprox_sub_eq_sum {d : ℕ}
    (μ ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ chebyshevCube (Fin d))
    (hν : ∀ᵐ x ∂ν, x ∈ chebyshevCube (Fin d))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (k : ℕ) :
    (∫ x, tensorChebyshevJacksonApprox f k x ∂μ) -
      (∫ x, tensorChebyshevJacksonApprox f k x ∂ν) =
      ∑ α ∈ tensorChebyshevMomentIndices d k, tensorChebyshevJacksonDamping k α *
        tensorChebyshevCoeff f α * tensorChebyshevMomentDiscrepancy μ ν α := by
  have hInt (m : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure m]
      (hm : ∀ᵐ x ∂m, x ∈ chebyshevCube (Fin d)) :
      (∫ x, tensorChebyshevJacksonApprox f k x ∂m) =
        ∑ α ∈ Fintype.piFinset (fun _ : Fin d => range (k + 1)),
          (tensorChebyshevJacksonDamping k α * tensorChebyshevCoeff f α) *
            ∫ x, tensorNormalizedChebyshev α (WithLp.ofLp x) ∂m := by
    unfold tensorChebyshevJacksonApprox
    rw [integral_finsetSum (f := fun α x =>
      (tensorChebyshevJacksonDamping k α * tensorChebyshevCoeff f α) *
        tensorNormalizedChebyshev α (WithLp.ofLp x)) _ (fun α _ =>
      (integrable_of_ae_mem_chebyshevCube_of_continuousOn m hm
        ((continuous_tensorNormalizedChebyshev α).comp
          (PiLp.continuous_ofLp 2 _)).continuousOn).const_mul _)]
    simp_rw [integral_const_mul]
  rw [hInt μ hμ, hInt ν hν, ← sum_sub_distrib]
  simp_rw [← mul_sub]
  change (∑ α ∈ Fintype.piFinset (fun _ : Fin d => range (k + 1)),
    _ * tensorChebyshevMomentDiscrepancy μ ν α) = _
  have hzero : tensorChebyshevMomentDiscrepancy μ ν (0 : Fin d → ℕ) = 0 := by
    simp [tensorChebyshevMomentDiscrepancy, tensorNormalizedChebyshev]
  have hmem : (0 : Fin d → ℕ) ∈ Fintype.piFinset (fun _ : Fin d => range (k + 1)) := by
    simp
  rw [← Finset.sum_erase_add _ _ hmem, hzero, mul_zero, add_zero]
  rfl

/-- Every Euclidean Lipschitz observable is controlled by the actual finite
tensor moment error. This includes arbitrary atomic and boundary-supported laws. -/
theorem integral_sub_le_tensorChebyshevMomentError {d : ℕ}
    (μ ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ chebyshevCube (Fin d))
    (hν : ∀ᵐ x ∂ν, x ∈ chebyshevCube (Fin d)) {k : ℕ} (hk : 1 ≤ k)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {L : NNReal}
    (hf : LipschitzOnWith L f (chebyshevCube (Fin d))) :
    (∫ x, f x ∂μ) - (∫ x, f x ∂ν) ≤
      12 * d * (L : ℝ) / k + sqrt ((d : ℝ) * π ^ d / 2) * (L : ℝ) *
        tensorChebyshevMomentError μ ν k := by
  let p := tensorChebyshevJacksonApprox f k
  have hIf (m : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure m]
      (hm : ∀ᵐ x ∂m, x ∈ chebyshevCube (Fin d)) : Integrable f m :=
    integrable_of_ae_mem_chebyshevCube_of_continuousOn m hm hf.continuousOn
  have hIp (m : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure m]
      (hm : ∀ᵐ x ∂m, x ∈ chebyshevCube (Fin d)) : Integrable p m :=
    integrable_of_ae_mem_chebyshevCube_of_continuousOn m hm
      (continuous_tensorChebyshevJacksonApprox f k).continuousOn
  have herror (m : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure m]
      (hm : ∀ᵐ x ∂m, x ∈ chebyshevCube (Fin d)) :
      |(∫ x, p x ∂m) - ∫ x, f x ∂m| ≤ 6 * d * (L : ℝ) / k := by
    rw [← integral_sub (hIp m hm) (hIf m hm), ← Real.norm_eq_abs]
    apply (norm_integral_le_of_norm_le_const (C := 6 * d * (L : ℝ) / k) ?_).trans_eq (by simp)
    filter_upwards [hm] with x hx
    simpa only [p, Real.norm_eq_abs, Fintype.card_fin] using
      abs_tensorChebyshevJacksonApprox_sub_le_of_lipschitzOnWith hf hk hx
  have hμerr := (abs_le.mp (herror μ hμ)).1
  have hνerr := (abs_le.mp (herror ν hν)).2
  have hmoment := sum_tensor_damping_coeff_mul_discrepancy_le hf μ ν k
  rw [← integral_tensorChebyshevJacksonApprox_sub_eq_sum μ ν hμ hν f k] at hmoment
  change (∫ x, p x ∂μ) - (∫ x, p x ∂ν) ≤ _ at hmoment
  calc
    _ ≤ 6 * d * (L : ℝ) / k + 6 * d * (L : ℝ) / k +
        sqrt ((d : ℝ) * π ^ d / 2) * (L : ℝ) * tensorChebyshevMomentError μ ν k := by linarith
    _ = _ := by ring

/-- The complete tensor moment comparison for genuine coupling-based
one-Wasserstein distance with Euclidean transport cost. The explicit positive
kernel improves the approximation term from `36d/k` to `12d/k`.
Source: MMRS Appendix A.1, Theorem 32.
atlas: chebyshev-moment-wasserstein (partial) -/
theorem wassersteinEDistOne_le_tensorChebyshevMomentError {d : ℕ}
    (μ ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ chebyshevCube (Fin d))
    (hν : ∀ᵐ x ∂ν, x ∈ chebyshevCube (Fin d)) {k : ℕ} (hk : 1 ≤ k) :
    wassersteinEDistOne μ ν ≤ ENNReal.ofReal
      (12 * d / k + sqrt ((d : ℝ) * π ^ d / 2) * tensorChebyshevMomentError μ ν k) := by
  apply wassersteinEDistOne_le_of_ae_mem_compact_of_lipschitzOn_integral_sub_le
    μ ν isCompact_chebyshevCube hμ hν
  intro f hf
  simpa using integral_sub_le_tensorChebyshevMomentError μ ν hμ hν hk hf

end NLAlib
