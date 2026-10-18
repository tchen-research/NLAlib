import NLAlib.Polynomial.FunctionApproximation.JacksonApproximation
import NLAlib.Polynomial.FunctionApproximation.ChebyshevEnergy
import NLAlib.ForMathlib.MeasureTheory.CompactKantorovich

/-! # Chebyshev moments and one-Wasserstein distance

The finite Jackson polynomial is paired directly against two actual probability
laws, so atoms and endpoint masses require no density expansion. Damping does
not increase coefficient energy. Compact transport duality then bounds the
genuine infimum over couplings.

Source: MMRS, Theorem 1 and Lemma 13, as rerouted in the measure-analysis
roadmap. Atlas `chebyshev-moment-wasserstein` (univariate clause).
-/

noncomputable section

open MeasureTheory Finset Polynomial Polynomial.Chebyshev

namespace NLAlib

/-- The difference of the actual degree-`j` Chebyshev moments of two laws. -/
def chebyshevMomentDiscrepancy (μ ν : Measure ℝ) (j : ℕ) : ℝ :=
  (∫ x, (T ℝ (j : ℤ)).eval x ∂μ) - ∫ x, (T ℝ (j : ℤ)).eval x ∂ν

/-- Weighted finite moment error. Squaring gives the source's sum of
`j⁻²` times squared moment discrepancies for `1 ≤ j ≤ k`. -/
def chebyshevMomentError (μ ν : Measure ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (∑ j ∈ Icc 1 k, (chebyshevMomentDiscrepancy μ ν j / j) ^ 2)

theorem chebyshevMomentError_nonneg (μ ν : Measure ℝ) (k : ℕ) :
    0 ≤ chebyshevMomentError μ ν k := Real.sqrt_nonneg _

/-- The error definition is exactly the source's weighted squared discrepancy,
with absolute values harmless under the square. -/
theorem chebyshevMomentError_sq (μ ν : Measure ℝ) (k : ℕ) :
    chebyshevMomentError μ ν k ^ 2 =
      ∑ j ∈ Icc 1 k, ((j : ℝ)⁻¹) ^ 2 * |chebyshevMomentDiscrepancy μ ν j| ^ 2 := by
  rw [chebyshevMomentError, Real.sq_sqrt (sum_nonneg (fun _ _ => sq_nonneg _))]
  apply sum_congr rfl
  intro j _
  simp only [sq_abs, div_eq_mul_inv, inv_pow]
  ring

private theorem integrable_of_ae_mem_Icc_of_continuousOn
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc (-1 : ℝ) 1)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1)) : Integrable f μ := by
  have hi := hf.integrableOn_compact (μ := μ) isCompact_Icc
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμ] at hi

/-- The coefficient-controlled Jackson polynomial obeys the weighted moment
bound, with the exact coefficient-energy constant. -/
theorem sum_damping_chebyshevCoeff_mul_discrepancy_le
    {f : ℝ → ℝ} {L : NNReal} (hf : LipschitzOnWith L f (Set.Icc (-1 : ℝ) 1))
    (μ ν : Measure ℝ) (k : ℕ) :
    (∑ j ∈ Icc 1 k, chebyshevJacksonDamping k j * chebyshevCoeff f j *
      chebyshevMomentDiscrepancy μ ν j) ≤ (L : ℝ) * chebyshevMomentError μ ν k := by
  let a := fun j : ℕ => (j : ℝ) * (chebyshevJacksonDamping k j * chebyshevCoeff f j)
  let b := fun j : ℕ => chebyshevMomentDiscrepancy μ ν j / j
  have heq (j : ℕ) (hj : j ∈ Icc 1 k) :
      a j * b j = chebyshevJacksonDamping k j * chebyshevCoeff f j *
        chebyshevMomentDiscrepancy μ ν j := by
    have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (by have := mem_Icc.mp hj; omega : j ≠ 0)
    dsimp [a, b]
    field_simp
  have henergy : (∑ j ∈ Icc 1 k, a j ^ 2) ≤ (L : ℝ) ^ 2 := by
    apply le_trans _ (sum_mul_sq_chebyshevCoeff_le_of_lipschitzOnWith hf (Icc 1 k)
      (by intro j hj; exact (mem_Icc.mp hj).1))
    apply sum_le_sum
    intro j hj
    have hρ := chebyshevJacksonDamping_mem_Icc (by have := mem_Icc.mp hj; omega : j ≤ k + 1)
    dsimp [a]
    calc
      _ = chebyshevJacksonDamping k j ^ 2 * ((j : ℝ) ^ 2 * chebyshevCoeff f j ^ 2) := by ring
      _ ≤ 1 * ((j : ℝ) ^ 2 * chebyshevCoeff f j ^ 2) :=
        mul_le_mul_of_nonneg_right (by nlinarith [hρ.1, hρ.2]) (by positivity)
      _ = _ := one_mul _
  have hroot : Real.sqrt (∑ j ∈ Icc 1 k, a j ^ 2) ≤ (L : ℝ) := by
    exact (Real.sqrt_le_sqrt henergy).trans_eq (Real.sqrt_sq L.coe_nonneg)
  calc
    _ = ∑ j ∈ Icc 1 k, a j * b j := sum_congr rfl (fun j hj => (heq j hj).symm)
    _ ≤ Real.sqrt (∑ j ∈ Icc 1 k, a j ^ 2) * Real.sqrt (∑ j ∈ Icc 1 k, b j ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ a b
    _ ≤ (L : ℝ) * chebyshevMomentError μ ν k :=
      mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _)

/-- Pairing the actual finite polynomial against the two laws cancels the
zeroth moment and leaves precisely the damped positive moment discrepancies. -/
theorem integral_chebyshevJacksonApprox_sub_eq_sum
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc (-1 : ℝ) 1)
    (hν : ∀ᵐ x ∂ν, x ∈ Set.Icc (-1 : ℝ) 1) (f : ℝ → ℝ) (k : ℕ) :
    (∫ x, (chebyshevJacksonApprox f k).eval x ∂μ) -
      (∫ x, (chebyshevJacksonApprox f k).eval x ∂ν) =
      ∑ j ∈ Icc 1 k, chebyshevJacksonDamping k j * chebyshevCoeff f j *
        chebyshevMomentDiscrepancy μ ν j := by
  have hInt (m : Measure ℝ) [IsProbabilityMeasure m]
      (hm : ∀ᵐ x ∂m, x ∈ Set.Icc (-1 : ℝ) 1) :
      (∫ x, (chebyshevJacksonApprox f k).eval x ∂m) =
        ∑ j ∈ range (k + 1), (chebyshevJacksonDamping k j * chebyshevCoeff f j) *
          ∫ x, (T ℝ (j : ℤ)).eval x ∂m := by
    simp only [chebyshevJacksonApprox, eval_finsetSum, eval_mul, eval_C]
    rw [integral_finsetSum (f := fun (j : ℕ) (x : ℝ) =>
      (chebyshevJacksonDamping k j * chebyshevCoeff f j) * (T ℝ (j : ℤ)).eval x)
      _ (fun j _ =>
      (integrable_of_ae_mem_Icc_of_continuousOn m hm
        (T ℝ (j : ℤ)).continuous.continuousOn).const_mul _)]
    simp_rw [integral_const_mul]
  rw [hInt μ hμ, hInt ν hν, ← sum_sub_distrib]
  simp_rw [← mul_sub]
  change (∑ j ∈ range (k + 1), _ * chebyshevMomentDiscrepancy μ ν j) = _
  have hzero : chebyshevMomentDiscrepancy μ ν 0 = 0 := by
    simp [chebyshevMomentDiscrepancy]
  have hrange : range (k + 1) = insert 0 (Icc 1 k) := by
    ext j
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hrange, sum_insert (by simp), hzero, mul_zero, zero_add]

/-- A Lipschitz observable is controlled by the weighted moment error. The
explicit positive kernel gives the stronger approximation term `12L/k`. -/
theorem integral_sub_le_chebyshevMomentError
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc (-1 : ℝ) 1)
    (hν : ∀ᵐ x ∂ν, x ∈ Set.Icc (-1 : ℝ) 1) {k : ℕ} (hk : 1 ≤ k)
    {f : ℝ → ℝ} {L : NNReal} (hf : LipschitzOnWith L f (Set.Icc (-1 : ℝ) 1)) :
    (∫ x, f x ∂μ) - (∫ x, f x ∂ν) ≤
      12 * (L : ℝ) / k + (L : ℝ) * chebyshevMomentError μ ν k := by
  let p := chebyshevJacksonApprox f k
  have hIf (m : Measure ℝ) [IsProbabilityMeasure m]
      (hm : ∀ᵐ x ∂m, x ∈ Set.Icc (-1 : ℝ) 1) : Integrable f m :=
    integrable_of_ae_mem_Icc_of_continuousOn m hm hf.continuousOn
  have hIp (m : Measure ℝ) [IsProbabilityMeasure m]
      (hm : ∀ᵐ x ∂m, x ∈ Set.Icc (-1 : ℝ) 1) : Integrable p.eval m :=
    integrable_of_ae_mem_Icc_of_continuousOn m hm p.continuous.continuousOn
  have herror (m : Measure ℝ) [IsProbabilityMeasure m]
      (hm : ∀ᵐ x ∂m, x ∈ Set.Icc (-1 : ℝ) 1) :
      |(∫ x, p.eval x ∂m) - ∫ x, f x ∂m| ≤ 6 * (L : ℝ) / k := by
    rw [← integral_sub (hIp m hm) (hIf m hm), ← Real.norm_eq_abs]
    apply (norm_integral_le_of_norm_le_const (C := 6 * (L : ℝ) / k) ?_).trans_eq (by simp)
    filter_upwards [hm] with x hx
    exact abs_eval_chebyshevJacksonApprox_sub_le hf hk hx
  have hμerr := (abs_le.mp (herror μ hμ)).1
  have hνerr := (abs_le.mp (herror ν hν)).2
  have hmoment := sum_damping_chebyshevCoeff_mul_discrepancy_le hf μ ν k
  rw [← integral_chebyshevJacksonApprox_sub_eq_sum μ ν hμ hν f k] at hmoment
  change (∫ x, p.eval x ∂μ) - (∫ x, p.eval x ∂ν) ≤ _ at hmoment
  calc
    _ ≤ 6 * (L : ℝ) / k + 6 * (L : ℝ) / k + (L : ℝ) * chebyshevMomentError μ ν k := by
      linarith
    _ = _ := by ring

/-- Weighted Chebyshev moment comparison for genuine coupling-based
one-Wasserstein distance, including arbitrary atomic laws on the interval.
The tensor clause is supplied separately.
Source: MMRS Theorem 1, with a stronger `12/k` approximation term.
atlas: chebyshev-moment-wasserstein (partial) -/
theorem wassersteinEDistOne_le_twelve_div_add_chebyshevMomentError
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc (-1 : ℝ) 1)
    (hν : ∀ᵐ x ∂ν, x ∈ Set.Icc (-1 : ℝ) 1) {k : ℕ} (hk : 1 ≤ k) :
    wassersteinEDistOne μ ν ≤ ENNReal.ofReal (12 / k + chebyshevMomentError μ ν k) := by
  apply wassersteinEDistOne_le_of_ae_mem_compact_of_lipschitzOn_integral_sub_le
    μ ν isCompact_Icc hμ hν
  intro f hf
  simpa using integral_sub_le_chebyshevMomentError μ ν hμ hν hk hf

/-- The univariate moment comparison with the displayed source constant `36`.
Source: MMRS Theorem 1. The stronger `12/k` estimate is available above.
atlas: chebyshev-moment-wasserstein (partial) -/
theorem wassersteinEDistOne_le_thirtySix_div_add_chebyshevMomentError
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc (-1 : ℝ) 1)
    (hν : ∀ᵐ x ∂ν, x ∈ Set.Icc (-1 : ℝ) 1) {k : ℕ} (hk : 1 ≤ k) :
    wassersteinEDistOne μ ν ≤ ENNReal.ofReal (36 / k + chebyshevMomentError μ ν k) := by
  apply (wassersteinEDistOne_le_twelve_div_add_chebyshevMomentError μ ν hμ hν hk).trans
  apply ENNReal.ofReal_le_ofReal
  gcongr
  norm_num

end NLAlib
