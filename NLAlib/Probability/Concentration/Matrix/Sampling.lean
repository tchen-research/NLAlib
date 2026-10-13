import NLAlib.Probability.Concentration.Matrix.MatrixChernoff
import NLAlib.ForMathlib.Analysis.ExpBounds
import NLAlib.Matrix.Functions.ExtremeEigenvalues

/-!
# Matrix Chernoff for sampling: explicit-constant tails

For `N` independent random positive semidefinite matrices `Mₖ` with `𝔼 Mₖ = I` and
`λmax(Mₖ) ≤ L`, the empirical average `N⁻¹ ∑ Mₖ` satisfies
`P(λmin ≤ 1 - ε) ≤ d e^{-ε² N/(2L)}` and `P(λmax ≥ 1 + ε) ≤ d e^{-ε² N/(3L)}`.
These are corollaries of the matrix Chernoff tails with simplified constants.

The scalar inequalities `-ε - (1-ε) log(1-ε) ≤ -ε²/2` and `ε - (1+ε) log(1+ε) ≤ -ε²/3`
are in `NLAlib.ForMathlib.Analysis.ExpBounds`, the spectral API (`lambdaMax_smul_of_pos`, …) in
`NLAlib.Matrix.Functions.ExtremeEigenvalues`.

Sources: Tropp 2015, §5.1 (Thm 5.1.1) with the simplified tails of Tropp 2012
(*User-friendly tail bounds*), Rem 5.3; Tropp 2011 (SRHT), Thm 2.2..
Atlas `matrix-chernoff-sampling`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped Pointwise ComplexOrder

noncomputable section

namespace NLAlib

/-! ### Sampling corollary of the matrix Chernoff inequality -/

section Sampling

variable {Ω : Type*} [MeasurableSpace Ω]

open scoped Matrix.Norms.L2Operator in
/-- Common reduction: the rescaled summands `N⁻¹ Mₖ` satisfy the hypotheses of
the matrix Chernoff theorem with `L/N`, their mean sum is `I`, and both tails of the conclusion hold
at `a = b = 1`. -/
private lemma matrix_chernoff_sampling_aux (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ}
    [NeZero d] (hN : 0 < N) (M : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ) (L : ℝ) (hL : 0 < L)
    (hMeas : ∀ k, Measurable (M k)) (hIndep : iIndepFun M μ)
    (hPSD : ∀ k, ∀ᵐ ω ∂μ, (M k ω).PosSemidef)
    (hBound : ∀ k, ∀ᵐ ω ∂μ, lambdaMax (M k ω) ≤ L)
    (hMean : ∀ k, ∫ ω, M k ω ∂μ = 1) :
    (∀ ε : ℝ, 0 ≤ ε → ε < 1 →
      μ.real {ω | lambdaMin ((1 / (N : ℝ)) • ∑ k, M k ω) ≤ 1 - ε} ≤
        chernoffLowerTail d 1 (L / N) ε) ∧
    (∀ ε : ℝ, 0 ≤ ε →
      μ.real {ω | 1 + ε ≤ lambdaMax ((1 / (N : ℝ)) • ∑ k, M k ω)} ≤
        chernoffUpperTail d 1 (L / N) ε) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  let X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ := fun k ω => (1 / (N : ℝ)) • M k ω
  have hXMeas : ∀ k, Measurable (X k) := fun k =>
    (measurable_const_smul (1 / (N : ℝ))).comp (hMeas k)
  have hXIndep : iIndepFun X μ :=
    hIndep.comp (fun _ A => (1 / (N : ℝ)) • A) (fun _ => measurable_const_smul _)
  have hXPSD : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef := fun k => by
    filter_upwards [hPSD k] with ω h
    exact h.smul hc.le
  have hXBound : ∀ k, ∀ᵐ ω ∂μ, lambdaMax (X k ω) ≤ L / N := fun k => by
    filter_upwards [hBound k] with ω h
    simp only [X, lambdaMax_smul_of_pos _ hc]
    rw [div_eq_mul_one_div L, mul_comm L]
    exact mul_le_mul_of_nonneg_left h hc.le
  have hsum : ∑ k, ∫ ω, X k ω ∂μ = 1 := by
    simp only [X, integral_smul, hMean, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_one_div_cancel hNr.ne', one_smul]
  have hY : ∀ ω, ∑ k, X k ω = (1 / (N : ℝ)) • ∑ k, M k ω := fun ω => by
    simp only [X, Finset.smul_sum]
  refine ⟨fun ε hε0 hε1 => ?_, fun ε hε0 => ?_⟩
  · have := measureReal_lambdaMin_sum_le_le_chernoffLowerTail μ X (by positivity)
      hXMeas hXIndep hXPSD hXBound hε0 hε1
    rw [hsum, lambdaMin_one, mul_one] at this
    simpa only [hY] using this
  · have := measureReal_lambdaMax_sum_ge_le_chernoffUpperTail μ X (by positivity)
      hXMeas hXIndep hXPSD hXBound hε0
    rw [hsum, lambdaMax_one, mul_one] at this
    simpa only [hY] using this

open scoped Matrix.Norms.L2Operator in
/-- **Matrix Chernoff for sampling, lower tail.** Let `M₁, …, M_N` be independent random
positive semidefinite `d × d` matrices with `λmax(Mₖ) ≤ L` and `𝔼 Mₖ = I`. Then for
`0 ≤ ε < 1`, `P(λmin(N⁻¹ ∑ₖ Mₖ) ≤ 1 - ε) ≤ d e^{-ε² N/(2L)}`.
Tropp 2015, Thm 5.1.1 with Tropp 2012, Rem 5.3; Tropp 2011, Thm 2.2.
Atlas `matrix-chernoff-sampling`. Deviation: the atlas's unspecified constant is the explicit
`2`; the index `Fin N` is inherited from the matrix Chernoff theorem.
atlas: matrix-chernoff-sampling -/
theorem matrix_chernoff_sampling_lower (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ}
    [NeZero d] (hN : 0 < N) (M : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ) (L : ℝ) (hL : 0 < L)
    (hMeas : ∀ k, Measurable (M k)) (hIndep : iIndepFun M μ)
    (hPSD : ∀ k, ∀ᵐ ω ∂μ, (M k ω).PosSemidef)
    (hBound : ∀ k, ∀ᵐ ω ∂μ, lambdaMax (M k ω) ≤ L)
    (hMean : ∀ k, ∫ ω, M k ω ∂μ = 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    μ.real {ω | lambdaMin ((1 / (N : ℝ)) • ∑ k, M k ω) ≤ 1 - ε}
      ≤ d * exp (-(ε ^ 2) * N / (2 * L)) := by
  refine ((matrix_chernoff_sampling_aux μ hN M L hL hMeas hIndep hPSD hBound hMean).1
    ε hε0 hε1).trans ?_
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hLN : L / N ≠ 0 := by positivity
  have h1ε : 0 < 1 - ε := by linarith
  rw [chernoffLowerTail, if_neg hLN]
  gcongr
  rw [show Real.rpow (1 - ε) (1 - ε) = exp (log (1 - ε) * (1 - ε)) from rpow_def_of_pos h1ε _,
    ← exp_sub, show Real.rpow (exp (-ε - log (1 - ε) * (1 - ε))) (1 / (L / N)) =
      exp ((-ε - log (1 - ε) * (1 - ε)) * (1 / (L / N))) from (exp_mul _ _).symm]
  gcongr
  have key := neg_sub_mul_log_one_sub_le hε0 hε1
  have hNL : 0 ≤ 1 / (L / N) := by positivity
  calc (-ε - log (1 - ε) * (1 - ε)) * (1 / (L / N)) ≤ -(ε ^ 2 / 2) * (1 / (L / N)) :=
        mul_le_mul_of_nonneg_right (by linarith) hNL
    _ = -(ε ^ 2) * N / (2 * L) := by field_simp

open scoped Matrix.Norms.L2Operator in
/-- **Matrix Chernoff for sampling, upper tail.** Under the hypotheses of
`matrix_chernoff_sampling_lower`, for `0 ≤ ε ≤ 1`,
`P(λmax(N⁻¹ ∑ₖ Mₖ) ≥ 1 + ε) ≤ d e^{-ε² N/(3L)}`.
Tropp 2015, Thm 5.1.1 with Tropp 2012, Rem 5.3; Tropp 2011, Thm 2.2.
Atlas `matrix-chernoff-sampling`. Deviation: the atlas's unspecified constant is the explicit
`3` (valid for `ε ≤ 1`); the index `Fin N` is inherited from the matrix Chernoff theorem.
atlas: matrix-chernoff-sampling -/
theorem matrix_chernoff_sampling_upper (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ}
    [NeZero d] (hN : 0 < N) (M : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ) (L : ℝ) (hL : 0 < L)
    (hMeas : ∀ k, Measurable (M k)) (hIndep : iIndepFun M μ)
    (hPSD : ∀ k, ∀ᵐ ω ∂μ, (M k ω).PosSemidef)
    (hBound : ∀ k, ∀ᵐ ω ∂μ, lambdaMax (M k ω) ≤ L)
    (hMean : ∀ k, ∫ ω, M k ω ∂μ = 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    μ.real {ω | 1 + ε ≤ lambdaMax ((1 / (N : ℝ)) • ∑ k, M k ω)}
      ≤ d * exp (-(ε ^ 2) * N / (3 * L)) := by
  refine ((matrix_chernoff_sampling_aux μ hN M L hL hMeas hIndep hPSD hBound hMean).2
    ε hε0).trans ?_
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hLN : L / N ≠ 0 := by positivity
  have h1ε : 0 < 1 + ε := by linarith
  rw [chernoffUpperTail, if_neg hLN]
  gcongr
  rw [show Real.rpow (1 + ε) (1 + ε) = exp (log (1 + ε) * (1 + ε)) from rpow_def_of_pos h1ε _,
    ← exp_sub, show Real.rpow (exp (ε - log (1 + ε) * (1 + ε))) (1 / (L / N)) =
      exp ((ε - log (1 + ε) * (1 + ε)) * (1 / (L / N))) from (exp_mul _ _).symm]
  gcongr
  have key := sub_mul_log_one_add_le hε0 hε1
  have hNL : 0 ≤ 1 / (L / N) := by positivity
  calc (ε - log (1 + ε) * (1 + ε)) * (1 / (L / N)) ≤ -(ε ^ 2 / 3) * (1 / (L / N)) :=
        mul_le_mul_of_nonneg_right (by linarith) hNL
    _ = -(ε ^ 2) * N / (3 * L) := by field_simp

end Sampling

end NLAlib
