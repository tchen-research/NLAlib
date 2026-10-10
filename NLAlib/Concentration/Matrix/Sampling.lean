import NLAlib.Concentration.Matrix.Chernoff.MatrixChernoff
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Real.Pointwise

/-!
# Matrix Chernoff for sampling: explicit-constant tails

For `N` independent random positive semidefinite matrices `Mₖ` with `𝔼 Mₖ = I` and
`λmax(Mₖ) ≤ L`, the empirical average `N⁻¹ ∑ Mₖ` satisfies
`P(λmin ≤ 1 - ε) ≤ d e^{-ε² N/(2L)}` and `P(λmax ≥ 1 + ε) ≤ d e^{-ε² N/(3L)}`.
This is the real corollary of `NLAlib.matrix_chernoff` with the simplified tails.

Also provides the scalar inequalities `-ε - (1-ε) log(1-ε) ≤ -ε²/2` and
`ε - (1+ε) log(1+ε) ≤ -ε²/3` (`0 ≤ ε ≤ 1`), and the spectral API
`lambdaMax_smul_of_pos`, `lambdaMin_smul_of_pos`, `lambdaMax_one`, `lambdaMin_one`.

Sources: Tropp 2015, §5.1 (Thm 5.1.1) with the simplified tails of Tropp 2012
(*User-friendly tail bounds*), Rem 5.3; Tropp 2011 (SRHT), Thm 2.2. Audit G1 C4.
Atlas `matrix-chernoff-sampling`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped Pointwise
open scoped Matrix.Norms.L2Operator

noncomputable section
set_option autoImplicit false

namespace NLAlib

/-! ### Scalar inequalities -/

/-- `-ε - (1 - ε) log(1 - ε) ≤ -ε²/2` for `0 ≤ ε < 1`. Proof: `g(ε) = (1-ε)log(1-ε) + ε - ε²/2`
vanishes at `0` and has derivative `-log(1-ε) - ε ≥ 0`. Tropp 2012, Rem 5.3 (lower tail);
atlas `matrix-chernoff-sampling` (helper). -/
theorem neg_sub_mul_log_one_sub_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    -ε - (1 - ε) * log (1 - ε) ≤ -(ε ^ 2 / 2) := by
  let g : ℝ → ℝ := fun t => (1 - t) * log (1 - t) + t - t ^ 2 / 2
  have hderiv : ∀ t, t < 1 → HasDerivAt g (-log (1 - t) - t) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub 1
    have hlog := h1.log (by linarith)
    have hprod := h1.mul hlog
    have hp : HasDerivAt (fun t : ℝ => t - t ^ 2 / 2) (1 - t) t := by
      have := (hasDerivAt_id' t).sub ((hasDerivAt_pow 2 t).div_const 2)
      exact this.congr_deriv (by norm_num)
    have := hprod.add hp
    refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    · field_simp [show (1 - t) ≠ 0 by linarith]
      ring
    · simp only [g, Pi.add_apply, Pi.mul_apply]; ring
  have hmono : MonotoneOn g (Set.Ico 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico 0 1) ?_ ?_ ?_
    · exact fun t ht => (hderiv t ht.2).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      exact (hderiv t ht.2).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      rw [(hderiv t ht.2).deriv]
      have := log_le_sub_one_of_pos (show 0 < 1 - t by linarith [ht.2])
      linarith
  have := hmono (Set.mem_Ico.2 ⟨le_rfl, by norm_num⟩) (Set.mem_Ico.2 ⟨hε0, hε1⟩) hε0
  simp only [g, sub_zero, log_one, mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_div] at this
  linarith

/-- `ε - (1 + ε) log(1 + ε) ≤ -ε²/3` for `0 ≤ ε ≤ 1`. Proof: `log(1+ε) ≥ 2ε/(ε+2)` (first
term of Mathlib's `hasSum_log_one_add`), and `(1+ε)·2ε/(ε+2) ≥ ε + ε²/3` iff `ε ≤ 1`.
Tropp 2012, Rem 5.3 (upper tail); atlas `matrix-chernoff-sampling` (helper). -/
theorem sub_mul_log_one_add_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ε - (1 + ε) * log (1 + ε) ≤ -(ε ^ 2 / 3) := by
  have h := hasSum_log_one_add hε0
  have hlow := le_hasSum h 0 (fun n _ => by positivity)
  simp only [CharP.cast_eq_zero, mul_zero, zero_add, ne_eq, one_ne_zero, not_false_eq_true,
    div_self, mul_one, pow_one] at hlow
  have hpos : 0 < ε + 2 := by linarith
  have key : ε + ε ^ 2 / 3 ≤ (1 + ε) * (2 * (ε / (ε + 2))) := by
    rw [← sub_nonneg]
    have : (1 + ε) * (2 * (ε / (ε + 2))) - (ε + ε ^ 2 / 3) = ε ^ 2 * (1 - ε) / (3 * (ε + 2)) := by
      field_simp
      ring
    rw [this]
    have : 0 ≤ 1 - ε := by linarith
    positivity
  nlinarith [mul_le_mul_of_nonneg_left hlow (show 0 ≤ 1 + ε by linarith)]

/-! ### Extreme eigenvalues of scalings and of the identity -/

section Spectral

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- `λmax(c A) = c λmax(A)` for `c > 0`. Tropp 2015, §2.1; atlas `matrix-chernoff-sampling`
(helper). -/
theorem lambdaMax_smul_of_pos (A : Matrix d d ℂ) {c : ℝ} (hc : 0 < c) :
    lambdaMax (c • A) = c * lambdaMax A := by
  have h := spectrum.unit_smul_eq_smul (R := ℝ) A (Units.mk0 c hc.ne')
  rw [Units.smul_def, Units.val_mk0] at h
  rw [lambdaMax, h, Units.smul_def, Units.val_mk0, Real.sSup_smul_of_nonneg hc.le, smul_eq_mul,
    lambdaMax]

/-- `λmin(c A) = c λmin(A)` for `c > 0`. Tropp 2015, §2.1; atlas `matrix-chernoff-sampling`
(helper). -/
theorem lambdaMin_smul_of_pos (A : Matrix d d ℂ) {c : ℝ} (hc : 0 < c) :
    lambdaMin (c • A) = c * lambdaMin A := by
  have h := spectrum.unit_smul_eq_smul (R := ℝ) A (Units.mk0 c hc.ne')
  rw [Units.smul_def, Units.val_mk0] at h
  rw [lambdaMin, h, Units.smul_def, Units.val_mk0, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul,
    lambdaMin]

/-- `λmax(I) = 1` for a nonempty index type. Tropp 2015, §2.1; atlas
`matrix-chernoff-sampling` (helper). -/
@[simp] theorem lambdaMax_one [Nonempty d] : lambdaMax (1 : Matrix d d ℂ) = 1 := by
  rw [lambdaMax, spectrum.one_eq, csSup_singleton]

/-- `λmin(I) = 1` for a nonempty index type. Tropp 2015, §2.1; atlas
`matrix-chernoff-sampling` (helper). -/
@[simp] theorem lambdaMin_one [Nonempty d] : lambdaMin (1 : Matrix d d ℂ) = 1 := by
  rw [lambdaMin, spectrum.one_eq, csInf_singleton]

end Spectral

/-! ### Sampling corollary of the matrix Chernoff inequality -/

section Sampling

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Common reduction: the rescaled summands `N⁻¹ Mₖ` satisfy the hypotheses of
`matrix_chernoff` with `L/N`, their mean sum is `I`, and both tails of the conclusion hold
at `a = b = 1`. -/
private lemma matrix_chernoff_sampling_aux (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ}
    [NeZero d] (hN : 0 < N) (M : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ) (L : ℝ) (hL : 0 < L)
    (hMeas : ∀ k, Measurable (M k)) (hIndep : iIndepFun M μ)
    (hHerm : ∀ k, ∀ᵐ ω ∂μ, (M k ω).IsHermitian)
    (hBound : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ lambdaMin (M k ω) ∧ lambdaMax (M k ω) ≤ L)
    (hMean : ∀ k, ∫ ω, M k ω ∂μ = 1) :
    (∀ ε : ℝ, 0 ≤ ε → ε < 1 →
      (μ {ω | lambdaMin ((1 / (N : ℝ)) • ∑ k, M k ω) ≤ 1 - ε}).toReal ≤
        chernoffLowerTail d 1 (L / N) ε) ∧
    (∀ ε : ℝ, 0 ≤ ε →
      (μ {ω | 1 + ε ≤ lambdaMax ((1 / (N : ℝ)) • ∑ k, M k ω)}).toReal ≤
        chernoffUpperTail d 1 (L / N) ε) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  let X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ := fun k ω => (1 / (N : ℝ)) • M k ω
  have hXMeas : ∀ k, Measurable (X k) := fun k =>
    (measurable_const_smul (1 / (N : ℝ))).comp (hMeas k)
  have hXIndep : iIndepFun X μ :=
    hIndep.comp (fun _ A => (1 / (N : ℝ)) • A) (fun _ => measurable_const_smul _)
  have hXHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian := fun k => by
    filter_upwards [hHerm k] with ω h
    exact h.smul (IsSelfAdjoint.all _)
  have hXBound : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ lambdaMin (X k ω) ∧ lambdaMax (X k ω) ≤ L / N := fun k => by
    filter_upwards [hBound k] with ω h
    simp only [X, lambdaMin_smul_of_pos _ hc, lambdaMax_smul_of_pos _ hc]
    refine ⟨mul_nonneg hc.le h.1, ?_⟩
    rw [div_eq_mul_one_div L, mul_comm L]
    exact mul_le_mul_of_nonneg_left h.2 hc.le
  have h := matrix_chernoff μ X (L / N) (by positivity) hXMeas hXIndep hXHerm hXBound
  dsimp only at h
  obtain ⟨ha, hb, -, hlow, hup⟩ := h
  have hsum : ∑ k, ∫ ω, X k ω ∂μ = 1 := by
    simp only [X, integral_smul, hMean, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_one_div_cancel hNr.ne', one_smul]
  rw [hsum, lambdaMin_one] at ha
  rw [hsum, lambdaMax_one] at hb
  have hY : ∀ ω, ∑ k, X k ω = (1 / (N : ℝ)) • ∑ k, M k ω := fun ω => by
    simp only [X, Finset.smul_sum]
  refine ⟨fun ε hε0 hε1 => ?_, fun ε hε0 => ?_⟩
  · have := hlow ε hε0 hε1
    rw [ha, mul_one] at this
    simpa only [hY] using this
  · have := hup ε hε0
    rw [hb, mul_one] at this
    simpa only [hY] using this

/-- **Matrix Chernoff for sampling, lower tail.** Let `M₁, …, M_N` be independent random
Hermitian `d × d` matrices with `0 ≤ λmin(Mₖ)`, `λmax(Mₖ) ≤ L` and `𝔼 Mₖ = I`. Then for
`0 ≤ ε < 1`, `P(λmin(N⁻¹ ∑ₖ Mₖ) ≤ 1 - ε) ≤ d e^{-ε² N/(2L)}`.
Tropp 2015, Thm 5.1.1 with Tropp 2012, Rem 5.3; Tropp 2011, Thm 2.2; audit G1 C4.
Atlas `matrix-chernoff-sampling`. Deviation: the atlas's unspecified constant is the explicit
`2`; the index `Fin N` is inherited from `matrix_chernoff`. -/
theorem matrix_chernoff_sampling_lower (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ}
    [NeZero d] (hN : 0 < N) (M : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ) (L : ℝ) (hL : 0 < L)
    (hMeas : ∀ k, Measurable (M k)) (hIndep : iIndepFun M μ)
    (hHerm : ∀ k, ∀ᵐ ω ∂μ, (M k ω).IsHermitian)
    (hBound : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ lambdaMin (M k ω) ∧ lambdaMax (M k ω) ≤ L)
    (hMean : ∀ k, ∫ ω, M k ω ∂μ = 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    (μ {ω | lambdaMin ((1 / (N : ℝ)) • ∑ k, M k ω) ≤ 1 - ε}).toReal
      ≤ d * exp (-(ε ^ 2) * N / (2 * L)) := by
  refine ((matrix_chernoff_sampling_aux μ hN M L hL hMeas hIndep hHerm hBound hMean).1
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

/-- **Matrix Chernoff for sampling, upper tail.** Under the hypotheses of
`matrix_chernoff_sampling_lower`, for `0 ≤ ε ≤ 1`,
`P(λmax(N⁻¹ ∑ₖ Mₖ) ≥ 1 + ε) ≤ d e^{-ε² N/(3L)}`.
Tropp 2015, Thm 5.1.1 with Tropp 2012, Rem 5.3; Tropp 2011, Thm 2.2; audit G1 C4.
Atlas `matrix-chernoff-sampling`. Deviation: the atlas's unspecified constant is the explicit
`3` (valid for `ε ≤ 1`); the index `Fin N` is inherited from `matrix_chernoff`. -/
theorem matrix_chernoff_sampling_upper (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ}
    [NeZero d] (hN : 0 < N) (M : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ) (L : ℝ) (hL : 0 < L)
    (hMeas : ∀ k, Measurable (M k)) (hIndep : iIndepFun M μ)
    (hHerm : ∀ k, ∀ᵐ ω ∂μ, (M k ω).IsHermitian)
    (hBound : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ lambdaMin (M k ω) ∧ lambdaMax (M k ω) ≤ L)
    (hMean : ∀ k, ∫ ω, M k ω ∂μ = 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (μ {ω | 1 + ε ≤ lambdaMax ((1 / (N : ℝ)) • ∑ k, M k ω)}).toReal
      ≤ d * exp (-(ε ^ 2) * N / (3 * L)) := by
  refine ((matrix_chernoff_sampling_aux μ hN M L hL hMeas hIndep hHerm hBound hMean).2
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

/-- **Matrix Chernoff for sampling** (both tails, the audit G1 C4 statement): for `0 ≤ ε < 1`,
`P(λmin(N⁻¹∑Mₖ) ≤ 1 - ε) ≤ d e^{-ε²N/(2L)}` and `P(λmax(N⁻¹∑Mₖ) ≥ 1 + ε) ≤ d e^{-ε²N/(3L)}`.
Tropp 2015, Thm 5.1.1 with Tropp 2012, Rem 5.3; Tropp 2011, Thm 2.2.
Atlas `matrix-chernoff-sampling`. Deviation: explicit constants `2` and `3`; `Fin N` index
inherited from `matrix_chernoff`. -/
theorem matrix_chernoff_sampling (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ}
    [NeZero d] (hN : 0 < N) (M : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ) (L : ℝ) (hL : 0 < L)
    (hMeas : ∀ k, Measurable (M k)) (hIndep : iIndepFun M μ)
    (hHerm : ∀ k, ∀ᵐ ω ∂μ, (M k ω).IsHermitian)
    (hBound : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ lambdaMin (M k ω) ∧ lambdaMax (M k ω) ≤ L)
    (hMean : ∀ k, ∫ ω, M k ω ∂μ = 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    (μ {ω | lambdaMin ((1 / (N : ℝ)) • ∑ k, M k ω) ≤ 1 - ε}).toReal
        ≤ d * exp (-(ε ^ 2) * N / (2 * L)) ∧
      (μ {ω | 1 + ε ≤ lambdaMax ((1 / (N : ℝ)) • ∑ k, M k ω)}).toReal
        ≤ d * exp (-(ε ^ 2) * N / (3 * L)) :=
  ⟨matrix_chernoff_sampling_lower μ hN M L hL hMeas hIndep hHerm hBound hMean hε0 hε1,
    matrix_chernoff_sampling_upper μ hN M L hL hMeas hIndep hHerm hBound hMean hε0 hε1.le⟩

end Sampling

end NLAlib
