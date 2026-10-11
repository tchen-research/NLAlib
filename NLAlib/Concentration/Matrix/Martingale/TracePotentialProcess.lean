import NLAlib.Concentration.Matrix.Martingale.TracePotential
import NLAlib.Concentration.Matrix.Martingale.TracePotentialStep
import NLAlib.ForMathlib.Analysis.Matrix.Order

/-!
# The actual compensated matrix trace process is a supermartingale

This is the globally integrable second-moment intermediate theorem. Its actual
conditional moment relation will be derived for the variance-budget localized process.
-/

noncomputable section
set_option maxHeartbeats 600000

open MeasureTheory Matrix Finset Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

/-- Actual adapted centered increments and actual integrable conditional second moments
give the compensated trace-exponential supermartingale. Only an upper bound on increments
is assumed. This is the global-second-moment intermediate used after localization, not
the final local-moment matrix Freedman theorem.
Source: operator rederivations Section 3.3 and supplied `audit:combined`.
atlas: matrix-freedman (partial) -/
theorem supermartingale_matrixCompensatedTracePotential_of_condExp_sq
    {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n] [Nonempty n]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}
    {X V : ℕ → Ω → Matrix n n ℂ}
    (hXMeas : ∀ j, StronglyMeasurable[ℱ (j + 1)] (X j))
    (hVMeas : ∀ j, StronglyMeasurable[ℱ j] (V j))
    (hXInt : ∀ j, Integrable (X j) μ) (hX2Int : ∀ j, Integrable (fun ω => X j ω ^ 2) μ)
    (hXHerm : ∀ j, ∀ᵐ ω ∂μ, (X j ω).IsHermitian)
    (hVActual : ∀ j, μ[(fun ω => X j ω ^ 2) | ℱ j] =ᵐ[μ] V j)
    (hMean : ∀ j, μ[X j | ℱ j] =ᵐ[μ] 0)
    {L θ : ℝ} (hθ : 0 < θ) (hθL : θ * L < 3)
    (hBound : ∀ j, ∀ᵐ ω ∂μ, X j ω ≤ algebraMap ℝ (Matrix n n ℂ) L) :
    Supermartingale (matrixCompensatedTracePotential θ ((θ ^ 2 / 2) / (1 - θ * L / 3)) X V) ℱ μ := by
  let g : ℝ := (θ ^ 2 / 2) / (1 - θ * L / 3)
  let Y : ℕ → Ω → Matrix n n ℂ := matrixIncrementSum X
  let W : ℕ → Ω → Matrix n n ℂ := matrixIncrementSum V
  let S : ℕ → Ω → ℝ := matrixCompensatedTracePotential θ g X V
  have hg : 0 ≤ g := by dsimp [g]; apply div_nonneg (by positivity); linarith
  have hYMeas : ∀ k, StronglyMeasurable[ℱ k] (Y k) := by
    intro k
    apply Finset.stronglyMeasurable_fun_sum (range k)
    intro j hj
    exact (hXMeas j).mono (ℱ.mono (Nat.succ_le_of_lt (mem_range.mp hj)))
  have hWMeas : ∀ k, StronglyMeasurable[ℱ k] (W k) := by
    intro k
    apply Finset.stronglyMeasurable_fun_sum (range k)
    intro j hj
    exact (hVMeas j).mono (ℱ.mono (Nat.le_of_lt (mem_range.mp hj)))
  have hVPSD : ∀ j, ∀ᵐ ω ∂μ, (V j ω).PosSemidef := by
    intro j
    have hp := ae_posSemidef_condExp_of_ae_posSemidef (ℱ.le j) (hX2Int j)
      ((hXHerm j).mono fun ω hω => by
        have heq : X j ω ^ 2 = (X j ω)ᴴ * X j ω := by rw [hω.eq, sq]
        rw [heq]
        exact Matrix.posSemidef_conjTranspose_mul_self _)
    filter_upwards [hp, hVActual j] with ω hp hEq
    rw [hEq] at hp
    exact hp
  have hYHerm : ∀ k, ∀ᵐ ω ∂μ, (Y k ω).IsHermitian := by
    intro k
    have hall : ∀ᵐ ω ∂μ, ∀ j, (X j ω).IsHermitian := ae_all_iff.mpr hXHerm
    filter_upwards [hall] with ω hω
    exact isSelfAdjoint_sum (range k) (fun j _ => hω j)
  have hWPSD : ∀ k, ∀ᵐ ω ∂μ, (W k ω).PosSemidef := by
    intro k
    have hall : ∀ᵐ ω ∂μ, ∀ j, (V j ω).PosSemidef := ae_all_iff.mpr hVPSD
    filter_upwards [hall] with ω hω
    exact Matrix.posSemidef_sum (range k) (fun j _ => hω j)
  have hYBound : ∀ k, ∀ᵐ ω ∂μ, Y k ω ≤ algebraMap ℝ (Matrix n n ℂ) ((k : ℝ) * L) := by
    intro k
    have hall : ∀ᵐ ω ∂μ, ∀ j, X j ω ≤ algebraMap ℝ (Matrix n n ℂ) L := ae_all_iff.mpr hBound
    filter_upwards [hall] with ω hω
    have h := Finset.sum_le_sum (fun j (_ : j ∈ range k) => hω j)
    have hsum : (∑ _j ∈ range k, algebraMap ℝ (Matrix n n ℂ) L) =
        algebraMap ℝ (Matrix n n ℂ) ((k : ℝ) * L) := by
      rw [← map_sum]
      simp only [Finset.sum_const, card_range, nsmul_eq_mul]
    rw [hsum] at h
    exact h
  have hPhiMeas : ∀ k, StronglyMeasurable[ℱ k] (fun ω => θ • Y k ω - g • W k ω) :=
    fun k => (hYMeas k |>.const_smul θ).sub (hWMeas k |>.const_smul g)
  have hPhiHerm : ∀ k, ∀ᵐ ω ∂μ, (θ • Y k ω - g • W k ω).IsHermitian := by
    intro k
    filter_upwards [hYHerm k, hWPSD k] with ω hY hW
    exact (hY.smul (IsSelfAdjoint.all θ)).sub (hW.isHermitian.smul (IsSelfAdjoint.all g))
  have hPhiBound : ∀ k, ∀ᵐ ω ∂μ, θ • Y k ω - g • W k ω ≤
      algebraMap ℝ (Matrix n n ℂ) (θ * ((k : ℝ) * L)) := by
    intro k
    filter_upwards [hYBound k, hWPSD k] with ω hY hW
    have hscale := matrix_smul_le_smul_of_nonneg hY hθ.le
    have hscale' : θ • Y k ω ≤ algebraMap ℝ (Matrix n n ℂ) (θ * ((k : ℝ) * L)) := by
      simpa only [Algebra.algebraMap_eq_smul_one, smul_smul] using hscale
    exact (sub_le_self _ (hW.smul hg).nonneg).trans hscale'
  have hSMeas : StronglyAdapted ℱ S :=
    fun k => continuous_traceExp.comp_stronglyMeasurable (hPhiMeas k)
  have hSInt : ∀ k, Integrable (S k) μ := by
    intro k
    have h := integrable_traceExp_add_of_ae_le_algebraMap
      ((hPhiMeas k).mono (ℱ.le k)).aestronglyMeasurable aestronglyMeasurable_const
      (hPhiHerm k) (ae_of_all μ fun _ => Matrix.isHermitian_zero)
      (hPhiBound k) (ae_of_all μ fun _ => (show (0 : Matrix n n ℂ) ≤ algebraMap ℝ (Matrix n n ℂ) 0 by simp))
    change Integrable (fun ω => traceExp (θ • Y k ω - g • W k ω)) μ
    simpa only [add_zero] using h
  apply supermartingale_nat hSMeas hSInt
  intro k
  have hstep := condExp_traceExp_variance_update_le (ℱ.le k)
    ((hXMeas k).mono (ℱ.le (k + 1))).measurable (hYMeas k).measurable (hWMeas k).measurable
    (hXInt k) (hX2Int k) (hXHerm k) (hYHerm k) (hWPSD k) (hMean k) hθ hθL (hBound k) (hYBound k)
  have hfun : (fun ω => traceExp (θ • (Y k ω + X k ω) -
      g • (W k ω + μ[(fun ω => X k ω ^ 2) | ℱ k] ω))) =ᵐ[μ] S (k + 1) := by
    filter_upwards [hVActual k] with ω hEq
    change traceExp (θ • (Y k ω + X k ω) - g • (W k ω + μ[(fun ω => X k ω ^ 2) | ℱ k] ω)) =
      traceExp (θ • matrixIncrementSum X (k + 1) ω - g • matrixIncrementSum V (k + 1) ω)
    rw [matrixIncrementSum_succ, matrixIncrementSum_succ, hEq]
  have hCE := condExp_congr_ae (m := ℱ k) (μ := μ) hfun
  filter_upwards [hstep, hCE] with ω hstepω hCEω
  rw [← hCEω]
  exact hstepω

end NLAlib
