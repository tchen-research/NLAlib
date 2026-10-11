import NLAlib.Concentration.Matrix.Martingale.TracePotentialProcess
import NLAlib.Concentration.Matrix.Martingale.TracePotentialCrossing
import NLAlib.ForMathlib.Probability.NonnegativeSupermartingale
import NLAlib.ForMathlib.Analysis.BernsteinParameter

/-!
# Matrix Freedman for globally integrable actual second moments

The compensated trace process, Ville's inequality, and the actual matrix crossing
give the parameter bound. The exact Bernstein parameter retains the stated constants.
-/

noncomputable section

open MeasureTheory Matrix Finset Filter Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal

namespace NLAlib

/-- Ville's inequality for the actual compensated matrix trace process bounds the
original matrix crossing. This intermediate states its supermartingale hypothesis
explicitly; the actual conditional-moment theorem below proves it.
Source: supplied operator rederivations Section 3.4; helper for `matrix-freedman`. -/
theorem measure_exists_matrix_crossing_le_of_trace_supermartingale
    {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n] [Nonempty n]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}
    {X V : ℕ → Ω → Matrix n n ℂ} {θ g t v : ℝ}
    (hθ : 0 < θ) (hg : 0 ≤ g)
    (hX : ∀ j, ∀ᵐ ω ∂μ, (X j ω).IsHermitian)
    (hV : ∀ j, ∀ᵐ ω ∂μ, (V j ω).IsHermitian)
    (hS : Supermartingale (matrixCompensatedTracePotential θ g X V) ℱ μ) :
    (μ {ω | ∃ k, t ≤ lambdaMax (matrixIncrementSum X k ω) ∧
        ‖matrixIncrementSum V k ω‖ ≤ v}).toReal ≤
      Fintype.card n * Real.exp (-θ * t + g * v) := by
  let S := matrixCompensatedTracePotential θ g X V
  have hall : ∀ᵐ ω ∂μ, (∀ j, (X j ω).IsHermitian) ∧ ∀ j, (V j ω).IsHermitian :=
    (ae_all_iff.mpr hX).and (ae_all_iff.mpr hV)
  have hHerm : ∀ᵐ ω ∂μ, ∀ k,
      (matrixIncrementSum X k ω).IsHermitian ∧ (matrixIncrementSum V k ω).IsHermitian := by
    filter_upwards [hall] with ω hω k
    exact ⟨isSelfAdjoint_sum (range k) (fun j _ => hω.1 j),
      isSelfAdjoint_sum (range k) (fun j _ => hω.2 j)⟩
  have hNonneg : ∀ k, 0 ≤ᵐ[μ] S k := by
    intro k
    filter_upwards [hHerm] with ω hω
    exact traceExp_nonneg_of_isHermitian _
      (((hω k).1.smul (IsSelfAdjoint.all θ)).sub ((hω k).2.smul (IsSelfAdjoint.all g)))
  have hinc : {ω | ∃ k, t ≤ lambdaMax (matrixIncrementSum X k ω) ∧
      ‖matrixIncrementSum V k ω‖ ≤ v} ≤ᵐ[μ] {ω | ∃ k, Real.exp (θ * t - g * v) ≤ S k ω} := by
    filter_upwards [hHerm] with ω hω hcross
    obtain ⟨k, ht, hv⟩ := hcross
    exact ⟨k, exp_sub_le_traceExp_compensated_of_crossing _ _
      (hω k).1 (hω k).2 hθ hg ht hv⟩
  have hVille := measure_exists_le_supermartingale_le hS hNonneg (Real.exp_pos (θ * t - g * v))
  have hzero : (∫ ω, S 0 ω ∂μ) = Fintype.card n := by
    simp [S]
  rw [hzero] at hVille
  have hmono := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hinc)
  refine hmono.trans (hVille.trans_eq ?_)
  rw [div_eq_mul_inv, ← Real.exp_neg]
  congr 2
  ring

/-- Actual integrable conditional second moments give the parameter matrix Freedman
bound on the arbitrary-time matrix crossing, with upper-only bounded increments.
This is the global integrability intermediate used after the audited predictable cut.
Source: Tropp 2011, Theorem 1.2; supplied operator rederivations Section 3.4;
atlas: matrix-freedman (partial) -/
theorem measure_exists_matrix_crossing_le_of_condExp_sq
    {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n] [Nonempty n]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}
    {X V : ℕ → Ω → Matrix n n ℂ}
    (hXMeas : ∀ j, StronglyMeasurable[ℱ (j + 1)] (X j))
    (hVMeas : ∀ j, StronglyMeasurable[ℱ j] (V j))
    (hXInt : ∀ j, Integrable (X j) μ) (hX2Int : ∀ j, Integrable (fun ω => X j ω ^ 2) μ)
    (hXHerm : ∀ j, ∀ᵐ ω ∂μ, (X j ω).IsHermitian)
    (hVActual : ∀ j, μ[(fun ω => X j ω ^ 2) | ℱ j] =ᵐ[μ] V j)
    (hMean : ∀ j, μ[X j | ℱ j] =ᵐ[μ] 0)
    {L θ t v : ℝ} (hθ : 0 < θ) (hθL : θ * L < 3)
    (hBound : ∀ j, ∀ᵐ ω ∂μ, X j ω ≤ algebraMap ℝ (Matrix n n ℂ) L) :
    (μ {ω | ∃ k, t ≤ lambdaMax (matrixIncrementSum X k ω) ∧
        ‖matrixIncrementSum V k ω‖ ≤ v}).toReal ≤
      Fintype.card n * Real.exp (-θ * t + ((θ ^ 2 / 2) / (1 - θ * L / 3)) * v) := by
  have hVHerm : ∀ j, ∀ᵐ ω ∂μ, (V j ω).IsHermitian := by
    intro j
    have hp := ae_posSemidef_condExp_of_ae_posSemidef (ℱ.le j) (hX2Int j)
      ((hXHerm j).mono fun ω hω => by
        have heq : X j ω ^ 2 = (X j ω)ᴴ * X j ω := by rw [hω.eq, sq]
        rw [heq]
        exact Matrix.posSemidef_conjTranspose_mul_self _)
    filter_upwards [hp, hVActual j] with ω hp hEq
    rw [hEq] at hp
    exact hp.isHermitian
  exact measure_exists_matrix_crossing_le_of_trace_supermartingale hθ
    (div_nonneg (by positivity) (by linarith)) hXHerm hVHerm
    (supermartingale_matrixCompensatedTracePotential_of_condExp_sq hXMeas hVMeas
      hXInt hX2Int hXHerm hVActual hMean hθ hθL hBound)

end NLAlib
