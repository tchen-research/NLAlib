import NLAlib.Probability.Concentration.Basic.MatrixCalculus
import NLAlib.Probability.Concentration.Matrix.LiebIntegralPosDef
import NLAlib.Matrix.OperatorTheory.Basic
import NLAlib.ForMathlib.Analysis.ExpBounds
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Lemma 6.6.2 — Matrix Bernstein mgf and cgf bounds

Main declaration: `NLAlib.bernstein_matrix_mgf_cgf_le`.

Atlas: `matrix-bernstein`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Lemma 6.6.2, printed pp. 97–98.
-/
open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open NLAlib

/-- For a centered Hermitian random matrix with `λmax X ≤ L` and `0 < θ < 3/L`, `𝔼 matrixExp (θ • X) ≼
matrixExp (c • 𝔼 X²)` and `matrixLog 𝔼 matrixExp (θ • X) ≼ c • 𝔼 X²`, where `c = (θ²/2)/(1 -
θL/3)`.

Tropp 2015, Lemma 6.6.2. Atlas: `matrix-bernstein`. Ported from the Prove2me mission *An
Introduction to Matrix Concentration Inequalities, Ch 6*. -/
theorem NLAlib.bernstein_matrix_mgf_cgf_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (X : Ω → Matrix (Fin d) (Fin d) ℂ) (L θ : ℝ)
    (hL : 0 < L) (hθ : 0 < θ) (hθL : θ < 3 / L)
    (hMeas : Measurable X) (hHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    (hL2 : MemLp X 2 μ) (hMean : (∫ ω, X ω ∂μ) = 0)
    (hBound : ∀ᵐ ω ∂μ, lambdaMax (X ω) ≤ L) :
    (∫ ω, matrixExp (θ • X ω) ∂μ) ≤
      (matrixExp (((θ ^ 2 / 2) / (1 - θ * L / 3)) • (∫ ω, X ω ^ 2 ∂μ))) ∧
    (matrixLog (∫ ω, matrixExp (θ • X ω) ∂μ)) ≤
      (((θ ^ 2 / 2) / (1 - θ * L / 3)) • (∫ ω, X ω ^ 2 ∂μ)) := by
  have hθL' : θ * L < 3 := (lt_div_iff₀ hL).mp hθL
  set c := (θ ^ 2 / 2) / (1 - θ * L / 3) with hc
  -- integrability
  have hXint : Integrable X μ := hL2.integrable one_le_two
  have hX2int : Integrable (fun ω => X ω ^ 2) μ := by
    refine Integrable.mono' (hL2.integrable_norm_pow two_ne_zero) ?_
      (Filter.Eventually.of_forall fun ω => ?_)
    · exact (continuous_pow 2).comp_aestronglyMeasurable hL2.1
    · rw [sq, sq]
      exact Matrix.l2_opNorm_mul _ _
  have hEcont : Continuous (fun A : Matrix (Fin d) (Fin d) ℂ => matrixExp (θ • A)) := by
    let : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) :=
      NormedAlgebra.restrictScalars ℚ ℂ _
    dsimp [matrixExp]
    fun_prop
  have hEint : Integrable (fun ω => matrixExp (θ • X ω)) μ := by
    refine Integrable.of_bound (hEcont.comp_aestronglyMeasurable hMeas.aestronglyMeasurable)
      (Real.exp (θ * L)) ?_
    filter_upwards [hHerm, hBound] with ω hH hB
    rw [matrixExp_smul_eq_cfc _ hH]
    apply norm_cfc_le (Real.exp_pos _).le
    intro x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_mem_spectrum_of_lambdaMax_le _ hH hB x hx) hθ.le)
  have hXθ : Integrable (fun ω => θ • X ω) μ := hXint.smul θ
  have hX2c : Integrable (fun ω => c • X ω ^ 2) μ := hX2int.smul c
  have hlin : Integrable (fun ω => (1 : Matrix (Fin d) (Fin d) ℂ) + θ • X ω) μ :=
    (integrable_const 1).add hXθ
  have hQint : Integrable (fun ω => (1 : Matrix (Fin d) (Fin d) ℂ) + θ • X ω + c • X ω ^ 2) μ :=
    hlin.add hX2c
  have hpt : ∀ᵐ ω ∂μ, matrixExp (θ • X ω) ≤ 1 + θ • X ω + c • X ω ^ 2 := by
    filter_upwards [hHerm, hBound] with ω hH hB
    exact matrixExp_smul_le_one_add_smul_add_smul_sq_of_spectrum_le _ hH
      (fun x hx => exp_mul_le_one_add_mul_add_sq_mul_of_le hθ hθL'
        (le_of_mem_spectrum_of_lambdaMax_le _ hH hB x hx))
  have hI1 : ∫ ω, matrixExp (θ • X ω) ∂μ ≤ 1 + c • ∫ ω, X ω ^ 2 ∂μ := by
    have h := integral_mono_ae hEint hQint hpt
    rw [integral_add hlin hX2c, integral_add (integrable_const 1) hXθ,
      integral_const, integral_smul, integral_smul, hMean] at h
    simpa using h
  -- the second moment is positive semidefinite
  have hS : (0 : Matrix (Fin d) (Fin d) ℂ) ≤ ∫ ω, X ω ^ 2 ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hHerm] with ω hH
    have : X ω ^ 2 = Matrix.conjTranspose (X ω) * X ω := by rw [hH.eq, sq]
    rw [Pi.zero_apply, this]
    exact (Matrix.posSemidef_conjTranspose_mul_self _).nonneg
  set S := ∫ ω, X ω ^ 2 ∂μ with hSdef
  have hSH : S.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hS).isHermitian
  have hBH : (c • S).IsHermitian := hSH.smul (isSelfAdjoint_iff.mpr (star_trivial c))
  have h1 : ∫ ω, matrixExp (θ • X ω) ∂μ ≤ matrixExp (c • S) :=
    hI1.trans (one_add_le_matrixExp_of_isHermitian _ hBH)
  refine ⟨Matrix.le_iff.mp h1, ?_⟩
  have hMPD : (∫ ω, matrixExp (θ • X ω) ∂μ).PosDef := by
    apply posDef_integral_of_ae_posDef μ _ hEint
    filter_upwards [hHerm] with ω hH
    exact (posDef_matrixExp_and_matrixLog_matrixExp _ (hH.smul (isSelfAdjoint_iff.mpr (star_trivial θ)))).1
  obtain ⟨hEPD, hlog⟩ := posDef_matrixExp_and_matrixLog_matrixExp (c • S) hBH
  have h2 : (matrixLog (∫ ω, matrixExp (θ • X ω) ∂μ)) ≤ (matrixLog (matrixExp (c • S))) :=
    CFC.log_monotoneOn hMPD.isStrictlyPositive hEPD.isStrictlyPositive h1
  rwa [hlog] at h2
