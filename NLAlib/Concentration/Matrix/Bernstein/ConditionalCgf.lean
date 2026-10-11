import NLAlib.Concentration.Matrix.Bernstein.BernsteinMgfCgf
import NLAlib.Concentration.Matrix.OperatorConvexity.LiebReindex
import NLAlib.ForMathlib.MeasureTheory.MatrixConditionalExpectation

/-!
# One-sided conditional matrix Bernstein cumulant bounds

Actual conditional centering and second moments give the conditional exponential and
logarithmic bounds. Only an upper bound on the increments is used; `L=0` is included.
-/

noncomputable section

open MeasureTheory Set Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

variable {Ω n : Type*} {m mΩ : MeasurableSpace Ω} [Fintype n] [DecidableEq n]
variable {μ : Measure Ω}

/-- An upper spectral bound alone makes the Hermitian matrix exponential integrable on
a finite measure space, even when the negative eigenvalues have no deterministic bound.
Source: scalar functional calculus and `exp(θx) ≤ exp(θL)` for `θ≥0`;
operator rederivations Section 3.1, atlas `matrix-freedman` (partial). -/
theorem integrable_matrixExp_smul_of_ae_le_algebraMap [IsFiniteMeasure μ]
    {X : Ω → Matrix n n ℂ} (hX : AEStronglyMeasurable X μ)
    (hHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian) {L θ : ℝ} (hθ : 0 ≤ θ)
    (hBound : ∀ᵐ ω ∂μ, X ω ≤ algebraMap ℝ (Matrix n n ℂ) L) :
    Integrable (fun ω => matrixExp (θ • X ω)) μ := by
  have hc : Continuous (fun A : Matrix n n ℂ => matrixExp (θ • A)) := by
    let : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
    dsimp [matrixExp]
    fun_prop
  refine Integrable.of_bound (hc.comp_aestronglyMeasurable hX) (Real.exp (θ * L)) ?_
  filter_upwards [hHerm, hBound] with ω hHerm hBound
  rw [matrixExp_smul_eq_cfc _ hHerm]
  apply norm_cfc_le (Real.exp_pos _).le
  intro x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    ((le_algebraMap_iff_spectrum_le hHerm).mp hBound x hx) hθ)

/-- Actual conditional centering and an integrable actual second moment yield
`I≤M`, `V≥0`, and `log M≤gV`, where `M=E[exp(θX)|m]`, `V=E[X²|m]`, and
`g=(θ²/2)/(1-θL/3)`. The one-sided bound permits arbitrarily negative increments.
No conditional-mgf or supermartingale inequality is an input, and `L=0` is included.
Source: Tropp 2011, Freedman's inequality; operator rederivations `eq:condcgf`.
atlas: matrix-freedman (partial) -/
theorem ae_condExp_matrixExp_one_le_and_condExp_sq_posSemidef_and_matrixLog_le
    [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    {X : Ω → Matrix n n ℂ} (hX : Integrable X μ)
    (hX2 : Integrable (fun ω => X ω ^ 2) μ) (hHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    (hMean : μ[X | m] =ᵐ[μ] 0) {L θ : ℝ} (hθ : 0 < θ) (hθL : θ * L < 3)
    (hBound : ∀ᵐ ω ∂μ, X ω ≤ algebraMap ℝ (Matrix n n ℂ) L) :
    ∀ᵐ ω ∂μ,
      (1 : Matrix n n ℂ) ≤ μ[(fun ω => matrixExp (θ • X ω)) | m] ω ∧
      (μ[(fun ω => X ω ^ 2) | m] ω).PosSemidef ∧
      matrixLog (μ[(fun ω => matrixExp (θ • X ω)) | m] ω) ≤
        ((θ ^ 2 / 2) / (1 - θ * L / 3)) • μ[(fun ω => X ω ^ 2) | m] ω := by
  let g : ℝ := (θ ^ 2 / 2) / (1 - θ * L / 3)
  let M : Ω → Matrix n n ℂ := μ[(fun ω => matrixExp (θ • X ω)) | m]
  let V : Ω → Matrix n n ℂ := μ[(fun ω => X ω ^ 2) | m]
  have hExp := integrable_matrixExp_smul_of_ae_le_algebraMap hX.1 hHerm hθ.le hBound
  have hXθ : Integrable (fun ω => θ • X ω) μ := hX.smul θ
  have hX2g : Integrable (fun ω => g • X ω ^ 2) μ := hX2.smul g
  have hlin : Integrable (fun ω => (1 : Matrix n n ℂ) + θ • X ω) μ :=
    (integrable_const 1).add hXθ
  have hquad : Integrable (fun ω => (1 : Matrix n n ℂ) + θ • X ω + g • X ω ^ 2) μ :=
    hlin.add hX2g
  have hCElin : μ[(fun ω => (1 : Matrix n n ℂ) + θ • X ω) | m] =ᵐ[μ] fun _ => (1 : Matrix n n ℂ) := by
    filter_upwards [condExp_add (integrable_const (1 : Matrix n n ℂ)) hXθ m,
      condExp_smul θ X m, hMean] with ω ha hs hzero
    change μ[(fun ω => (1 : Matrix n n ℂ) + θ • X ω) | m] ω = _ at ha
    change μ[(fun ω => θ • X ω) | m] ω = θ • μ[X | m] ω at hs
    change μ[X | m] ω = 0 at hzero
    rw [ha, condExp_const hm 1]
    change 1 + μ[(fun ω => θ • X ω) | m] ω = 1
    rw [hs, hzero, smul_zero, add_zero]
  have hCEquad : μ[(fun ω => (1 : Matrix n n ℂ) + θ • X ω + g • X ω ^ 2) | m] =ᵐ[μ]
      fun ω => 1 + g • V ω := by
    filter_upwards [condExp_add hlin hX2g m, condExp_smul g (fun ω => X ω ^ 2) m, hCElin]
      with ω ha hs hl
    change μ[(fun ω => (1 : Matrix n n ℂ) + θ • X ω + g • X ω ^ 2) | m] ω = _ at ha
    change μ[(fun ω => g • X ω ^ 2) | m] ω = g • V ω at hs
    change μ[(fun ω => (1 : Matrix n n ℂ) + θ • X ω) | m] ω = 1 at hl
    rw [ha]
    change μ[(fun ω => (1 : Matrix n n ℂ) + θ • X ω) | m] ω +
      μ[(fun ω => g • X ω ^ 2) | m] ω = 1 + g • V ω
    rw [hl, hs]
  have htangent : (fun ω => (1 : Matrix n n ℂ) + θ • X ω) ≤ᵐ[μ]
      fun ω => matrixExp (θ • X ω) := by
    filter_upwards [hHerm] with ω hω
    exact one_add_le_matrixExp_of_isHermitian _
      (hω.smul (isSelfAdjoint_iff.mpr (star_trivial θ)))
  have hlinear := ae_condExp_le_condExp_of_ae_le hm hlin hExp htangent
  have hpolynomial : (fun ω => matrixExp (θ • X ω)) ≤ᵐ[μ]
      fun ω => (1 : Matrix n n ℂ) + θ • X ω + g • X ω ^ 2 := by
    filter_upwards [hHerm, hBound] with ω hω hB
    exact matrixExp_smul_le_one_add_smul_add_smul_sq_of_spectrum_le _ hω
      (fun x hx => exp_mul_le_one_add_mul_add_sq_mul_of_le hθ hθL
        ((le_algebraMap_iff_spectrum_le hω).mp hB x hx))
  have hupper := ae_condExp_le_condExp_of_ae_le hm hExp hquad hpolynomial
  have hV := ae_posSemidef_condExp_of_ae_posSemidef hm hX2 (hHerm.mono fun ω hω => by
    have heq : X ω ^ 2 = (X ω)ᴴ * X ω := by rw [hω.eq, sq]
    rw [heq]
    exact Matrix.posSemidef_conjTranspose_mul_self _)
  filter_upwards [hlinear, hupper, hCElin, hCEquad, hV] with ω hl hu hcl hcu hv
  change μ[(fun ω => (1 : Matrix n n ℂ) + θ • X ω) | m] ω ≤ M ω at hl
  change M ω ≤ μ[(fun ω => (1 : Matrix n n ℂ) + θ • X ω + g • X ω ^ 2) | m] ω at hu
  rw [hcl] at hl
  rw [hcu] at hu
  refine ⟨hl, hv, ?_⟩
  have hMpd : (M ω).PosDef := by
    have hp := (Matrix.PosDef.one : (1 : Matrix n n ℂ).PosDef).add_posSemidef (Matrix.le_iff.mp hl)
    have heq : 1 + (M ω - 1) = M ω := by abel
    rw [heq] at hp
    exact hp
  have hgv : (g • V ω).IsHermitian := hv.isHermitian.smul
    (isSelfAdjoint_iff.mpr (star_trivial g))
  have hexp := posDef_matrixExp_and_matrixLog_matrixExp_finite (g • V ω) hgv
  have hu' : M ω ≤ matrixExp (g • V ω) :=
    hu.trans (one_add_le_matrixExp_of_isHermitian _ hgv)
  have hlog := CFC.log_monotoneOn hMpd.isStrictlyPositive hexp.1.isStrictlyPositive hu'
  change matrixLog (M ω) ≤ matrixLog (matrixExp (g • V ω)) at hlog
  rw [hexp.2] at hlog
  exact hlog

end NLAlib
