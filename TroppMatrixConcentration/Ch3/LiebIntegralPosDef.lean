import TroppMatrixConcentration.Defs.Probability
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Expectation of an almost surely positive-definite matrix

Lean name: `TroppMatrixConcentration.ch3_lieb_integral_posDef`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015), https://arxiv.org/abs/1501.01571v1; Auxiliary positive-definite integration fact used in Corollary 3.4.2, printed p. 35; quadratic-form definition (2.1.10), printed p. 20.
-/
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open TroppMatrixConcentration
set_option autoImplicit false

theorem TroppMatrixConcentration.ch3_lieb_integral_posDef {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (Z : Ω → Matrix (Fin d) (Fin d) ℂ)
    (hInt : Integrable Z μ) (hPD : ∀ᵐ ω ∂μ, (Z ω).PosDef) :
    (∫ ω, Z ω ∂μ).PosDef := by
  have hNonneg : ∀ᵐ ω ∂μ, (0 : Matrix (Fin d) (Fin d) ℂ) ≤ Z ω := by
    filter_upwards [hPD] with ω hω
    exact hω.posSemidef.nonneg
  have hMeanHerm : (∫ ω, Z ω ∂μ).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (integral_nonneg_of_ae hNonneg)).isHermitian
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hMeanHerm
  intro v hv
  let L : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun A => star v ⬝ᵥ (A *ᵥ v)
      map_add' := by intros; simp [Matrix.add_mulVec, dotProduct_add]
      map_smul' := by intros; simp [Matrix.smul_mulVec, dotProduct_smul] }
  let T := L.toContinuousLinearMap
  have htInt : Integrable (fun ω => T (Z ω)) μ := T.integrable_comp hInt
  have hreInt := Complex.reCLM.integrable_comp htInt
  have htpos : ∀ᵐ ω ∂μ, 0 < T (Z ω) := by
    filter_upwards [hPD] with ω hω
    exact hω.dotProduct_mulVec_pos hv
  have hrePos : ∀ᵐ ω ∂μ, 0 < (T (Z ω)).re := by
    filter_upwards [htpos] with ω hω
    exact (Complex.pos_iff.1 hω).1
  have himZero : ∀ᵐ ω ∂μ, (T (Z ω)).im = 0 := by
    filter_upwards [htpos] with ω hω
    exact (Complex.pos_iff.1 hω).2.symm
  have hposInt : 0 < ∫ ω, (T (Z ω)).re ∂μ := by
    apply (integral_pos_iff_support_of_nonneg_ae (hrePos.mono (fun _ h => h.le)) hreInt).2
    have hs : Function.support (fun ω => (T (Z ω)).re) =ᵐ[μ] (Set.univ : Set Ω) := by
      filter_upwards [hrePos] with ω hω
      apply propext
      change (T (Z ω)).re ≠ 0 ↔ True
      exact iff_true_intro hω.ne'
    rw [measure_congr hs]
    simp
  change 0 < T (∫ ω, Z ω ∂μ)
  rw [← T.integral_comp_comm hInt, Complex.pos_iff]
  constructor
  · change 0 < Complex.reCLM (∫ x, T (Z x) ∂μ)
    rw [← Complex.reCLM.integral_comp_comm htInt]
    exact hposInt
  · change 0 = Complex.imCLM (∫ x, T (Z x) ∂μ)
    rw [← Complex.imCLM.integral_comp_comm htInt]
    change 0 = ∫ x, (T (Z x)).im ∂μ
    rw [integral_congr_ae himZero, integral_zero]
