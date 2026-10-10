import NLAlib.Concentration.HansonWright

/-!
# Concentration of squared sub-Gaussian projections

The identity-matrix specialization of Hanson–Wright, with its expectation,
Frobenius norm and spectral norm evaluated explicitly. This is the reusable
probabilistic input for sub-Gaussian JL and independent isotropic row bounds.

Source: `open_problems_operator_rederivations.tex`, Lemma `pg:squares`;
Vershynin 2018, Theorem 6.2.1. Supports atlas `jl-subgaussian` and
`subgaussian-matrix-norm`.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

/-- **Squared projection concentration.** Independent random variables with MGF
proxy `K²` and unit second moments satisfy the explicit Hanson–Wright tail for
`|∑ Yᵢ² - card ι|`. Integrability follows from the MGF assumptions. The family
is nonempty so the identity matrix has spectral norm one.

Source: operator re-derivation Lemma `pg:squares`, specializing the proved
`hanson_wright_mgf`; supports atlas `jl-subgaussian` and
`subgaussian-matrix-norm`. -/
theorem measure_le_abs_sum_sq_sub_card_of_hasSubgaussianMGF
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Y : ι → Ω → ℝ) (K : ℝ) (hK : 0 < K) (hind : iIndepFun Y μ)
    (hmgf : ∀ i, HasSubgaussianMGF (Y i) ⟨K ^ 2, sq_nonneg K⟩ μ)
    (hsq : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ = 1) {u : ℝ} (hu : 0 ≤ u) :
    (μ {ω | u ≤ |∑ i, Y i ω ^ 2 - (Fintype.card ι : ℝ)|}).toReal ≤
      2 * Real.exp (-(1 / (256 * Real.exp 1 ^ 2)) *
        min (u ^ 2 / ((Fintype.card ι : ℝ) * K ^ 4)) (u / K ^ 2)) := by
  have hquad (y : ι → ℝ) : quadForm (1 : Matrix ι ι ℝ) y = ∑ i, y i ^ 2 := by
    simp [quadForm, dotProduct, pow_two]
  have hmean : ∫ ω, quadForm (1 : Matrix ι ι ℝ) (fun i => Y i ω) ∂μ =
      (Fintype.card ι : ℝ) := by
    simp_rw [hquad]
    rw [integral_finsetSum _ fun i _ => (hmgf i).memLp 2 |>.integrable_sq]
    simp [hsq]
  have hF : frobNorm (1 : Matrix ι ι ℝ) ^ 2 = (Fintype.card ι : ℝ) := by
    rw [frobNorm_sq]
    simp [frobSq, frobInner, Matrix.one_apply]
  have hS : specNorm (1 : Matrix ι ι ℝ) = 1 := by
    rw [specNorm_eq_norm, ← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp
  have h := hanson_wright_mgf (1 : Matrix ι ι ℝ) Y K hK hind hmgf u hu
  rw [hmean] at h
  simpa only [hquad, hF, hS, mul_one, mul_comm (K ^ 4)] using h

end NLAlib
