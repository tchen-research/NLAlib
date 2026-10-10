/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu

Ported from HighDimProb commit c0cb8d9e0ff2c3408c92681eb8bf0232e4673bae,
HighDimProb/Concentration/HansonWright.lean, to Lean 4.33.1.
The original Apache-2.0 copyright notice is retained. Only the two used legacy
vocabulary definitions are supplied locally; there is no HighDimProb dependency.
-/
import NLAlib.Concentration.HansonWright.UniversalBound
import NLAlib.Concentration.OrliczMGF
import NLAlib.Matrix.QuadForm
import NLAlib.Matrix.Norms
import NLAlib.Matrix.FiniteIndexTransport

/-!
# Hanson–Wright in NLAlib's matrix vocabulary

The complete independent-coordinate MGF proof is split into focused leaves.
This module transports it to `quadForm`, `frobNorm`, and `specNorm`, relabels an arbitrary
finite index type `ι` through `Fintype.equivFin ι` (the leaf proof is over `Fin n`), then
uses the proved Orlicz-to-MGF bridge for the centered ψ₂ formulation.
Atlas: `hanson-wright`. Vershynin 2018, Theorem 6.2.1.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal Matrix.Norms.L2Operator

noncomputable section
set_option autoImplicit false

namespace NLAlib

private theorem hw_quadraticForm_eq_quadForm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    HansonWrightProof.matrixQuadraticForm A x = quadForm A x := by
  rw [quadForm_eq_sum]
  unfold HansonWrightProof.matrixQuadraticForm
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem hw_frobeniusNorm_eq_frobNorm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    HansonWrightProof.deterministicFrobeniusNorm A = frobNorm A := by
  unfold HansonWrightProof.deterministicFrobeniusNorm HansonWrightProof.frobeniusNormSq frobNorm
  rw [frobSq_eq_sum_sq]

private theorem hw_centeredQuadraticForm_eq {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (μ : Measure Ω) (A : Matrix (Fin n) (Fin n) ℝ) (X : Fin n → Ω → ℝ) :
    HansonWrightProof.centeredQuadraticForm μ A X =
      (fun ω => quadForm A (fun i => X i ω) -
        ∫ ω', quadForm A (fun i => X i ω') ∂μ) := by
  funext ω
  unfold HansonWrightProof.centeredQuadraticForm HansonWrightProof.randomQuadraticForm
  simp_rw [hw_quadraticForm_eq_quadForm]

private theorem hanson_wright_mgf_fin {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (X : Fin n → Ω → ℝ) (K : ℝ) (hK : 0 < K)
    (hind : iIndepFun X μ)
    (hmgf : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ)
    (t : ℝ) (ht : 0 ≤ t) :
    (μ {ω | t ≤ |quadForm A (fun i => X i ω) -
      ∫ ω', quadForm A (fun i => X i ω') ∂μ|}).toReal ≤
      2 * exp (-(1 / (256 * exp 1 ^ 2)) *
        min (t ^ 2 / (K ^ 4 * frobNorm A ^ 2)) (t / (K ^ 2 * specNorm A))) := by
  have h := HansonWrightProof.hanson_wright_inequality_hdp_explicit_constant
    (A := A) (X := X) hK hind hmgf t ht
  rw [hw_centeredQuadraticForm_eq, hw_frobeniusNorm_eq_frobNorm] at h
  change (μ {ω | t ≤ |quadForm A (fun i => X i ω) -
    ∫ ω', quadForm A (fun i => X i ω') ∂μ|}).toReal ≤
    2 * exp (-HansonWrightProof.hansonWrightUniversalConstant *
      min (t ^ 2 / (K ^ 4 * frobNorm A ^ 2)) (t / (K ^ 2 * specNorm A))) at h
  simpa only [HansonWrightProof.hansonWrightUniversalConstant,
    show (4 : ℝ) * (64 * exp 1 ^ 2) = 256 * exp 1 ^ 2 by ring] using h

/-- Relabelling the coordinates by an equivalence does not change the quadratic form.
Atlas `hanson-wright` (index transport). -/
theorem quadForm_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι ι ℝ) (e : ι ≃ κ)
    (z : ι → ℝ) : quadForm (A.reindex e e) (fun k => z (e.symm k)) = quadForm A z := by
  rw [quadForm_eq_sum, quadForm_eq_sum]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [e.symm.sum_comp (fun i => ∑ k, A i (e.symm k) * (z i * z (e.symm k)))]
  exact Finset.sum_congr rfl fun i _ =>
    e.symm.sum_comp (fun j => A i j * (z i * z j))

/-- **Hanson–Wright, MGF form.** Independent coordinates with sub-Gaussian
variance proxy `K²` satisfy the quadratic-form tail bound with the explicit
constant `1/(256 exp(1)²)`. The matrix is arbitrary, and zero matrix/dimension
cases use Lean's total real division convention. The MGF assumption also implies
coordinate centering; no quadratic-form MGF certificate is assumed.
Vershynin 2018, Theorem 6.2.1; atlas `hanson-wright`. Deviation: none in the statement;
the index type is an arbitrary `[Fintype ι]` (the ported leaf proof is over `Fin n` and is
transported through `Fintype.equivFin ι`).
Ported from HighDimProb commit c0cb8d9e0ff2c3408c92681eb8bf0232e4673bae.
atlas: hanson-wright -/
theorem hanson_wright_mgf {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (X : ι → Ω → ℝ) (K : ℝ) (hK : 0 < K)
    (hind : iIndepFun X μ)
    (hmgf : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ)
    (t : ℝ) (ht : 0 ≤ t) :
    (μ {ω | t ≤ |quadForm A (fun i => X i ω) -
      ∫ ω', quadForm A (fun i => X i ω') ∂μ|}).toReal ≤
      2 * exp (-(1 / (256 * exp 1 ^ 2)) *
        min (t ^ 2 / (K ^ 4 * frobNorm A ^ 2)) (t / (K ^ 2 * specNorm A))) := by
  let e := Fintype.equivFin ι
  have h := hanson_wright_mgf_fin (A.reindex e e) (fun k => X (e.symm k)) K hK
    (hind.precomp e.symm.injective) (fun k => hmgf (e.symm k)) t ht
  have hq : ∀ ω, quadForm (A.reindex e e) (fun k => X (e.symm k) ω) =
      quadForm A (fun i => X i ω) := fun ω => quadForm_reindex A e (fun i => X i ω)
  simp only [hq, frobNorm_reindex, specNorm_reindex] at h
  exact h

/-- **Hanson–Wright, exponential-square/ψ₂ form.** Independent centered
coordinates with nonnegative expectations `E exp((Xᵢ/K)²) ≤ 2` satisfy the
quadratic-form tail bound with explicit constant `1/(20736 exp(1)²)`.
The already-proved Orlicz-to-MGF bridge gives variance proxy `9K²`; the bound
therefore uses the common original ψ₂ scale with a conservative constant.
Vershynin 2018, Theorem 6.2.1; atlas `hanson-wright`. Deviation: the constant
`1/(20736 e²)` is explicit (Vershynin's `c` is unspecified); the index type is an arbitrary
`[Fintype ι]`.
atlas: hanson-wright -/
theorem hanson_wright_of_lintegral_exp_sq_le_two {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (X : ι → Ω → ℝ) (K : ℝ) (hK : 0 < K)
    (hind : iIndepFun X μ) (hX : ∀ i, AEMeasurable (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hpsi : ∀ i, ∫⁻ ω, ENNReal.ofReal (exp ((X i ω / K) ^ 2)) ∂μ ≤ 2)
    (t : ℝ) (ht : 0 ≤ t) :
    (μ {ω | t ≤ |quadForm A (fun i => X i ω) -
      ∫ ω', quadForm A (fun i => X i ω') ∂μ|}).toReal ≤
      2 * exp (-(1 / (20736 * exp 1 ^ 2)) *
        min (t ^ 2 / (K ^ 4 * frobNorm A ^ 2)) (t / (K ^ 2 * specNorm A))) := by
  have hmgf : ∀ i, HasSubgaussianMGF (X i) ⟨(3 * K) ^ 2, sq_nonneg (3 * K)⟩ μ := by
    intro i
    have hp : (⟨9 * K ^ 2, by positivity⟩ : ℝ≥0) =
        ⟨(3 * K) ^ 2, sq_nonneg (3 * K)⟩ := by
      ext
      ring
    rw [← hp]
    exact hasSubgaussianMGF_of_lintegral_exp_sq_le_two (hX i) K hK (hmean i) (hpsi i)
  have h := hanson_wright_mgf A X (3 * K) (by positivity) hind hmgf t ht
  let u := t ^ 2 / (K ^ 4 * frobNorm A ^ 2)
  let v := t / (K ^ 2 * specNorm A)
  let c : ℝ := 1 / (256 * exp 1 ^ 2)
  have hv : 0 ≤ v := div_nonneg ht
    (mul_nonneg (sq_nonneg K) (specNorm_nonneg A))
  have hquad : t ^ 2 / ((3 * K) ^ 4 * frobNorm A ^ 2) = u / 81 := by
    dsimp [u]
    rw [div_div]
    congr 1
    ring
  have hlinear : t / ((3 * K) ^ 2 * specNorm A) = v / 9 := by
    dsimp [v]
    rw [div_div]
    congr 1
    ring
  rw [hquad, hlinear] at h
  have hmin : (1 / 81 : ℝ) * min u v ≤ min (u / 81) (v / 9) := by
    apply le_min
    · nlinarith [min_le_left u v]
    · nlinarith [min_le_right u v]
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hscale : c / 81 = 1 / (20736 * exp 1 ^ 2) := by
    dsimp [c]
    rw [div_div]
    congr 1
    ring
  have hexp : exp (-c * min (u / 81) (v / 9)) ≤
      exp (-(1 / (20736 * exp 1 ^ 2)) * min u v) := by
    apply exp_le_exp.mpr
    rw [← hscale]
    nlinarith [mul_le_mul_of_nonneg_left hmin hc]
  exact h.trans (mul_le_mul_of_nonneg_left hexp (by norm_num))

end NLAlib
