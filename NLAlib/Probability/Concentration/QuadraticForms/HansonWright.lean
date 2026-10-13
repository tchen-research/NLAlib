/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu

Ported from HighDimProb (Y. Zhang, J. D. Lee, F. Liu; Apache-2.0),
HighDimProb/Concentration/HansonWright.lean, to Lean 4.33.1.
The original Apache-2.0 copyright notice is retained. The proof is stated in NLAlib's matrix
vocabulary (`quadForm`, `frobSq`, `frobNorm`, `specNorm`); there is no HighDimProb dependency.
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import NLAlib.Probability.Concentration.QuadraticForms.TailAssembly
import NLAlib.Probability.SubGaussian.OrliczMGF
import NLAlib.Matrix.Basic.QuadForm
import NLAlib.Matrix.Spectral.EckartYoung
import NLAlib.Matrix.Norms.RankNorm
import NLAlib.Matrix.Norms.Reindex
import NLAlib.Matrix.Subspaces.OrthogonalProducts
/-!
# Hanson–Wright in NLAlib's matrix vocabulary

The complete independent-coordinate MGF proof is split into focused leaves
(`Centering`, `Decoupling`, `DiagonalCGF`, `CutAverages`, `Geometry`, `LinearFormComparison`,
`VectorProductComparison`, `TailAssembly`). This module fixes the universal constant
`1/(256 e²)` (the private `Fin n` leaves), relabels an arbitrary finite index type `ι` through
`Fintype.equivFin ι`, then uses the Orlicz-to-MGF bridge for the centered ψ₂ formulation.
Atlas: `hanson-wright`. Vershynin 2018, Theorem 6.2.1; Rudelson–Vershynin 2013.
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

noncomputable section
set_option maxRecDepth 5000

namespace NLAlib

/-- Hanson–Wright tail with a general constant `C` satisfying the four leaf conditions, for a
matrix with nonzero Frobenius and spectral norms: the MGF certificate `HasHansonWrightMGF` is
proved from independence and coordinate sub-Gaussian bounds, then the Chernoff bound is
optimised. -/
private theorem hanson_wright_of_constants {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {X : Fin n → Ω → ℝ}
    {K C t : ℝ} (hK : 0 < K) (hC : 0 < C)
    (hC_domain : 4 * exp 1 ≤ C)
    (hC_diag_quad : 8 * exp 1 ^ 3 ≤ C)
    (hC_offdiag_domain : 16 * exp 1 ≤ C ^ 2)
    (hC_offdiag_quad : 64 * exp 1 ^ 2 ≤ C)
    (hF : 0 < frobNorm A) (hOp : 0 < specNorm A)
    (hind : iIndepFun X μ)
    (hmgf : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |centeredQuadraticForm μ A X ω|} ≤
      2 * exp (-(1 / (4 * C)) *
        min (t ^ 2 / (K ^ 4 * frobNorm A ^ 2))
          (t / (K ^ 2 * specNorm A))) := by
  have hHW : HasHansonWrightMGF μ A X K C :=
    hasHansonWrightMGF_of_subgaussian hK hC hC_domain hC_diag_quad
      hC_offdiag_domain hC_offdiag_quad hOp hind hmgf
  have hv : 0 < K ^ 4 * frobNorm A ^ 2 := by positivity
  have hb : 0 < K ^ 2 * specNorm A := by positivity
  exact measureReal_abs_ge_le_two_mul_exp_of_cgf_le hC hv hb
    (Y := centeredQuadraticForm μ A X)
    (fun l hl => by
      have hl' : |l| ≤ (2 * C * K ^ 2 * specNorm A)⁻¹ := by
        convert hl using 2
        ring
      simpa [mul_assoc, mul_left_comm, mul_comm] using hHW.1 l hl')
    (fun l hl => by
      have hl' : |l| ≤ (2 * C * K ^ 2 * specNorm A)⁻¹ := by
        convert hl using 2
        ring
      exact hHW.2 l hl') ht

/-- The `Fin n` leaf of `hanson_wright_mgf`, with the constant `1/(4 · 64 e²)`. -/
private theorem hanson_wright_mgf_fin {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {X : Fin n → Ω → ℝ} {K : ℝ} (hK : 0 < K)
    (hind : iIndepFun X μ)
    (hmgf : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ) (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |centeredQuadraticForm μ A X ω|} ≤
      2 * exp (-(1 / (4 * (64 * exp 1 ^ 2))) *
        min (t ^ 2 / (K ^ 4 * frobNorm A ^ 2)) (t / (K ^ 2 * specNorm A))) := by
  let C0 : ℝ := 64 * exp 1 ^ 2
  have hexp_pos : 0 < exp 1 := exp_pos 1
  have hexp_ge_one : 1 ≤ exp 1 := one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
  have hexp_le_eight : exp 1 ≤ 8 := by
    nlinarith [exp_one_lt_three.le]
  have hC0_pos : 0 < C0 := by
    dsimp [C0]
    positivity
  have hC0_domain : 4 * exp 1 ≤ C0 := by
    dsimp [C0]
    have hmul := mul_le_mul_of_nonneg_left hexp_ge_one
      (by positivity : 0 ≤ 4 * exp 1)
    nlinarith
  have hC0_diag_quad : 8 * exp 1 ^ 3 ≤ C0 := by
    dsimp [C0]
    have hmul := mul_le_mul_of_nonneg_left hexp_le_eight
      (by positivity : 0 ≤ 8 * exp 1 ^ 2)
    nlinarith
  have hC0_ge_offdiag : 16 * exp 1 ≤ C0 := by
    dsimp [C0]
    have hmul := mul_le_mul_of_nonneg_left hexp_ge_one
      (by positivity : 0 ≤ 16 * exp 1)
    nlinarith
  have hC0_ge_one : 1 ≤ C0 := by
    dsimp [C0]
    nlinarith [hexp_ge_one, sq_nonneg (exp 1)]
  have hC0_sq_ge : C0 ≤ C0 ^ 2 := by
    have hC0_nonneg : 0 ≤ C0 := hC0_pos.le
    have hmul := mul_le_mul hC0_ge_one (le_refl C0) hC0_nonneg hC0_nonneg
    simpa [pow_two] using hmul
  have hC0_offdiag_domain : 16 * exp 1 ≤ C0 ^ 2 :=
    hC0_ge_offdiag.trans hC0_sq_ge
  have hC0_offdiag_quad : 64 * exp 1 ^ 2 ≤ C0 := by
    dsimp [C0]
    rfl
  change μ.real {ω | t ≤ |centeredQuadraticForm μ A X ω|} ≤
    2 * exp (-(1 / (4 * C0)) *
      min (t ^ 2 / (K ^ 4 * frobNorm A ^ 2))
        (t / (K ^ 2 * specNorm A)))
  by_cases hF : 0 < frobNorm A
  · by_cases hOp : 0 < specNorm A
    · exact
        hanson_wright_of_constants (μ := μ) (A := A) (X := X)
          (K := K) (C := C0) (t := t) hK hC0_pos hC0_domain
          hC0_diag_quad hC0_offdiag_domain hC0_offdiag_quad hF hOp
          hind hmgf ht
    · have hOp_nonneg : 0 ≤ specNorm A := specNorm_nonneg A
      have hOp_zero : specNorm A = 0 := le_antisymm (le_of_not_gt hOp) hOp_nonneg
      have hfirst_nonneg :
          0 ≤ t ^ 2 / (K ^ 4 * frobNorm A ^ 2) := by positivity
      have hsecond_zero : t / (K ^ 2 * specNorm A) = 0 := by
        rw [hOp_zero, mul_zero, div_zero]
      have hmin :
          min (t ^ 2 / (K ^ 4 * frobNorm A ^ 2))
              (t / (K ^ 2 * specNorm A)) = 0 := by
        rw [hsecond_zero, min_eq_right hfirst_nonneg]
      calc
        μ.real {ω | t ≤ |centeredQuadraticForm μ A X ω|} ≤ (1 : ℝ) := measureReal_le_one
        _ ≤ 2 * exp (-(1 / (4 * C0)) *
            min (t ^ 2 / (K ^ 4 * frobNorm A ^ 2))
              (t / (K ^ 2 * specNorm A))) := by
            rw [hmin]
            norm_num
  · have hF_nonneg : 0 ≤ frobNorm A := frobNorm_nonneg A
    have hF_zero : frobNorm A = 0 := le_antisymm (le_of_not_gt hF) hF_nonneg
    have hOp_nonneg : 0 ≤ specNorm A := specNorm_nonneg A
    have hfirst_zero :
        t ^ 2 / (K ^ 4 * frobNorm A ^ 2) = 0 := by
      rw [hF_zero]
      simp
    have hsecond_nonneg : 0 ≤ t / (K ^ 2 * specNorm A) :=
      div_nonneg ht (mul_nonneg (sq_nonneg K) hOp_nonneg)
    have hmin :
        min (t ^ 2 / (K ^ 4 * frobNorm A ^ 2))
            (t / (K ^ 2 * specNorm A)) = 0 := by
      rw [hfirst_zero, min_eq_left hsecond_nonneg]
    calc
      μ.real {ω | t ≤ |centeredQuadraticForm μ A X ω|} ≤ (1 : ℝ) := measureReal_le_one
      _ ≤ 2 * exp (-(1 / (4 * C0)) *
          min (t ^ 2 / (K ^ 4 * frobNorm A ^ 2))
            (t / (K ^ 2 * specNorm A))) := by
          rw [hmin]
          norm_num

/-- **Hanson–Wright, MGF form.** Independent coordinates with sub-Gaussian
variance proxy `K²` satisfy the quadratic-form tail bound with the explicit
constant `1/(256 exp(1)²)`. The matrix is arbitrary, and zero matrix/dimension
cases use Lean's total real division convention. The MGF assumption also implies
coordinate centering; no quadratic-form MGF certificate is assumed.
Vershynin 2018, Theorem 6.2.1; Rudelson–Vershynin 2013, Theorem 1.1; atlas `hanson-wright`.
Deviation: the constant `1/(256 e²)` is explicit (the sources' `c` is unspecified); the index
type is an arbitrary `[Fintype ι]` (the leaf proof is over `Fin n` and is transported through
`Fintype.equivFin ι`). Ported from HighDimProb (Zhang–Lee–Liu, Apache-2.0).
atlas: hanson-wright -/
theorem hanson_wright_mgf {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (X : ι → Ω → ℝ) (K : ℝ) (hK : 0 < K)
    (hind : iIndepFun X μ)
    (hmgf : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ)
    (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |quadForm A (fun i => X i ω) -
      ∫ ω', quadForm A (fun i => X i ω') ∂μ|} ≤
      2 * exp (-(1 / (256 * exp 1 ^ 2)) *
        min (t ^ 2 / (K ^ 4 * frobNorm A ^ 2)) (t / (K ^ 2 * specNorm A))) := by
  let e := Fintype.equivFin ι
  have h := hanson_wright_mgf_fin (A := A.reindex e e) (X := fun k => X (e.symm k)) hK
    (hind.precomp e.symm.injective) (fun k => hmgf (e.symm k)) t ht
  rw [show (4 : ℝ) * (64 * exp 1 ^ 2) = 256 * exp 1 ^ 2 by ring] at h
  have hq : ∀ ω, quadForm (A.reindex e e) (fun k => X (e.symm k) ω) =
      quadForm A (fun i => X i ω) := fun ω => quadForm_reindex A e (fun i => X i ω)
  simp only [centeredQuadraticForm, randomQuadraticForm, hq, frobNorm_reindex,
    specNorm_reindex] at h
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
    μ.real {ω | t ≤ |quadForm A (fun i => X i ω) -
      ∫ ω', quadForm A (fun i => X i ω') ∂μ|} ≤
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
