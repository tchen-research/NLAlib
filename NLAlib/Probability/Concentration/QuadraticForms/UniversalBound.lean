/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu

Ported from HighDimProb commit c0cb8d9e0ff2c3408c92681eb8bf0232e4673bae,
HighDimProb/Concentration/HansonWright.lean, to Lean 4.33.1.
The original Apache-2.0 copyright notice is retained. The proof is stated in NLAlib's matrix
vocabulary (`quadForm`, `frobSq`, `frobNorm`, `specNorm`); there is no HighDimProb dependency.
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import NLAlib.Probability.Concentration.QuadraticForms.TailAssembly
/-!
# Hanson–Wright proof: UniversalBound

A focused leaf of the transported independent-coordinate proof.
Its declarations live in namespace `NLAlib` (generic scalar sub-Gaussian facts are in
`NLAlib.Probability.SubGaussian.*`); the public bounds are in `NLAlib.Probability.Concentration.QuadraticForms.HansonWright`.
Atlas: `hanson-wright`. Source: HighDimProb commit c0cb8d9e0ff2c3408c92681eb8bf0232e4673bae.
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal Matrix.Norms.L2Operator

noncomputable section
set_option maxRecDepth 5000

namespace NLAlib

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Hanson-Wright tail bound with the MGF certificate proved from sub-Gaussian coordinates.

This theorem does not take `HasHansonWrightMGF` as a hypothesis.  Instead it proves
that certificate from independence and coordinate sub-Gaussian MGF bounds, then
optimizes the resulting Chernoff bound. -/
theorem hanson_wright_inequality {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {X : Fin n → Ω → ℝ}
    {K C t : ℝ} (hK : 0 < K) (hC : 0 < C)
    (hC_domain : 4 * exp 1 ≤ C)
    (hC_diag_quad : 8 * exp 1 ^ 3 ≤ C)
    (hC_offdiag_domain : 16 * exp 1 ≤ C ^ 2)
    (hC_offdiag_quad : 64 * exp 1 ^ 2 ≤ C)
    (hF : 0 < frobNorm A) (hOp : 0 < specNorm A)
    (h_indep : iIndepFun X μ)
    (hX_subG : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ)
    (ht : 0 ≤ t) :
    (μ {ω | t ≤ |centeredQuadraticForm μ A X ω|}).toReal ≤
      2 * exp (-(1 / (4 * C)) *
        min (t ^ 2 / (K ^ 4 * frobNorm A ^ 2))
          (t / (K ^ 2 * specNorm A))) := by
  have hHW : HasHansonWrightMGF μ A X K C :=
    hasHansonWrightMGF_of_subgaussian hK hC hC_domain hC_diag_quad
      hC_offdiag_domain hC_offdiag_quad hOp h_indep hX_subG
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

end NLAlib
