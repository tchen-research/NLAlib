/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.RandomMatrix.Gaussian.Basic.SandwichDeviation
import NLAlib.RandomMatrix.Gaussian.InverseMoments.DeviationInputs
import NLAlib.Matrix.Measurability.GramPseudoinverse
import NLAlib.Matrix.Measurability.SpectralMeasurable
import NLAlib.ForMathlib.Probability.FiniteProductEvents
import NLAlib.RandomMatrix.Gaussian.Invariance.Invariance

/-!
# One-sided deviations after conditioning on Gaussian head blocks

The two inverse bad events cost `2 t⁻ᵖ`; one-sided concentration of the independent tail
block costs `exp (-u²/2)`. The statements concern separate Frobenius and spectral events.
Source: HMT (2011), proofs of Theorems 10.7–10.8, with the sharpened native inverse-Frobenius
tail; supports atlas `rsvd-tail`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

private theorem gaussianMatrix_prod_sandwich_deviation {a q r p : ℕ} (hp : 4 ≤ p)
    (S : Matrix (Fin a) (Fin q) ℝ) (N : Matrix (Fin a) (Fin r) ℝ → ℝ)
    (hNm : Measurable N) {cF cS t u : ℝ} (hcF : 0 ≤ cF) (hcS : 0 ≤ cS)
    (ht : 1 ≤ t) (hu : 0 ≤ u)
    (hconc : ∀ D : Matrix (Fin (r + p)) (Fin r) ℝ,
      (gaussianMatrix (Fin q) (Fin (r + p))).real
        {H | cF * frobNorm D + cS * specNorm D + u * (specNorm S * specNorm D) <
          N (S * H * D)} ≤ Real.exp (-u ^ 2 / 2)) :
    ((gaussianMatrix (Fin r) (Fin (r + p))).prod
      (gaussianMatrix (Fin q) (Fin (r + p)))).real
      {z | cF * (t * Real.sqrt (12 * (r : ℝ) / p)) +
          cS * (t * (Real.exp 1 * Real.sqrt (r + p) / ((p : ℝ) + 1))) +
          u * (specNorm S * (t * (Real.exp 1 * Real.sqrt (r + p) / ((p : ℝ) + 1)))) <
        N (S * z.2 * pinvR z.1)} ≤ 2 * t ^ (-(p : ℝ)) + Real.exp (-u ^ 2 / 2) := by
  let A : ℝ := t * Real.sqrt (12 * (r : ℝ) / p)
  let B : ℝ := t * (Real.exp 1 * Real.sqrt (r + p) / ((p : ℝ) + 1))
  let E := {G : Matrix (Fin r) (Fin (r + p)) ℝ |
    A < frobNorm (pinvR G) ∨ B < specNorm (pinvR G)}
  let F := {z : Matrix (Fin r) (Fin (r + p)) ℝ × Matrix (Fin q) (Fin (r + p)) ℝ |
    cF * A + cS * B + u * (specNorm S * B) < N (S * z.2 * pinvR z.1)}
  have hFm : MeasurableSet F := measurableSet_lt measurable_const (hNm.comp
    ((measurable_const.matrix_mul measurable_snd).matrix_mul
      (measurable_pinvR.comp measurable_fst)))
  have hFrob : Measurable (fun G : Matrix (Fin r) (Fin (r + p)) ℝ => frobNorm (pinvR G)) :=
    Real.continuous_sqrt.measurable.comp (measurable_frobSq.comp measurable_pinvR)
  have hSpec : Measurable (fun G : Matrix (Fin r) (Fin (r + p)) ℝ => specNorm (pinvR G)) :=
    measurable_specNorm_of_entries (Matrix.measurable_iff_entries.mp measurable_pinvR)
  have hEm : MeasurableSet E :=
    (measurableSet_lt measurable_const hFrob).union (measurableSet_lt measurable_const hSpec)
  have hE : (gaussianMatrix (Fin r) (Fin (r + p))).real E ≤ 2 * t ^ (-(p : ℝ)) := by
    calc
      _ ≤ (gaussianMatrix (Fin r) (Fin (r + p))).real {G | A < frobNorm (pinvR G)} +
          (gaussianMatrix (Fin r) (Fin (r + p))).real {G | B < specNorm (pinvR G)} :=
        measureReal_union_le _ _
      _ ≤ t ^ (-(p : ℝ)) + t ^ (-(p : ℝ)) := add_le_add
        (gaussianMatrix_lt_frobNorm_pinvR_le_sharp hp t ht)
        (gaussianMatrix_lt_specNorm_pinvR_le_rsvd hp t ht)
      _ = _ := by ring
  have hsections : ∀ G, G ∉ E → (gaussianMatrix (Fin q) (Fin (r + p))).real
      {H | (G, H) ∈ F} ≤ Real.exp (-u ^ 2 / 2) := by
    intro G hG
    change ¬ (A < frobNorm (pinvR G) ∨ B < specNorm (pinvR G)) at hG
    simp only [not_or, not_lt] at hG
    refine (measureReal_mono ?_).trans (hconc (pinvR G))
    intro H hH
    change cF * A + cS * B + u * (specNorm S * B) < N (S * H * pinvR G) at hH
    change cF * frobNorm (pinvR G) + cS * specNorm (pinvR G) +
      u * (specNorm S * specNorm (pinvR G)) < N (S * H * pinvR G)
    have hb : cF * frobNorm (pinvR G) + cS * specNorm (pinvR G) +
        u * (specNorm S * specNorm (pinvR G)) ≤ cF * A + cS * B + u * (specNorm S * B) := by
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hG.1 hcF) (mul_le_mul_of_nonneg_left hG.2 hcS))
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG.2 (specNorm_nonneg S)) hu)
    exact hb.trans_lt hH
  exact (measureReal_prod_le_measureReal_add_of_sections_le_of_measurableSet
    _ _ E F hEm hFm (Real.exp_pos _).le
    (Filter.Eventually.of_forall hsections)).trans (add_le_add hE (le_refl _))

/-- An independent Gaussian tail times the pseudoinverse of a Gaussian head has the
sharpened Frobenius deviation bound, including the empty and one-row head.
Source: HMT (2011), proof of Theorem 10.7; supports atlas `rsvd-tail`. -/
theorem gaussianMatrix_prod_lt_frobNorm_mul_pinvR_le {a q r p : ℕ} (hp : 4 ≤ p)
    (S : Matrix (Fin a) (Fin q) ℝ) {t u : ℝ} (ht : 1 ≤ t) (hu : 0 ≤ u) :
    ((gaussianMatrix (Fin r) (Fin (r + p))).prod
      (gaussianMatrix (Fin q) (Fin (r + p)))).real
      {z | (t * Real.sqrt (12 * (r : ℝ) / p)) * frobNorm S +
          u * (t * (Real.exp 1 * Real.sqrt (r + p) / ((p : ℝ) + 1))) * specNorm S <
        frobNorm (S * z.2 * pinvR z.1)} ≤
      2 * t ^ (-(p : ℝ)) + Real.exp (-u ^ 2 / 2) := by
  have h := gaussianMatrix_prod_sandwich_deviation (r := r) hp S frobNorm
    (Real.continuous_sqrt.measurable.comp measurable_frobSq)
    (frobNorm_nonneg S) (show (0 : ℝ) ≤ 0 from le_refl _) ht hu
    (fun D => by simpa only [zero_mul, add_zero] using gaussianMatrix_lt_frobNorm_mul_mul_le S D hu)
  simpa only [zero_mul, mul_zero, add_zero, mul_assoc, mul_left_comm, mul_comm] using h

/-- The spectral counterpart is a separate probability statement with the same explicit
failure bound. Source: HMT (2011), proof of Theorem 10.8; supports atlas `rsvd-tail`. -/
theorem gaussianMatrix_prod_lt_specNorm_mul_pinvR_le {a q r p : ℕ} (hp : 4 ≤ p)
    (S : Matrix (Fin a) (Fin q) ℝ) {t u : ℝ} (ht : 1 ≤ t) (hu : 0 ≤ u) :
    ((gaussianMatrix (Fin r) (Fin (r + p))).prod
      (gaussianMatrix (Fin q) (Fin (r + p)))).real
      {z | (t * Real.sqrt (12 * (r : ℝ) / p)) * specNorm S +
          (t * (Real.exp 1 * Real.sqrt (r + p) / ((p : ℝ) + 1))) * frobNorm S +
          u * (t * (Real.exp 1 * Real.sqrt (r + p) / ((p : ℝ) + 1))) * specNorm S <
        specNorm (S * z.2 * pinvR z.1)} ≤
      2 * t ^ (-(p : ℝ)) + Real.exp (-u ^ 2 / 2) := by
  have h := gaussianMatrix_prod_sandwich_deviation (r := r) hp S specNorm
    (measurable_specNorm_of_entries fun i j => Matrix.measurable_entry i j)
    (specNorm_nonneg S) (frobNorm_nonneg S) ht hu
    (fun D => gaussianMatrix_lt_specNorm_mul_mul_le S D hu)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

/-- The Frobenius conditional deviation transported to the actual two orthogonal blocks of
one Gaussian sketch. Source: HMT (2011), proof of Theorem 10.7; supports `rsvd-tail`. -/
theorem gaussianMatrix_lt_frobNorm_mul_block_mul_pinvR_block_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n k p a q : ℕ} (G : Ω → Matrix (Fin n) (Fin (k + p)) ℝ)
    (hG : HasLaw G (gaussianMatrix (Fin n) (Fin (k + p))) μ)
    (V₁ : Matrix (Fin n) (Fin k) ℝ) (V₂ : Matrix (Fin n) (Fin q) ℝ)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    (S : Matrix (Fin a) (Fin q) ℝ) (hp : 4 ≤ p) {t u : ℝ} (ht : 1 ≤ t) (hu : 0 ≤ u) :
    μ.real {ω | (t * Real.sqrt (12 * (k : ℝ) / p)) * frobNorm S +
        u * (t * (Real.exp 1 * Real.sqrt (k + p) / ((p : ℝ) + 1))) * specNorm S <
      frobNorm (S * (V₂ᵀ * G ω) * pinvR (V₁ᵀ * G ω))} ≤
      2 * t ^ (-(p : ℝ)) + Real.exp (-u ^ 2 / 2) := by
  have hPair := (gaussianMatrix_indepFun_block_of_hasLaw hG V₁ V₂ hV₁ hV₂ hV).hasLaw_prod
    (hasLaw_gaussianMatrix_block_of_hasLaw hG V₁ hV₁)
    (hasLaw_gaussianMatrix_block_of_hasLaw hG V₂ hV₂)
  have hm : Measurable (fun z : Matrix (Fin k) (Fin (k + p)) ℝ ×
      Matrix (Fin q) (Fin (k + p)) ℝ => frobNorm (S * z.2 * pinvR z.1)) :=
    Real.continuous_sqrt.measurable.comp (measurable_frobSq.comp
      ((measurable_const.matrix_mul measurable_snd).matrix_mul
        (measurable_pinvR.comp measurable_fst)))
  rw [hPair.measureReal_eq (p := fun z =>
    (t * Real.sqrt (12 * (k : ℝ) / p)) * frobNorm S +
        u * (t * (Real.exp 1 * Real.sqrt (k + p) / ((p : ℝ) + 1))) * specNorm S <
      frobNorm (S * z.2 * pinvR z.1)) (measurableSet_lt measurable_const hm)]
  exact gaussianMatrix_prod_lt_frobNorm_mul_pinvR_le hp S ht hu

/-- The spectral counterpart on the actual two orthogonal blocks of one Gaussian sketch.
This is a separate event from the Frobenius bound, with the same individual failure.
Source: HMT (2011), proof of Theorem 10.8; supports `rsvd-tail`. -/
theorem gaussianMatrix_lt_specNorm_mul_block_mul_pinvR_block_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n k p a q : ℕ} (G : Ω → Matrix (Fin n) (Fin (k + p)) ℝ)
    (hG : HasLaw G (gaussianMatrix (Fin n) (Fin (k + p))) μ)
    (V₁ : Matrix (Fin n) (Fin k) ℝ) (V₂ : Matrix (Fin n) (Fin q) ℝ)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    (S : Matrix (Fin a) (Fin q) ℝ) (hp : 4 ≤ p) {t u : ℝ} (ht : 1 ≤ t) (hu : 0 ≤ u) :
    μ.real {ω | (t * Real.sqrt (12 * (k : ℝ) / p)) * specNorm S +
        (t * (Real.exp 1 * Real.sqrt (k + p) / ((p : ℝ) + 1))) * frobNorm S +
        u * (t * (Real.exp 1 * Real.sqrt (k + p) / ((p : ℝ) + 1))) * specNorm S <
      specNorm (S * (V₂ᵀ * G ω) * pinvR (V₁ᵀ * G ω))} ≤
      2 * t ^ (-(p : ℝ)) + Real.exp (-u ^ 2 / 2) := by
  have hPair := (gaussianMatrix_indepFun_block_of_hasLaw hG V₁ V₂ hV₁ hV₂ hV).hasLaw_prod
    (hasLaw_gaussianMatrix_block_of_hasLaw hG V₁ hV₁)
    (hasLaw_gaussianMatrix_block_of_hasLaw hG V₂ hV₂)
  have hm : Measurable (fun z : Matrix (Fin k) (Fin (k + p)) ℝ ×
      Matrix (Fin q) (Fin (k + p)) ℝ => specNorm (S * z.2 * pinvR z.1)) :=
    measurable_specNorm_of_entries (Matrix.measurable_iff_entries.mp
      ((measurable_const.matrix_mul measurable_snd).matrix_mul
        (measurable_pinvR.comp measurable_fst)))
  rw [hPair.measureReal_eq (p := fun z =>
    (t * Real.sqrt (12 * (k : ℝ) / p)) * specNorm S +
        (t * (Real.exp 1 * Real.sqrt (k + p) / ((p : ℝ) + 1))) * frobNorm S +
        u * (t * (Real.exp 1 * Real.sqrt (k + p) / ((p : ℝ) + 1))) * specNorm S <
      specNorm (S * z.2 * pinvR z.1)) (measurableSet_lt measurable_const hm)]
  exact gaussianMatrix_prod_lt_specNorm_mul_pinvR_le hp S ht hu

end NLAlib
