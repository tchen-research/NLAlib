import NLAlib.Gaussian.InverseMoments.RegularizedIntegrability
import NLAlib.Matrix.GramCutoffCalculus
import NLAlib.Matrix.GramSoftMinMeasurable

/-!
# Integrability of unshifted Gram cutoff vector fields

Positive compact test support bounds the inverse on the active region. All
Gaussian Stein vector-field products therefore have genuine polynomial
dominators under the original law, without an identity regularization.
Atlas: wishart-lambda-min-tail.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Matrix ContDiff

namespace NLAlib

/-- A cut off unshifted Gram coordinate vector field is Gaussian integrable.
Source: bounded tests and the global gradient energy bound;
atlas wishart-lambda-min-tail (unshifted Stein helper).
atlas: gram-cutoff-vector-field -/
theorem integrable_test_mul_unshiftedGramGradient_single_gaussianMatrix
    {r k : ℕ} (hr : 0 < r) (n : ℕ) (hn : 0 < n)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioi 0) (i : Fin r) (j : Fin k) :
    Integrable (fun G : Fin r → Fin k → ℝ =>
      ψ (inversePowerSoftMin n (Matrix.of G * (Matrix.of G)ᵀ)) *
        gramSoftMinGradient n 0 (Matrix.of G) i j) (gaussianMatrix r k) := by
  let : NeZero r := ⟨hr.ne'⟩
  obtain ⟨P, hP⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  have hψzero : ψ 0 = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => lt_irrefl (0 : ℝ) (hψs h)
  have hP0 : 0 ≤ P := by simpa only [hψzero, norm_zero] using hP 0
  have hFm : Measurable (fun G : Fin r → Fin k → ℝ =>
      inversePowerSoftMin n (Matrix.of G * (Matrix.of G)ᵀ)) := by
    simpa only [regularizedGram_zero] using
      (measurable_inversePowerSoftMin_regularizedGram (ι := Fin r) (κ := Fin k) n 0)
  have hDm := measurable_gramSoftMinGradient_entry (ι := Fin r) (κ := Fin k) n 0 i j
  have hm : Measurable (fun G : Fin r → Fin k → ℝ =>
      ψ (inversePowerSoftMin n (Matrix.of G * (Matrix.of G)ᵀ)) *
        gramSoftMinGradient n 0 (Matrix.of G) i j) :=
    (hψ.continuous.measurable.comp hFm).mul hDm
  apply integrable_of_abs_le_frobSq_polynomial_gaussianMatrix r k 1 _ hm 0 (2 * P)
  intro G
  have hG := frobSq_nonneg (Matrix.of G)
  have hDsq := sq_gramSoftMinGradient_unshifted_single_le n hn (Matrix.of G) i j
  have hDabs : |gramSoftMinGradient n 0 (Matrix.of G) i j| ≤ 2 * (1 + frobSq (Matrix.of G)) := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * (1 + frobSq (Matrix.of G)))).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (frobSq (Matrix.of G))]
  rw [abs_mul]
  have hh := mul_le_mul
    (by simpa only [Real.norm_eq_abs] using
      hP (inversePowerSoftMin n (Matrix.of G * (Matrix.of G)ᵀ)))
    hDabs (abs_nonneg _) hP0
  simpa only [zero_add, pow_one, mul_assoc, mul_comm, mul_left_comm] using hh

/-- The coordinate times a cut off unshifted Gram vector field is Gaussian
integrable, as required by scalar Stein. Source: finite Frobenius coordinate
bounds and Gaussian polynomial moments; atlas wishart-lambda-min-tail (helper).
atlas: gram-cutoff-vector-field -/
theorem integrable_coordinate_mul_test_mul_unshiftedGramGradient_single_gaussianMatrix
    {r k : ℕ} (hr : 0 < r) (n : ℕ) (hn : 0 < n)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioi 0) (i : Fin r) (j : Fin k) :
    Integrable (fun G : Fin r → Fin k → ℝ =>
      G i j * (ψ (inversePowerSoftMin n (Matrix.of G * (Matrix.of G)ᵀ)) *
        gramSoftMinGradient n 0 (Matrix.of G) i j)) (gaussianMatrix r k) := by
  let : NeZero r := ⟨hr.ne'⟩
  obtain ⟨P, hP⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  have hψzero : ψ 0 = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => lt_irrefl (0 : ℝ) (hψs h)
  have hP0 : 0 ≤ P := by simpa only [hψzero, norm_zero] using hP 0
  have hFm : Measurable (fun G : Fin r → Fin k → ℝ =>
      inversePowerSoftMin n (Matrix.of G * (Matrix.of G)ᵀ)) := by
    simpa only [regularizedGram_zero] using
      (measurable_inversePowerSoftMin_regularizedGram (ι := Fin r) (κ := Fin k) n 0)
  have hDm := measurable_gramSoftMinGradient_entry (ι := Fin r) (κ := Fin k) n 0 i j
  have hEntry : Measurable (fun G : Fin r → Fin k → ℝ => G i j) :=
    (measurable_pi_apply j).comp (measurable_pi_apply i)
  have hm : Measurable (fun G : Fin r → Fin k → ℝ =>
      G i j * (ψ (inversePowerSoftMin n (Matrix.of G * (Matrix.of G)ᵀ)) *
        gramSoftMinGradient n 0 (Matrix.of G) i j)) :=
    hEntry.mul ((hψ.continuous.measurable.comp hFm).mul hDm)
  apply integrable_of_abs_le_frobSq_polynomial_gaussianMatrix r k 2 _ hm 0 (2 * P)
  intro G
  have hG := frobSq_nonneg (Matrix.of G)
  have hDsq := sq_gramSoftMinGradient_unshifted_single_le n hn (Matrix.of G) i j
  have hDabs : |gramSoftMinGradient n 0 (Matrix.of G) i j| ≤ 2 * (1 + frobSq (Matrix.of G)) := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * (1 + frobSq (Matrix.of G)))).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (frobSq (Matrix.of G))]
  have hrowsq : G i j ^ 2 ≤ ∑ j', G i j' ^ 2 :=
    Finset.single_le_sum (fun j' _ => sq_nonneg (G i j')) (Finset.mem_univ j)
  have hfullsq : (∑ j', G i j' ^ 2) ≤ ∑ i', ∑ j', G i' j' ^ 2 :=
    Finset.single_le_sum (fun i' _ => Finset.sum_nonneg fun j' _ => sq_nonneg (G i' j'))
      (Finset.mem_univ i)
  have hEsq : G i j ^ 2 ≤ frobSq (Matrix.of G) := by
    simpa only [frobSq, frobInner, Matrix.of_apply, ← pow_two] using hrowsq.trans hfullsq
  have hEabs : |G i j| ≤ 1 + frobSq (Matrix.of G) := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 1 + frobSq (Matrix.of G))).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (frobSq (Matrix.of G))]
  have htest :
      |ψ (inversePowerSoftMin n (Matrix.of G * (Matrix.of G)ᵀ)) *
        gramSoftMinGradient n 0 (Matrix.of G) i j| ≤ 2 * P * (1 + frobSq (Matrix.of G)) := by
    rw [abs_mul]
    have hh := mul_le_mul
      (by simpa only [Real.norm_eq_abs] using
        hP (inversePowerSoftMin n (Matrix.of G * (Matrix.of G)ᵀ)))
      hDabs (abs_nonneg _) hP0
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hh
  rw [abs_mul]
  have hh := mul_le_mul hEabs htest (abs_nonneg _) (by positivity : 0 ≤ 1 + frobSq (Matrix.of G))
  convert! hh using 1
  simp only [zero_add]
  ring

end NLAlib
