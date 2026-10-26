import NLAlib.Matrix.Functions.VarianceProfileGeometry
import NLAlib.Probability.SubGaussian.SortedMaximum
import NLAlib.Probability.Gaussian.Concentration.LipschitzConcentration
import NLAlib.Probability.Gaussian.Basic.StandardVector
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Expected maxima of Gaussian variance-profile radii

Each weighted Gaussian radius has its exact second moment and its sharp
rowwise Lipschitz constant. The sorted sub-Gaussian maximal estimate then
controls their maximum by the maximum row energy and a logarithmic
envelope of the rowwise Lipschitz constants.

Source: van Handel, arXiv:1502.05003v4, proof of Theorem 4.1.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace NLAlib

variable {n : ℕ}

/-- A weighted Gaussian row radius belongs to `L²`, including zero weights. -/
theorem memLp_varianceProfileRadius_gaussianVector
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : ∀ i j, 0 ≤ B i j) (i : Fin n) :
    MemLp (fun g => varianceProfileRadius B g i) 2 (gaussianVector (Fin n)) := by
  have hV : MemLp (fun g : Fin n → ℝ =>
      (WithLp.toLp 2 (fun j => Real.sqrt (B i j) * g j) : EuclideanSpace ℝ (Fin n)))
      2 (gaussianVector (Fin n)) := by
    rw [memLp_piLp_iff]
    intro j
    exact (memLp_two_of_hasLaw_gaussianReal (hasLaw_eval_gaussianVector j)).const_mul _
  simpa only [varianceProfileRadius_eq_norm B hB] using hV.norm

/-- The second moment of a weighted Gaussian row radius is its row
variance sum, with every coordinate variance equal to one. -/
theorem integral_varianceProfileRadius_sq_gaussianVector
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : ∀ i j, 0 ≤ B i j) (i : Fin n) :
    (∫ g, varianceProfileRadius B g i ^ 2 ∂gaussianVector (Fin n)) = ∑ j, B i j := by
  simp_rw [varianceProfileRadius_sq B hB]
  rw [integral_finsetSum _ (fun j _ =>
    (memLp_two_of_hasLaw_gaussianReal (hasLaw_eval_gaussianVector j)).integrable_sq.const_mul _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, integral_sq_eq_one_of_hasLaw_gaussianReal (hasLaw_eval_gaussianVector j), mul_one]

/-- The expected maximum of the actual weighted Gaussian row radii is
bounded by their maximum root second moment and a universal logarithmic
Lipschitz envelope. Independence between different rows is unnecessary. -/
theorem integral_norm_varianceProfileRadius_gaussianVector_le
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : ∀ i j, 0 ≤ B i j)
    (L : Fin n → ℝ) (hL : ∀ i, 0 ≤ L i) (hLip : ∀ i j, B i j ≤ L i ^ 2)
    (a D : ℝ) (ha : 0 ≤ a) (hD : 0 < D)
    (hrow : ∀ i, ∑ j, B i j ≤ a ^ 2)
    (henv : ∀ i, L i ^ 2 * Real.log (((i : ℕ) : ℝ) + 2) ≤ D ^ 2) :
    (∫ g, ‖fun i => varianceProfileRadius B g i‖ ∂gaussianVector (Fin n)) ≤ a + 16 * D := by
  let m : Fin n → ℝ := fun i => ∫ g, varianceProfileRadius B g i ∂gaussianVector (Fin n)
  have hi (i : Fin n) := memLp_varianceProfileRadius_gaussianVector B hB i
  have hm0 (i : Fin n) : 0 ≤ m i := integral_nonneg fun g => varianceProfileRadius_nonneg B g i
  have hm (i : Fin n) : m i ≤ a := by
    apply integral_le_of_integral_sq_le (gaussianVector (Fin n)) _
      ((hi i).integrable (by norm_num)) (hi i).integrable_sq a ha
    rw [integral_varianceProfileRadius_sq_gaussianVector B hB]
    exact hrow i
  have hmgf (i : Fin n) : HasSubgaussianMGF (fun g => varianceProfileRadius B g i - m i)
      ⟨L i ^ 2, sq_nonneg _⟩ (gaussianVector (Fin n)) := by
    simpa only [one_mul] using hasSubgaussianMGF_of_logSobolev
      hasEuclideanLogSobolev_gaussianVector (fun g => varianceProfileRadius B g i) (L i) (hL i)
        (fun g h => abs_varianceProfileRadius_sub_le B hB g h i (L i) (hL i) (hLip i))
  have hb := integral_norm_pi_le_sixteen_of_hasSubgaussianMGF_log_envelope
    (fun i g => varianceProfileRadius B g i - m i) (fun i => ⟨L i ^ 2, sq_nonneg _⟩)
      hmgf D hD henv
  have hmi : MemLp (fun g => fun i => varianceProfileRadius B g i - m i)
      2 (gaussianVector (Fin n)) := by
    apply memLp_pi_iff.mpr
    intro i
    exact (hi i).sub (memLp_const _)
  have hRi : Integrable (fun g => ‖fun i => varianceProfileRadius B g i‖)
      (gaussianVector (Fin n)) :=
    (integrable_pi_iff.mpr (fun i => (hi i).integrable (by norm_num))).norm
  have hbound := integral_mono hRi ((integrable_const a).add (hmi.norm.integrable (by norm_num))) (fun g => by
    have hnorm : ‖m‖ ≤ a := (pi_norm_le_iff_of_nonneg ha).mpr (fun i => by
      rw [Real.norm_of_nonneg (hm0 i)]
      exact hm i)
    have heq : (fun i => varianceProfileRadius B g i) = m + (fun i => varianceProfileRadius B g i - m i) := by
      funext i
      simp only [Pi.add_apply]
      ring
    rw [heq]
    change ‖m + (fun i => varianceProfileRadius B g i - m i)‖ ≤
      a + ‖fun i => varianceProfileRadius B g i - m i‖
    linarith [norm_add_le m (fun i => varianceProfileRadius B g i - m i)])
  simp only [Pi.add_apply] at hbound
  rw [integral_add (integrable_const a) (hmi.norm.integrable (by norm_num)),
    integral_const, probReal_univ, one_smul] at hbound
  linarith

end NLAlib
