import NLAlib.RandomMatrix.Gaussian.Basic.Lipschitz

/-!
# Integrability of polynomial growth under Gaussian matrix laws

Every natural power of a constant plus the elementwise sup norm of the matrix
(`open scoped Matrix.Norms.Elementwise`, the norm of the coordinates) is integrable. These dominators justify Gaussian integration by parts for
the finite resolvent regularizations in the operator hard-edge proof.

Atlas: gaussian-matrix-def and wishart-lambda-min-tail.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix.Norms.Elementwise

namespace NLAlib

/-- The squared Frobenius size is bounded by the number of coordinates times
the squared elementwise sup norm. Source: finite-coordinate norm comparison;
atlas wishart-lambda-min-tail (Gaussian domination helper). -/
theorem frobSq_of_le_card_mul_sq_norm {r k : ℕ} (G : Matrix (Fin r) (Fin k) ℝ) :
    frobSq G ≤ (r : ℝ) * k * ‖G‖ ^ 2 := by
  have hentry (i : Fin r) (j : Fin k) : (G i j) ^ 2 ≤ ‖G‖ ^ 2 := by
    have h := Matrix.norm_entry_le_entrywise_sup_norm (A := G) (i := i) (j := j)
    simpa only [Real.norm_eq_abs, sq_abs] using
      pow_le_pow_left₀ (norm_nonneg (G i j)) h 2
  simp only [frobSq, frobInner_eq_sum_mul, ← sq]
  calc (∑ i, ∑ j, (G i j) ^ 2) ≤ ∑ _i : Fin r, ∑ _j : Fin k, ‖G‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    _ = _ := by simp; ring

/-- A nonnegative constant plus the elementwise sup norm of a Gaussian
matrix has every natural moment. Source: Gaussian moments of all orders
and the Lp triangle inequality; atlas gaussian-matrix-def and
wishart-lambda-min-tail (domination helper). -/
theorem integrable_const_add_norm_gaussianMatrix_pow (r k n : ℕ) (c : ℝ)
    (hc : 0 ≤ c) :
    Integrable (fun G : Matrix (Fin r) (Fin k) ℝ => (c + ‖G‖) ^ n)
      (gaussianMatrix (Fin r) (Fin k)) := by
  have : @BorelSpace (Matrix (Fin r) (Fin k) ℝ)
      (UniformSpace.toTopologicalSpace (self := PseudoMetricSpace.toUniformSpace)) _ :=
    Matrix.instBorelSpace
  have hx : MemLp (fun G : Matrix (Fin r) (Fin k) ℝ => G) (n : ℝ≥0∞)
      (gaussianMatrix (Fin r) (Fin k)) :=
    (hasGaussianLaw_id_gaussianMatrix (Fin r) (Fin k)).memLp (by simp)
  have hconst : MemLp (fun _ : Matrix (Fin r) (Fin k) ℝ => c) (n : ℝ≥0∞)
      (gaussianMatrix (Fin r) (Fin k)) := memLp_const c
  have hsum := hconst.add hx.norm
  have hint := hsum.integrable_norm_pow'
  convert! hint using 1
  funext G
  exact congrArg (fun z : ℝ => z ^ n) (Real.norm_of_nonneg (add_nonneg hc (norm_nonneg G))).symm

end NLAlib
