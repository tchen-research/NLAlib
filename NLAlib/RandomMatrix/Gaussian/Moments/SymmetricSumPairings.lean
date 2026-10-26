import NLAlib.RandomMatrix.Gaussian.Basic.SymmetricSum
import NLAlib.RandomMatrix.Gaussian.Moments.LinearFormPairings
import NLAlib.RandomMatrix.Gaussian.Moments.SymmetricProfileDiagrams

/-!
# Homogeneous symmetric Gaussian comparator diagrams

The true symmetric Gaussian sum `G + Gᴴ` has covariance twice the two
endpoint orientations. Its trace moments dominate the unit-profile oriented
diagram sum. An individual unit diagram has exactly `r ^ v` labelings,
where `v` is its endpoint-quotient vertex count.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace NLAlib

open EndpointPairingQuotient

/-- Products of entries of the actual symmetric Gaussian sum are integrable. -/
theorem integrable_prod_gaussianSymmetricSum_entry {r k : ℕ}
    (idx : Fin k → Fin r × Fin r) :
    Integrable (fun G => ∏ i, gaussianSymmetricSum G (idx i).1 (idx i).2)
      (gaussianMatrix (Fin r) (Fin r)) := by
  simp_rw [gaussianSymmetricSum_apply_eq_linForm]
  exact integrable_prod_linForm_gaussianMatrix (fun i => gaussianSymmetricSumEntryCoefficient (idx i).1 (idx i).2)

/-- The exact Wick formula for entries of `G + Gᴴ` uses covariance twice
the sum of the two endpoint orientations, including diagonal variance four. -/
theorem integral_prod_gaussianSymmetricSum_entry_eq_sum_pairings {r k : ℕ}
    (idx : Fin k → Fin r × Fin r) :
    (∫ G, ∏ i, gaussianSymmetricSum G (idx i).1 (idx i).2 ∂gaussianMatrix (Fin r) (Fin r)) =
      ∑ π : GaussianPairings k, gaussianPairingWeight (fun i j =>
        2 * ((if (idx i).1 = (idx j).1 ∧ (idx i).2 = (idx j).2 then 1 else 0) +
          (if (idx i).1 = (idx j).2 ∧ (idx i).2 = (idx j).1 then 1 else 0))) π := by
  simp_rw [gaussianSymmetricSum_apply_eq_linForm]
  rw [integral_prod_linForm_gaussianMatrix_eq_sum_pairings]
  simp_rw [sum_gaussianSymmetricSumEntryCoefficient_mul]

/-- Positive trace powers of the actual symmetric Gaussian sum are integrable. -/
theorem integrable_trace_gaussianSymmetricSum_pow (r k : ℕ) :
    Integrable (fun G : Matrix (Fin r) (Fin r) ℝ =>
      ((gaussianSymmetricSum G) ^ (k + 1)).trace) (gaussianMatrix (Fin r) (Fin r)) := by
  have htrace (G : Matrix (Fin r) (Fin r) ℝ) :
      ((gaussianSymmetricSum G) ^ (k + 1)).trace =
        ∑ x : Fin (k + 1) → Fin r, ∏ i,
          gaussianSymmetricSum G (x i) (x (finRotate (k + 1) i)) := by
    simpa only [List.ofFn_const, List.prod_replicate] using
      Matrix.trace_list_ofFn_prod_eq_sum_cyclic (fun _ : Fin (k + 1) => gaussianSymmetricSum G)
  simp_rw [htrace]
  exact integrable_finsetSum _ (fun x _ => integrable_prod_gaussianSymmetricSum_entry
    (fun i => (x i, x (finRotate (k + 1) i))))

/-- The sum of all oriented unit-profile diagrams is dominated by the
actual homogeneous symmetric Gaussian trace moment. The comparator is the
explicit ensemble `G + Gᴴ`, with its stated unnormalized covariance. -/
theorem sum_symmetricCycleDiagramWeight_one_le_integral_trace_gaussianSymmetricSum_pow
    (r k : ℕ) :
    (∑ π : GaussianPairings (k + 1),
      ∑ flip : Fin (gaussianPairingEdges π).length → Bool,
        ∑ x : Fin (k + 1) → Fin r,
          symmetricCycleDiagramWeight (Matrix.of fun _ _ => (1 : ℝ)) π flip x) ≤
      ∫ G, ((gaussianSymmetricSum G) ^ (k + 1)).trace ∂gaussianMatrix (Fin r) (Fin r) := by
  have htrace (G : Matrix (Fin r) (Fin r) ℝ) :
      ((gaussianSymmetricSum G) ^ (k + 1)).trace =
        ∑ x : Fin (k + 1) → Fin r, ∏ i,
          gaussianSymmetricSum G (x i) (x (finRotate (k + 1) i)) := by
    simpa only [List.ofFn_const, List.prod_replicate] using
      Matrix.trace_list_ofFn_prod_eq_sum_cyclic (fun _ : Fin (k + 1) => gaussianSymmetricSum G)
  have hmoment :
      (∫ G, ((gaussianSymmetricSum G) ^ (k + 1)).trace ∂gaussianMatrix (Fin r) (Fin r)) =
        ∑ x : Fin (k + 1) → Fin r, ∑ π : GaussianPairings (k + 1),
          gaussianPairingWeight (fun i j =>
            2 * ((if x i = x j ∧ x (finRotate (k + 1) i) = x (finRotate (k + 1) j)
              then 1 else 0) +
              (if x i = x (finRotate (k + 1) j) ∧ x (finRotate (k + 1) i) = x j
              then 1 else 0))) π := by
    simp_rw [htrace]
    rw [integral_finsetSum _ (fun x _ => integrable_prod_gaussianSymmetricSum_entry
      (fun i => (x i, x (finRotate (k + 1) i))))]
    apply Finset.sum_congr rfl
    intro x _
    exact integral_prod_gaussianSymmetricSum_entry_eq_sum_pairings
      (fun i => (x i, x (finRotate (k + 1) i)))
  rw [hmoment]
  calc
    _ = ∑ x : Fin (k + 1) → Fin r, ∑ π : GaussianPairings (k + 1),
        ∑ flip : Fin (gaussianPairingEdges π).length → Bool,
          symmetricCycleDiagramWeight (Matrix.of fun _ _ => (1 : ℝ)) π flip x := by
      symm
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro π _
      exact Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro π _
      rw [← gaussianPairingWeight_cycle_covariance_eq_sum_diagrams]
      simp only [Matrix.of_apply, one_pow]
      apply gaussianPairingWeight_le_gaussianPairingWeight
      · intro i j
        exact add_nonneg (by split_ifs <;> norm_num) (by split_ifs <;> norm_num)
      · intro i j
        have h : 0 ≤ (if x i = x j ∧ x (finRotate (k + 1) i) = x (finRotate (k + 1) j) then (1 : ℝ) else 0) +
            (if x i = x (finRotate (k + 1) j) ∧ x (finRotate (k + 1) i) = x j then 1 else 0) :=
          add_nonneg (by split_ifs <;> norm_num) (by split_ifs <;> norm_num)
        linarith

/-- An oriented unit-profile Wick diagram counts all assignments of the
quotient vertices, hence has exactly `r ^ v` contributions in dimension `r`. -/
theorem sum_symmetricCycleDiagramWeight_one {r k : ℕ} (π : GaussianPairings k)
    (flip : Fin (gaussianPairingEdges π).length → Bool) :
    (∑ x : Fin k → Fin r, symmetricCycleDiagramWeight (Matrix.of fun _ _ => (1 : ℝ)) π flip x) =
      (r : ℝ) ^ Nat.card (symmetricCycleVertexQuotient π flip) := by
  classical
  let a := fun e : Fin (gaussianPairingEdges π).length => ((gaussianPairingEdges π).get e).1
  let b := fun e : Fin (gaussianPairingEdges π).length => ((gaussianPairingEdges π).get e).2
  let Q := symmetricCycleVertexQuotient π flip
  let : Fintype Q := Fintype.ofFinite Q
  have h := sum_prod_indicator_eq_sum_quotient a
    (fun e => orientedCycleSource (b e) (flip e))
    (fun e => finRotate k (a e))
    (fun e => orientedCycleTarget (b e) (flip e)) (fun _ _ : Fin r => (1 : ℝ))
  simpa only [symmetricCycleDiagramWeight, Matrix.of_apply, one_pow, Finset.prod_const_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.card_eq_fintype_card, a, b,
    symmetricCycleVertexQuotient] using h

end NLAlib
