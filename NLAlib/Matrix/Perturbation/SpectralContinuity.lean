import NLAlib.Matrix.Spectral.Weyl

/-!
# Continuity of singular values on matrix arrays

The Frobenius Lipschitz inequality `abs_singularValues_sub_le_frobNorm` gives continuity of
every singular value in the array topology `ι → κ → ℝ`; this supplies the cutoff neighbourhood
around deficient Gram matrices. Atlas: `norm-lipschitz`, `wishart-lambda-min-tail`.
-/

noncomputable section

open Filter
open scoped Topology Matrix

namespace NLAlib

/-- The Frobenius norm is continuous on finite matrix arrays.
Finite sums, products and the continuous square root; atlas `norm-lipschitz` (helper). -/
theorem continuous_frobNorm_array {ι κ : Type*} [Fintype ι] [Fintype κ] :
    Continuous (fun G : ι → κ → ℝ => frobNorm (Matrix.of G)) := by
  simp only [frobNorm, frobSq, frobInner_eq_sum_mul]
  fun_prop

/-- Every singular value is continuous on finite matrix arrays (the Frobenius Lipschitz bound
`abs_singularValues_sub_le_frobNorm`); at `k = card κ - 1` this is the smallest singular value.
Supports `wishart-lambda-min-tail` (cutoff neighbourhoods).
atlas: norm-lipschitz -/
theorem continuous_singularValues_array {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (k : ℕ) : Continuous (fun G : ι → κ → ℝ => singularValues (Matrix.of G) k) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro G
  have hdiff : Continuous (fun H : ι → κ → ℝ =>
      frobNorm (Matrix.of H - Matrix.of G)) :=
    continuous_frobNorm_array.comp (continuous_id.sub continuous_const)
  have hzero : Tendsto (fun H : ι → κ → ℝ => frobNorm (Matrix.of H - Matrix.of G))
      (𝓝 G) (𝓝 (0 : ℝ)) := by
    have hh : ContinuousAt (fun H : ι → κ → ℝ =>
        frobNorm (Matrix.of H - Matrix.of G)) G := hdiff.continuousAt
    simpa only [sub_self, frobNorm_zero] using hh.tendsto
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp hzero).2 ε hε] with H hH
  rw [Real.dist_eq]
  exact (abs_singularValues_sub_le_frobNorm (Matrix.of H) (Matrix.of G) k).trans_lt hH

/-- The squared smallest singular value of a transposed finite array,
`σ_{card ι - 1}((of G)ᵀ)²`, is continuous (transpose continuity and the Frobenius Lipschitz
bound). Supports `wishart-lambda-min-tail` (cutoff neighbourhoods).
atlas: norm-lipschitz -/
theorem continuous_sq_singularValues_transpose_last_array {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] :
    Continuous (fun G : ι → κ → ℝ => singularValues (Matrix.of G)ᵀ (Fintype.card ι - 1) ^ 2) := by
  have ht : Continuous (fun G : ι → κ → ℝ => fun j i => G i j) :=
    continuous_pi fun _ => continuous_pi fun _ => (continuous_apply _).comp (continuous_apply _)
  exact ((continuous_singularValues_array (Fintype.card ι - 1)).comp ht).pow 2

end NLAlib
