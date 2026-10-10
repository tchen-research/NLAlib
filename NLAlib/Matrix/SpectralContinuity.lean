import NLAlib.Matrix.Spectral
import Mathlib.Topology.Instances.Matrix

/-!
# Continuity of the smallest singular value on matrix arrays

The Frobenius Lipschitz inequality gives continuity in the array topology.
This supplies the cutoff neighborhood around deficient Gram matrices.
Atlas: norm-lipschitz and wishart-lambda-min-tail.
-/

noncomputable section

open Filter
open scoped Topology Matrix

namespace NLAlib

/-- The Frobenius norm is continuous on finite matrix arrays.
Source: finite sums, products, and the continuous square root;
atlas norm-lipschitz (cutoff helper). -/
theorem continuous_frobNorm_array {ι κ : Type*} [Fintype ι] [Fintype κ] :
    Continuous (fun G : ι → κ → ℝ => frobNorm (Matrix.of G)) := by
  unfold frobNorm frobSq frobInner
  fun_prop

/-- The smallest singular value is continuous on finite matrix arrays.
Source: the Frobenius Lipschitz bound; atlas norm-lipschitz and
wishart-lambda-min-tail (cutoff helper).
atlas: norm-lipschitz -/
theorem continuous_sigmaMin_array {ι κ : Type*} [Fintype ι] [Fintype κ] :
    Continuous (fun G : ι → κ → ℝ => sigmaMin (Matrix.of G)) := by
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
  exact (abs_sigmaMin_sub_sigmaMin_le_frobNorm (Matrix.of H) (Matrix.of G)).trans_lt hH

/-- The squared smallest singular value of a transposed finite array is continuous.
Source: transpose continuity and the Frobenius Lipschitz bound;
atlas wishart-lambda-min-tail (cutoff helper).
atlas: norm-lipschitz -/
theorem continuous_sigmaMin_transpose_sq_array {ι κ : Type*} [Fintype ι] [Fintype κ] :
    Continuous (fun G : ι → κ → ℝ => sigmaMin (Matrix.of G)ᵀ ^ 2) := by
  have ht : Continuous (fun G : ι → κ → ℝ => fun j i => G i j) :=
    continuous_pi fun _ => continuous_pi fun _ => (continuous_apply _).comp (continuous_apply _)
  exact (continuous_sigmaMin_array.comp ht).pow 2

end NLAlib
