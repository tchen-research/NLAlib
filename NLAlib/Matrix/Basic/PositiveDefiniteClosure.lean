import Mathlib.Analysis.Matrix.Order

/-!
# Extending continuous inequalities to the PSD boundary

Positive perturbation by the identity approaches every PSD real matrix
through positive definite matrices. Source: Horn--Johnson (2013), Section 7.8;
supports determinant inequalities and Schur-product inequalities.
-/

noncomputable section
open Matrix Filter
open scoped Topology MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] in
/-- A continuous real-valued inequality valid on the positive definite cone
extends to every PSD matrix by adding a positive scalar identity and taking
the right-hand limit. Empty dimensions are included.
Horn--Johnson (2013), Section 7.8; helper for determinant boundary cases. -/
theorem le_of_posSemidef_of_continuous_of_forall_posDef
    {f g : Matrix n n ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ M : Matrix n n ℝ, M.PosDef → f M ≤ g M)
    {A : Matrix n n ℝ} (hA : A.PosSemidef) : f A ≤ g A := by
  have hc : Continuous (fun t : ℝ => A + t • (1 : Matrix n n ℝ)) := by fun_prop
  have hfl : Tendsto (fun t : ℝ => f (A + t • (1 : Matrix n n ℝ))) (𝓝[>] 0) (𝓝 (f A)) := by
    simpa only [Function.comp_def, zero_smul, add_zero] using
      ((hf.comp hc).continuousAt (x := 0)).tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hgl : Tendsto (fun t : ℝ => g (A + t • (1 : Matrix n n ℝ))) (𝓝[>] 0) (𝓝 (g A)) := by
    simpa only [Function.comp_def, zero_smul, add_zero] using
      ((hg.comp hc).continuousAt (x := 0)).tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  apply le_of_tendsto_of_tendsto hfl hgl
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact h _ (Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul ht))

end NLAlib
