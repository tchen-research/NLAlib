import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.DenselyOrdered

/-! # Endpoint control from a bounded interior derivative

Continuity supplies the two endpoint values; differentiability is needed only
on the open interval. This is useful for square-root interpolation paths.
-/

noncomputable section
set_option autoImplicit false
open Set
open scoped NNReal

/-- A continuous path on the unit interval with uniformly bounded interior
derivative moves its endpoints by at most that bound. -/
theorem norm_sub_endpoints_le_of_hasDerivAt_Ioo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} {C : ℝ} (hC : 0 ≤ C)
    (hc : ContinuousOn f (Icc 0 1))
    (hf : ∀ t ∈ Ioo 0 1, HasDerivAt f (f' t) t)
    (hb : ∀ t ∈ Ioo 0 1, ‖f' t‖ ≤ C) : ‖f 1 - f 0‖ ≤ C := by
  have hl : LipschitzOnWith ⟨C, hC⟩ f (Ioo 0 1) := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun t ht => (hf t ht).differentiableAt) _ (convex_Ioo 0 1)
    intro t ht
    change ‖deriv f t‖ ≤ C
    rw [(hf t ht).deriv]
    exact hb t ht
  have hclosure : closure (Ioo (0 : ℝ) 1) = Icc 0 1 := closure_Ioo zero_ne_one
  have hlc := hl.closure (by rwa [hclosure])
  rw [hclosure] at hlc
  have h := hlc.dist_le_mul 1 (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)
    0 (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
  convert h using 1 <;> norm_num [dist_eq_norm]
  rfl
