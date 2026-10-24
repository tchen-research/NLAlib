import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix

/-! # Fixed vectors and decaying matrix powers

Pointwise decay on every vector is equivalent to matrix-power decay in finite dimensions.
Decay also excludes a nonzero fixed vector and makes `1 - H` invertible. These elementary
bridges support the stationary-splitting convergence criterion.
-/

noncomputable section

open Filter
open scoped Matrix Topology

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- In finite dimensions, matrix powers decay exactly when they decay on every vector. -/
theorem tendsto_pow_zero_iff_forall_mulVec (H : Matrix n n 𝕜) :
    Tendsto (fun k : ℕ => H ^ k) atTop (𝓝 0) ↔
      ∀ v : n → 𝕜, Tendsto (fun k : ℕ => (H ^ k) *ᵥ v) atTop (𝓝 0) := by
  constructor
  · intro h v
    have hc : Continuous (fun T : Matrix n n 𝕜 => T *ᵥ v) := by fun_prop
    simpa only [Function.comp_def, zero_mulVec] using hc.continuousAt.tendsto.comp h
  · intro h
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have hj := (tendsto_pi_nhds.mp (h (Pi.single j 1))) i
    simpa only [mulVec_single_one, col_apply, Pi.zero_apply, Matrix.zero_apply] using hj

/-- Decaying matrix powers exclude eigenvalue one, so `1 - H` is invertible. -/
theorem isUnit_one_sub_of_tendsto_pow_zero {H : Matrix n n 𝕜}
    (hH : Tendsto (fun k : ℕ => H ^ k) atTop (𝓝 0)) : IsUnit (1 - H) := by
  apply mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have hz : (1 - H) *ᵥ (x - y) = 0 := by
    rw [mulVec_sub, hxy, sub_self]
  have hfix : H *ᵥ (x - y) = x - y := by
    rw [sub_mulVec, one_mulVec] at hz
    exact (sub_eq_zero.mp hz).symm
  have hp (k : ℕ) : (H ^ k) *ᵥ (x - y) = x - y := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', ← mulVec_mulVec, ih, hfix]
  have ht := (tendsto_pow_zero_iff_forall_mulVec H).mp hH (x - y)
  simp only [hp] at ht
  exact sub_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds ht)

end Matrix
