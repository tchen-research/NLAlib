import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Supremum norm of pairwise scalar products

The supremum norm of `(i,j) ↦ a i * b j` is the product of the two supremum
norms. Empty finite index types are included. This is the elementary finite
norm identity underlying the Kronecker spectral-norm theorem.
-/

noncomputable section

namespace NLAlib

/-- Supremum norms of finite real lists multiply for pairwise products.
The identity includes empty factors, whose supremum norms are zero.
-/
theorem norm_pair_mul {m n : Type*} [Fintype m] [Fintype n] (a : m → ℝ) (b : n → ℝ) :
    ‖(fun ij : m × n => a ij.1 * b ij.2)‖ = ‖a‖ * ‖b‖ := by
  classical
  rcases isEmpty_or_nonempty m with hm | hm
  · simp [Pi.norm_def]
  rcases isEmpty_or_nonempty n with hn | hn
  · simp [Pi.norm_def]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg a) (norm_nonneg b))).mpr
    intro ij
    rw [norm_mul]
    exact mul_le_mul (norm_le_pi_norm a ij.1) (norm_le_pi_norm b ij.2)
      (norm_nonneg _) (norm_nonneg _)
  · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun i => ‖a i‖₊)
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun j => ‖b j‖₊)
    have hai : ‖a‖ = ‖a i‖ := by simpa only [Pi.norm_def, coe_nnnorm] using congrArg NNReal.toReal hi
    have hbj : ‖b‖ = ‖b j‖ := by simpa only [Pi.norm_def, coe_nnnorm] using congrArg NNReal.toReal hj
    rw [hai, hbj, ← norm_mul]
    exact norm_le_pi_norm (fun ij : m × n => a ij.1 * b ij.2) (i, j)

end NLAlib
