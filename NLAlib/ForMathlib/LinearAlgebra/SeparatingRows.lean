import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.CharZero.Infinite

/-!
# One deterministic coordinate separating finitely many rows

The finite union of proper dual kernels cannot cover a vector space over
the infinite real field. Applying this to row differences gives a vector
whose matrix image has pairwise distinct coordinates.
-/

noncomputable section
open Matrix
namespace NLAlib
variable {m n : Type*} [Fintype m] [Fintype n]

/-- Pairwise distinct real matrix rows admit a single deterministic vector
whose image coordinates are pairwise distinct. The proof uses finite
hyperplane avoidance over the infinite real field, with no measure theory.
Horn--Johnson (2013), proof of Theorem 7.5.9;
supports the finite exponential Gram certificate. -/
theorem exists_mulVec_injective_of_rows_injective (A : Matrix m n ℝ)
    (hA : Function.Injective A.row) : ∃ z : n → ℝ, Function.Injective (A *ᵥ z) := by
  classical
  let pairs := {p : m × m // p.1 ≠ p.2}
  let f (p : pairs) : Module.Dual ℝ (n → ℝ) := dotProductBilin ℝ ℝ (A.row p.val.1 - A.row p.val.2)
  have hf (p : pairs) : ∃ z, f p z ≠ 0 := by
    by_contra hn
    push Not at hn
    have hzero : A.row p.val.1 - A.row p.val.2 = 0 :=
      dotProduct_eq_zero _ hn
    exact p.property (hA (sub_eq_zero.mp hzero))
  obtain ⟨z, hz⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f hf
  refine ⟨z, ?_⟩
  intro i j hij
  by_contra hne
  apply hz ⟨(i, j), hne⟩
  change (A.row i - A.row j) ⬝ᵥ z = 0
  rw [sub_dotProduct]
  exact sub_eq_zero.mpr hij

end NLAlib
