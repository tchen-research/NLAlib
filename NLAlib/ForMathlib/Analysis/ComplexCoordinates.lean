import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Real and imaginary coordinates of complex vectors

The real-linear equivalence uses disjoint finite coordinate copies. It is
algebraic for any index type and continuous when the index type is finite.
-/

noncomputable section
namespace Complex

/-- Real and imaginary coordinates as a real-linear equivalence. -/
def realCoordinates (ι : Type*) : (ι → ℂ) ≃ₗ[ℝ] (ι ⊕ ι → ℝ) where
  toFun z := Sum.elim (fun i => (z i).re) (fun i => (z i).im)
  invFun x i := (x (Sum.inl i) : ℂ) + (x (Sum.inr i) : ℂ) * I
  left_inv z := by funext i; exact re_add_im (z i)
  right_inv x := by funext s; cases s <;> simp
  map_add' z w := by funext s; cases s <;> simp
  map_smul' c z := by funext s; cases s <;> simp

@[simp] theorem realCoordinates_inl {ι : Type*} (z : ι → ℂ) (i : ι) :
    realCoordinates ι z (Sum.inl i) = (z i).re := rfl

@[simp] theorem realCoordinates_inr {ι : Type*} (z : ι → ℂ) (i : ι) :
    realCoordinates ι z (Sum.inr i) = (z i).im := rfl

/-- In finite dimensions the coordinate equivalence is continuous in both
 directions for the ordinary product topologies. -/
def realCoordinatesContinuousLinearEquiv (ι : Type*) [Fintype ι] :
    (ι → ℂ) ≃L[ℝ] (ι ⊕ ι → ℝ) := (realCoordinates ι).toContinuousLinearEquiv

end Complex
