import NLAlib.Matrix.Basic.QuadForm
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
/-!
# Finite Hermitian quadratic minimization

Completing the square gives the unique minimizer of a positive definite
Hermitian quadratic. The objective is real-valued over either real or
complex coordinates. Supports Tikhonov regularization and reduced-Hessian
constrained optimization.
-/
noncomputable section
open Matrix
open scoped Matrix ComplexOrder
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The real Hermitian quadratic objective `xᴴHx/2 - Re(fᴴx)`. -/
def quadraticObjective (H : Matrix n n 𝕜) (f x : n → 𝕜) : ℝ :=
  (1 / 2 : ℝ) * RCLike.re (quadForm H x) - RCLike.re (star f ⬝ᵥ x)

/-- Completing the square at a solution of the Hermitian normal equation. -/
theorem quadraticObjective_add_of_mulVec_eq {H : Matrix n n 𝕜} (hH : H.IsHermitian)
    {f x : n → 𝕜} (hx : H *ᵥ x = f) (y : n → 𝕜) :
    quadraticObjective H f (x + y) = quadraticObjective H f x +
      (1 / 2 : ℝ) * RCLike.re (quadForm H y) := by
  have hc : star f ⬝ᵥ y = star x ⬝ᵥ (H *ᵥ y) := by
    rw [← hx, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hH.eq]
  have hq := hH.re_quadForm_smul_add_smul x y 1 1
  simp only [RCLike.ofReal_one, one_smul, one_pow, one_mul] at hq
  unfold quadraticObjective
  rw [hq, dotProduct_add, map_add, hc]
  ring

/-- A positive definite quadratic has a strict, unique minimum at each
solution of its normal equation. -/
theorem quadraticObjective_minimizer_of_posDef {H : Matrix n n 𝕜} (hH : H.PosDef)
    {f x : n → 𝕜} (hx : H *ᵥ x = f) :
    (∀ y, quadraticObjective H f x ≤ quadraticObjective H f y) ∧
      ∀ y, quadraticObjective H f y ≤ quadraticObjective H f x → y = x := by
  have he (y : n → 𝕜) : quadraticObjective H f y = quadraticObjective H f x +
      (1 / 2 : ℝ) * RCLike.re (quadForm H (y - x)) := by
    simpa only [add_sub_cancel] using
      quadraticObjective_add_of_mulVec_eq hH.isHermitian hx (y - x)
  constructor
  · intro y
    rw [he y]
    have hn := hH.posSemidef.re_quadForm_nonneg (y - x)
    linarith
  · intro y hy
    by_contra hne
    have hpos : 0 < RCLike.re (quadForm H (y - x)) :=
      (RCLike.pos_iff.mp (hH.quadForm_pos (sub_ne_zero.mpr hne))).1
    rw [he y] at hy
    linarith

/-- The unique minimizer of a positive definite Hermitian quadratic is
`H⁻¹f`, with the total matrix inverse justified by positive definiteness. -/
theorem quadraticObjective_inv_mulVec_minimizer {H : Matrix n n 𝕜} (hH : H.PosDef)
    (f : n → 𝕜) :
    (∀ y, quadraticObjective H f (H⁻¹ *ᵥ f) ≤ quadraticObjective H f y) ∧
      ∀ y, quadraticObjective H f y ≤ quadraticObjective H f (H⁻¹ *ᵥ f) → y = H⁻¹ *ᵥ f := by
  apply quadraticObjective_minimizer_of_posDef hH
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hH.isUnit), Matrix.one_mulVec]

end NLAlib
