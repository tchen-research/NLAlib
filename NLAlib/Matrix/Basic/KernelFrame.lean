import NLAlib.Matrix.Basic.Pseudoinverse
import NLAlib.Matrix.Subspaces.OrthogonalProducts
/-!+# Orthonormal coordinates for a matrix kernel

An orthonormal frame spanning the constraint null space gives the exact
decomposition into feasible directions and adjoint constraint directions.
These elementary identities support null-space KKT solvers.
-/
noncomputable section
open Matrix
open scoped Matrix ComplexOrder
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {m n r : Type*}
  [Fintype m] [Fintype n] [Fintype r] [DecidableEq m] [DecidableEq n] [DecidableEq r]

/-- An orthonormal matrix frame whose range is the entire constraint kernel. -/
structure IsKernelFrame (B : Matrix m n 𝕜) (Z : Matrix n r 𝕜) : Prop where
  orth : HasOrthonormalCols Z
  range_eq : LinearMap.range Z.mulVecLin = LinearMap.ker B.mulVecLin

/-- A kernel frame is annihilated by the constraint matrix. -/
theorem IsKernelFrame.mul_eq_zero {B : Matrix m n 𝕜} {Z : Matrix n r 𝕜}
    (hZ : IsKernelFrame B Z) : B * Z = 0 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  have h : Z *ᵥ v ∈ LinearMap.ker B.mulVecLin := by
    rw [← hZ.range_eq]
    exact ⟨v, rfl⟩
  change B *ᵥ (Z *ᵥ v) = 0 at h
  simpa only [Matrix.mulVec_mulVec, Matrix.zero_mulVec] using h

/-- Exact coordinates of every feasible direction. -/
theorem IsKernelFrame.mulVec_conjTranspose_mulVec {B : Matrix m n 𝕜} {Z : Matrix n r 𝕜}
    (hZ : IsKernelFrame B Z) {v : n → 𝕜} (hv : B *ᵥ v = 0) :
    Z *ᵥ (Zᴴ *ᵥ v) = v := by
  have hm : v ∈ LinearMap.range Z.mulVecLin := by
    rw [hZ.range_eq]
    exact hv
  obtain ⟨w, rfl⟩ := hm
  change Z *ᵥ (Zᴴ *ᵥ (Z *ᵥ w)) = Z *ᵥ w
  rw [Matrix.mulVec_mulVec w Zᴴ Z, hZ.orth.conjTranspose_mul_self, Matrix.one_mulVec]

/-- Constraint-space and null-space projections give an exact decomposition.
The full-row-rank hypothesis justifies the ordinary inverse in the formula. -/
theorem IsKernelFrame.decomposition {B : Matrix m n 𝕜} {Z : Matrix n r 𝕜}
    (hZ : IsKernelFrame B Z) (hB : IsUnit (B * Bᴴ)) (v : n → 𝕜) :
    v = Z *ᵥ (Zᴴ *ᵥ v) + Bᴴ *ᵥ ((B * Bᴴ)⁻¹ *ᵥ (B *ᵥ v)) := by
  let w := v - Bᴴ *ᵥ ((B * Bᴴ)⁻¹ *ᵥ (B *ᵥ v))
  have hw : B *ᵥ w = 0 := by
    dsimp only [w]
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hB), Matrix.one_mulVec,
      sub_self]
  have hZw : Zᴴ *ᵥ w = Zᴴ *ᵥ v := by
    dsimp only [w]
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    have hz : Zᴴ * Bᴴ = 0 := by
      rw [← Matrix.conjTranspose_mul, hZ.mul_eq_zero, Matrix.conjTranspose_zero]
    rw [hz, Matrix.zero_mulVec, sub_zero]
  have he := hZ.mulVec_conjTranspose_mulVec hw
  rw [hZw] at he
  dsimp only [w] at he
  linear_combination -he

/-- A vector orthogonal to all feasible directions lies in the adjoint
constraint range, with its explicit least-norm multiplier. -/
theorem IsKernelFrame.eq_conjTranspose_mulVec_of_conjTranspose_mulVec_eq_zero
    {B : Matrix m n 𝕜} {Z : Matrix n r 𝕜} (hZ : IsKernelFrame B Z)
    (hB : IsUnit (B * Bᴴ)) {v : n → 𝕜} (hv : Zᴴ *ᵥ v = 0) :
    v = Bᴴ *ᵥ ((B * Bᴴ)⁻¹ *ᵥ (B *ᵥ v)) := by
  simpa only [hv, Matrix.mulVec_zero, zero_add] using hZ.decomposition hB v

end NLAlib
