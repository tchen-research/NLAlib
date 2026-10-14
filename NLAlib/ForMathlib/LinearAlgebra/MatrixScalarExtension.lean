import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Linear independence under a field embedding

A left inverse for a matrix with independent columns remains a left inverse
after mapping its entries to an extension field. This avoids assumptions about
an ordered or infinite scalar field.
-/

noncomputable section
namespace Matrix

variable {K L m n : Type*} [Field K] [Field L]
variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Independent matrix columns remain independent after extending the scalar field. -/
theorem linearIndependent_cols_map (σ : K →+* L) {A : Matrix m n K}
    (hA : LinearIndependent K A.col) : LinearIndependent L (A.map σ).col := by
  have hinj : Function.Injective A.mulVecLin := Matrix.mulVec_injective_iff.mpr hA
  obtain ⟨g, hg⟩ := A.mulVecLin.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  let B := LinearMap.toMatrix' g
  have hBA : B * A = 1 := by
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
    change (LinearMap.toMatrix' g) *ᵥ (A *ᵥ v) = v
    rw [LinearMap.toMatrix'_mulVec]
    exact congrArg (fun f : (n → K) →ₗ[K] (n → K) => f v) hg
  have hmap : (B.map σ) * A.map σ = 1 := by
    rw [← Matrix.map_mul, hBA, Matrix.map_one _ (map_zero σ) (map_one σ)]
  apply Matrix.mulVec_injective_iff.mp
  intro x y hxy
  have h := congrArg (fun v => B.map σ *ᵥ v) hxy
  simpa only [Matrix.mulVec_mulVec, hmap, Matrix.one_mulVec] using h

end Matrix
