import NLAlib.Matrix.Basic.MoorePenrose

/-!
# Moore--Penrose inverse under real scalar extension

Embedding a real matrix into an RCLike field preserves the four Penrose identities,
and uniqueness therefore identifies the actual Moore--Penrose inverse after extension.
No rank hypothesis is needed. Source: Horn--Johnson, Matrix Analysis, Section 7.3.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- Extending a real matrix to real or complex scalars commutes with its Moore--Penrose
inverse, including deficient and empty matrices. -/
theorem moorePenroseInverse_map_ofReal {m n 𝕜 : Type*} [Fintype m] [Fintype n]
    [RCLike 𝕜] (A : Matrix m n ℝ) :
    moorePenroseInverse (A.map (algebraMap ℝ 𝕜)) =
      (moorePenroseInverse A).map (algebraMap ℝ 𝕜) := by
  let f := algebraMap ℝ 𝕜
  have hf : Function.Semiconj f star star := by intro r; simp [f]
  apply (isMoorePenroseInverse (A.map f)).unique
  have h := isMoorePenroseInverse A
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Matrix.map_mul, ← Matrix.map_mul, h.mul_mul_eq]
  · rw [← Matrix.map_mul, ← Matrix.map_mul, h.inv_mul_inv_eq]
  · rw [← Matrix.map_mul, ← Matrix.conjTranspose_map f hf, h.conjTranspose_mul_eq]
  · rw [← Matrix.map_mul, ← Matrix.conjTranspose_map f hf, h.conjTranspose_inv_mul_eq]

end NLAlib
