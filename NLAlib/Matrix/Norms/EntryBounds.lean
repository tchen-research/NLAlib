/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Matrix.Norms.Core
/-!
# Entries are bounded by the spectral norm

`|A i j| ≤ ‖A‖₂` for a real matrix (`abs_apply_le_specNorm`): the entry is a coordinate of
`A *ᵥ eⱼ`, whose Euclidean norm is at most `‖A‖₂`.-/


namespace NLAlib

open scoped Matrix.Norms.L2Operator in
/-- The norm of any entry of a real or complex matrix is bounded by its
spectral norm, on arbitrary finite index types. -/
theorem norm_apply_le_specNorm {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n 𝕜) (i : m) (j : n) :
    ‖A i j‖ ≤ specNorm A := by
  let e : EuclideanSpace 𝕜 n := EuclideanSpace.single j 1
  let y : EuclideanSpace 𝕜 m := WithLp.toLp 2 (Matrix.mulVec A e.ofLp)
  have hcoord : ‖y i‖ ≤ ‖y‖ := PiLp.norm_apply_le y i
  have hop : ‖y‖ ≤ specNorm A * ‖e‖ := Matrix.l2_opNorm_mulVec A e
  calc
    ‖A i j‖ = ‖y i‖ := by simp [y,e]
    _ ≤ ‖y‖ := hcoord
    _ ≤ specNorm A * ‖e‖ := hop
    _ = specNorm A := by simp [e]

open scoped Matrix.Norms.L2Operator in
/-- The absolute value of a real matrix entry is bounded by its spectral norm.-/
theorem abs_apply_le_specNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m n ℝ) (i : m) (j : n) : |A i j| ≤ specNorm A := by
  simpa only [Real.norm_eq_abs] using norm_apply_le_specNorm A i j

end NLAlib
