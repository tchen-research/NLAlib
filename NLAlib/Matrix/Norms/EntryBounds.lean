/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Matrix.Norms.Core
/-!
# Entries are bounded by the spectral norm

`|A i j| ≤ ‖A‖₂` for a real matrix (`abs_apply_le_specNorm`): the entry is a coordinate of
`A *ᵥ eⱼ`, whose Euclidean norm is at most `‖A‖₂`.

Source: ported from `SparseFockFormal.ConcreteLadderIteration.abs_entry_le_l2_opNorm`, commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

open scoped Matrix.Norms.L2Operator

namespace NLAlib

/-- A single entry of a real matrix is bounded by its spectral norm.

Source: ported from `SparseFockFormal.ConcreteLadderIteration.abs_entry_le_l2_opNorm`
(generalised to rectangular matrices), b9da2b5d96e5fd70252e9c6551aefc92643e7d0b;
supports `sparse-ose`. -/
theorem abs_apply_le_specNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m n ℝ) (i : m) (j : n) : |A i j| ≤ specNorm A := by
  rw [specNorm_eq_norm]
  let e : EuclideanSpace ℝ n := EuclideanSpace.single j 1
  let y : EuclideanSpace ℝ m :=
    (EuclideanSpace.equiv m ℝ).symm (Matrix.mulVec A e)
  have hcoord : ‖y i‖ ≤ ‖y‖ := PiLp.norm_apply_le y i
  have hop : ‖y‖ ≤ ‖A‖ * ‖e‖ := by
    simpa [y] using Matrix.l2_opNorm_mulVec A e
  calc
    |A i j| = ‖y i‖ := by
      simp [y, e, Real.norm_eq_abs]
    _ ≤ ‖y‖ := hcoord
    _ ≤ ‖A‖ * ‖e‖ := hop
    _ = ‖A‖ := by simp [e]

end NLAlib
