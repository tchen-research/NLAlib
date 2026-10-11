import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.LinearMap

/-!
# Rank subadditivity for finite rectangular matrices

The rank of a sum is bounded by the sum of the ranks. Source: Horn–Johnson,
Matrix Analysis, Section 0.4; supports `weyl-product-singular-values`.
-/

noncomputable section

namespace NLAlib

/-- The rank of a matrix sum is at most the sum of the ranks.
Horn–Johnson, Matrix Analysis, Section 0.4; arbitrary finite indices.
-/
theorem rank_add_le {m n K : Type*} [Field K] [Fintype m] [Fintype n]
    (A B : Matrix m n K) : (A + B).rank ≤ A.rank + B.rank := by
  change Module.finrank K (LinearMap.range (A + B).mulVecLin) ≤
    Module.finrank K (LinearMap.range A.mulVecLin) +
      Module.finrank K (LinearMap.range B.mulVecLin)
  rw [Matrix.mulVecLin_add]
  have h : LinearMap.range (A.mulVecLin + B.mulVecLin) ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin :=
    LinearMap.range_add_le A.mulVecLin B.mulVecLin
  exact (Submodule.finrank_mono h).trans
    (Submodule.finrank_add_le_finrank_add_finrank
      (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin))

end NLAlib
