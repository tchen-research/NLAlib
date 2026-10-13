import NLAlib.Matrix.Subspaces.Projections
/-!
# An orthonormal basis matrix for any subspace

`orthonormalBasisMatrix S`: a canonical matrix with orthonormal columns and range `S`, for any
subspace `S ⊆ 𝕜ᵐ` (columns indexed by `Fin (finrank S)`), built from Mathlib's
`stdOrthonormalBasis`, so every Krylov space has an orthonormal basis with no hypothesis
(`hasOrthonormalCols_orthonormalBasisMatrix`, `range_orthonormalBasisMatrix`).

Golub–Van Loan 2013, §5.4 (orthonormal bases of subspaces); `docs/KRYLOV_DEFINITIONS.md` §3.1.
Atlas: `orthonormal-basis-matrix`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m : Type*} [Fintype m]

omit [Fintype m] in
/-- `S` transported to `EuclideanSpace` (internal). -/
private def toEuclideanSubmodule (S : Submodule 𝕜 (m → 𝕜)) :
    Submodule 𝕜 (EuclideanSpace 𝕜 m) :=
  S.map (WithLp.linearEquiv 2 𝕜 (m → 𝕜)).symm.toLinearMap

omit [Fintype m] in
private lemma finrank_toEuclideanSubmodule (S : Submodule 𝕜 (m → 𝕜)) :
    Module.finrank 𝕜 (toEuclideanSubmodule S) = Module.finrank 𝕜 S :=
  LinearEquiv.finrank_map_eq _ _

/-- Mathlib's `stdOrthonormalBasis` of `S`, reindexed by `Fin (finrank S)` (internal). -/
private def euclideanBasis (S : Submodule 𝕜 (m → 𝕜)) :
    OrthonormalBasis (Fin (Module.finrank 𝕜 S)) 𝕜 (toEuclideanSubmodule S) :=
  (stdOrthonormalBasis 𝕜 (toEuclideanSubmodule S)).reindex
    (finCongr (finrank_toEuclideanSubmodule S))

/-- A canonical matrix whose columns form an orthonormal basis of the subspace `S ⊆ 𝕜ᵐ`, indexed
by `Fin (finrank S)`; built from Mathlib's `stdOrthonormalBasis`. It gives every Krylov space (and
any other subspace) an orthonormal basis with no hypothesis. Golub–Van Loan 2013, §5.4.
atlas: orthonormal-basis-matrix -/
def orthonormalBasisMatrix (S : Submodule 𝕜 (m → 𝕜)) : Matrix m (Fin (Module.finrank 𝕜 S)) 𝕜 :=
  Matrix.of fun i j => (euclideanBasis S j : EuclideanSpace 𝕜 m).ofLp i

/-- `orthonormalBasisMatrix S` has orthonormal columns. Golub–Van Loan 2013, §5.4.
atlas: orthonormal-basis-matrix -/
theorem hasOrthonormalCols_orthonormalBasisMatrix (S : Submodule 𝕜 (m → 𝕜)) :
    HasOrthonormalCols (orthonormalBasisMatrix S) := by
  ext j k
  have h := (euclideanBasis S).orthonormal
  rw [orthonormal_iff_ite] at h
  have := h j k
  rw [Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct] at this
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, orthonormalBasisMatrix, Matrix.of_apply,
    Matrix.one_apply]
  rw [← this]
  simp [dotProduct, mul_comm]

/-- The columns of `orthonormalBasisMatrix S` span `S`: `range Q = S`. Golub–Van Loan 2013, §5.4.
atlas: orthonormal-basis-matrix -/
theorem range_orthonormalBasisMatrix (S : Submodule 𝕜 (m → 𝕜)) :
    LinearMap.range (orthonormalBasisMatrix S).mulVecLin = S := by
  rw [Matrix.range_mulVecLin]
  have hcols : Set.range (orthonormalBasisMatrix S).col =
      ⇑((WithLp.linearEquiv 2 𝕜 (m → 𝕜)).toLinearMap ∘ₗ (toEuclideanSubmodule S).subtype) ''
        Set.range (euclideanBasis S) := by
    rw [← Set.range_comp]; rfl
  rw [hcols, ← Submodule.map_span, ← (euclideanBasis S).coe_toBasis, Module.Basis.span_eq,
    Submodule.map_comp, Submodule.map_subtype_top, toEuclideanSubmodule, ← Submodule.map_comp]
  simp

end NLAlib
