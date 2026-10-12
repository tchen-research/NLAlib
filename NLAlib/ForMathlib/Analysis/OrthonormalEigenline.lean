import NLAlib.ForMathlib.Analysis.OrthonormalCons
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# An orthonormal eigenline and its compressed characteristic factor

A unit vector followed by an orthonormal basis of its orthogonal complement
is an orthonormal basis. For an eigenvector, the compression supplies exactly
the remaining characteristic factor.
-/

noncomputable section
open Module Polynomial
open scoped InnerProductSpace Matrix

namespace NLAlib

/-- A first-column eigenvalue factors out of the characteristic polynomial.
Source: Horn–Johnson (2013), §1.4; first-column Laplace expansion. -/
theorem charpoly_eq_X_sub_C_mul_succ_submatrix
    {R : Type*} [CommRing R] {k : ℕ} (M : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
    (μ : R) (hcol : ∀ i, M i 0 = if i = 0 then μ else 0) :
    M.charpoly = (X - C μ) * (M.submatrix Fin.succ Fin.succ).charpoly := by
  have hcharm : M.charmatrix.submatrix Fin.succ Fin.succ =
      (M.submatrix Fin.succ Fin.succ).charmatrix := by
    ext i j
    simp [Matrix.charmatrix_apply, Matrix.submatrix_apply, Matrix.diagonal_apply]
  rw [Matrix.charpoly, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, Matrix.charmatrix_apply_eq, hcol,
    ite_true, Fin.succAbove_zero, hcharm]
  have hzero (i : Fin k) : M.charmatrix i.succ 0 = 0 := by
    rw [Matrix.charmatrix_apply_ne _ _ _ (Fin.succ_ne_zero i), hcol,
      if_neg (Fin.succ_ne_zero i), C_0, neg_zero]
  simp only [hzero, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  rfl

/-- Compressing away a unit eigenvector removes exactly its characteristic
linear factor. Source: Horn–Johnson (2013), proof of Theorem 2.3.1; no
normality or simplicity assumption is needed. -/
theorem charpoly_eq_X_sub_C_mul_orthogonal_compression
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {k : ℕ} (f : Module.End 𝕜 E) {u : E} (hu : ‖u‖ = 1) {μ : 𝕜}
    (hfu : f u = μ • u) (hk : finrank 𝕜 E = k + 1) :
    f.charpoly = (X - C μ) *
      (((𝕜 ∙ u)ᗮ.orthogonalProjectionOnto.toLinearMap.comp
        (f.comp (𝕜 ∙ u)ᗮ.subtype)) : Module.End 𝕜 (𝕜 ∙ u)ᗮ).charpoly := by
  have hune : u ≠ 0 := by intro h; simp [h] at hu
  let W : Submodule 𝕜 E := (𝕜 ∙ u)ᗮ
  have hdim : finrank 𝕜 W = k := by
    have h := (𝕜 ∙ u).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton hune, hk] at h
    dsimp [W]
    omega
  let bW : OrthonormalBasis (Fin k) 𝕜 W := (stdOrthonormalBasis 𝕜 W).reindex (finCongr hdim)
  obtain ⟨b, hb₀, hbS⟩ := exists_orthonormalBasis_cons hk u hu bW
  let Cμ : Module.End 𝕜 W := W.orthogonalProjectionOnto.toLinearMap.comp (f.comp W.subtype)
  let M := f.toMatrix b.toBasis b.toBasis
  have hcol (i : Fin (k + 1)) : M i 0 = if i = 0 then μ else 0 := by
    simp only [M, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis, hb₀, hfu, map_smul]
    rw [← hb₀]
    change (μ • b.toBasis.repr (b.toBasis 0)) i = _
    rw [b.toBasis.repr_self]
    simp [Finsupp.single_apply, eq_comm]
  have htail : M.submatrix Fin.succ Fin.succ = Cμ.toMatrix bW.toBasis bW.toBasis := by
    ext i j
    simp only [M, Matrix.submatrix_apply, LinearMap.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.repr_apply_apply, hbS, Cμ, LinearMap.comp_apply,
      ContinuousLinearMap.coe_coe, Submodule.subtype_apply,
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  have h := charpoly_eq_X_sub_C_mul_succ_submatrix M μ hcol
  rw [htail, LinearMap.charpoly_toMatrix] at h
  simpa only [M, LinearMap.charpoly_toMatrix] using h

end NLAlib
