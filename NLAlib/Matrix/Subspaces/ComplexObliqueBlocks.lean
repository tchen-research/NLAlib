import NLAlib.Matrix.Subspaces.ComplexGramIsometry
import NLAlib.ForMathlib.Analysis.OrthonormalSum
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Range-adapted complex unitary blocks of an idempotent

Every complex idempotent is unitarily similar to `[I T; 0 0]`, where the
identity block has its actual rank. Zero and full rank are included.
-/

noncomputable section
open Module
open scoped InnerProductSpace Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- Complex orthonormal coordinates adapted to an idempotent's actual
range give the exact block form `[I T; 0 0]`, with identity size equal to
its actual rank. Both coordinate Gram identities are supplied.
Horn–Johnson 2013, Corollary 3.4.3.3; includes rank zero, full rank and
empty dimension.
atlas: cs-decomposition (partial) -/
theorem exists_unitary_idempotent_range_blocks {n : Type*}
    [Fintype n] [DecidableEq n] (P : Matrix n n ℂ) (hP : IsIdempotentElem P) :
    ∃ H : Matrix n (Fin P.rank ⊕ Fin (Fintype.card n - P.rank)) ℂ,
    ∃ T : Matrix (Fin P.rank) (Fin (Fintype.card n - P.rank)) ℂ,
      Hᴴ * H = 1 ∧ H * Hᴴ = 1 ∧ Hᴴ * P * H = Matrix.fromBlocks 1 T 0 0 := by
  classical
  let f := P.toEuclideanLin
  let R := LinearMap.range f
  let b := EuclideanSpace.basisFun n ℂ
  have hr : finrank ℂ R = P.rank := (P.rank_eq_finrank_range_toLin b.toBasis b.toBasis).symm
  have hs : finrank ℂ Rᗮ = Fintype.card n - P.rank := by
    have h := R.finrank_add_finrank_orthogonal
    rw [hr, finrank_euclideanSpace] at h
    omega
  let br := (stdOrthonormalBasis ℂ R).reindex (finCongr hr)
  let bs := (stdOrthonormalBasis ℂ Rᗮ).reindex (finCongr hs)
  obtain ⟨c, hcR, hcS⟩ := exists_orthonormalBasis_sum R br bs
  have hf : f.comp f = f := by
    have h := congrArg (fun M : Matrix n n ℂ => M.toEuclideanLin) (show P * P = P from hP)
    simpa only [f, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same] using h
  have hfix (x : R) : f x = x := by
    obtain ⟨y, hy⟩ := x.property
    rw [← hy]
    exact LinearMap.congr_fun hf y
  let F := f.toMatrix c.toBasis c.toBasis
  have h11 : F.toBlocks₁₁ = 1 := by
    ext i j
    simp only [F, Matrix.toBlocks₁₁, LinearMap.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.repr_apply_apply, hcR, hfix, ← Submodule.coe_inner, br.inner_eq_ite,
      Matrix.one_apply, Matrix.of_apply]
  have h21 : F.toBlocks₂₁ = 0 := by
    ext i j
    simp only [F, Matrix.toBlocks₂₁, LinearMap.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.repr_apply_apply, hcR, hcS, hfix, Matrix.zero_apply]
    exact Submodule.inner_left_of_mem_orthogonal (br j).property (bs i).property
  have h22 : F.toBlocks₂₂ = 0 := by
    ext i j
    simp only [F, Matrix.toBlocks₂₂, LinearMap.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.repr_apply_apply, hcS, Matrix.zero_apply]
    exact Submodule.inner_left_of_mem_orthogonal (LinearMap.mem_range_self f (bs j)) (bs i).property
  let H : Matrix n (Fin P.rank ⊕ Fin (Fintype.card n - P.rank)) ℂ := b.toBasis.toMatrix c.toBasis
  have hH : Hᴴ * H = 1 := b.toMatrix_orthonormalBasis_conjTranspose_mul_self c
  have hHt : H * Hᴴ = 1 := b.toMatrix_orthonormalBasis_self_mul_conjTranspose c
  have hback : c.toBasis.toMatrix b.toBasis = Hᴴ := by
    calc
      c.toBasis.toMatrix b.toBasis = c.toBasis.toMatrix b.toBasis * (H * Hᴴ) := by
        rw [hHt, Matrix.mul_one]
      _ = Hᴴ := by
        rw [← Matrix.mul_assoc]
        change (c.toBasis.toMatrix b.toBasis * b.toBasis.toMatrix c.toBasis) * Hᴴ = _
        rw [Basis.toMatrix_mul_toMatrix_flip, Matrix.one_mul]
  have hF : Hᴴ * P * H = F := by
    have h := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      c.toBasis b.toBasis c.toBasis b.toBasis f
    have hstd : f.toMatrix b.toBasis b.toBasis = P := LinearMap.toMatrix_toLin b.toBasis b.toBasis P
    rw [hback, hstd] at h
    exact h
  refine ⟨H, F.toBlocks₁₂, hH, hHt, ?_⟩
  rw [hF]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks F]
  rw [h11, h21, h22]

end NLAlib
