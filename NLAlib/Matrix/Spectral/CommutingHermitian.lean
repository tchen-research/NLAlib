import NLAlib.Matrix.Subspaces.OrthogonalProducts
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Matrix.Hermitian
/-!+# Unitary diagonalization of commuting Hermitian pairs

Collect orthonormal bases of the mutually orthogonal joint eigenspaces.
This gives the real and complex forms uniformly, including repeated
eigenvalues and empty dimensions.
-/
noncomputable section
open Matrix Module
open scoped Matrix
namespace NLAlib
set_option maxHeartbeats 1200000
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- A commuting Hermitian pair has one orthonormal eigenvector matrix,
and both diagonal lists are real. Horn–Johnson (2013), Theorem 2.5.5. -/
theorem exists_unitary_congruence_diagonal_of_commute {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) :
    ∃ (U : Matrix n n 𝕜) (a b : n → ℝ), HasOrthonormalCols U ∧
      Uᴴ * A * U = diagonal (fun i => (a i : 𝕜)) ∧
      Uᴴ * B * U = diagonal (fun i => (b i : 𝕜)) := by
  classical
  let a := A.toEuclideanLin
  let b := B.toEuclideanLin
  have ha : a.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hb : b.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
  have hab : Commute a b := by
    change a.comp b = b.comp a
    simpa only [a, b, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same] using
      congrArg (fun M : Matrix n n 𝕜 => M.toEuclideanLin) hAB.eq
  let W : (𝕜 × 𝕜) → Submodule 𝕜 (EuclideanSpace 𝕜 n) :=
    fun i => Module.End.eigenspace a i.2 ⊓ Module.End.eigenspace b i.1
  have hsum : DirectSum.IsInternal W := ha.directSum_isInternal_of_commute hb hab
  have horth : OrthogonalFamily 𝕜 (fun i => W i) (fun i => (W i).subtypeₗᵢ) :=
    ha.orthogonalFamily_eigenspace_inf_eigenspace hb
  let s := Σ i : 𝕜 × 𝕜, Fin (Module.finrank 𝕜 (W i))
  let c₀ := hsum.collectedBasis (fun i => (stdOrthonormalBasis 𝕜 (W i)).toBasis)
  let : Fintype s := FiniteDimensional.fintypeBasisIndex c₀
  have hc₀ : Orthonormal 𝕜 c₀ := by
    simpa only [c₀, DirectSum.IsInternal.collectedBasis_coe, Submodule.coe_subtypeₗᵢ] using!
      horth.orthonormal_sigma_orthonormal
        (show ∀ i, Orthonormal 𝕜 (stdOrthonormalBasis 𝕜 (W i)).toBasis by simp)
  let c := c₀.toOrthonormalBasis hc₀
  have hc : Fintype.card s = Fintype.card n := by
    rw [← Module.finrank_eq_card_basis c.toBasis]
    exact finrank_euclideanSpace
  let e : s ≃ n := Fintype.equivOfCardEq hc
  let v : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) := c.reindex e
  let U : Matrix n n 𝕜 := Matrix.of (fun i j => v j i)
  have hU : HasOrthonormalCols U := by
    apply (hasOrthonormalCols_iff_orthonormal U).mpr
    have he : (fun j => WithLp.toLp 2 (U.col j)) = v := by
      funext j
      rfl
    rw [he]
    exact v.orthonormal
  have hcol (j : n) : v j ∈ W (e.symm j).1 := by
    simpa only [v, c, OrthonormalBasis.reindex_apply, Basis.coe_toOrthonormalBasis] using
      hsum.collectedBasis_mem (fun i => (stdOrthonormalBasis 𝕜 (W i)).toBasis) (e.symm j)
  have hAU : A * U = U * diagonal (fun j => (e.symm j).1.2) := by
    ext i j
    have he := Module.End.mem_eigenspace_iff.mp (hcol j).1
    have hi := congrArg (fun x : EuclideanSpace 𝕜 n => x i) he
    rw [Matrix.mul_diagonal]
    simpa [a, U, Matrix.toLpLin_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      smul_eq_mul, mul_comm] using hi
  have hBU : B * U = U * diagonal (fun j => (e.symm j).1.1) := by
    ext i j
    have he := Module.End.mem_eigenspace_iff.mp (hcol j).2
    have hi := congrArg (fun x : EuclideanSpace 𝕜 n => x i) he
    rw [Matrix.mul_diagonal]
    simpa [b, U, Matrix.toLpLin_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      smul_eq_mul, mul_comm] using hi
  have hUA : Uᴴ * A * U = diagonal (fun j => (e.symm j).1.2) := by
    rw [Matrix.mul_assoc, hAU, ← Matrix.mul_assoc, hU.conjTranspose_mul_self, Matrix.one_mul]
  have hUB : Uᴴ * B * U = diagonal (fun j => (e.symm j).1.1) := by
    rw [Matrix.mul_assoc, hBU, ← Matrix.mul_assoc, hU.conjTranspose_mul_self, Matrix.one_mul]
  have hreal (M : Matrix n n 𝕜) (hM : M.IsHermitian) (d : n → 𝕜)
      (hd : Uᴴ * M * U = diagonal d) (i : n) : (RCLike.re (d i) : 𝕜) = d i := by
    have hh : (diagonal d).IsHermitian := hd ▸ Matrix.isHermitian_conjTranspose_mul_mul U hM
    exact RCLike.conj_eq_iff_re.mp (by simpa using congrFun (congrFun hh.eq i) i)
  refine ⟨U, fun i => RCLike.re (e.symm i).1.2,
    fun i => RCLike.re (e.symm i).1.1, hU, ?_, ?_⟩
  · simpa only [hreal A hA _ hUA] using hUA
  · simpa only [hreal B hB _ hUB] using hUB

end NLAlib
