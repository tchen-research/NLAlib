import NLAlib.Matrix.Spectral.RealInvariantSubspace
import NLAlib.Matrix.Spectral.QuasiTriangular
import NLAlib.ForMathlib.Analysis.OrthonormalSum
/-!
# Orthogonal real Schur forms

Invariant real lines and planes yield an orthonormal basis with consecutive
diagonal blocks of size at most two, in all finite dimensions.
-/

noncomputable section
open Module
open scoped InnerProductSpace Matrix
namespace NLAlib

/-- Prefixing a block of size at most two to a quasitriangular tail
preserves the real Schur zero pattern, provided the lower left block vanishes.
Horn–Johnson 2013, Theorem 2.3.1; block induction helper. -/
theorem isUpperQuasiTriangular_of_small_leading_block {p q : ℕ} {K : Type*} [Zero K]
    {T : Matrix (Fin (p + q)) (Fin (p + q)) K} (hp : p ≤ 2)
    (hzero : ∀ i : Fin q, ∀ j : Fin p, T (Fin.natAdd p i) (Fin.castAdd q j) = 0)
    (htail : IsUpperQuasiTriangular (T.submatrix (Fin.natAdd p) (Fin.natAdd p))) :
    IsUpperQuasiTriangular T := by
  constructor
  · intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · intro h; have := i.isLt; simp only [Fin.val_castAdd] at h; omega
    · intro h; have := i.isLt; simp only [Fin.val_castAdd, Fin.val_natAdd] at h; omega
    · intro _; exact hzero i j
    · intro h; exact htail.1 i j (by simp only [Fin.val_natAdd] at h; omega)
  · intro i j l
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      refine Fin.addCases (fun l => ?_) (fun l => ?_) l
    · intro h₁ h₂; have := i.isLt; simp only [Fin.val_castAdd] at h₁ h₂; omega
    · intro h₁ h₂; have := j.isLt; simp only [Fin.val_castAdd, Fin.val_natAdd] at h₂; omega
    · intro h₁ _; have := i.isLt; simp only [Fin.val_castAdd, Fin.val_natAdd] at h₁; omega
    · intro h₁ _; have := i.isLt; simp only [Fin.val_castAdd, Fin.val_natAdd] at h₁; omega
    · intro _ _; exact Or.inl (hzero i j)
    · intro _ _; exact Or.inl (hzero i j)
    · intro _ _; exact Or.inr (hzero j l)
    · intro h₁ h₂
      exact htail.2 i j l (by simp only [Fin.val_natAdd] at h₁; omega)
        (by simp only [Fin.val_natAdd] at h₂; omega)

/-- Every finite-dimensional real endomorphism has an orthonormal basis
in which its matrix is upper quasitriangular, with one- and two-dimensional
diagonal blocks. Dimension zero is included. Horn–Johnson 2013,
Theorem 2.3.1; this statement records the block zero pattern. -/
theorem exists_orthonormalBasis_upper_quasi_triangular {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ) (T : Module.End ℝ E) (hk : finrank ℝ E = k) :
    ∃ b : OrthonormalBasis (Fin k) ℝ E,
      IsUpperQuasiTriangular (T.toMatrix b.toBasis b.toBasis) := by
  classical
  induction k using Nat.strong_induction_on generalizing E with
  | h k ih =>
    by_cases hk0 : k = 0
    · have : IsEmpty (Fin k) := by rw [hk0]; infer_instance
      exact ⟨(stdOrthonormalBasis ℝ E).reindex (finCongr hk),
        ⟨fun i => isEmptyElim i, fun i => isEmptyElim i⟩⟩
    have : Nontrivial E := Module.finrank_pos_iff.mp (by rw [hk]; omega)
    obtain ⟨P, hPdim, hP⟩ := exists_invariant_subspace_finrank_one_or_two T
    let p := finrank ℝ P
    let q := finrank ℝ Pᗮ
    have hsum : p + q = k := P.finrank_add_finrank_orthogonal.trans hk
    have hp : p ≤ 2 := by rcases hPdim with h | h <;> dsimp [p] <;> omega
    have hq : q < k := by rcases hPdim with h | h <;> dsimp [p] at hsum <;> omega
    let C : Module.End ℝ Pᗮ :=
      Pᗮ.orthogonalProjectionOnto.toLinearMap.comp (T.comp Pᗮ.subtype)
    obtain ⟨bQ, hbQ⟩ := ih q hq C rfl
    let bP := stdOrthonormalBasis ℝ P
    obtain ⟨b₀, hbP, hbQ'⟩ := exists_orthonormalBasis_sum P bP bQ
    let b₁ : OrthonormalBasis (Fin (p + q)) ℝ E := b₀.reindex finSumFinEquiv
    have hleft (i : Fin p) : b₁ (Fin.castAdd q i) = (bP i : E) := by
      simpa only [b₁, OrthonormalBasis.reindex_apply,
        finSumFinEquiv_symm_apply_castAdd] using hbP i
    have hright (i : Fin q) : b₁ (Fin.natAdd p i) = (bQ i : E) := by
      simpa only [b₁, p, OrthonormalBasis.reindex_apply,
        finSumFinEquiv_symm_apply_natAdd] using hbQ' i
    have htri : IsUpperQuasiTriangular (T.toMatrix b₁.toBasis b₁.toBasis) := by
      apply isUpperQuasiTriangular_of_small_leading_block hp
      · intro i j
        simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply, hleft, hright]
        exact Submodule.inner_left_of_mem_orthogonal (hP _ (bP j).property) (bQ i).property
      · have heq : (T.toMatrix b₁.toBasis b₁.toBasis).submatrix (Fin.natAdd p) (Fin.natAdd p) =
            C.toMatrix bQ.toBasis bQ.toBasis := by
          ext i j
          simp only [Matrix.submatrix_apply, LinearMap.toMatrix_apply,
            OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
            OrthonormalBasis.repr_apply_apply, hright, C, LinearMap.comp_apply,
            ContinuousLinearMap.coe_coe, Submodule.subtype_apply,
            Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
        rwa [heq]
    let b := b₁.reindex (finCongr hsum)
    refine ⟨b, ?_, ?_⟩
    · intro i j hij
      simpa only [b, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply,
        OrthonormalBasis.reindex_apply] using htri.1 ((finCongr hsum).symm i)
          ((finCongr hsum).symm j) (by simpa using hij)
    · intro i j l hij hjl
      simpa only [b, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply,
        OrthonormalBasis.reindex_apply] using htri.2 ((finCongr hsum).symm i)
          ((finCongr hsum).symm j) ((finCongr hsum).symm l)
            (by simpa using hij) (by simpa using hjl)

end NLAlib
