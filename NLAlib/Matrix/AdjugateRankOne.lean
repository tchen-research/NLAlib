import NLAlib.Matrix.EigenvalueSimplicity
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The nonzero rank-one adjugate at nullity one

Rank normal form proves that nullity one gives a nonzero cofactor. The two
adjugate identities then force every column and row into the corresponding
one-dimensional kernels.
Source: Horn–Johnson (2013), Theorem 1.4.12.
-/

noncomputable section
open Module
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

omit [DecidableEq n] in
/-- Transposition preserves the nullity of a square matrix over any field.
Source: Horn–Johnson (2013), §0.4; row rank equals column rank. -/
theorem finrank_ker_mulVecLin_transpose_eq (M : Matrix n n K) :
    finrank K (LinearMap.ker Mᵀ.mulVecLin) = finrank K (LinearMap.ker M.mulVecLin) := by
  have hM := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hT := LinearMap.finrank_range_add_finrank_ker Mᵀ.mulVecLin
  change M.rank + _ = _ at hM
  change Mᵀ.rank + _ = _ at hT
  rw [Matrix.rank_transpose] at hT
  omega

/-- A square matrix of nullity one has a nonzero adjugate, including size
one where the cofactor is the empty determinant. Source: Horn–Johnson
(2013), Theorem 1.4.12; rank normal form gives a nonzero cofactor. -/
theorem adjugate_ne_zero_of_finrank_ker_eq_one (M : Matrix n n K)
    (hdim : finrank K (LinearMap.ker M.mulVecLin) = 1) : M.adjugate ≠ 0 := by
  classical
  have hr := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  change M.rank + finrank K (LinearMap.ker M.mulVecLin) = finrank K (n → K) at hr
  rw [hdim, Module.finrank_fintype_fun_eq_card] at hr
  have hnull : Fintype.card n - M.rank = 1 := by omega
  obtain ⟨V, U, e, hV, hU, hM⟩ := Matrix.exists_rank_normal_form M
  let j : Fin M.rank ⊕ Fin (Fintype.card n - M.rank) := Sum.inr ⟨0, by omega⟩
  let d : Fin M.rank ⊕ Fin (Fintype.card n - M.rank) → K := Sum.elim (fun _ => 1) (fun _ => 0)
  have hblock : (Matrix.fromBlocks (1 : Matrix (Fin M.rank) (Fin M.rank) K) 0 0
      (0 : Matrix (Fin (Fintype.card n - M.rank)) (Fin (Fintype.card n - M.rank)) K)) =
      Matrix.diagonal d := by
    simpa only [Matrix.diagonal_one, Matrix.diagonal_zero] using
      Matrix.fromBlocks_diagonal (fun _ : Fin M.rank => (1 : K))
        (fun _ : Fin (Fintype.card n - M.rank) => (0 : K))
  have hdiag : (Matrix.diagonal d).adjugate j j = 1 := by
    rw [Matrix.adjugate_diagonal, Matrix.diagonal_apply_eq]
    apply Finset.prod_eq_one
    intro k hk
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    cases k with
    | inl k => rfl
    | inr k =>
      exfalso
      apply hkj
      congr 1
      apply Fin.ext
      have := k.isLt
      dsimp [j]
      omega
  intro hzero
  have hadj : (V * M * U).adjugate = 0 := by
    rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, hzero,
      Matrix.zero_mul, Matrix.mul_zero]
  rw [hM, hblock, Matrix.adjugate_submatrix_equiv_self] at hadj
  have hj := congrArg (fun N => N (e.symm j) (e.symm j)) hadj
  have hj' : (Matrix.diagonal d).adjugate j j = 0 := by simpa using hj
  exact one_ne_zero (hdiag.symm.trans hj')

/-- With one-dimensional nullspace, the adjugate is a nonzero scalar times
the outer product of arbitrary nonzero right and left nullvectors. Source:
Horn–Johnson (2013), Theorem 1.4.12; no algebraic simplicity is required. -/
theorem exists_adjugate_eq_smul_vecMulVec_of_finrank_ker_eq_one
    (M : Matrix n n K) {x y : n → K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hMx : M *ᵥ x = 0) (hyM : y ᵥ* M = 0)
    (hdim : finrank K (LinearMap.ker M.mulVecLin) = 1) :
    ∃ γ : K, γ ≠ 0 ∧ M.adjugate = γ • Matrix.vecMulVec x y := by
  have hdet : M.det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, hMx⟩
  have hspan : K ∙ x = LinearMap.ker M.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem x _).mpr hMx)
      (by rw [finrank_span_singleton hx, hdim])
  have hspanT : K ∙ y = LinearMap.ker Mᵀ.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem y _).mpr (by
        simpa only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose] using hyM))
      (by rw [finrank_span_singleton hy, finrank_ker_mulVecLin_transpose_eq, hdim])
  have hMadj : M * M.adjugate = 0 := by rw [Matrix.mul_adjugate, hdet, zero_smul]
  have hadjM : M.adjugate * M = 0 := by rw [Matrix.adjugate_mul, hdet, zero_smul]
  have hcols (j : n) : ∃ c : K, c • x = Matrix.col M.adjugate j := by
    have hk : Matrix.col M.adjugate j ∈ LinearMap.ker M.mulVecLin := by
      funext i
      exact congrArg (fun N : Matrix n n K => N i j) hMadj
    rw [← hspan] at hk
    exact Submodule.mem_span_singleton.mp hk
  choose c hc using hcols
  have hadj : M.adjugate = Matrix.vecMulVec x c := by
    ext i j
    have h := congrFun (hc j) i
    simpa only [Matrix.col_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      mul_comm] using h.symm
  have hcM : c ᵥ* M = 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    rw [hadj, Matrix.vecMulVec_mul] at hadjM
    funext j
    have h := congrArg (fun N : Matrix n n K => N i j) hadjM
    exact (mul_eq_zero.mp h).resolve_left hi
  have hcKer : c ∈ LinearMap.ker Mᵀ.mulVecLin := by
    simpa only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose] using hcM
  rw [← hspanT] at hcKer
  obtain ⟨γ, hγ⟩ := Submodule.mem_span_singleton.mp hcKer
  have hform : M.adjugate = γ • Matrix.vecMulVec x y := by
    rw [hadj, ← hγ, Matrix.vecMulVec_smul]
  refine ⟨γ, ?_, hform⟩
  intro hzero
  apply adjugate_ne_zero_of_finrank_ker_eq_one M hdim
  rw [hform, hzero, zero_smul]

end NLAlib
