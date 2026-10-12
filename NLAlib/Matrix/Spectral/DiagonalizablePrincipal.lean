import NLAlib.Matrix.Spectral.DiagonalizableBlocks
/-!
# Eigenvalue multiplicity and principal submatrices

An eigenspace whose dimension exceeds the number of removed coordinates
contains a nonzero vector supported on the retained coordinates. This gives
an eigenvector of the corresponding principal submatrix.
Source: Horn–Johnson (2013), Theorem 1.4.10.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- An eigenvalue survives principal compression whenever its geometric
multiplicity exceeds the number of removed coordinates. Source:
Horn–Johnson (2013), Theorem 1.4.10; the field and finite index type are
arbitrary and no diagonalizability hypothesis is needed.
atlas: diagonalizable-def (partial) -/
theorem mem_spectrum_principal_submatrix_of_finrank_eigenspace_gt
    (A : Matrix n n K) (μ : K) (s : Finset n)
    (hdim : Fintype.card n - s.card < Module.finrank K (Module.End.eigenspace A.toLin' μ)) :
    μ ∈ spectrum K (A.submatrix (fun j : s => j.val) (fun j : s => j.val)) := by
  classical
  let W := Module.End.eigenspace A.toLin' μ
  let T : W →ₗ[K] ({j : n // j ∉ s} → K) :=
    { toFun x := fun j => x.val j.val
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hker : T.ker ≠ ⊥ := by
    intro hzero
    have hrank := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hzero)
    have hcard : Module.finrank K ({j : n // j ∉ s} → K) = Fintype.card n - s.card := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_subtype_compl, Fintype.card_coe]
    rw [hcard] at hrank
    exact (not_le_of_gt hdim) hrank
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hout (j : n) (hj : j ∉ s) : v.val j = 0 := congrFun hv ⟨j, hj⟩
  let w : s → K := fun j => v.val j.val
  have hw : w ≠ 0 := by
    intro hwzero
    apply hv0
    apply Subtype.ext
    funext j
    by_cases hj : j ∈ s
    · exact congrFun hwzero ⟨j, hj⟩
    · exact hout j hj
  have heig : A *ᵥ v.val = μ • v.val := Module.End.mem_eigenspace_iff.mp v.property
  have hAw : A.submatrix (fun j : s => j.val) (fun j : s => j.val) *ᵥ w = μ • w := by
    funext i
    have hsum := Fintype.sum_subtype_add_sum_subtype (fun j : n => j ∈ s)
      (fun j => A i.val j * v.val j)
    have hzero : (∑ j : {j : n // j ∉ s}, A i.val j.val * v.val j.val) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [hout j.val j.property, mul_zero]
    rw [hzero, add_zero] at hsum
    change (∑ j : s, A i.val j.val * v.val j.val) = μ * v.val i.val
    convert! hsum.trans (congrFun heig i.val) using 1
    congr 1
    ext j
    simp
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨w, hw, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hAw, sub_self]

/-- Geometric multiplicity at least `k` forces an eigenvalue into every
principal submatrix of order at least `n-k+1`. Source: Horn–Johnson (2013),
Theorem 1.4.10; the equivalent natural-number condition `n < |s| + k`
avoids truncated subtraction and includes all edge cases.
atlas: diagonalizable-def (partial) -/
theorem mem_spectrum_principal_submatrix_of_le_finrank_eigenspace
    (A : Matrix n n K) (μ : K) (s : Finset n) (k : ℕ)
    (hk : k ≤ Module.finrank K (Module.End.eigenspace A.toLin' μ))
    (hs : Fintype.card n < s.card + k) :
    μ ∈ spectrum K (A.submatrix (fun j : s => j.val) (fun j : s => j.val)) :=
  mem_spectrum_principal_submatrix_of_finrank_eigenspace_gt A μ s (by
    have := s.card_le_univ
    omega)

end NLAlib
