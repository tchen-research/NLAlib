import NLAlib.Matrix.Inequalities.OverlappingBlockDeterminant
import NLAlib.Matrix.Basic.PositiveDefiniteClosure
/-!
# Koteljanski's inequality for arbitrary principal index sets

Disjoint coordinate partitions identify the common-index Schur complement
with the usual principal union/intersection inequality and equality case.
Source: Horn--Johnson (2013), Theorem 7.8.9;
atlas `hadamard-fischer-inequalities`.
-/

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [DecidableEq n]

/-- Splitting a principal set into two disjoint parts identifies its
determinant with the corresponding symmetric block determinant.
Horn--Johnson (2013), Section 7.8; helper for overlapping principal minors. -/
theorem det_principal_union_eq_det_fromBlocks {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (s t : Finset n) (hst : Disjoint s t) :
    (A.toBlock (· ∈ s ∪ t) (· ∈ s ∪ t)).det =
      (fromBlocks (A.toBlock (· ∈ s) (· ∈ s)) (A.toBlock (· ∈ s) (· ∈ t))
        (A.toBlock (· ∈ s) (· ∈ t))ᵀ (A.toBlock (· ∈ t) (· ∈ t))).det := by
  classical
  let e := Equiv.Finset.union s t hst
  have hsym (i j : n) : A i j = A j i := by simpa using hA.apply j i
  have hm : (A.toBlock (· ∈ s ∪ t) (· ∈ s ∪ t)).submatrix e e =
      fromBlocks (A.toBlock (· ∈ s) (· ∈ s)) (A.toBlock (· ∈ s) (· ∈ t))
        (A.toBlock (· ∈ s) (· ∈ t))ᵀ (A.toBlock (· ∈ t) (· ∈ t)) := by
    ext i j
    cases i <;> cases j <;> first | rfl | exact hsym _ _
  rw [← hm, Matrix.det_submatrix_equiv_self]

/-- Three pairwise disjoint principal sets satisfy the overlapping
determinant inequality; positive definite equality is the exact zero cross
Schur block after eliminating the shared set.
Horn--Johnson (2013), Theorem 7.8.9; helper for union/intersection notation. -/
theorem det_principal_three_sets_le_and_eq_iff {A : Matrix n n ℝ} (hA : A.PosDef)
    (I J K : Finset n) (hIJ : Disjoint I J) (hIK : Disjoint I K) (hJK : Disjoint J K) :
    (A.toBlock (· ∈ I ∪ (J ∪ K)) (· ∈ I ∪ (J ∪ K))).det * (A.toBlock (· ∈ I) (· ∈ I)).det ≤
      (A.toBlock (· ∈ I ∪ J) (· ∈ I ∪ J)).det * (A.toBlock (· ∈ I ∪ K) (· ∈ I ∪ K)).det ∧
    ((A.toBlock (· ∈ I ∪ (J ∪ K)) (· ∈ I ∪ (J ∪ K))).det * (A.toBlock (· ∈ I) (· ∈ I)).det =
      (A.toBlock (· ∈ I ∪ J) (· ∈ I ∪ J)).det * (A.toBlock (· ∈ I ∪ K) (· ∈ I ∪ K)).det ↔
      A.toBlock (· ∈ J) (· ∈ K) -
        A.toBlock (· ∈ J) (· ∈ I) * (A.toBlock (· ∈ I) (· ∈ I))⁻¹ *
          A.toBlock (· ∈ I) (· ∈ K) = 0) := by
  classical
  let P := A.toBlock (· ∈ I) (· ∈ I)
  let U := A.toBlock (· ∈ I) (· ∈ J)
  let V := A.toBlock (· ∈ I) (· ∈ K)
  let D := A.toBlock (· ∈ J) (· ∈ J)
  let E := A.toBlock (· ∈ J) (· ∈ K)
  let F := A.toBlock (· ∈ K) (· ∈ K)
  let H := fromBlocks P (fromCols U V) (fromCols U V)ᵀ (fromBlocks D E Eᵀ F)
  have hIJK : Disjoint I (J ∪ K) := Finset.disjoint_union_right.mpr ⟨hIJ, hIK⟩
  let eJK := Equiv.Finset.union J K hJK
  let e : (I ⊕ (J ⊕ K)) ≃ (I ∪ (J ∪ K) : Finset n) :=
    (Equiv.sumCongr (Equiv.refl I) eJK).trans (Equiv.Finset.union I (J ∪ K) hIJK)
  let f : I ⊕ (J ⊕ K) → n := fun i => (e i).val
  have hsym (i j : n) : A i j = A j i := by simpa using hA.isHermitian.apply j i
  have hRep : A.submatrix f f = H := by
    ext i j
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
      first | rfl | exact hsym _ _
  have hH : H.PosDef := by
    rw [← hRep]
    exact hA.submatrix (Subtype.val_injective.comp e.injective)
  have hDetH : H.det = (A.toBlock (· ∈ I ∪ (J ∪ K)) (· ∈ I ∪ (J ∪ K))).det := by
    rw [← hRep]
    exact Matrix.det_submatrix_equiv_self e (A.toBlock (· ∈ I ∪ (J ∪ K)) (· ∈ I ∪ (J ∪ K)))
  have hUt : Uᵀ = A.toBlock (· ∈ J) (· ∈ I) := by
    ext i j
    exact hsym _ _
  have h := det_overlapping_blocks_le_and_eq_iff P U V D E F hH
  change (H.det * P.det ≤ _ ∧ (H.det * P.det = _ ↔ _)) at h
  rw [hDetH, ← det_principal_union_eq_det_fromBlocks hA.isHermitian I J hIJ,
    ← det_principal_union_eq_det_fromBlocks hA.isHermitian I K hIK, hUt] at h
  exact h

/-- Koteljanski's principal-minor inequality and its exact positive-definite
equality case: eliminate the intersection, then the cross block between
the two exclusive index sets must vanish. Empty intersections are included.
Horn--Johnson (2013), Theorem 7.8.9.
atlas: hadamard-fischer-inequalities (partial) -/
theorem det_principal_union_mul_inter_le_and_eq_iff_of_posDef
    {A : Matrix n n ℝ} (hA : A.PosDef) (α β : Finset n) :
    (A.toBlock (· ∈ α ∪ β) (· ∈ α ∪ β)).det * (A.toBlock (· ∈ α ∩ β) (· ∈ α ∩ β)).det ≤
      (A.toBlock (· ∈ α) (· ∈ α)).det * (A.toBlock (· ∈ β) (· ∈ β)).det ∧
    ((A.toBlock (· ∈ α ∪ β) (· ∈ α ∪ β)).det * (A.toBlock (· ∈ α ∩ β) (· ∈ α ∩ β)).det =
      (A.toBlock (· ∈ α) (· ∈ α)).det * (A.toBlock (· ∈ β) (· ∈ β)).det ↔
      A.toBlock (· ∈ α \ β) (· ∈ β \ α) -
        A.toBlock (· ∈ α \ β) (· ∈ α ∩ β) * (A.toBlock (· ∈ α ∩ β) (· ∈ α ∩ β))⁻¹ *
          A.toBlock (· ∈ α ∩ β) (· ∈ β \ α) = 0) := by
  have hij : Disjoint (α ∩ β) (α \ β) := by simp [Finset.disjoint_left]; aesop
  have hik : Disjoint (α ∩ β) (β \ α) := by simp [Finset.disjoint_left]; aesop
  have hjk : Disjoint (α \ β) (β \ α) := by simp [Finset.disjoint_left]; aesop
  have hu : (α ∩ β) ∪ ((α \ β) ∪ (β \ α)) = α ∪ β := by ext i; simp; tauto
  have ha : (α ∩ β) ∪ (α \ β) = α := by ext i; simp; tauto
  have hb : (α ∩ β) ∪ (β \ α) = β := by ext i; simp; tauto
  let D (s : Finset n) : ℝ := (A.toBlock (· ∈ s) (· ∈ s)).det
  have hh := det_principal_three_sets_le_and_eq_iff hA
    (α ∩ β) (α \ β) (β \ α) hij hik hjk
  change D ((α ∩ β) ∪ ((α \ β) ∪ (β \ α))) * D (α ∩ β) ≤
      D ((α ∩ β) ∪ (α \ β)) * D ((α ∩ β) ∪ (β \ α)) ∧
    (D ((α ∩ β) ∪ ((α \ β) ∪ (β \ α))) * D (α ∩ β) =
      D ((α ∩ β) ∪ (α \ β)) * D ((α ∩ β) ∪ (β \ α)) ↔ _) at hh
  rw [hu, ha, hb] at hh
  exact hh

/-- Koteljanski's principal-minor inequality extends to all PSD matrices by
positive identity perturbation and determinant continuity. Its SPD equality
condition is deliberately kept in the separate theorem above.
Horn--Johnson (2013), Theorem 7.8.9 and semidefinite extension.
atlas: hadamard-fischer-inequalities (partial) -/
theorem det_principal_union_mul_inter_le_of_posSemidef
    {A : Matrix n n ℝ} (hA : A.PosSemidef) (α β : Finset n) :
    (A.toBlock (· ∈ α ∪ β) (· ∈ α ∪ β)).det * (A.toBlock (· ∈ α ∩ β) (· ∈ α ∩ β)).det ≤
      (A.toBlock (· ∈ α) (· ∈ α)).det * (A.toBlock (· ∈ β) (· ∈ β)).det := by
  apply le_of_posSemidef_of_continuous_of_forall_posDef (f := fun M : Matrix n n ℝ =>
    (M.toBlock (· ∈ α ∪ β) (· ∈ α ∪ β)).det * (M.toBlock (· ∈ α ∩ β) (· ∈ α ∩ β)).det)
    (g := fun M : Matrix n n ℝ => (M.toBlock (· ∈ α) (· ∈ α)).det * (M.toBlock (· ∈ β) (· ∈ β)).det)
    (by unfold Matrix.toBlock; fun_prop) (by unfold Matrix.toBlock; fun_prop)
    (fun M hM => (det_principal_union_mul_inter_le_and_eq_iff_of_posDef hM α β).1) hA

end NLAlib
