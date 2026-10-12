import NLAlib.Matrix.Basic.JacobiMinor
import NLAlib.Matrix.Inequalities.HadamardDeterminant
/-!
# Singleton complement minors and inverse Hadamard

Jacobi's identity identifies inverse diagonal entries with deleted principal
minors. Hadamard on the inverse gives the local inequality underlying Szász,
with equality exactly for a diagonal matrix.
Source: Horn--Johnson (2013), Lemma 7.8.8 and Theorem 7.8.11;
supports `hadamard-fischer-inequalities`.
-/

noncomputable section
open Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Deleting one principal coordinate gives the determinant times the
corresponding inverse diagonal entry, including a one-dimensional ambient
matrix with its empty complementary minor. Horn--Johnson (2013),
Lemma 7.8.8; helper for Szász's inequality. -/
theorem det_principal_complement_singleton_eq_det_mul_inv_diag
    (A : Matrix n n ℝ) (hA : IsUnit A.det) (i : n) :
    (A.toBlock (fun j => j ≠ i) (fun j => j ≠ i)).det = A.det * A⁻¹ i i := by
  classical
  let e : {j : n // j ≠ i} ⊕ {j : n // ¬j ≠ i} ≃ n := Equiv.sumCompl (fun j => j ≠ i)
  let : Subsingleton {j : n // ¬j ≠ i} := ⟨fun x y => Subtype.ext (by
    have hx : x.val = i := not_ne_iff.mp x.property
    have hy : y.val = i := not_ne_iff.mp y.property
    exact hx.trans hy.symm)⟩
  have h := det_inverse_complement_minor_eq_sign_mul_div A hA e e
  simp only [Equiv.self_trans_symm, Equiv.Perm.sign_refl, Units.val_one, Int.cast_one, one_mul] at h
  change (A⁻¹.toBlock (fun j => ¬j ≠ i) (fun j => ¬j ≠ i)).det =
    (A.toBlock (fun j => j ≠ i) (fun j => j ≠ i)).det / A.det at h
  rw [Matrix.det_eq_elem_of_subsingleton _ ⟨i, by simp⟩] at h
  change A⁻¹ i i = (A.toBlock (fun j => j ≠ i) (fun j => j ≠ i)).det / A.det at h
  rw [h]
  field_simp [hA.ne_zero]

/-- For an invertible matrix, diagonal structure is preserved and reflected
by inversion. Horn--Johnson (2013), Section 0.8;
helper for the equality case in inverse Hadamard. -/
theorem isDiag_inv_iff_of_isUnit {A : Matrix n n ℝ} (hA : IsUnit A) :
    A⁻¹.IsDiag ↔ A.IsDiag := by
  let : Invertible A := hA.invertible
  constructor
  · intro h
    rw [← Matrix.inv_inv_of_invertible A, ← h.diagonal_diag, Matrix.inv_diagonal]
    exact Matrix.isDiag_diagonal _
  · intro h
    rw [← h.diagonal_diag, Matrix.inv_diagonal]
    exact Matrix.isDiag_diagonal _

/-- The product of all one-coordinate-deleted principal minors is at least
the determinant to the dimension minus one. For positive definite matrices,
equality holds exactly for diagonal matrices. This is the local Szász step.
Horn--Johnson (2013), Lemma 7.8.8 and Theorem 7.8.11. -/
theorem det_pow_card_pred_le_prod_complement_singleton_and_eq_iff
    [Nonempty n] {A : Matrix n n ℝ} (hA : A.PosDef) :
    A.det ^ (Fintype.card n - 1) ≤
      ∏ i, (A.toBlock (fun j => j ≠ i) (fun j => j ≠ i)).det ∧
    (A.det ^ (Fintype.card n - 1) =
      (∏ i, (A.toBlock (fun j => j ≠ i) (fun j => j ≠ i)).det) ↔ A.IsDiag) := by
  have hAd := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hprod : (∏ i, (A.toBlock (fun j => j ≠ i) (fun j => j ≠ i)).det) =
      A.det ^ Fintype.card n * ∏ i, A⁻¹ i i := by
    simp_rw [det_principal_complement_singleton_eq_det_mul_inv_diag A hAd]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have hpow : A.det ^ (Fintype.card n - 1) = A.det ^ Fintype.card n * A⁻¹.det := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    nth_rw 2 [show Fintype.card n = (Fintype.card n - 1) + 1 by have := Fintype.card_pos (α := n); omega]
    rw [pow_succ, mul_assoc, mul_inv_cancel₀ hA.det_pos.ne', mul_one]
  have hpp : 0 < A.det ^ Fintype.card n := pow_pos hA.det_pos _
  rw [hprod, hpow]
  constructor
  · exact mul_le_mul_of_nonneg_left (det_le_prod_diag_of_posSemidef hA.inv.posSemidef) hpp.le
  · constructor
    · intro h
      have he := mul_left_cancel₀ hpp.ne' h
      exact (isDiag_inv_iff_of_isUnit hA.isUnit).mp
        ((det_eq_prod_diag_iff_isDiag_of_posDef hA.inv).mp he)
    · intro h
      have he := (det_eq_prod_diag_iff_isDiag_of_posDef hA.inv).mpr
        ((isDiag_inv_iff_of_isUnit hA.isUnit).mpr h)
      rw [he]

end NLAlib
