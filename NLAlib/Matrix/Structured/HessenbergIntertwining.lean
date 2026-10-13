import NLAlib.Matrix.Structured.Hessenberg
import NLAlib.Matrix.Factorizations.Triangular
import NLAlib.Matrix.Basic.Orthonormal

/-!
# Oriented Hessenberg intertwining and diagonal signs

Putting the known unreduced Hessenberg matrix on the right gives a direct flag induction.
Source: Golub–Van Loan, Theorem 7.4.2; matrix toolkit rederivations, `lem:intertwine`.
-/

noncomputable section

open Matrix Finset

namespace NLAlib

/-- An intertwiner fixing the first coordinate between two upper Hessenberg matrices is
upper triangular when the matrix on its right is unreduced.
Source: matrix toolkit rederivations, `lem:intertwine`. -/
theorem isUpperTriangular_of_hessenberg_intertwines {n : ℕ}
    {G H W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hG : IsUpperHessenberg G) (hH : IsUnreducedHessenberg H)
    (hcomm : G * W = W * H) (hcol : W.col 0 = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).col 0) :
    W.IsUpperTriangular := by
  have hcolumns : ∀ k : ℕ, ∀ j : Fin (n + 1), j.val = k → ∀ i : Fin (n + 1), j < i → W i j = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro j hj i hij
      by_cases hk0 : k = 0
      · have hj0 : j = 0 := Fin.ext (by simpa only [Fin.val_zero, hk0] using hj)
        subst j
        have h := congrFun hcol i
        change W i 0 = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i 0 at h
        rw [h, Matrix.one_apply_ne (by intro hi; subst i; exact lt_irrefl _ hij)]
      · let p : Fin (n + 1) := ⟨k - 1, by omega⟩
        have hkn : k - 1 < k := by omega
        have hleft : (∑ a, G i a * W a p) = 0 := by
          apply sum_eq_zero
          intro a ha
          by_cases hak : a.val < k
          · rw [hG i a (by have := hij; omega), zero_mul]
          · rw [ih (k - 1) hkn p rfl a (by dsimp [p]; exact Fin.mk_lt_mk.mpr (by omega)), mul_zero]
        have hright : (∑ a, W i a * H a p) = W i j * H j p := by
          apply sum_eq_single j
          · intro a ha haj
            by_cases hak : a.val < k
            · rw [ih a.val hak a rfl i (by have := hij; exact Fin.mk_lt_mk.mpr (by omega)), zero_mul]
            · rw [hH.1 a p (by
                have hne : a.val ≠ j.val := fun h => haj (Fin.ext h)
                dsimp [p]
                omega), mul_zero]
          · simp
        have h := congrFun (congrFun hcomm i) p
        rw [Matrix.mul_apply, Matrix.mul_apply, hleft, hright] at h
        exact (mul_eq_zero.mp h.symm).resolve_right (hH.2 j p (by dsimp [p]; omega))
  intro i j hij
  exact hcolumns j.val j rfl i hij

/-- An orthogonal upper triangular real matrix is diagonal with entries in `{−1,1}`.
Source: the triangular inverse identity and orthogonality. -/
theorem exists_diagonal_sign_of_isUpperTriangular {n : Type*} [Fintype n] [LinearOrder n]
    {W : Matrix n n ℝ} (hU : W.IsUpperTriangular) (hOrth : HasOrthonormalCols W) :
    ∃ d : n → ℝ, (∀ i, d i = 1 ∨ d i = -1) ∧ W = Matrix.diagonal d := by
  have hOrthEq : Wᵀ * W = 1 := hOrth
  have hOther : W * Wᵀ = 1 := mul_eq_one_comm.mp hOrthEq
  have hTranspose : Wᵀ.IsUpperTriangular := by
    have h := isUpperTriangular_inv hU
    rwa [Matrix.inv_eq_right_inv hOther] at h
  have hdiag := eq_diagonal_of_isLowerTriangular_of_isUpperTriangular
    (isUpperTriangular_transpose_iff.mp hTranspose) hU
  refine ⟨fun i => W i i, ?_, hdiag⟩
  intro i
  have h := congrFun (congrFun hOrthEq i) i
  rw [hdiag, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal] at h
  simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h
  rcases le_or_gt (W i i) 0 with hnonpos | hpos
  · right
    nlinarith
  · left
    nlinarith

end NLAlib
