import NLAlib.Matrix.Structured.Hessenberg
import NLAlib.Matrix.Functions.CFCQuadratic

/-! # Eigenvectors of unreduced tridiagonal matrices

A nonzero eigenvector of an unreduced real symmetric tridiagonal matrix has a
nonzero first coordinate. This gives a simple spectrum without a perturbation
argument. Source: Gautschi (2004), Theorem 1.19; the finite recurrence proof also
applies to arbitrary upper Hessenberg transposes.
-/

noncomputable section

open Matrix
open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- For an upper Hessenberg transpose with nonzero superdiagonal, an eigenvector
whose first coordinate vanishes is zero. This includes dimension one. -/
theorem eq_zero_of_mulVec_eq_smul_of_apply_zero_eq_zero
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : IsUpperHessenberg Hᵀ)
    (hsub : ∀ i j : Fin n, i.val + 1 = j.val → H i j ≠ 0)
    (hn : 0 < n) {v : Fin n → ℝ} {θ : ℝ} (hv : H *ᵥ v = θ • v)
    (hv0 : v ⟨0, hn⟩ = 0) : v = 0 := by
  have hall (k : ℕ) (hk : k < n) : v ⟨k, hk⟩ = 0 := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      by_cases hk0 : k = 0
      · subst k
        exact hv0
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        let i : Fin n := ⟨k - 1, by omega⟩
        let j : Fin n := ⟨k, hk⟩
        have hvi : v i = 0 := ih (k - 1) (by omega) i.isLt
        have hrow := congrFun hv i
        change (∑ l : Fin n, H i l * v l) = θ * v i at hrow
        rw [hvi, mul_zero, Finset.sum_eq_single j] at hrow
        · exact (mul_eq_zero.mp hrow).resolve_left (hsub i j (by simp [i, j]; omega))
        · intro l _ hlj
          by_cases hl : l.val < k
          · rw [ih l.val hl l.isLt, mul_zero]
          · have hlt : i.val + 1 < l.val := by
              have hne : l.val ≠ k := fun he => hlj (Fin.ext he)
              simp only [i]
              omega
            rw [show H i l = 0 from hH l i hlt, zero_mul]
        · simp
  funext i
  exact hall i.val i.isLt

/-- Every nonzero eigenvector of an unreduced Hessenberg transpose has nonzero
first coordinate. Source: Gautschi (2004), Theorem 1.19. -/
theorem apply_zero_ne_zero_of_mulVec_eq_smul
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : IsUpperHessenberg Hᵀ)
    (hsub : ∀ i j : Fin n, i.val + 1 = j.val → H i j ≠ 0)
    (hn : 0 < n) {v : Fin n → ℝ} {θ : ℝ} (hv : H *ᵥ v = θ • v)
    (hvne : v ≠ 0) : v ⟨0, hn⟩ ≠ 0 :=
  fun h => hvne (eq_zero_of_mulVec_eq_smul_of_apply_zero_eq_zero hH hsub hn hv h)

/-- The first coordinate determines an eigenvector in an unreduced Hessenberg
transpose, for a fixed eigenvalue. -/
theorem eq_of_mulVec_eq_smul_of_apply_zero_eq
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : IsUpperHessenberg Hᵀ)
    (hsub : ∀ i j : Fin n, i.val + 1 = j.val → H i j ≠ 0)
    (hn : 0 < n) {v w : Fin n → ℝ} {θ : ℝ}
    (hv : H *ᵥ v = θ • v) (hw : H *ᵥ w = θ • w)
    (h0 : v ⟨0, hn⟩ = w ⟨0, hn⟩) : v = w := by
  apply sub_eq_zero.mp
  apply eq_zero_of_mulVec_eq_smul_of_apply_zero_eq_zero hH hsub hn
  · rw [Matrix.mulVec_sub, hv, hw, smul_sub]
  · exact sub_eq_zero.mpr h0

/-- Every first eigenvector coordinate of a Hermitian unreduced tridiagonal
matrix is nonzero. Source: Gautschi (2004), Theorem 1.19. -/
theorem _root_.Matrix.IsHermitian.eigenvectorBasis_apply_zero_ne_zero
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHermitian)
    (htri : IsUpperHessenberg Hᵀ)
    (hsub : ∀ i j : Fin n, i.val + 1 = j.val → H i j ≠ 0)
    (hn : 0 < n) (i : Fin n) : hH.eigenvectorBasis i ⟨0, hn⟩ ≠ 0 := by
  apply apply_zero_ne_zero_of_mulVec_eq_smul htri hsub hn (hH.mulVec_eigenvectorBasis i)
  intro hzero
  have hnorm := eigenvectorBasis_dotProduct_eigenvectorBasis hH i i
  rw [hzero] at hnorm
  simp at hnorm

/-- A Hermitian unreduced tridiagonal matrix has distinct eigenvalues.
Source: Gautschi (2004), Theorem 1.19. -/
theorem _root_.Matrix.IsHermitian.eigenvalues_injective_of_unreduced
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHermitian)
    (htri : IsUpperHessenberg Hᵀ)
    (hsub : ∀ i j : Fin n, i.val + 1 = j.val → H i j ≠ 0) :
    Function.Injective hH.eigenvalues := by
  intro i j hij
  by_contra hne
  have hn : 0 < n := by have := i.isLt; omega
  let z : Fin n := ⟨0, hn⟩
  let v : Fin n → ℝ := hH.eigenvectorBasis i
  let w : Fin n → ℝ := hH.eigenvectorBasis j
  have hve : H *ᵥ v = hH.eigenvalues i • v := hH.mulVec_eigenvectorBasis i
  have hwe : H *ᵥ w = hH.eigenvalues i • w := by rw [hij]; exact hH.mulVec_eigenvectorBasis j
  have heq : w z • v = v z • w := by
    apply eq_of_mulVec_eq_smul_of_apply_zero_eq htri hsub hn
    · rw [Matrix.mulVec_smul, hve, smul_smul, smul_smul, mul_comm]
    · rw [Matrix.mulVec_smul, hwe, smul_smul, smul_smul, mul_comm]
    · change w z * v z = v z * w z
      ring
  have hdot := congrArg (fun u : Fin n → ℝ => v ⬝ᵥ u) heq
  have hvv : v ⬝ᵥ v = 1 := by simpa [v] using eigenvectorBasis_dotProduct_eigenvectorBasis hH i i
  have hvw : v ⬝ᵥ w = 0 := by simpa [v, w, hne] using eigenvectorBasis_dotProduct_eigenvectorBasis hH i j
  rw [dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, hvv, hvw,
    mul_one, mul_zero] at hdot
  exact hH.eigenvectorBasis_apply_zero_ne_zero htri hsub hn j hdot

end NLAlib
