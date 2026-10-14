import NLAlib.Polynomial.OrthogonalPolynomials.Orthonormal
import NLAlib.Matrix.Structured.TridiagonalSpectrum

/-! # Compressed multiplication for finite moment systems

The Jacobi matrix is multiplication by `X` compressed to the normalized
moment-polynomial basis. Positive norms make it unreduced and Hermitian, and
its characteristic polynomial is the canonical monic orthogonal polynomial.
This construction gives actual Gauss nodes for general positive measures.
Source: Gautschi (2004), Theorems 1.19 and 1.27; operator derivations OP5–OP11.
-/

noncomputable section

open Polynomial Matrix Finset
open scoped Matrix

namespace NLAlib

/-- Multiplication by `X` compressed to the first `n` normalized moment polynomials.
The definition is total; its spectral interpretation assumes nonsingular moment
systems and positive squared norms at the included orders. -/
def orthogonalPolynomialJacobiMatrix (L : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => L (X * orthonormalMomentPolynomial L j.val * orthonormalMomentPolynomial L i.val)

/-- The moment Jacobi matrix is Hermitian by commutativity of scalar polynomial
multiplication, even before positivity is assumed. -/
theorem isHermitian_orthogonalPolynomialJacobiMatrix (L : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ) :
    (orthogonalPolynomialJacobiMatrix L n).IsHermitian := by
  ext i j
  change L (X * orthonormalMomentPolynomial L i.val * orthonormalMomentPolynomial L j.val) =
    L (X * orthonormalMomentPolynomial L j.val * orthonormalMomentPolynomial L i.val)
  exact congrArg L (by ac_rfl)

/-- Pairing normalized moment polynomials after multiplication by X extracts
the two reciprocal square-root norms from their monic polynomial pairing. -/
theorem functional_X_orthonormalMomentPolynomial_mul (L : ℝ[X] →ₗ[ℝ] ℝ) (i j : ℕ) :
    L (X * orthonormalMomentPolynomial L j * orthonormalMomentPolynomial L i) =
      (Real.sqrt (orthogonalPolynomialNorm L j))⁻¹ *
        (Real.sqrt (orthogonalPolynomialNorm L i))⁻¹ *
        L (monicOrthogonalPolynomial L j * (X * monicOrthogonalPolynomial L i)) := by
  rw [orthonormalMomentPolynomial, orthonormalMomentPolynomial]
  rw [show X * (C (Real.sqrt (orthogonalPolynomialNorm L j))⁻¹ * monicOrthogonalPolynomial L j) *
      (C (Real.sqrt (orthogonalPolynomialNorm L i))⁻¹ * monicOrthogonalPolynomial L i) =
      C ((Real.sqrt (orthogonalPolynomialNorm L j))⁻¹ *
        (Real.sqrt (orthogonalPolynomialNorm L i))⁻¹) *
        (monicOrthogonalPolynomial L j * (X * monicOrthogonalPolynomial L i)) by
      rw [C_mul]; ring, C_mul', map_smul, smul_eq_mul]

/-- Entries beyond neighboring polynomial degrees vanish in the moment Jacobi
matrix. This is the finite compressed-multiplication tridiagonal identity. -/
theorem orthogonalPolynomialJacobiMatrix_apply_eq_zero (L : ℝ[X] →ₗ[ℝ] ℝ) {n : ℕ}
    (hL : ∀ k ≤ n, hankelMomentDet L k ≠ 0) (i j : Fin n)
    (hij : i.val + 1 < j.val) : orthogonalPolynomialJacobiMatrix L n i j = 0 := by
  rw [orthogonalPolynomialJacobiMatrix, functional_X_orthonormalMomentPolynomial_mul]
  rw [(isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L
    (hL j.val j.isLt.le)).orthogonal (X * monicOrthogonalPolynomial L i.val) (by
      rw [degree_mul, degree_X, degree_eq_natDegree
        (monic_monicOrthogonalPolynomial L i.val).ne_zero, natDegree_monicOrthogonalPolynomial]
      exact_mod_cast (show 1 + i.val < j.val by omega)), mul_zero]

/-- Every adjacent Jacobi entry is positive when the included squared norms are
positive. Source: Gautschi (2004), Theorem 1.27. -/
theorem orthogonalPolynomialJacobiMatrix_superdiagonal_pos (L : ℝ[X] →ₗ[ℝ] ℝ) {n : ℕ}
    (hL : ∀ k ≤ n, hankelMomentDet L k ≠ 0)
    (hH : ∀ k < n, 0 < orthogonalPolynomialNorm L k) (i j : Fin n)
    (hij : i.val + 1 = j.val) : 0 < orthogonalPolynomialJacobiMatrix L n i j := by
  rw [orthogonalPolynomialJacobiMatrix, functional_X_orthonormalMomentPolynomial_mul]
  have hj := isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L (hL j.val j.isLt.le)
  rw [hj.functional_mul_eq_sq_of_monic
    (monic_X.mul (monic_monicOrthogonalPolynomial L i.val)) (by
      rw [natDegree_X_mul (monic_monicOrthogonalPolynomial L i.val).ne_zero,
        natDegree_monicOrthogonalPolynomial]
      omega)]
  exact mul_pos (mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (hH _ j.isLt)))
    (inv_pos.mpr (Real.sqrt_pos.mpr (hH _ i.isLt)))) (hH _ j.isLt)

/-- Positive finite moments give an unreduced Jacobi matrix with a simple spectrum.
Source: Gautschi (2004), Theorem 1.19.
atlas: orthogonal-polynomial-zeros (partial) -/
theorem eigenvalues_orthogonalPolynomialJacobiMatrix_injective
    (L : ℝ[X] →ₗ[ℝ] ℝ) {n : ℕ} (hL : ∀ k ≤ n, hankelMomentDet L k ≠ 0)
    (hH : ∀ k < n, 0 < orthogonalPolynomialNorm L k) :
    Function.Injective (isHermitian_orthogonalPolynomialJacobiMatrix L n).eigenvalues := by
  apply (isHermitian_orthogonalPolynomialJacobiMatrix L n).eigenvalues_injective_of_unreduced
  · intro i j hij
    exact orthogonalPolynomialJacobiMatrix_apply_eq_zero L hL j i hij
  · intro i j hij
    exact (orthogonalPolynomialJacobiMatrix_superdiagonal_pos L hL hH i j hij).ne'

/-- Pairing a finite normalized polynomial expansion with one basis polynomial
recovers exactly its coefficient. This is the finite orthonormal coordinate bridge. -/
theorem functional_sum_C_mul_orthonormalMomentPolynomial_mul (L : ℝ[X] →ₗ[ℝ] ℝ) {n : ℕ}
    (hL : ∀ k ≤ n, hankelMomentDet L k ≠ 0)
    (hH : ∀ k < n, 0 < orthogonalPolynomialNorm L k) (v : Fin n → ℝ) (i : Fin n) :
    L ((∑ j : Fin n, C (v j) * orthonormalMomentPolynomial L j.val) *
      orthonormalMomentPolynomial L i.val) = v i := by
  rw [Finset.sum_mul, map_sum]
  have hterm (j : Fin n) : L (C (v j) * orthonormalMomentPolynomial L j.val *
      orthonormalMomentPolynomial L i.val) = v j * (if j = i then 1 else 0) := by
    rw [mul_assoc, C_mul', map_smul, smul_eq_mul,
      functional_orthonormalMomentPolynomial_mul L (hL _ j.isLt.le) (hL _ i.isLt.le)
        (hH _ j.isLt) (hH _ i.isLt)]
    simp only [Fin.val_inj]
  simp_rw [hterm]
  simp

/-- Every eigenvalue of compressed multiplication is a zero of the canonical
degree-`n` monic polynomial. This includes finite-support termination.
Source: Gautschi (2004), Theorem 1.19.
atlas: orthogonal-polynomial-zeros (partial) -/
theorem eval_monicOrthogonalPolynomial_eigenvalues_eq_zero
    (L : ℝ[X] →ₗ[ℝ] ℝ) {n : ℕ} (hL : ∀ k ≤ n, hankelMomentDet L k ≠ 0)
    (hH : ∀ k < n, 0 < orthogonalPolynomialNorm L k) (i : Fin n) :
    (monicOrthogonalPolynomial L n).eval
      ((isHermitian_orthogonalPolynomialJacobiMatrix L n).eigenvalues i) = 0 := by
  let B := orthogonalPolynomialJacobiMatrix L n
  let hB := isHermitian_orthogonalPolynomialJacobiMatrix L n
  let θ := hB.eigenvalues i
  let v : Fin n → ℝ := hB.eigenvectorBasis i
  let F : ℝ[X] := ∑ j : Fin n, C (v j) * orthonormalMomentPolynomial L j.val
  let s : ℝ[X] := (X - C θ) * F
  have hFpair (j : Fin n) : L (F * orthonormalMomentPolynomial L j.val) = v j :=
    functional_sum_C_mul_orthonormalMomentPolynomial_mul L hL hH v j
  have hv : B *ᵥ v = θ • v := hB.mulVec_eigenvectorBasis i
  have hF0 : F ≠ 0 := by
    intro hzero
    have hv0 : v = 0 := by
      ext j
      have hj := hFpair j
      simpa only [hzero, zero_mul, map_zero, Pi.zero_apply] using hj.symm
    have hnorm := eigenvectorBasis_dotProduct_eigenvectorBasis hB i i
    simp only at hnorm
    change v ⬝ᵥ v = 1 at hnorm
    rw [hv0, zero_dotProduct] at hnorm
    exact zero_ne_one hnorm
  have hFdeg : F.degree < n := by
    apply mem_degreeLT.mp
    apply Submodule.sum_mem
    intro j _
    rw [C_mul']
    apply mem_degreeLT.mpr
    exact (degree_smul_le _ _).trans_lt (by
      rw [degree_orthonormalMomentPolynomial (hH _ j.isLt)]
      exact_mod_cast j.isLt)
  have hSpair (j : Fin n) : L (s * orthonormalMomentPolynomial L j.val) = 0 := by
    have hXF : L (X * F * orthonormalMomentPolynomial L j.val) = (B *ᵥ v) j := by
      simp only [F, Finset.mul_sum, Finset.sum_mul, map_sum, Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro k _
      rw [show X * (C (v k) * orthonormalMomentPolynomial L k.val) *
          orthonormalMomentPolynomial L j.val =
          C (v k) * (X * orthonormalMomentPolynomial L k.val *
            orthonormalMomentPolynomial L j.val) by ring, C_mul', map_smul, smul_eq_mul]
      exact mul_comm _ _
    change L (((X - C θ) * F) * orthonormalMomentPolynomial L j.val) = 0
    rw [sub_mul, sub_mul, map_sub, hXF, mul_assoc, C_mul', map_smul,
      smul_eq_mul, hFpair, hv, Pi.smul_apply, smul_eq_mul, sub_self]
  have hSmonic (j : Fin n) : L (s * monicOrthogonalPolynomial L j.val) = 0 := by
    rw [← sqrt_norm_mul_orthonormalMomentPolynomial (hH _ j.isLt),
      show s * (C (Real.sqrt (orthogonalPolynomialNorm L j.val)) *
        orthonormalMomentPolynomial L j.val) =
        C (Real.sqrt (orthogonalPolynomialNorm L j.val)) *
          (s * orthonormalMomentPolynomial L j.val) by ring,
      C_mul', map_smul, hSpair, smul_zero]
  have hSorth (r : ℝ[X]) (hr : r.degree < n) : L (s * r) = 0 := by
    obtain ⟨c, hc⟩ := exists_sum_smul_monicOrthogonalPolynomial_eq_of_degree_lt L hr
    rw [← hc, Finset.mul_sum, map_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [mul_smul_comm, map_smul, hSmonic ⟨j, mem_range.mp hj⟩, smul_zero]
  have hs0 : s ≠ 0 := mul_ne_zero (monic_X_sub_C θ).ne_zero hF0
  have hsd : s.natDegree = n := by
    have hlt : ¬ s.degree < n := fun h => hs0
      (eq_zero_of_degree_lt_of_orthogonal_of_hankelMomentDet_ne_zero L
        (hL n le_rfl) h hSorth)
    have hge : n ≤ s.natDegree := by
      exact Nat.le_of_not_gt (fun h => hlt ((natDegree_lt_iff_degree_lt hs0).mp h))
    have hle : s.natDegree ≤ n := by
      have h := natDegree_mul_le (p := X - C θ) (q := F)
      rw [natDegree_X_sub_C] at h
      have hFn := (natDegree_lt_iff_degree_lt hF0).mpr hFdeg
      exact h.trans (by omega)
    exact le_antisymm hle hge
  have hsSpec : IsMonicOrthogonalPolynomial L n (s * C s.leadingCoeff⁻¹) := by
    refine ⟨monic_mul_leadingCoeff_inv hs0, ?_, ?_⟩
    · rw [natDegree_mul_leadingCoeff_inv _ hs0, hsd]
    · intro r hr
      rw [show (s * C s.leadingCoeff⁻¹) * r = C s.leadingCoeff⁻¹ * (s * r) by ring,
        C_mul', map_smul, hSorth _ hr, smul_zero]
  have heq := hsSpec.eq_of_hankelMomentDet_ne_zero
    (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L (hL n le_rfl)) (hL n le_rfl)
  rw [← heq]
  change (s * C s.leadingCoeff⁻¹).eval θ = 0
  simp only [s, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul]

/-- The characteristic polynomial of the actual moment Jacobi matrix is the
canonical monic orthogonal polynomial. Its simple Hermitian spectrum therefore
constructs every real Gauss node.
Source: Gautschi (2004), Theorems 1.19 and 1.27.
atlas: orthogonal-polynomial-zeros (partial) -/
theorem charpoly_orthogonalPolynomialJacobiMatrix
    (L : ℝ[X] →ₗ[ℝ] ℝ) {n : ℕ} (hL : ∀ k ≤ n, hankelMomentDet L k ≠ 0)
    (hH : ∀ k < n, 0 < orthogonalPolynomialNorm L k) :
    (orthogonalPolynomialJacobiMatrix L n).charpoly = monicOrthogonalPolynomial L n := by
  let B := orthogonalPolynomialJacobiMatrix L n
  let hB := isHermitian_orthogonalPolynomialJacobiMatrix L n
  apply sub_eq_zero.mp
  apply eq_zero_of_degree_lt_of_eval_index_eq_zero (s := Finset.univ)
    (v := hB.eigenvalues) (eigenvalues_orthogonalPolynomialJacobiMatrix_injective L hL hH).injOn
  · have hdeg : B.charpoly.degree = (n : WithBot ℕ) := by
      rw [degree_eq_natDegree (charpoly_monic B).ne_zero, charpoly_natDegree_eq_dim,
        Fintype.card_fin]
    have hPdeg : (monicOrthogonalPolynomial L n).degree = (n : WithBot ℕ) := by
      rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial L n).ne_zero,
        natDegree_monicOrthogonalPolynomial]
    simpa only [card_univ, Fintype.card_fin] using
      (degree_sub_lt_left (hdeg.trans hPdeg.symm) (charpoly_monic B).ne_zero
        ((charpoly_monic B).leadingCoeff.trans (monic_monicOrthogonalPolynomial L n).leadingCoeff.symm)).trans_eq hdeg
  · intro i _
    simp only [eval_sub, eval_monicOrthogonalPolynomial_eigenvalues_eq_zero L hL hH i, sub_zero]
    rw [hB.charpoly_eq, eval_prod]
    apply Finset.prod_eq_zero (mem_univ i)
    simp

end NLAlib
