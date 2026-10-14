import NLAlib.Polynomial.OrthogonalPolynomials.JacobiMatrix
import NLAlib.Polynomial.OrthogonalPolynomials.CoefficientBounds
import NLAlib.Polynomial.Quadrature.GaussMeasure
import NLAlib.Polynomial.OrthogonalPolynomials.SupportGaps

/-! # Strict location of Gauss nodes

An eigenvector of compressed multiplication determines a nonzero lower-degree
polynomial. Its Rayleigh identity and positivity of endpoint-weighted squares
place every nonterminal Gauss node strictly inside the support interval.
Source: Gautschi (2004), Theorem 1.19; operator derivations OP8–OP11.
-/

noncomputable section

open Polynomial Matrix MeasureTheory Finset Set
open scoped Matrix

namespace NLAlib

/-- A nonzero Jacobi eigenvector gives a nonzero polynomial whose scalar
Rayleigh value is the eigenvalue; positive support gives strict endpoint bounds.
The eigenvector is arbitrary, rather than a chosen spectral basis.
Source: Gautschi (2004), Theorem 1.19.
atlas: orthogonal-polynomial-zeros (partial) -/
theorem eigenvalue_orthogonalPolynomialJacobiMatrix_mem_Ioo
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn : (n + 1 : ℕ∞) ≤ μ.support.encard)
    {v : Fin n → ℝ} (hv0 : v ≠ 0) {θ : ℝ}
    (hv : orthogonalPolynomialJacobiMatrix (polynomialIntegral μ hμ) n *ᵥ v = θ • v) :
    θ ∈ Ioo a b := by
  let L := polynomialIntegral μ hμ
  let B := orthogonalPolynomialJacobiMatrix L n
  let F : ℝ[X] := ∑ j : Fin n, C (v j) * orthonormalMomentPolynomial L j.val
  have hn0 : 0 < n := by
    by_contra hn0
    have hz : n = 0 := by omega
    subst n
    apply hv0
    ext i
    exact Fin.elim0 i
  have hL (k : ℕ) (hk : k ≤ n) : hankelMomentDet L k ≠ 0 :=
    hankelMomentDet_ne_zero_of_le_support_encard μ hμ
      ((by exact_mod_cast (show k ≤ n + 1 by omega) : (k : ℕ∞) ≤ n + 1).trans hn)
  have hH (k : ℕ) (hk : k < n) : 0 < orthogonalPolynomialNorm L k :=
    orthogonalPolynomialNorm_pos_of_lt_support_encard μ hμ
      ((by exact_mod_cast (show k + 1 ≤ n + 1 by omega) : (k + 1 : ℕ∞) ≤ n + 1).trans hn)
  have hFpair (j : Fin n) : L (F * orthonormalMomentPolynomial L j.val) = v j :=
    functional_sum_C_mul_orthonormalMomentPolynomial_mul L hL hH v j
  have hF0 : F ≠ 0 := by
    intro hz
    apply hv0
    ext j
    have h := hFpair j
    simpa only [hz, zero_mul, map_zero, Pi.zero_apply] using h.symm
  have hFdeg : F.degree < n := by
    apply mem_degreeLT.mp
    apply Submodule.sum_mem
    intro j _
    rw [C_mul']
    apply mem_degreeLT.mpr
    exact (degree_smul_le _ _).trans_lt (by
      rw [degree_orthonormalMomentPolynomial (hH _ j.isLt)]
      exact_mod_cast j.isLt)
  have hFdeg' : F.degree ≤ (n - 1 : ℕ) := by
    have h := (natDegree_lt_iff_degree_lt hF0).mpr hFdeg
    rw [degree_eq_natDegree hF0]
    exact_mod_cast (show F.natDegree ≤ n - 1 by omega)
  have hXFpair (j : Fin n) : L (X * F * orthonormalMomentPolynomial L j.val) = (B *ᵥ v) j := by
    simp only [F, Finset.mul_sum, Finset.sum_mul, map_sum, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro k _
    rw [show X * (C (v k) * orthonormalMomentPolynomial L k.val) *
        orthonormalMomentPolynomial L j.val =
        C (v k) * (X * orthonormalMomentPolynomial L k.val *
          orthonormalMomentPolynomial L j.val) by ring, C_mul', map_smul, smul_eq_mul]
    exact mul_comm _ _
  have hnorm : L (F ^ 2) = v ⬝ᵥ v := by
    rw [pow_two]
    conv_lhs => rhs; unfold F
    rw [Finset.mul_sum, map_sum]
    simp only [dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    rw [show F * (C (v j) * orthonormalMomentPolynomial L j.val) =
      C (v j) * (F * orthonormalMomentPolynomial L j.val) by ring,
      C_mul', map_smul, smul_eq_mul, hFpair]
  have hXnorm : L (X * F ^ 2) = θ * L (F ^ 2) := by
    rw [pow_two, ← mul_assoc]
    conv_lhs => rhs; unfold F
    rw [Finset.mul_sum, map_sum]
    have heq : (∑ j : Fin n, L (X * F * (C (v j) * orthonormalMomentPolynomial L j.val))) =
        v ⬝ᵥ (B *ᵥ v) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show X * F * (C (v j) * orthonormalMomentPolynomial L j.val) =
          C (v j) * (X * F * orthonormalMomentPolynomial L j.val) by ring,
          C_mul', map_smul, smul_eq_mul, hXFpair]
    rw [heq, hv, dotProduct_smul, smul_eq_mul, ← pow_two F, hnorm]
  have hnormpos : 0 < L (F ^ 2) := by
    rw [hnorm]
    simpa only [star_trivial] using (dotProduct_star_self_pos_iff (v := v)).mpr hv0
  have hsupport : ((n - 1 : ℕ) : ℕ∞) + 2 ≤ μ.support.encard := by
    have heq : ((n - 1 : ℕ) : ℕ∞) + 2 = (n : ℕ∞) + 1 := by
      exact_mod_cast (show n - 1 + 2 = n + 1 by omega)
    rw [heq]
    exact hn
  have ha := integral_eval_mul_sq_pos hμ hsupport hF0 hFdeg' (monic_X_sub_C a).ne_zero
    (by simp) (by
      filter_upwards [hs] with x hx
      simpa only [eval_sub, eval_X, eval_C] using sub_nonneg.mpr hx.1)
  have hb := integral_eval_mul_sq_pos hμ hsupport hF0 hFdeg' (r := C b - X)
    (by
      intro hz
      have h := congrArg (fun p : ℝ[X] => p.coeff 1) hz
      simp at h) (by
      exact (degree_sub_le _ _).trans (max_le (degree_C_le.trans (by norm_num)) (by simp))) (by
      filter_upwards [hs] with x hx
      simpa only [eval_sub, eval_X, eval_C] using sub_nonneg.mpr hx.2)
  have haL : 0 < L ((X - C a) * F ^ 2) := by
    simpa only [L, polynomialIntegral_apply, eval_mul, eval_sub, eval_X, eval_C, eval_pow] using ha
  have hbL : 0 < L ((C b - X) * F ^ 2) := by
    simpa only [L, polynomialIntegral_apply, eval_mul, eval_sub, eval_X, eval_C, eval_pow] using hb
  rw [sub_mul, map_sub, C_mul', map_smul, smul_eq_mul, hXnorm] at haL hbL
  exact ⟨by nlinarith, by nlinarith⟩

/-- Every nonterminal canonical Gauss node lies strictly inside a support
interval. No eigenvector normalization is assumed in the statement.
Source: Gautschi (2004), Theorem 1.19.
atlas: orthogonal-polynomial-zeros (partial) -/
theorem gaussNodes_mem_Ioo {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn : (n + 1 : ℕ∞) ≤ μ.support.encard) (i : Fin n) :
    gaussNodes μ hμ n i ∈ Ioo a b := by
  let hB := isHermitian_orthogonalPolynomialJacobiMatrix (polynomialIntegral μ hμ) n
  apply eigenvalue_orthogonalPolynomialJacobiMatrix_mem_Ioo hμ hs hn
    (v := hB.eigenvectorBasis i)
  · intro hzero
    have h := eigenvectorBasis_dotProduct_eigenvectorBasis hB i i
    simp only at h
    rw [hzero, zero_dotProduct] at h
    exact zero_ne_one h
  · exact hB.mulVec_eigenvectorBasis i

/-- Every canonical Gauss node lies in a closed support enclosure, including
finite-support termination when the nodes are exactly the support. -/
theorem gaussNodes_mem_Icc {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn : (n : ℕ∞) ≤ μ.support.encard) (i : Fin n) :
    gaussNodes μ hμ n i ∈ Icc a b := by
  rcases hn.eq_or_lt with heq | hlt
  · have hsupport : μ.support ⊆ Icc a b := Measure.support_subset_of_isClosed isClosed_Icc hs
    apply hsupport
    apply (eval_monicOrthogonalPolynomial_eq_zero_iff_mem_support_of_encard_eq hμ heq.symm _).mp
    exact (eval_monicOrthogonalPolynomial_eq_zero_iff_exists_gaussNodes hμ hn _).mpr ⟨i, rfl⟩
  · exact ⟨(gaussNodes_mem_Ioo hμ hs
      (by simpa only [Nat.cast_add, Nat.cast_one] using ENat.natCast_add_one_le_iff.mpr hlt) i).1.le,
      (gaussNodes_mem_Ioo hμ hs
      (by simpa only [Nat.cast_add, Nat.cast_one] using ENat.natCast_add_one_le_iff.mpr hlt) i).2.le⟩

end NLAlib
