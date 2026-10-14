import NLAlib.Polynomial.OrthogonalPolynomials.JacobiMoments
import NLAlib.Polynomial.OrthogonalPolynomials.CoefficientBounds
import Mathlib.Analysis.Matrix.Order

/-! # Endpoint order bounds for the actual measure Jacobi matrix

The coefficient quadratic form is the integral of `x` times the squared actual
polynomial expansion. Interval support proves PSD endpoint shifts; one extra support
point makes both shifts positive definite. Finite-support termination is explicit.
-/

noncomputable section
open Matrix Polynomial MeasureTheory Finset Set
open scoped Matrix MatrixOrder

namespace NLAlib

private theorem jacobi_expansion_forms (L : ℝ[X] →ₗ[ℝ] ℝ) {N : ℕ}
    (hL : ∀ k ≤ N, hankelMomentDet L k ≠ 0)
    (hH : ∀ k < N, 0 < orthogonalPolynomialNorm L k) (v : Fin N → ℝ) :
    let F : ℝ[X] := ∑ j : Fin N, C (v j) * orthonormalMomentPolynomial L j.val
    L (F ^ 2) = v ⬝ᵥ v ∧ L (X * F ^ 2) = v ⬝ᵥ (orthogonalPolynomialJacobiMatrix L N *ᵥ v) := by
  dsimp only
  let F : ℝ[X] := ∑ j : Fin N, C (v j) * orthonormalMomentPolynomial L j.val
  have hpair (j : Fin N) : L (F * orthonormalMomentPolynomial L j.val) = v j :=
    functional_sum_C_mul_orthonormalMomentPolynomial_mul L hL hH v j
  have hXpair (j : Fin N) : L (X * F * orthonormalMomentPolynomial L j.val) =
      (orthogonalPolynomialJacobiMatrix L N *ᵥ v) j := by
    simp only [F, Finset.mul_sum, Finset.sum_mul, map_sum, Matrix.mulVec, dotProduct]
    apply sum_congr rfl
    intro k _
    rw [show X * (C (v k) * orthonormalMomentPolynomial L k.val) *
        orthonormalMomentPolynomial L j.val = C (v k) *
          (X * orthonormalMomentPolynomial L k.val * orthonormalMomentPolynomial L j.val) by ring,
      C_mul', map_smul, smul_eq_mul]
    exact mul_comm _ _
  constructor
  · rw [pow_two]
    rw [Finset.mul_sum, map_sum]
    apply sum_congr rfl
    intro j _
    rw [show F * (C (v j) * orthonormalMomentPolynomial L j.val) =
      C (v j) * (F * orthonormalMomentPolynomial L j.val) by ring,
      C_mul', map_smul, smul_eq_mul, hpair]
  · rw [pow_two, ← mul_assoc]
    rw [Finset.mul_sum, map_sum]
    apply sum_congr rfl
    intro j _
    rw [show X * F * (C (v j) * orthonormalMomentPolynomial L j.val) =
      C (v j) * (X * F * orthonormalMomentPolynomial L j.val) by ring,
      C_mul', map_smul, smul_eq_mul, hXpair]

/-- The actual measure Jacobi matrix lies between support interval endpoints in
matrix order, including finite-support termination.
Source: focused mathematical reroutes, Section 3 (BL2).
atlas: gauss-radau-lobatto (partial) -/
theorem orthogonalPolynomialJacobiMatrix_endpoint_shifts_posSemidef {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) {a c : ℝ} (hμac : ∀ᵐ x ∂μ, x ∈ Icc a c)
    (N : ℕ) (hs : (N : ℕ∞) ≤ μ.support.encard) :
    let J := orthogonalPolynomialJacobiMatrix (polynomialIntegral μ hμ) N
    (J - a • 1).PosSemidef ∧ (c • 1 - J).PosSemidef := by
  dsimp only
  let L := polynomialIntegral μ hμ
  let J := orthogonalPolynomialJacobiMatrix L N
  have hL (k : ℕ) (hk : k ≤ N) : hankelMomentDet L k ≠ 0 :=
    hankelMomentDet_ne_zero_of_le_support_encard μ hμ ((by exact_mod_cast hk : (k : ℕ∞) ≤ N).trans hs)
  have hH (k : ℕ) (hk : k < N) : 0 < orthogonalPolynomialNorm L k :=
    orthogonalPolynomialNorm_pos_of_lt_support_encard μ hμ
      ((by exact_mod_cast Nat.succ_le_of_lt hk : (k + 1 : ℕ∞) ≤ N).trans hs)
  have hJh := isHermitian_orthogonalPolynomialJacobiMatrix L N
  have hscalar (z : ℝ) : (z • (1 : Matrix (Fin N) (Fin N) ℝ)).IsHermitian := by
    simp [Matrix.IsHermitian]
  have hform (v : Fin N → ℝ) (z : ℝ) :
      let F : ℝ[X] := ∑ j : Fin N, C (v j) * orthonormalMomentPolynomial L j.val
      L ((X - C z) * F ^ 2) = star v ⬝ᵥ ((J - z • 1) *ᵥ v) := by
    dsimp only
    obtain ⟨hn, hx⟩ := jacobi_expansion_forms L hL hH v
    rw [sub_mul, map_sub, C_mul', map_smul, smul_eq_mul, hx, hn]
    simp only [J, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      star_trivial, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  constructor
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hJh.sub (hscalar a))
    intro v
    rw [← hform v a]
    change 0 ≤ ∫ x, ((X - C a) * (∑ j : Fin N, C (v j) * orthonormalMomentPolynomial L j.val) ^ 2).eval x ∂μ
    apply integral_nonneg_of_ae
    filter_upwards [hμac] with x hx
    simpa only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, Pi.zero_apply] using
      mul_nonneg (sub_nonneg.mpr hx.1) (sq_nonneg _)
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ((hscalar c).sub hJh)
    intro v
    have heq : star v ⬝ᵥ ((c • 1 - J) *ᵥ v) = - (star v ⬝ᵥ ((J - c • 1) *ᵥ v)) := by
      rw [← neg_sub J (c • 1), Matrix.neg_mulVec, dotProduct_neg]
    rw [heq, ← hform v c]
    change 0 ≤ -(∫ x, ((X - C c) * (∑ j : Fin N, C (v j) * orthonormalMomentPolynomial L j.val) ^ 2).eval x ∂μ)
    apply neg_nonneg.mpr
    apply integral_nonpos_of_ae
    filter_upwards [hμac] with x hx
    simpa only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, Pi.zero_apply] using
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx.2) (sq_nonneg _)

/-- One extra original support point makes both actual Jacobi endpoint shifts positive
definite. This is the clean sufficient nondegeneracy for Radau/Lobatto Schur inverses.
Source: focused mathematical reroutes, Section 3 (BL4), (BL7).
atlas: gauss-radau-lobatto (partial) -/
theorem orthogonalPolynomialJacobiMatrix_endpoint_shifts_posDef {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) {a c : ℝ} (hμac : ∀ᵐ x ∂μ, x ∈ Icc a c)
    (N : ℕ) (hs : (N + 1 : ℕ∞) ≤ μ.support.encard) :
    let J := orthogonalPolynomialJacobiMatrix (polynomialIntegral μ hμ) N
    (J - a • 1).PosDef ∧ (c • 1 - J).PosDef := by
  dsimp only
  let L := polynomialIntegral μ hμ
  let J := orthogonalPolynomialJacobiMatrix L N
  have hL (k : ℕ) (hk : k ≤ N) : hankelMomentDet L k ≠ 0 :=
    hankelMomentDet_ne_zero_of_le_support_encard μ hμ
      ((by exact_mod_cast (show k ≤ N + 1 by omega) : (k : ℕ∞) ≤ N + 1).trans hs)
  have hH (k : ℕ) (hk : k < N) : 0 < orthogonalPolynomialNorm L k :=
    orthogonalPolynomialNorm_pos_of_lt_support_encard μ hμ
      ((by exact_mod_cast (show k + 1 ≤ N + 1 by omega) : (k + 1 : ℕ∞) ≤ N + 1).trans hs)
  have hJh := isHermitian_orthogonalPolynomialJacobiMatrix L N
  have hscalar (z : ℝ) : (z • (1 : Matrix (Fin N) (Fin N) ℝ)).IsHermitian := by
    simp [Matrix.IsHermitian]
  have hpos (v : Fin N → ℝ) (hv : v ≠ 0) :
      0 < star v ⬝ᵥ ((J - a • 1) *ᵥ v) ∧ 0 < star v ⬝ᵥ ((c • 1 - J) *ᵥ v) := by
    let F : ℝ[X] := ∑ j : Fin N, C (v j) * orthonormalMomentPolynomial L j.val
    have hF0 : F ≠ 0 := by
      intro hz
      apply hv
      funext i
      have h := functional_sum_C_mul_orthonormalMomentPolynomial_mul L hL hH v i
      change L (F * orthonormalMomentPolynomial L i.val) = v i at h
      simpa only [hz, zero_mul, map_zero, Pi.zero_apply] using h.symm
    have hFdeg : F.degree < N := by
      apply mem_degreeLT.mp
      apply Submodule.sum_mem
      intro j _
      rw [C_mul']
      apply mem_degreeLT.mpr
      exact (degree_smul_le _ _).trans_lt (by
        rw [degree_orthonormalMomentPolynomial (hH _ j.isLt)]
        exact_mod_cast j.isLt)
    have hn : 0 < N := lt_of_le_of_lt (Nat.zero_le F.natDegree)
      ((natDegree_lt_iff_degree_lt hF0).mpr hFdeg)
    have hFd : F.degree ≤ (N - 1 : ℕ) := by
      rw [degree_eq_natDegree hF0]
      have hd := (natDegree_lt_iff_degree_lt hF0).mpr hFdeg
      exact_mod_cast (show F.natDegree ≤ N - 1 by omega)
    have hs' : ((N - 1 : ℕ) : ℕ∞) + 2 ≤ μ.support.encard := by
      have heq : ((N - 1 : ℕ) : ℕ∞) + 2 = (N : ℕ∞) + 1 := by
        exact_mod_cast (show N - 1 + 2 = N + 1 by omega)
      rw [heq]
      exact hs
    have ha := integral_eval_mul_sq_pos hμ hs' hF0 hFd (X_sub_C_ne_zero a) (by simp) (by
      filter_upwards [hμac] with x hx
      simpa only [eval_sub, eval_X, eval_C] using sub_nonneg.mpr hx.1)
    have hc := integral_eval_mul_sq_pos hμ hs' hF0 hFd (r := C c - X) (by
      intro hz
      have h := congrArg (fun p : ℝ[X] => p.coeff 1) hz
      simp at h) (by
      exact (degree_sub_le _ _).trans (max_le (degree_C_le.trans (by norm_num)) (by simp))) (by
      filter_upwards [hμac] with x hx
      simpa only [eval_sub, eval_X, eval_C] using sub_nonneg.mpr hx.2)
    have haL : 0 < L ((X - C a) * F ^ 2) := by
      simpa only [L, polynomialIntegral_apply, eval_mul, eval_sub, eval_X, eval_C, eval_pow] using ha
    have hcL : 0 < L ((C c - X) * F ^ 2) := by
      simpa only [L, polynomialIntegral_apply, eval_mul, eval_sub, eval_X, eval_C, eval_pow] using hc
    obtain ⟨hFn, hFx⟩ := jacobi_expansion_forms L hL hH v
    change L (F ^ 2) = _ at hFn
    change L (X * F ^ 2) = _ at hFx
    rw [sub_mul, map_sub, C_mul', map_smul, smul_eq_mul, hFx, hFn] at haL hcL
    constructor
    · simpa only [J, star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul, smul_eq_mul] using haL
    · simpa only [J, star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul, smul_eq_mul] using hcL
  exact ⟨Matrix.PosDef.of_dotProduct_mulVec_pos (hJh.sub (hscalar a)) (fun v hv => (hpos v hv).1),
    Matrix.PosDef.of_dotProduct_mulVec_pos ((hscalar c).sub hJh) (fun v hv => (hpos v hv).2)⟩

end NLAlib
