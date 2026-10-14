import NLAlib.Polynomial.OrthogonalPolynomials.MeasureMoments
import NLAlib.Polynomial.OrthogonalPolynomials.FiniteMomentSystem
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef

/-!
# Positive Hankel moment matrices

The finite polynomial coefficient chart identifies squared integral norms with
Hankel quadratic forms. Measure support determines positive definiteness exactly.
Source: Gautschi (2004), Chapter 1; atlas `hankel-moment-positivity`.
-/

noncomputable section

open Polynomial Finset Matrix MeasureTheory
open scoped Matrix

namespace NLAlib

/-- The squared bilinear norm of a finite monomial expansion is its Hankel quadratic
form. This identity holds over any field, without positivity or conjugation.
Source: OF3, Gautschi (2004), Chapter 1.
atlas: hankel-moment-positivity (partial) -/
theorem functional_sum_monomial_sq_eq_dotProduct {𝕜 : Type*} [Field 𝕜]
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) (c : Fin n → 𝕜) :
    L ((∑ i : Fin n, monomial i.val (c i)) ^ 2) = c ⬝ᵥ (hankelMomentMatrix L n *ᵥ c) := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum, map_sum, dotProduct, mulVec,
    hankelMomentMatrix]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [monomial_mul_monomial, ← C_mul_X_pow_eq_monomial, C_mul', map_smul]
  simp only [smul_eq_mul]
  ring_nf

/-- Every real Hankel moment matrix is symmetric. -/
theorem isHermitian_hankelMomentMatrix (L : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ) :
    (hankelMomentMatrix L n).IsHermitian := by
  ext i j
  simp only [hankelMomentMatrix, conjTranspose_apply, star_trivial, Nat.add_comm]

/-- Every finite Hankel matrix of a positive real measure is PSD.
Source: Gautschi (2004), Section 1.1, polynomial squared integral identity.
atlas: hankel-moment-positivity (partial) -/
theorem posSemidef_hankelMomentMatrix (μ : Measure ℝ) (hμ : HasPolynomialMoments μ) (n : ℕ) :
    (hankelMomentMatrix (polynomialIntegral μ hμ) n).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (isHermitian_hankelMomentMatrix _ _)
  intro c
  rw [star_trivial, ← functional_sum_monomial_sq_eq_dotProduct]
  change 0 ≤ ∫ x, ((∑ i : Fin n, monomial i.val (c i)) ^ 2).eval x ∂μ
  simp only [eval_pow]
  exact integral_nonneg (fun x => sq_nonneg _)

/-- A real measure Hankel matrix is PD exactly when the squared integral form is
positive on every nonzero polynomial of degree below its order. -/
theorem posDef_hankelMomentMatrix_iff_integral_sq_eval_pos (μ : Measure ℝ)
    (hμ : HasPolynomialMoments μ) (n : ℕ) :
    (hankelMomentMatrix (polynomialIntegral μ hμ) n).PosDef ↔
      ∀ p : ℝ[X], p.degree < n → p ≠ 0 → 0 < ∫ x, (p.eval x) ^ 2 ∂μ := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨_, hpos⟩ p hp hp0
    let c : Fin n → ℝ := fun i => p.coeff i.val
    have hc : c ≠ 0 := by
      intro hzero
      apply hp0
      rw [eq_sum_monomial_fin_of_degree_lt hp]
      have hc' (i : Fin n) : p.coeff i.val = 0 := congrFun hzero i
      simp only [hc', monomial_zero_right, Finset.sum_const_zero]
    have h := hpos hc
    rw [star_trivial, ← functional_sum_monomial_sq_eq_dotProduct] at h
    change 0 < ∫ x, ((∑ i : Fin n, monomial i.val (c i)) ^ 2).eval x ∂μ at h
    rw [show (∑ i : Fin n, monomial i.val (c i)) = p from
      (eq_sum_monomial_fin_of_degree_lt hp).symm] at h
    simpa only [eval_pow] using h
  · intro hpos
    refine ⟨isHermitian_hankelMomentMatrix _ _, ?_⟩
    intro c hc
    rw [star_trivial, ← functional_sum_monomial_sq_eq_dotProduct]
    let p : ℝ[X] := ∑ i : Fin n, monomial i.val (c i)
    have hp0 : p ≠ 0 := (sum_monomial_fin_eq_zero_iff c).not.mpr hc
    have hp : p.degree < n := by
      apply mem_degreeLT.mp
      apply Submodule.sum_mem
      intro i _
      apply mem_degreeLT.mpr
      exact (degree_monomial_le _ _).trans_lt (by exact_mod_cast i.isLt)
    simpa only [polynomialIntegral_apply, eval_pow] using hpos p hp hp0

/-- Hankel moment positive definiteness is exactly the support-cardinality condition,
including the empty matrix and zero measure. Source: Gautschi (2004), Section 1.1.
atlas: hankel-moment-positivity (partial), orthogonal-polynomials-measure-def (partial) -/
theorem posDef_hankelMomentMatrix_iff_le_support_encard (μ : Measure ℝ)
    (hμ : HasPolynomialMoments μ) (n : ℕ) :
    (hankelMomentMatrix (polynomialIntegral μ hμ) n).PosDef ↔
      (n : ℕ∞) ≤ μ.support.encard := by
  exact (posDef_hankelMomentMatrix_iff_integral_sq_eval_pos μ hμ n).trans
    (integral_sq_eval_pos_iff_le_support_encard μ hμ n)

/-- Positive support nondegeneracy makes the finite Hankel moment determinant nonzero. -/
theorem hankelMomentDet_ne_zero_of_le_support_encard (μ : Measure ℝ)
    (hμ : HasPolynomialMoments μ) {n : ℕ} (hn : (n : ℕ∞) ≤ μ.support.encard) :
    hankelMomentDet (polynomialIntegral μ hμ) n ≠ 0 := by
  have hpos := (posDef_hankelMomentMatrix_iff_le_support_encard μ hμ n).mpr hn
  exact isUnit_iff_ne_zero.mp (Matrix.isUnit_iff_isUnit_det _ |>.mp hpos.isUnit)

/-- For positive-measure Hankel matrices, positive definiteness is equivalent simply
to a positive determinant, since positive semidefiniteness is already known. -/
theorem posDef_hankelMomentMatrix_iff_det_pos (μ : Measure ℝ)
    (hμ : HasPolynomialMoments μ) (n : ℕ) :
    (hankelMomentMatrix (polynomialIntegral μ hμ) n).PosDef ↔
      0 < hankelMomentDet (polynomialIntegral μ hμ) n := by
  constructor
  · exact fun h => h.det_pos
  · intro h
    exact (posSemidef_hankelMomentMatrix μ hμ n).posDef_iff_det_ne_zero.mpr h.ne'

/-- Hankel moment determinants are positive exactly up to the support-cardinality
threshold. The empty determinant remains one for the zero measure. -/
theorem hankelMomentDet_pos_iff_le_support_encard (μ : Measure ℝ)
    (hμ : HasPolynomialMoments μ) (n : ℕ) :
    0 < hankelMomentDet (polynomialIntegral μ hμ) n ↔
      (n : ℕ∞) ≤ μ.support.encard :=
  (posDef_hankelMomentMatrix_iff_det_pos μ hμ n).symm.trans
    (posDef_hankelMomentMatrix_iff_le_support_encard μ hμ n)

/-- The leading Hankel moment determinants through order `n` are all positive exactly
when the order-`n` moment form is positive definite; this also includes order zero.
Source: Gautschi (2004), Chapter 1, Hankel positivity criterion.
atlas: hankel-moment-positivity (partial) -/
theorem posDef_hankelMomentMatrix_iff_leading_dets_pos (μ : Measure ℝ)
    (hμ : HasPolynomialMoments μ) (n : ℕ) :
    (hankelMomentMatrix (polynomialIntegral μ hμ) n).PosDef ↔
      ∀ k ≤ n, 0 < hankelMomentDet (polynomialIntegral μ hμ) k := by
  rw [posDef_hankelMomentMatrix_iff_le_support_encard]
  constructor
  · intro hn k hkn
    exact (hankelMomentDet_pos_iff_le_support_encard μ hμ k).mpr
      ((by exact_mod_cast hkn : (k : ℕ∞) ≤ n).trans hn)
  · intro h
    exact (hankelMomentDet_pos_iff_le_support_encard μ hμ n).mp (h n le_rfl)

end NLAlib
