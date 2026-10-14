import NLAlib.Krylov.Quadrature.SpectralMeasure
import NLAlib.Polynomial.OrthogonalPolynomials.MeasureOrthogonality
import NLAlib.Krylov.Spaces.MinimalPolynomial

/-!
# Polynomial spectral moments and Krylov grade

Actual finite spectral measures have polynomial moments, their Hankel matrices
are Krylov Gram matrices, and their support cardinality is the vector's grade.
This leaf supplies the trusted measure API independently of any Lanczos
recursion or decomposition. Source: Gautschi (2004), §1.1; OP1–OP4.
-/

noncomputable section
open Matrix Polynomial MeasureTheory Finset
open scoped Matrix Polynomial
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A finite spectral measure has every polynomial moment, including zero
starting vectors and empty matrices. -/
theorem hasPolynomialMoments_spectralMeasure {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (b : n → ℝ) : HasPolynomialMoments (spectralMeasure hA b) := by
  intro p
  unfold spectralMeasure
  exact integrable_finsetSum_measure.mpr fun i _ =>
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- The moment matrix of a spectral measure is the Gram matrix of the first
Krylov vectors, without a nonsingularity assumption.
Source: Gautschi (2004), Section 1.1; operator derivations OP2.
atlas: hankel-moment-positivity (partial) -/
theorem hankelMomentMatrix_spectralMeasure_eq_transpose_mul
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (b : n → ℝ) (q : ℕ) :
    let K : Matrix n (Fin q) ℝ := fun r j => ((A ^ j.val) *ᵥ b) r
    hankelMomentMatrix
      (polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b))
      q = Kᵀ * K := by
  ext i j
  change (∫ x, (X ^ (i.val + j.val) : ℝ[X]).eval x ∂spectralMeasure hA b) =
    ((A ^ i.val) *ᵥ b) ⬝ᵥ ((A ^ j.val) *ᵥ b)
  rw [pow_add]
  simp only [eval_mul]
  rw [integral_eval_mul_eval_spectralMeasure]
  simp only [map_pow, aeval_X]

/-- The number of distinct positive-mass spectral support points is exactly
the vector's Krylov grade. Zero vectors and empty matrices give zero support.
Source: Gautschi (2004), Sections 1.1 and 2.2; operator derivations OP2.
atlas: hankel-moment-positivity (partial), orthogonal-polynomials-measure-def (partial) -/
theorem support_encard_spectralMeasure_eq_krylovGrade {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (b : n → ℝ) :
    (spectralMeasure hA b).support.encard = (krylovGrade A b : ℕ∞) := by
  let μ := spectralMeasure hA b
  let hμ := hasPolynomialMoments_spectralMeasure hA b
  have hle : (krylovGrade A b : ℕ∞) ≤ μ.support.encard := by
    apply (integral_sq_eval_pos_iff_le_support_encard μ hμ _).mp
    intro p hp hp0
    have hv0 : aeval A p *ᵥ b ≠ 0 := fun h => hp0 (eq_zero_of_aeval_mulVec_eq_zero hp h)
    have hpos := (dotProduct_star_self_pos_iff (v := aeval A p *ᵥ b)).mpr hv0
    simpa only [μ, pow_two, integral_eval_mul_eval_spectralMeasure, star_trivial] using hpos
  have hmin0 : (∫ x, (vectorMinpoly A b).eval x ^ 2 ∂μ) = 0 := by
    simp only [μ, pow_two, integral_eval_mul_eval_spectralMeasure,
      aeval_vectorMinpoly_mulVec, zero_dotProduct]
  have hs := (integral_sq_eval_eq_zero_iff (vectorMinpoly A b)
    (hμ.integrable_sq _)).mp hmin0
  have hsub : μ.support ⊆ ((vectorMinpoly A b).roots.toFinset : Set ℝ) := by
    intro x hx
    simpa only [Finset.mem_coe, Multiset.mem_toFinset,
      mem_roots (vectorMinpoly_monic A b).ne_zero, IsRoot.def] using hs x hx
  have hcard : (vectorMinpoly A b).roots.toFinset.card ≤ krylovGrade A b := by
    exact (Multiset.toFinset_card_le _).trans
      ((card_roots' _).trans_eq (natDegree_vectorMinpoly A b))
  exact le_antisymm ((Set.encard_mono hsub).trans (by exact_mod_cast hcard)) hle

/-- A spectral-measure Hankel matrix is positive definite exactly through the
Krylov grade, including its empty order-zero case.
Source: Gautschi (2004), Section 1.1; operator derivations OP2.
atlas: hankel-moment-positivity (partial) -/
theorem posDef_hankelMomentMatrix_spectralMeasure_iff {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (b : n → ℝ) (q : ℕ) :
    (hankelMomentMatrix
      (polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b))
      q).PosDef ↔ q ≤ krylovGrade A b := by
  rw [posDef_hankelMomentMatrix_iff_le_support_encard,
    support_encard_spectralMeasure_eq_krylovGrade]
  exact_mod_cast Iff.rfl

end NLAlib
