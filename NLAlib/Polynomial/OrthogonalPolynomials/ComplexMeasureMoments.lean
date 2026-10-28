import NLAlib.Polynomial.Quadrature.ComplexExactness
import NLAlib.Polynomial.OrthogonalPolynomials.MomentPositivity

/-!
# Complex polynomial moments of a real measure

Actual complex Bochner integrals extend the real moment functional. Finite
Hankel nondegeneracy and canonical monic polynomials commute with this scalar
extension. Thus nonreal modification roots do not require a new measure law.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial MeasureTheory Finset
namespace NLAlib

/-- Integration of complex polynomial evaluation on the original real variable. -/
def complexPolynomialIntegral (μ : Measure ℝ) (hμ : HasPolynomialMoments μ) : ℂ[X] →ₗ[ℂ] ℂ where
  toFun p := ∫ x : ℝ, p.eval (x : ℂ) ∂μ
  map_add' p q := by
    simp only [eval_add]
    exact integral_add (hμ.integrable_complex_eval p) (hμ.integrable_complex_eval q)
  map_smul' c p := by
    simp only [eval_smul, smul_eq_mul, RingHom.id_apply]
    exact integral_const_mul c _

/-- The complex moment functional is the actual Bochner integral. -/
@[simp] theorem complexPolynomialIntegral_apply (μ : Measure ℝ) (hμ : HasPolynomialMoments μ)
    (p : ℂ[X]) : complexPolynomialIntegral μ hμ p = ∫ x : ℝ, p.eval (x : ℂ) ∂μ := rfl

/-- Real polynomial moments are unchanged under scalar extension. -/
theorem complexPolynomialIntegral_apply_map (μ : Measure ℝ) (hμ : HasPolynomialMoments μ)
    (p : ℝ[X]) :
    complexPolynomialIntegral μ hμ (p.map Complex.ofRealHom) = (polynomialIntegral μ hμ p : ℂ) := by
  change (∫ x : ℝ, (p.map Complex.ofRealHom).eval (Complex.ofRealHom x) ∂μ) = _
  simp_rw [eval_map_apply]
  exact integral_complex_ofReal

/-- The finite complex Hankel system is exactly the scalar extension of the
real Hankel system, without higher-moment assumptions. -/
theorem hankelMomentMatrix_complexPolynomialIntegral (μ : Measure ℝ)
    (hμ : HasPolynomialMoments μ) (n : ℕ) :
    hankelMomentMatrix (complexPolynomialIntegral μ hμ) n =
      (hankelMomentMatrix (polynomialIntegral μ hμ) n).map Complex.ofRealHom := by
  ext i j
  have h := complexPolynomialIntegral_apply_map μ hμ (X^(i.val+j.val))
  simpa only [Polynomial.map_pow, Polynomial.map_X, Matrix.map_apply, hankelMomentMatrix,
    Complex.ofRealHom_eq_coe] using h

/-- The complex Hankel determinant is the real determinant viewed in `ℂ`. -/
theorem hankelMomentDet_complexPolynomialIntegral (μ : Measure ℝ)
    (hμ : HasPolynomialMoments μ) (n : ℕ) :
    hankelMomentDet (complexPolynomialIntegral μ hμ) n =
      ((hankelMomentDet (polynomialIntegral μ hμ) n : ℝ) : ℂ) := by
  rw [hankelMomentDet, hankelMomentMatrix_complexPolynomialIntegral]
  exact (Complex.ofRealHom.map_det (hankelMomentMatrix (polynomialIntegral μ hμ) n)).symm

/-- Complex Hankel nondegeneracy follows from the actual real support count. -/
theorem hankelMomentDet_complexPolynomialIntegral_ne_zero {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) {n : ℕ} (hs : (n : ℕ∞) ≤ μ.support.encard) :
    hankelMomentDet (complexPolynomialIntegral μ hμ) n ≠ 0 := by
  rw [hankelMomentDet_complexPolynomialIntegral]
  exact Complex.ofReal_ne_zero.mpr (hankelMomentDet_ne_zero_of_le_support_encard μ hμ hs)

/-- Complex scalar extension preserves the canonical finite monic polynomial.
The nondegeneracy assumption is only at its requested order. -/
theorem monicOrthogonalPolynomial_complexPolynomialIntegral_eq_map
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {n : ℕ}
    (hn : hankelMomentDet (polynomialIntegral μ hμ) n ≠ 0) :
    monicOrthogonalPolynomial (complexPolynomialIntegral μ hμ) n =
      (monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom := by
  let p := monicOrthogonalPolynomial (polynomialIntegral μ hμ) n
  have hp := isMonicOrthogonalPolynomial_monicOrthogonalPolynomial (polynomialIntegral μ hμ) hn
  have hnc : hankelMomentDet (complexPolynomialIntegral μ hμ) n ≠ 0 := by
    rw [hankelMomentDet_complexPolynomialIntegral]
    exact Complex.ofReal_ne_zero.mpr hn
  apply (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial (complexPolynomialIntegral μ hμ) hnc).eq_of_hankelMomentDet_ne_zero _ hnc
  refine ⟨hp.monic.map _, ?_, ?_⟩
  · rw [natDegree_map, hp.natDegree_eq]
  · intro q hq
    by_cases hq0 : q=0
    · simp [hq0]
    have hqd := (natDegree_lt_iff_degree_lt hq0).mpr hq
    rw [q.as_sum_range' (q.natDegree+1) (Nat.lt_succ_self _), mul_sum, map_sum]
    apply Finset.sum_eq_zero
    intro j hj
    have hjn : j < n := by have := Finset.mem_range.mp hj; omega
    have he : p.map Complex.ofRealHom * monomial j (q.coeff j) =
        C (q.coeff j) * ((p * X^j).map Complex.ofRealHom) := by
      simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
      rw [← C_mul_X_pow_eq_monomial]
      ring
    rw [he, C_mul', map_smul, complexPolynomialIntegral_apply_map]
    rw [hp.orthogonal (X^j) (by rw [degree_X_pow]; exact_mod_cast hjn)]
    simp

end NLAlib
