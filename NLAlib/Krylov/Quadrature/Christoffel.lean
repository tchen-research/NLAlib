import NLAlib.Krylov.Quadrature.SpectralMoments
import NLAlib.Polynomial.OrthogonalPolynomials.ChristoffelFactorization
import NLAlib.Polynomial.OrthogonalPolynomials.PositiveMomentFunctional

/-!
# Christoffel modification of actual spectral moments

Weighting the spectral measure by `X` gives the actual matrix energy pairing.
Positive definiteness yields finite weighted moment nondegeneracy and zero-shift
Christoffel quotients through the Krylov grade. Source: Gautschi (2004), §1.3;
operator re-derivations, SPD interpretation after AQ15.
-/

noncomputable section
open Polynomial Matrix MeasureTheory
open scoped Matrix
namespace NLAlib
variable {m : Type*} [Fintype m] [DecidableEq m] {A : Matrix m m ℝ} {b : m → ℝ}

/-- The `X`-weighted actual spectral moment pairing is the matrix energy
pairing of polynomial Krylov vectors.
Source: operator re-derivations, the SPD Christoffel/CG connection.
atlas: kernel-polynomials-christoffel (partial) -/
theorem polynomialWeightedFunctional_spectralMeasure_X_mul
    (hA : A.IsHermitian) (b : m → ℝ) (p q : ℝ[X]) :
    polynomialWeightedFunctional
      (polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b))
      X (p*q) = (aeval A p *ᵥ b) ⬝ᵥ (A *ᵥ (aeval A q *ᵥ b)) := by
  have h := integral_eval_mul_eval_spectralMeasure hA b p (X*q)
  simp only [eval_mul, eval_X, map_mul, aeval_X, ← Matrix.mulVec_mulVec] at h
  change (∫ x, (X*(p*q)).eval x ∂spectralMeasure hA b) = _
  simp only [eval_mul, eval_X]
  rw [← h]
  apply integral_congr_ae
  filter_upwards with x
  ring

/-- A positive definite matrix gives a positive definite `X`-weighted spectral
Hankel system at every order through the vector's Krylov grade.
Source: the actual matrix energy pairing and polynomial Krylov injectivity.
atlas: kernel-polynomials-christoffel (partial) -/
theorem posDef_hankelMomentMatrix_polynomialWeightedFunctional_spectralMeasure_X
    (hA : A.PosDef) (b : m → ℝ) {k : ℕ} (hk : k ≤ krylovGrade A b) :
    (hankelMomentMatrix (polynomialWeightedFunctional
      (polynomialIntegral (spectralMeasure hA.isHermitian b)
        (hasPolynomialMoments_spectralMeasure hA.isHermitian b)) X) k).PosDef := by
  rw [posDef_hankelMomentMatrix_iff_functional_sq_pos]
  intro p hp hp0
  rw [pow_two, polynomialWeightedFunctional_spectralMeasure_X_mul]
  have hv0 : aeval A p *ᵥ b ≠ 0 := fun h =>
    hp0 (eq_zero_of_aeval_mulVec_eq_zero (hp.trans_le (by exact_mod_cast hk)) h)
  simpa only [star_trivial] using hA.dotProduct_mulVec_pos hv0

/-- Before Krylov termination, the original monic spectral polynomial is
nonzero at zero for a positive definite matrix. This proves that the actual
zero-shift Christoffel quotient is defined without a denominator hypothesis.
Source: positive energy orthogonality, the SPD Christoffel/CG connection.
atlas: kernel-polynomials-christoffel (partial) -/
theorem eval_monicOrthogonalPolynomial_spectralMeasure_zero_ne_zero
    (hA : A.PosDef) (b : m → ℝ) {k : ℕ} (hk : k ≤ krylovGrade A b) :
    (monicOrthogonalPolynomial
      (polynomialIntegral (spectralMeasure hA.isHermitian b)
        (hasPolynomialMoments_spectralMeasure hA.isHermitian b)) k).eval 0 ≠ 0 := by
  let L := polynomialIntegral (spectralMeasure hA.isHermitian b)
    (hasPolynomialMoments_spectralMeasure hA.isHermitian b)
  let P := monicOrthogonalPolynomial L k
  have hL : hankelMomentDet L k ≠ 0 := by
    apply hankelMomentDet_ne_zero_of_le_support_encard
    rw [support_encard_spectralMeasure_eq_krylovGrade]
    exact_mod_cast hk
  have hP := isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L hL
  intro hz
  obtain ⟨r, hr⟩ := dvd_iff_isRoot.mpr hz
  have hP0 : P ≠ 0 := hP.monic.ne_zero
  have hr0 : r ≠ 0 := by
    intro h
    have := hr
    rw [h, mul_zero] at this
    exact hP0 this
  have hrd : r.degree < k := by
    have hd := congrArg natDegree hr
    rw [natDegree_monicOrthogonalPolynomial,
      natDegree_mul (monic_X_sub_C 0).ne_zero hr0, natDegree_X_sub_C] at hd
    rw [degree_eq_natDegree hr0]
    exact_mod_cast (show r.natDegree < k by omega)
  have horth := hP.orthogonal r hrd
  have henergy : polynomialWeightedFunctional L X (r*r) = 0 := by
    change L (X*(r*r)) = 0
    change L (monicOrthogonalPolynomial L k * r) = 0 at horth
    rw [hr] at horth
    simpa only [C_0, sub_zero, mul_assoc] using horth
  have hpos := (posDef_hankelMomentMatrix_iff_functional_sq_pos _ k).mp
    (posDef_hankelMomentMatrix_polynomialWeightedFunctional_spectralMeasure_X hA b hk) r hrd hr0
  rw [pow_two] at hpos
  exact hpos.ne' henergy

/-- The zero-shift Christoffel quotient of the actual spectral measure is its
canonical energy-orthogonal polynomial before termination.
Source: operator re-derivations, the SPD Christoffel/CG connection.
atlas: kernel-polynomials-christoffel (partial) -/
theorem monicOrthogonalPolynomial_weighted_spectralMeasure_eq_christoffelPolynomial
    (hA : A.PosDef) (b : m → ℝ) {k : ℕ} (hk : k < krylovGrade A b) :
    monicOrthogonalPolynomial (polynomialWeightedFunctional
      (polynomialIntegral (spectralMeasure hA.isHermitian b)
        (hasPolynomialMoments_spectralMeasure hA.isHermitian b)) X) k =
      christoffelPolynomial (polynomialIntegral (spectralMeasure hA.isHermitian b)
        (hasPolynomialMoments_spectralMeasure hA.isHermitian b)) 0 k := by
  have hL (j : ℕ) (hj : j ≤ k+1) :
      hankelMomentDet (polynomialIntegral (spectralMeasure hA.isHermitian b)
        (hasPolynomialMoments_spectralMeasure hA.isHermitian b)) j ≠ 0 := by
    apply hankelMomentDet_ne_zero_of_le_support_encard
    rw [support_encard_spectralMeasure_eq_krylovGrade]
    exact_mod_cast (show j ≤ krylovGrade A b by omega)
  simpa only [C_0, sub_zero] using
    monicOrthogonalPolynomial_polynomialWeightedFunctional_X_sub_C _ k hL
      (eval_monicOrthogonalPolynomial_spectralMeasure_zero_ne_zero hA b hk.le)

/-- The actual monic spectral Jacobi matrix has its zero-shift Christoffel
lower/upper factorization at every size through the Krylov grade. Every quotient
denominator and pivot is derived to be nonzero from positive definiteness.
Source: AQ15, actual finite SPD spectral-measure specialization.
atlas: kernel-polynomials-christoffel (partial) -/
theorem monicJacobiMatrix_spectralMeasure_eq_christoffel_factors
    (hA : A.PosDef) (b : m → ℝ) {q : ℕ} (hq : q ≤ krylovGrade A b) :
    let L := polynomialIntegral (spectralMeasure hA.isHermitian b)
      (hasPolynomialMoments_spectralMeasure hA.isHermitian b)
    monicJacobiMatrix q (orthogonalRecurrenceAlpha L) (orthogonalRecurrenceBeta L) =
      darbouxLowerMatrix q (christoffelElimination L 0) *
        darbouxUpperMatrix q (christoffelQuotient L 0) := by
  let L := polynomialIntegral (spectralMeasure hA.isHermitian b)
    (hasPolynomialMoments_spectralMeasure hA.isHermitian b)
  have hL (k : ℕ) (hk : k ≤ q) : hankelMomentDet L k ≠ 0 := by
    apply hankelMomentDet_ne_zero_of_le_support_encard
    rw [support_encard_spectralMeasure_eq_krylovGrade]
    exact_mod_cast hk.trans hq
  have hz (k : ℕ) (hk : k ≤ q) : (monicOrthogonalPolynomial L k).eval 0 ≠ 0 :=
    eval_monicOrthogonalPolynomial_spectralMeasure_zero_ne_zero hA b (hk.trans hq)
  simpa only [zero_smul, sub_zero] using
    monicJacobiMatrix_sub_scalar_one_eq_christoffel_factors_of_finite q hL hz

/-- The actual energy-weighted spectral Jacobi matrix has the reversed
Christoffel factors and exact finite last-coordinate correction, including
the full finite-support size and the empty size.
Source: AQ15, actual finite SPD spectral-measure specialization.
atlas: kernel-polynomials-christoffel (partial) -/
theorem monicJacobiMatrix_weighted_spectralMeasure_eq_reversed_factors_add_boundary
    (hA : A.PosDef) (b : m → ℝ) {q : ℕ} (hq : q ≤ krylovGrade A b) :
    let L := polynomialIntegral (spectralMeasure hA.isHermitian b)
      (hasPolynomialMoments_spectralMeasure hA.isHermitian b)
    monicJacobiMatrix q (orthogonalRecurrenceAlpha (polynomialWeightedFunctional L X))
        (orthogonalRecurrenceBeta (polynomialWeightedFunctional L X)) =
      darbouxUpperMatrix q (christoffelQuotient L 0) *
        darbouxLowerMatrix q (christoffelElimination L 0) +
          christoffelElimination L 0 (q-1) • terminalCoordinateMatrix q := by
  let L := polynomialIntegral (spectralMeasure hA.isHermitian b)
    (hasPolynomialMoments_spectralMeasure hA.isHermitian b)
  have hL (k : ℕ) (hk : k ≤ q) : hankelMomentDet L k ≠ 0 := by
    apply hankelMomentDet_ne_zero_of_le_support_encard
    rw [support_encard_spectralMeasure_eq_krylovGrade]
    exact_mod_cast hk.trans hq
  have hz (k : ℕ) (hk : k ≤ q) : (monicOrthogonalPolynomial L k).eval 0 ≠ 0 :=
    eval_monicOrthogonalPolynomial_spectralMeasure_zero_ne_zero hA b (hk.trans hq)
  simpa only [C_0, sub_zero, zero_smul, add_zero] using
    monicJacobiMatrix_christoffel_eq_reversed_factors_add_boundary_of_finite q hL hz

end NLAlib
