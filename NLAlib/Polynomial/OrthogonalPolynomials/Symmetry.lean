import NLAlib.Polynomial.OrthogonalPolynomials.Recurrence
import Mathlib.Algebra.Polynomial.RingDivision

/-! # Reflection symmetry of monic orthogonal polynomials

Uniqueness makes reflection of a symmetric moment functional act on its monic
orthogonal polynomial by its degree parity. The measure corollary uses the native
push-forward equality under negation.
Source: Gautschi (2004), Theorem 1.17; operator derivations OP16–OP19.
-/

noncomputable section

open Polynomial MeasureTheory

namespace NLAlib

variable {𝕜 : Type*} [Field 𝕜]

/-- Reflection and the degree sign preserve monic orthogonality for a symmetric
moment functional. No positive measure or complex conjugation is needed. -/
theorem IsMonicOrthogonalPolynomial.neg_one_pow_mul_comp_neg_X
    {L : 𝕜[X] →ₗ[𝕜] 𝕜} {n : ℕ} {p : 𝕜[X]}
    (hp : IsMonicOrthogonalPolynomial L n p)
    (hs : ∀ r : 𝕜[X], L (r.comp (-X)) = L r) :
    IsMonicOrthogonalPolynomial L n ((-1 : 𝕜[X]) ^ n * p.comp (-X)) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hp.natDegree_eq] using hp.monic.neg_one_pow_natDegree_mul_comp_neg_X
  · rw [natDegree_mul, natDegree_comp]
    all_goals simp [hp.natDegree_eq, hp.monic.ne_zero]
  · intro r hr
    rw [show (-1 : 𝕜[X]) ^ n = C ((-1 : 𝕜) ^ n) by simp, mul_assoc, C_mul', map_smul]
    have hswap : L (p.comp (-X) * r) = L (p * r.comp (-X)) := by
      simpa only [mul_comp, comp_neg_X_comp_neg_X] using hs (p * r.comp (-X))
    rw [hswap, hp.orthogonal _ (by simpa only [degree_comp_neg_X] using hr), smul_zero]

/-- For nonsingular symmetric moments, the monic polynomial has the parity of
its degree. Source: Gautschi (2004), Theorem 1.17.
atlas: symmetric-measure-even-odd-reduction (partial) -/
theorem neg_one_pow_mul_comp_neg_X_monicOrthogonalPolynomial
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) (hL : hankelMomentDet L n ≠ 0)
    (hs : ∀ r : 𝕜[X], L (r.comp (-X)) = L r) :
    (-1 : 𝕜[X]) ^ n * (monicOrthogonalPolynomial L n).comp (-X) =
      monicOrthogonalPolynomial L n := by
  have hp := isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L hL
  exact (hp.neg_one_pow_mul_comp_neg_X hs).eq_of_hankelMomentDet_ne_zero hp hL

/-- A real measure invariant under negation gives a reflection-invariant moment
functional. This is the native measure-to-polynomial symmetry bridge. -/
theorem polynomialIntegral_comp_neg_X {μ : Measure ℝ} (hμ : HasPolynomialMoments μ)
    (hs : Measure.map (fun x : ℝ => -x) μ = μ) (p : ℝ[X]) :
    polynomialIntegral μ hμ (p.comp (-X)) = polynomialIntegral μ hμ p := by
  simp only [polynomialIntegral_apply, eval_comp, eval_neg, eval_X]
  rw [← integral_map_of_stronglyMeasurable measurable_neg p.continuous.stronglyMeasurable, hs]

/-- The monic polynomial of a symmetric positive measure has its degree parity,
including the last finite-support polynomial. Source: Gautschi (2004), Theorem 1.17.
atlas: symmetric-measure-even-odd-reduction (partial) -/
theorem neg_one_pow_mul_comp_neg_X_monicOrthogonalPolynomial_polynomialIntegral
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ)
    (hs : Measure.map (fun x : ℝ => -x) μ = μ) {n : ℕ}
    (hn : (n : ℕ∞) ≤ μ.support.encard) :
    (-1 : ℝ[X]) ^ n * (monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).comp (-X) =
      monicOrthogonalPolynomial (polynomialIntegral μ hμ) n :=
  neg_one_pow_mul_comp_neg_X_monicOrthogonalPolynomial (polynomialIntegral μ hμ) n
    (hankelMomentDet_ne_zero_of_le_support_encard μ hμ hn)
    (polynomialIntegral_comp_neg_X hμ hs)

/-- Each real monic recurrence diagonal is zero for reflection-invariant moments,
including the boundary where its squared norm vanishes.
Source: Gautschi (2004), Theorem 1.17.
atlas: symmetric-measure-even-odd-reduction (partial) -/
theorem orthogonalRecurrenceAlpha_eq_zero_of_comp_neg_X
    (L : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ) (hL : hankelMomentDet L n ≠ 0)
    (hs : ∀ r : ℝ[X], L (r.comp (-X)) = L r) : orthogonalRecurrenceAlpha L n = 0 := by
  let p := monicOrthogonalPolynomial L n
  have hpar := neg_one_pow_mul_comp_neg_X_monicOrthogonalPolynomial L n hL hs
  have hsign : ((-1 : ℝ[X]) ^ n) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    simp
  have hsq : (p.comp (-X)) ^ 2 = p ^ 2 := by
    have h := congrArg (fun r : ℝ[X] => r ^ 2) hpar
    rw [mul_pow, hsign, one_mul] at h
    exact h
  have h := hs (X * p ^ 2)
  rw [mul_comp, pow_comp, X_comp, hsq, neg_mul, map_neg] at h
  have hz : L (X * p ^ 2) = 0 := by linarith
  change L (X * p ^ 2) / orthogonalPolynomialNorm L n = 0
  rw [hz, zero_div]

/-- All real recurrence diagonal coefficients of a symmetric positive measure
vanish before and at finite-support termination.
Source: Gautschi (2004), Theorem 1.17.
atlas: symmetric-measure-even-odd-reduction (partial) -/
theorem orthogonalRecurrenceAlpha_polynomialIntegral_eq_zero {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) (hs : Measure.map (fun x : ℝ => -x) μ = μ) {n : ℕ}
    (hn : (n : ℕ∞) ≤ μ.support.encard) :
    orthogonalRecurrenceAlpha (polynomialIntegral μ hμ) n = 0 :=
  orthogonalRecurrenceAlpha_eq_zero_of_comp_neg_X _ n
    (hankelMomentDet_ne_zero_of_le_support_encard μ hμ hn)
    (polynomialIntegral_comp_neg_X hμ hs)

end NLAlib
