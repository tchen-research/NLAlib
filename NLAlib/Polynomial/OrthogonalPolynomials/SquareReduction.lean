import NLAlib.Polynomial.OrthogonalPolynomials.SquareMeasures

/-! # Even and odd orthogonal polynomials under squaring

For a symmetric positive measure, the even monic polynomials are those of its
square-map pushforward. The odd polynomials are `X` times those of the square-map
pushforward of its square-density measure. Monomial tests prove the identities
without an infinite polynomial completion.
Source: Gautschi (2004), Theorem 1.18; operator derivations OP17–OP19.
-/

noncomputable section

open Polynomial MeasureTheory

namespace NLAlib

private theorem functional_comp_X_sq_mul_X_pow_eq_zero_of_odd
    (L : ℝ[X] →ₗ[ℝ] ℝ) (hs : ∀ p : ℝ[X], L (p.comp (-X)) = L p)
    (p : ℝ[X]) {j : ℕ} (hj : Odd j) : L (p.comp (X ^ 2) * X ^ j) = 0 := by
  have hcomp : (p.comp (X ^ 2)).comp (-X) = p.comp (X ^ 2) := by
    rw [comp_assoc]
    congr 1
    simp [pow_comp]
  have h := hs (p.comp (X ^ 2) * X ^ j)
  rw [mul_comp, hcomp, pow_comp, X_comp, hj.neg_pow, mul_neg, map_neg] at h
  linarith

/-- Even monic polynomials of a symmetric measure are the monic polynomials
of the native square-map pushforward composed with `X²`, including termination.
Source: Gautschi (2004), Theorem 1.18.
atlas: symmetric-measure-even-odd-reduction (partial) -/
theorem monicOrthogonalPolynomial_two_mul_eq_comp_X_sq
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ)
    (hs : Measure.map (fun x : ℝ => -x) μ = μ) (k : ℕ)
    (hk : (2 * k : ℕ∞) ≤ μ.support.encard) :
    monicOrthogonalPolynomial (polynomialIntegral μ hμ) (2 * k) =
      (monicOrthogonalPolynomial
        (polynomialIntegral (Measure.map (fun x : ℝ => x ^ 2) μ) (hasPolynomialMoments_map_sq hμ))
        k).comp (X ^ 2) := by
  let L := polynomialIntegral μ hμ
  let ν := Measure.map (fun x : ℝ => x ^ 2) μ
  let hν := hasPolynomialMoments_map_sq hμ
  let P := monicOrthogonalPolynomial (polynomialIntegral ν hν) k
  have hνdet := hankelMomentDet_map_sq_ne_zero hμ hk
  have hP := isMonicOrthogonalPolynomial_monicOrthogonalPolynomial (polynomialIntegral ν hν) hνdet
  have hspec : IsMonicOrthogonalPolynomial L (2 * k) (P.comp (X ^ 2)) := by
    refine ⟨?_, ?_, ?_⟩
    · exact hP.monic.expand (by decide : 0 < 2)
    · change (expand ℝ 2 P).natDegree = 2 * k
      rw [natDegree_expand, hP.natDegree_eq]
      omega
    · intro q hq
      apply functional_mul_eq_zero_of_monomial_tests L _ hq
      intro j
      by_cases hj : Even j.val
      · obtain ⟨l, hjeq⟩ := even_iff_exists_two_mul.mp hj
        have hl : l < k := by have := j.isLt; omega
        have h := hP.orthogonal (X ^ l) (by rw [degree_X_pow]; exact_mod_cast hl)
        change polynomialIntegral ν hν (P * X ^ l) = 0 at h
        rw [polynomialIntegral_map_sq] at h
        simpa only [L, hjeq, mul_comp, pow_comp, X_comp, ← pow_mul] using h
      · exact functional_comp_X_sq_mul_X_pow_eq_zero_of_odd L
          (polynomialIntegral_comp_neg_X hμ hs) P (Nat.not_even_iff_odd.mp hj)
  exact (isMonicOrthogonalPolynomial_polynomialIntegral μ hμ hk).eq_of_hankelMomentDet_ne_zero
    hspec (hankelMomentDet_ne_zero_of_le_support_encard μ hμ hk)

/-- Odd monic polynomials of a symmetric measure are `X` times the polynomials
of the native square-map pushforward of `x² dμ`, composed with `X²`.
Source: Gautschi (2004), Theorem 1.18.
atlas: symmetric-measure-even-odd-reduction (partial) -/
theorem monicOrthogonalPolynomial_two_mul_add_one_eq_X_mul_comp_X_sq
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ)
    (hs : Measure.map (fun x : ℝ => -x) μ = μ) (k : ℕ)
    (hk : (2 * k + 1 : ℕ∞) ≤ μ.support.encard) :
    monicOrthogonalPolynomial (polynomialIntegral μ hμ) (2 * k + 1) =
      X * (monicOrthogonalPolynomial
        (polynomialIntegral
          (Measure.map (fun x : ℝ => x ^ 2)
            (μ.withDensity (fun x : ℝ => ENNReal.ofReal (x ^ 2))))
          (hasPolynomialMoments_map_sq (hasPolynomialMoments_withDensity_sq hμ))) k).comp (X ^ 2) := by
  let L := polynomialIntegral μ hμ
  let ν := Measure.map (fun x : ℝ => x ^ 2)
    (μ.withDensity (fun x : ℝ => ENNReal.ofReal (x ^ 2)))
  let hν := hasPolynomialMoments_map_sq (hasPolynomialMoments_withDensity_sq hμ)
  let P := monicOrthogonalPolynomial (polynomialIntegral ν hν) k
  have hνdet := hankelMomentDet_map_sq_withDensity_sq_ne_zero hμ hk
  have hP := isMonicOrthogonalPolynomial_monicOrthogonalPolynomial (polynomialIntegral ν hν) hνdet
  have hPcomp : (P.comp (X ^ 2)).Monic := hP.monic.expand (by decide : 0 < 2)
  have hspec : IsMonicOrthogonalPolynomial L (2 * k + 1) (X * P.comp (X ^ 2)) := by
    refine ⟨monic_X.mul hPcomp, ?_, ?_⟩
    · rw [natDegree_X_mul hPcomp.ne_zero]
      change (expand ℝ 2 P).natDegree + 1 = 2 * k + 1
      rw [natDegree_expand, hP.natDegree_eq]
      omega
    · intro q hq
      apply functional_mul_eq_zero_of_monomial_tests L _ hq
      intro j
      by_cases hj : Even j.val
      · rw [show X * P.comp (X ^ 2) * X ^ j.val = P.comp (X ^ 2) * X ^ (j.val + 1) by
          rw [pow_succ]; ring]
        exact functional_comp_X_sq_mul_X_pow_eq_zero_of_odd L
          (polynomialIntegral_comp_neg_X hμ hs) P hj.add_one
      · obtain ⟨l, hjeq⟩ := Odd.exists_bit1 (Nat.not_even_iff_odd.mp hj)
        have hl : l < k := by have := j.isLt; omega
        have h := hP.orthogonal (X ^ l) (by rw [degree_X_pow]; exact_mod_cast hl)
        change polynomialIntegral ν hν (P * X ^ l) = 0 at h
        rw [polynomialIntegral_map_sq _ (hasPolynomialMoments_withDensity_sq hμ),
          polynomialIntegral_withDensity_sq μ hμ] at h
        have hid : X * P.comp (X ^ 2) * X ^ (2 * l + 1) =
            X ^ 2 * (P * X ^ l).comp (X ^ 2) := by
          simp only [mul_comp, pow_comp, X_comp, ← pow_mul, pow_add, pow_one]
          ring
        change L (X * P.comp (X ^ 2) * X ^ j.val) = 0
        rw [hjeq, hid]
        exact h
  exact (isMonicOrthogonalPolynomial_polynomialIntegral μ hμ hk).eq_of_hankelMomentDet_ne_zero
    hspec (hankelMomentDet_ne_zero_of_le_support_encard μ hμ hk)

end NLAlib
