import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Strict Laguerre inequality for real-rooted polynomials

The multiplicative identity for `p'²-p p''` reduces the strict inequality
away from the roots to products of real linear factors.
-/

noncomputable section
open Polynomial Real Set
namespace NLAlib

/-- The Laguerre expression is additive under products with squared factors.
Source: the product rule; helper for interval Lebesgue peaks. -/
theorem polynomial_laguerre_mul (p q : ℝ[X]) (x : ℝ) :
    (p * q).derivative.eval x ^ 2 - (p * q).eval x * (p * q).derivative.derivative.eval x =
      q.eval x ^ 2 * (p.derivative.eval x ^ 2 - p.eval x * p.derivative.derivative.eval x) +
      p.eval x ^ 2 * (q.derivative.eval x ^ 2 - q.eval x * q.derivative.derivative.eval x) := by
  simp only [derivative_mul, derivative_add, eval_add, eval_mul]
  ring

private theorem laguerre_prod_nonneg (m : Multiset ℝ) (x : ℝ) :
    let p : ℝ[X] := (m.map (X - C ·)).prod
    0 ≤ p.derivative.eval x ^ 2 - p.eval x * p.derivative.derivative.eval x := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons r m ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [polynomial_laguerre_mul]
    simp only [derivative_sub, derivative_X, derivative_C, sub_zero, derivative_one,
      eval_one, one_pow, eval_sub, eval_X, eval_C, eval_zero, mul_zero, sub_zero, mul_one]
    exact add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) ih)

private theorem laguerre_prod_pos (m : Multiset ℝ) (hm : m ≠ 0) (x : ℝ)
    (hx : ((m.map (X - C ·)).prod : ℝ[X]).eval x ≠ 0) :
    let p : ℝ[X] := (m.map (X - C ·)).prod
    0 < p.derivative.eval x ^ 2 - p.eval x * p.derivative.derivative.eval x := by
  obtain hzero | ⟨r, hr⟩ := m.empty_or_exists_mem
  · exact (hm hzero).elim
  obtain ⟨m, rfl⟩ := Multiset.exists_cons_of_mem hr
  have hq : ((m.map (X - C ·)).prod : ℝ[X]).eval x ≠ 0 := by
    simp only [Multiset.map_cons, Multiset.prod_cons, eval_mul] at hx
    exact (mul_ne_zero_iff.mp hx).2
  simp only [Multiset.map_cons, Multiset.prod_cons]
  rw [polynomial_laguerre_mul]
  simp only [derivative_sub, derivative_X, derivative_C, sub_zero, derivative_one,
    eval_one, one_pow, eval_sub, eval_X, eval_C, eval_zero, mul_zero, sub_zero, mul_one]
  exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hq)
    (mul_nonneg (sq_nonneg _) (laguerre_prod_nonneg m x))

/-- A nonconstant polynomial that splits over the reals satisfies the strict
Laguerre inequality at every point where it does not vanish.
Source: products of real linear factors; focused reroutes, interval peak argument. -/
theorem polynomial_laguerre_pos_of_splits {p : ℝ[X]} (hp : p.Splits)
    (hpc : p.derivative ≠ 0) {x : ℝ} (hx : p.eval x ≠ 0) :
    0 < p.derivative.eval x ^ 2 - p.eval x * p.derivative.derivative.eval x := by
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset.mp hp
  have hm0 : m ≠ 0 := by
    intro hm0
    rw [hm0, Multiset.map_zero, Multiset.prod_zero, mul_one] at hm
    apply hpc
    rw [hm, derivative_C]
  have hlc : p.leadingCoeff ≠ 0 := by
    intro h
    exact hx (by rw [leadingCoeff_eq_zero.mp h, eval_zero])
  have hprod : ((m.map (X - C ·)).prod : ℝ[X]).eval x ≠ 0 := by
    rw [hm, eval_mul, eval_C] at hx
    exact (mul_ne_zero_iff.mp hx).2
  have hpos := laguerre_prod_pos m hm0 x hprod
  conv_rhs => rw [hm]
  rw [polynomial_laguerre_mul]
  simp only [derivative_C, derivative_zero, eval_zero, eval_C, zero_pow (by decide : 2 ≠ 0),
    mul_zero, sub_self, zero_add]
  exact mul_pos (sq_pos_of_ne_zero hlc) hpos

/-- Every critical point of a positive nonconstant real-rooted polynomial
has strictly negative second derivative.
Source: strict Laguerre inequality; focused reroutes, interval peak argument. -/
theorem polynomial_second_derivative_neg_of_splits {p : ℝ[X]} (hp : p.Splits)
    (hpc : p.derivative ≠ 0) {x : ℝ} (hx : 0 < p.eval x) (hcrit : p.derivative.eval x = 0) :
    p.derivative.derivative.eval x < 0 := by
  have h := polynomial_laguerre_pos_of_splits hp hpc hx.ne'
  rw [hcrit] at h
  nlinarith

/-- A positive nonconstant real-rooted polynomial has strictly decreasing
logarithmic derivative on every root-free interval.
Source: strict Laguerre inequality and the mean value theorem;
focused reroutes, interval peak uniqueness. -/
theorem strictAntiOn_polynomial_logDeriv_of_splits {p : ℝ[X]} (hp : p.Splits)
    (hpc : p.derivative ≠ 0) {a b : ℝ} (hpos : ∀ x ∈ Ioo a b, 0 < p.eval x) :
    StrictAntiOn (fun x => p.derivative.eval x / p.eval x) (Ioo a b) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo a b)
    (p.derivative.continuousOn.div p.continuousOn (fun x hx => (hpos x hx).ne'))
  intro x hx
  rw [interior_Ioo] at hx
  have hd := p.derivative.hasDerivAt x |>.div (p.hasDerivAt x) (hpos x hx).ne'
  rw [hd.deriv]
  apply div_neg_of_neg_of_pos
  · have h := polynomial_laguerre_pos_of_splits hp hpc (hpos x hx).ne'
    nlinarith
  · exact sq_pos_of_ne_zero (hpos x hx).ne'

/-- A positive nonconstant real-rooted polynomial has at most one critical
point on any root-free interval.
Source: strict decrease of the logarithmic derivative; focused reroutes. -/
theorem eq_of_polynomial_critical_of_splits {p : ℝ[X]} (hp : p.Splits)
    (hpc : p.derivative ≠ 0) {a b : ℝ} (hpos : ∀ x ∈ Ioo a b, 0 < p.eval x)
    {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b)
    (hxc : p.derivative.eval x = 0) (hyc : p.derivative.eval y = 0) : x = y := by
  apply (strictAntiOn_polynomial_logDeriv_of_splits hp hpc hpos).injOn hx hy
  simp only [hxc, hyc, zero_div]

/-- A real polynomial whose degree exceeds its known distinct real roots by
at most one splits over the reals.
Source: division by the root product leaves a polynomial of degree at most one;
helper for the actual interpolation gap polynomials. -/
theorem polynomial_splits_of_natDegree_le_card_add_one {p : ℝ[X]} (hp : p ≠ 0)
    (s : Finset ℝ) (hs : ∀ r ∈ s, p.eval r = 0) (hdeg : p.natDegree ≤ s.card + 1) : p.Splits := by
  let q : ℝ[X] := ∏ r ∈ s, (X - C r)
  have hqdeg : q.natDegree = s.card := by
    dsimp [q]
    rw [natDegree_prod_of_monic s (fun r : ℝ => X - C r) (fun r _ => monic_X_sub_C r)]
    simp
  have hq0 : q ≠ 0 := by
    dsimp [q]
    exact (monic_prod_of_monic s (fun r : ℝ => X - C r) (fun r _ => monic_X_sub_C r)).ne_zero
  have hqdvd : q ∣ p := by
    apply Finset.prod_dvd_of_coprime
    · intro a _ b _ hab
      exact pairwise_coprime_X_sub_C Function.injective_id hab
    · intro r hr
      exact dvd_iff_isRoot.mpr (hs r hr)
  obtain ⟨r, hpr⟩ := hqdvd
  have hr0 : r ≠ 0 := by intro h; rw [h, mul_zero] at hpr; exact hp hpr
  have hrdeg : r.natDegree ≤ 1 := by
    rw [hpr, natDegree_mul hq0 hr0, hqdeg] at hdeg
    omega
  rw [hpr]
  exact (Splits.prod (fun r _ => Splits.X_sub_C r)).mul
    (Splits.of_degree_le_one (natDegree_le_iff_degree_le.mp hrdeg))

end NLAlib
