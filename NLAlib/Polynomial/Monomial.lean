import NLAlib.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Data.Nat.Choose.Sum

/-!
# Compressed monomials in the Chebyshev basis

Finite binomial identities and an exponential bound prove the polynomial approximation
of Sachdeva–Vishnoi, Theorem 3.3 (atlas `monomial-chebyshev-approx`).
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Finset Real

namespace NLAlib

/-- Pascal's rule for a two-sided binomial walk, used in the proof of
Sachdeva–Vishnoi, Theorem 3.3 (`monomial-chebyshev-approx`). -/
theorem sum_choose_int_sub_two_mul_succ {R : Type*} [CommRing R]
    (f : ℤ → R) (s : ℕ) :
    (∑ j ∈ range (s + 2), ((s + 1).choose j : R) * f ((s + 1 : ℕ) - 2 * (j : ℤ))) =
      ∑ j ∈ range (s + 1), (s.choose j : R) *
        (f ((s : ℤ) - 2 * (j : ℤ) + 1) + f ((s : ℤ) - 2 * (j : ℤ) - 1)) := by
  rw [show s + 2 = (s + 1) + 1 by omega, sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.cast_add,
    Int.natCast_zero, mul_zero, sub_zero]
  have hsplit : ∀ j : ℕ,
      ((s + 1).choose (j + 1) : R) * f ((s : ℤ) + 1 - 2 * ((j : ℤ) + 1)) =
        (s.choose j : R) * f ((s : ℤ) - 2 * (j : ℤ) - 1) +
        (s.choose (j + 1) : R) * f ((s : ℤ) - 2 * ((j : ℤ) + 1) + 1) := by
    intro j
    have h1 : (s : ℤ) + 1 - 2 * ((j : ℤ) + 1) = (s : ℤ) - 2 * (j : ℤ) - 1 := by ring
    have h2 : (s : ℤ) - 2 * ((j : ℤ) + 1) + 1 = (s : ℤ) - 2 * (j : ℤ) - 1 := by ring
    rw [Nat.choose_succ_succ', Nat.cast_add, h1, h2, add_mul]
  simp_rw [hsplit, sum_add_distrib, mul_add]
  rw [sum_add_distrib]
  have hshift : (∑ j ∈ range (s + 1), (s.choose (j + 1) : R) *
      f ((s : ℤ) - 2 * ((j : ℤ) + 1) + 1)) + f ((s : ℤ) + 1) =
      ∑ j ∈ range (s + 1), (s.choose j : R) * f ((s : ℤ) - 2 * (j : ℤ) + 1) := by
    have h := sum_range_succ' (fun j => (s.choose j : R) *
      f ((s : ℤ) - 2 * (j : ℤ) + 1)) (s + 1)
    rw [sum_range_succ] at h
    simpa using h.symm
  simp only [mul_add] at hshift
  rw [add_assoc, hshift, add_comm]

/-- Exact Chebyshev expansion of a monomial, before truncation.
Source: Sachdeva–Vishnoi, Theorem 3.3 (`monomial-chebyshev-approx`). -/
theorem sum_choose_mul_chebyshev_eq_two_mul_X_pow (s : ℕ) :
    (∑ j ∈ range (s + 1), C (s.choose j : ℝ) * T ℝ ((s : ℤ) - 2 * (j : ℤ))) =
      (2 * X : ℝ[X]) ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    simp_rw [C_eq_natCast]
    rw [sum_choose_int_sub_two_mul_succ]
    have hrec : ∀ r : ℤ, T ℝ (r + 1) + T ℝ (r - 1) = (2 * X : ℝ[X]) * T ℝ r := by
      intro r
      rw [T_add_one]
      ring
    simp_rw [hrec]
    have hmul : ∀ j : ℕ, (s.choose j : ℝ[X]) * (2 * X * T ℝ ((s : ℤ) - 2 * (j : ℤ))) =
        (2 * X : ℝ[X]) * ((s.choose j : ℝ[X]) * T ℝ ((s : ℤ) - 2 * (j : ℤ))) := by
      intro j; ring
    simp_rw [hmul]
    rw [← mul_sum, pow_succ', ← ih]
    simp only [C_eq_natCast]

/-- The retained binomial Chebyshev sum of degree at most `d`.
Source: Sachdeva–Vishnoi, Theorem 3.3 (`monomial-chebyshev-approx`). -/
def monomialChebyshevApprox (s d : ℕ) : ℝ[X] :=
  C ((2 : ℝ) ^ s)⁻¹ * ∑ j ∈ (range (s + 1)).filter
    (fun j : ℕ => Int.natAbs ((s : ℤ) - 2 * (j : ℤ)) ≤ d),
      C (s.choose j : ℝ) * T ℝ ((s : ℤ) - 2 * (j : ℤ))

/-- The compressed monomial has degree at most the retained frequency cutoff.
Source: Sachdeva–Vishnoi, Theorem 3.3 (`monomial-chebyshev-approx`). -/
theorem degree_monomialChebyshevApprox_le (s d : ℕ) :
    (monomialChebyshevApprox s d).degree ≤ d := by
  unfold monomialChebyshevApprox
  rw [C_mul']
  refine (degree_smul_le _ _).trans ((degree_sum_le _ _).trans ?_)
  refine Finset.sup_le fun j hj => ?_
  have hd := (mem_filter.mp hj).2
  rw [C_mul']
  exact (degree_smul_le _ _).trans (by rw [degree_T]; exact_mod_cast hd)

/-- Exact generating function of the finite binomial walk.
Source: Sachdeva–Vishnoi, Theorem 3.3 (`monomial-chebyshev-approx`), Chernoff proof. -/
theorem sum_choose_mul_exp_int_sub_two_mul (s : ℕ) (θ : ℝ) :
    (∑ j ∈ range (s + 1), (s.choose j : ℝ) * exp (θ * (((s : ℤ) - 2 * (j : ℤ) : ℤ) : ℝ))) =
      (exp θ + exp (-θ)) ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [show s + 1 + 1 = s + 2 by omega,
      sum_choose_int_sub_two_mul_succ (fun r : ℤ => exp (θ * (r : ℝ))) s]
    have hrec : ∀ r : ℤ, exp (θ * ((r + 1 : ℤ) : ℝ)) + exp (θ * ((r - 1 : ℤ) : ℝ)) =
        (exp θ + exp (-θ)) * exp (θ * (r : ℝ)) := by
      intro r
      push_cast
      rw [mul_add, mul_sub, mul_one, exp_add, exp_sub, div_eq_mul_inv, ← exp_neg]
      ring
    simp_rw [hrec]
    have hmul : ∀ j : ℕ, (s.choose j : ℝ) *
        ((exp θ + exp (-θ)) * exp (θ * (((s : ℤ) - 2 * (j : ℤ) : ℤ) : ℝ))) =
        (exp θ + exp (-θ)) *
          ((s.choose j : ℝ) * exp (θ * (((s : ℤ) - 2 * (j : ℤ) : ℤ) : ℝ))) := by
      intro j; ring
    simp_rw [hmul]
    rw [← mul_sum, ih, pow_succ']

/-- Normalized generating function bound for the finite binomial walk.
Source: Sachdeva–Vishnoi, Theorem 3.3 (`monomial-chebyshev-approx`). -/
theorem inv_two_pow_mul_sum_choose_mul_exp_le (s : ℕ) (θ : ℝ) :
    ((2 : ℝ) ^ s)⁻¹ *
      (∑ j ∈ range (s + 1), (s.choose j : ℝ) * exp (θ * (((s : ℤ) - 2 * (j : ℤ) : ℤ) : ℝ))) ≤
        exp ((s : ℝ) * θ ^ 2 / 2) := by
  rw [sum_choose_mul_exp_int_sub_two_mul]
  have hcosh : exp θ + exp (-θ) = 2 * cosh θ := by rw [cosh_eq]; ring
  rw [hcosh, mul_pow, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  have h := pow_le_pow_left₀ (le_of_lt (cosh_pos θ)) (cosh_le_exp_half_sq θ) s
  refine h.trans_eq ?_
  rw [← exp_nat_mul]
  congr 1
  ring

/-- Exponential Markov bound for the absolute tail of a finite binomial walk.
Source: Sachdeva–Vishnoi, Theorem 3.3 (`monomial-chebyshev-approx`); no probability
or measure-theoretic hypothesis is involved. -/
theorem inv_two_pow_mul_sum_choose_abs_tail_le (s : ℕ) {d θ : ℝ}
    (hθ : 0 ≤ θ) :
    ((2 : ℝ) ^ s)⁻¹ *
      (∑ j ∈ (range (s + 1)).filter
        (fun j : ℕ => d < |(((s : ℤ) - 2 * (j : ℤ) : ℤ) : ℝ)|),
          (s.choose j : ℝ)) ≤ 2 * exp (-θ * d + (s : ℝ) * θ ^ 2 / 2) := by
  let w : ℕ → ℝ := fun j => ((2 : ℝ) ^ s)⁻¹ * (s.choose j : ℝ)
  let r : ℕ → ℝ := fun j => ((s : ℤ) - 2 * (j : ℤ) : ℤ)
  let tail := (range (s + 1)).filter (fun j => d < |r j|)
  change ((2 : ℝ) ^ s)⁻¹ * (∑ j ∈ tail, (s.choose j : ℝ)) ≤ _
  rw [mul_sum]
  change (∑ j ∈ tail, w j) ≤ _
  have hmarkov : ∀ j ∈ tail, 1 ≤ exp (-θ * d) * (exp (θ * r j) + exp (-θ * r j)) := by
    intro j hj
    have hr := (mem_filter.mp hj).2
    rcases le_or_gt 0 (r j) with hpos | hneg
    · rw [abs_of_nonneg hpos] at hr
      have hm : 1 ≤ exp (-θ * d + θ * r j) := one_le_exp_iff.mpr (by nlinarith)
      rw [exp_add] at hm
      nlinarith [exp_pos (-θ * d), exp_pos (-θ * r j)]
    · rw [abs_of_neg hneg] at hr
      have hm : 1 ≤ exp (-θ * d + -θ * r j) := one_le_exp_iff.mpr (by nlinarith)
      rw [exp_add] at hm
      nlinarith [exp_pos (-θ * d), exp_pos (θ * r j)]
  have hsum : (∑ j ∈ tail, w j) ≤
      ∑ j ∈ range (s + 1), exp (-θ * d) * w j * (exp (θ * r j) + exp (-θ * r j)) := by
    refine (sum_le_sum fun j hj => ?_).trans
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun j _ _ => by
        dsimp [w]; positivity))
    have hw : 0 ≤ w j := by dsimp [w]; positivity
    nlinarith [mul_le_mul_of_nonneg_right (hmarkov j hj) hw]
  have hplus := inv_two_pow_mul_sum_choose_mul_exp_le s θ
  have hminus := inv_two_pow_mul_sum_choose_mul_exp_le s (-θ)
  have htotal : (∑ j ∈ range (s + 1),
      exp (-θ * d) * w j * (exp (θ * r j) + exp (-θ * r j))) =
      exp (-θ * d) *
        (((2 : ℝ) ^ s)⁻¹ * (∑ j ∈ range (s + 1),
          (s.choose j : ℝ) * exp (θ * (((s : ℤ) - 2 * (j : ℤ) : ℤ) : ℝ))) +
        ((2 : ℝ) ^ s)⁻¹ * (∑ j ∈ range (s + 1),
          (s.choose j : ℝ) * exp ((-θ) * (((s : ℤ) - 2 * (j : ℤ) : ℤ) : ℝ)))) := by
    simp only [mul_add, mul_sum, sum_add_distrib]
    apply congrArg₂ (· + ·) <;> apply sum_congr rfl <;> intro j hj <;> dsimp [w, r] <;> ring
  rw [htotal] at hsum
  have he := exp_pos (-θ * d)
  have hfinal := mul_le_mul_of_nonneg_left (add_le_add hplus hminus) he.le
  rw [neg_sq] at hfinal
  refine hsum.trans (hfinal.trans_eq ?_)
  rw [exp_add]
  ring

/-- Optimized finite binomial tail with the exact constant used by the monomial approximant.
Source: Sachdeva–Vishnoi, Theorem 3.3 (`monomial-chebyshev-approx`). -/
theorem inv_two_pow_mul_sum_choose_natAbs_tail_le {s : ℕ} (hs : 0 < s) (d : ℕ) :
    ((2 : ℝ) ^ s)⁻¹ *
      (∑ j ∈ (range (s + 1)).filter
        (fun j : ℕ => d < Int.natAbs ((s : ℤ) - 2 * (j : ℤ))), (s.choose j : ℝ)) ≤
      2 * exp (- (d : ℝ) ^ 2 / (2 * s)) := by
  have h := inv_two_pow_mul_sum_choose_abs_tail_le s
    (d := (d : ℝ)) (θ := d / s) (by positivity)
  have hpred : ∀ j : ℕ, (d : ℝ) < |(((s : ℤ) - 2 * (j : ℤ) : ℤ) : ℝ)| ↔
      d < Int.natAbs ((s : ℤ) - 2 * (j : ℤ)) := by
    intro j
    rw [← Int.cast_abs, ← Int.natCast_natAbs]
    exact_mod_cast Iff.rfl
  simp_rw [hpred] at h
  convert h using 1
  congr 2
  field_simp
  ring

/-- Evaluation of the untruncated finite Chebyshev expansion.
Source: Sachdeva–Vishnoi, Theorem 3.3 (`monomial-chebyshev-approx`). -/
theorem pow_eq_inv_two_pow_mul_sum_choose_eval_T (s : ℕ) (x : ℝ) :
    x ^ s = ((2 : ℝ) ^ s)⁻¹ *
      (∑ j ∈ range (s + 1), (s.choose j : ℝ) * (T ℝ ((s : ℤ) - 2 * (j : ℤ))).eval x) := by
  have h := congrArg (Polynomial.eval x) (sum_choose_mul_chebyshev_eq_two_mul_X_pow s)
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_ofNat, eval_X] at h
  rw [h, mul_pow, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- The error of a truncated monomial is bounded by the omitted finite binomial mass.
Source: Sachdeva–Vishnoi, Theorem 3.3 (`monomial-chebyshev-approx`). -/
theorem abs_pow_sub_eval_monomialChebyshevApprox_le_sum (s d : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |x ^ s - (monomialChebyshevApprox s d).eval x| ≤ ((2 : ℝ) ^ s)⁻¹ *
      (∑ j ∈ (range (s + 1)).filter
        (fun j : ℕ => d < Int.natAbs ((s : ℤ) - 2 * (j : ℤ))), (s.choose j : ℝ)) := by
  have hsplit := sum_filter_add_sum_filter_not (range (s + 1))
    (fun j : ℕ => Int.natAbs ((s : ℤ) - 2 * (j : ℤ)) ≤ d)
    (fun j : ℕ => (s.choose j : ℝ) * (T ℝ ((s : ℤ) - 2 * (j : ℤ))).eval x)
  simp only [not_le] at hsplit
  rw [pow_eq_inv_two_pow_mul_sum_choose_eval_T, ← hsplit]
  simp only [monomialChebyshevApprox, eval_mul, eval_C, eval_finsetSum]
  rw [mul_add, add_sub_cancel_left, abs_mul, abs_of_nonneg (by positivity :
    0 ≤ ((2 : ℝ) ^ s)⁻¹)]
  refine mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans
    (sum_le_sum fun j hj => ?_)) (by positivity)
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  have hT := abs_eval_T_real_le_one ((s : ℤ) - 2 * (j : ℤ)) (abs_le.mpr hx)
  exact (mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg _)).trans_eq (mul_one _)

/-- The explicit Chebyshev truncation approximates a positive-degree monomial on `[-1,1]`
with the exact error `2 exp(-d²/(2s))`.
Source: Sachdeva–Vishnoi, Theorem 3.3. The approximation is a finite binomial sum;
the exponential tail is proved without probability or any assumed approximation theorem.
atlas: monomial-chebyshev-approx -/
theorem abs_pow_sub_eval_monomialChebyshevApprox_le {s : ℕ} (hs : 0 < s) (d : ℕ)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |x ^ s - (monomialChebyshevApprox s d).eval x| ≤
      2 * exp (- (d : ℝ) ^ 2 / (2 * s)) :=
  (abs_pow_sub_eval_monomialChebyshevApprox_le_sum s d hx).trans
    (inv_two_pow_mul_sum_choose_natAbs_tail_le hs d)

/-- The zero monomial is represented exactly by the constant polynomial `1`.
Source: Sachdeva–Vishnoi, Theorem 3.3, degenerate case (`monomial-chebyshev-approx`). -/
@[simp] theorem monomialChebyshevApprox_zero (d : ℕ) : monomialChebyshevApprox 0 d = 1 := by
  simp [monomialChebyshevApprox, Finset.sum_filter]

/-- Retaining all possible walk frequencies recovers the monomial exactly.
Source: Sachdeva–Vishnoi, Theorem 3.3 (`monomial-chebyshev-approx`), degenerate case. -/
theorem monomialChebyshevApprox_eq_X_pow {s d : ℕ} (hsd : s ≤ d) :
    monomialChebyshevApprox s d = X ^ s := by
  have hfilter : (range (s + 1)).filter
      (fun j : ℕ => Int.natAbs ((s : ℤ) - 2 * (j : ℤ)) ≤ d) = range (s + 1) := by
    apply filter_eq_self.mpr
    intro j hj
    have hj' : j ≤ s := Nat.le_of_lt_succ (mem_range.mp hj)
    have habs : |(s : ℤ) - 2 * (j : ℤ)| ≤ (s : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
    have hn : Int.natAbs ((s : ℤ) - 2 * (j : ℤ)) ≤ s := by
      rw [← Int.natCast_natAbs] at habs
      exact_mod_cast habs
    exact hn.trans hsd
  apply Polynomial.funext
  intro x
  simp only [monomialChebyshevApprox, hfilter, eval_mul, eval_C, eval_finsetSum, eval_pow, eval_X]
  exact (pow_eq_inv_two_pow_mul_sum_choose_eval_T s x).symm

/-- Monomial approximation in the existential polynomial interface used by Krylov proofs.
Source: Sachdeva–Vishnoi, Theorem 3.3.
atlas: monomial-chebyshev-approx -/
theorem exists_degree_le_abs_pow_sub_eval_le {s : ℕ} (hs : 0 < s) (d : ℕ) :
    ∃ p : ℝ[X], p.degree ≤ d ∧ ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |x ^ s - p.eval x| ≤ 2 * exp (- (d : ℝ) ^ 2 / (2 * s)) :=
  ⟨monomialChebyshevApprox s d, degree_monomialChebyshevApprox_le s d,
    fun _ hx => abs_pow_sub_eval_monomialChebyshevApprox_le hs d hx⟩

end NLAlib
