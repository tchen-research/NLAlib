import NLAlib.Polynomial.BestApproximation.Basic
import NLAlib.Polynomial.BestApproximation.RationalCompactness
import Mathlib.Topology.ContinuousMap.Interval

/-!
# Attainment of best uniform rational approximation

The compact coefficient-limit theorem yields a pole-free fraction attaining the infimum.
Mathlib's normalized `RatFunc` numerator and denominator preserve type and evaluation.
Source: Trefethen, ATAP, Theorem 24.1; operator rederivations, `polybest:rational-limit`.
Atlas: `rational-equioscillation` (existence).
-/

noncomputable section

open Polynomial Set

namespace NLAlib

/-- A pole-free polynomial fraction defines a rational function of the same or smaller type.
Source: Trefethen, ATAP, Chapter 23; normalization divides out the polynomial gcd. -/
theorem isPoleFreeRationalApproximation_div {s : Set ℝ} {m n : ℕ} (p q : ℝ[X])
    (hp : p.degree ≤ m) (hq : q.degree ≤ n) (hq0 : q ≠ 0)
    (hpole : ∀ x ∈ s, q.eval x ≠ 0) :
    IsPoleFreeRationalApproximation s m n
      (algebraMap ℝ[X] (RatFunc ℝ) p / algebraMap ℝ[X] (RatFunc ℝ) q) := by
  refine ⟨?_, (degree_le_of_dvd (RatFunc.denom_div_dvd p q) hq0).trans hq, ?_⟩
  · by_cases hp0 : p = 0
    · simp [hp0]
    · exact (degree_le_of_dvd (RatFunc.num_div_dvd p hq0) hp0).trans hp
  · intro x hx hzero
    obtain ⟨a, ha⟩ := RatFunc.denom_div_dvd p q
    apply hpole x hx
    rw [ha, eval_mul, hzero, zero_mul]

/-- Canonical rational-function evaluation equals the original pole-free polynomial ratio.
Source: Trefethen, ATAP, Chapter 23. -/
theorem rationalContinuousMap_div_apply_eq {s : Set ℝ} {m n : ℕ} (p q : ℝ[X])
    (hp : p.degree ≤ m) (hq : q.degree ≤ n) (hq0 : q ≠ 0)
    (hpole : ∀ x ∈ s, q.eval x ≠ 0) (x : s) :
    rationalContinuousMap s
      (algebraMap ℝ[X] (RatFunc ℝ) p / algebraMap ℝ[X] (RatFunc ℝ) q)
      (isPoleFreeRationalApproximation_div p q hp hq hq0 hpole).2.2 x =
      p.eval (x : ℝ) / q.eval (x : ℝ) := by
  let r := algebraMap ℝ[X] (RatFunc ℝ) p / algebraMap ℝ[X] (RatFunc ℝ) q
  have hr := isPoleFreeRationalApproximation_div p q hp hq hq0 hpole
  have hrel : r.num * q = p * r.denom :=
    (RatFunc.num_mul_eq_mul_denom_iff hq0).mpr rfl
  have hev : r.num.eval (x : ℝ) * q.eval (x : ℝ) =
      p.eval (x : ℝ) * r.denom.eval (x : ℝ) := by
    simpa only [eval_mul] using congrArg (fun P : ℝ[X] => P.eval (x : ℝ)) hrel
  change r.num.eval (x : ℝ) / r.denom.eval (x : ℝ) = _
  exact (div_eq_div_iff (hr.2.2 x x.property) (hpole x x.property)).mpr hev

/-- Zero is a pole-free rational approximant of every type. Source: ATAP, Chapter 23. -/
theorem isPoleFreeRationalApproximation_zero (s : Set ℝ) (m n : ℕ) :
    IsPoleFreeRationalApproximation s m n 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp
  · simp only [RatFunc.denom_zero, degree_one]
    exact_mod_cast Nat.zero_le n
  · simp

/-- The rational approximation set is nonempty. Source: ATAP, Chapter 23. -/
theorem rationalApproximationSpace_nonempty (s : Set ℝ) (m n : ℕ) :
    (rationalApproximationSpace s m n).Nonempty :=
  ⟨rationalContinuousMap s 0 (isPoleFreeRationalApproximation_zero s m n).2.2,
    0, isPoleFreeRationalApproximation_zero s m n, rfl⟩

/-- Rational minimax error is nonnegative. Source: ATAP, Chapter 24. -/
theorem rationalMinimaxError_nonneg {s : Set ℝ} [CompactSpace s]
    (m n : ℕ) (f : C(s, ℝ)) : 0 ≤ rationalMinimaxError m n f := Metric.infDist_nonneg

/-- Every pole-free rational competitor bounds the best uniform rational error.
Source: ATAP, Chapter 24. -/
theorem rationalMinimaxError_le_norm_sub {s : Set ℝ} [CompactSpace s] (m n : ℕ)
    (f : C(s, ℝ)) {g : C(s, ℝ)} (hg : g ∈ rationalApproximationSpace s m n) :
    rationalMinimaxError m n f ≤ ‖f - g‖ := by
  simpa [rationalMinimaxError, dist_eq_norm] using (Metric.infDist_le_dist_of_mem (x := f) hg)

/-- Best real type-`(m,n)` uniform rational approximation is attained on every nondegenerate
real interval. Source: Trefethen, ATAP, Theorem 24.1; joint coefficient compactness and
iterative real-pole cancellation. The output is Mathlib's canonical `RatFunc`.
atlas: rational-equioscillation (partial) -/
theorem exists_norm_sub_eq_rationalMinimaxError {a b : ℝ} (hab : a < b) (m n : ℕ)
    (f : C(Icc a b, ℝ)) :
    ∃ (r : RatFunc ℝ) (hr : IsPoleFreeRationalApproximation (Icc a b) m n r),
      ‖f - rationalContinuousMap (Icc a b) r hr.2.2‖ = rationalMinimaxError m n f := by
  let : Fact (a ≤ b) := ⟨hab.le⟩
  let ff : C(ℝ, ℝ) := ContinuousMap.IccExtendCM f
  let E := rationalMinimaxError m n f
  have hnear : ∀ ε > 0, ∃ p q : ℝ[X], p.degree ≤ m ∧ q.degree ≤ n ∧ q ≠ 0 ∧
      ∀ x ∈ Icc a b, |ff x * q.eval x - p.eval x| ≤ (E + ε) * |q.eval x| := by
    intro ε hε
    obtain ⟨g, hg, hdist⟩ := (Metric.infDist_lt_iff
      (rationalApproximationSpace_nonempty (Icc a b) m n)).mp
        (show Metric.infDist f (rationalApproximationSpace (Icc a b) m n) < E + ε by
          change E < E + ε; linarith)
    obtain ⟨r, hr, hrg⟩ := hg
    have hnorm : ‖f - rationalContinuousMap (Icc a b) r hr.2.2‖ < E + ε := by
      simpa [← hrg, dist_eq_norm] using hdist
    refine ⟨r.num, r.denom, hr.1, hr.2.1, RatFunc.denom_ne_zero r, ?_⟩
    intro x hx
    have hpoint : |ff x - r.num.eval x / r.denom.eval x| ≤ E + ε := by
      have hb := (f - rationalContinuousMap (Icc a b) r hr.2.2).norm_coe_le_norm ⟨x, hx⟩
      have hval : ff x = f ⟨x, hx⟩ := ContinuousMap.IccExtendCM_of_mem hx
      change |f ⟨x, hx⟩ - r.num.eval x / r.denom.eval x| ≤ _ at hb
      rw [← hval] at hb
      exact hb.trans hnorm.le
    have heq : ff x * r.denom.eval x - r.num.eval x =
        r.denom.eval x * (ff x - r.num.eval x / r.denom.eval x) := by
      field_simp [hr.2.2 x hx]
    rw [heq, abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left hpoint (abs_nonneg (r.denom.eval x))]
  obtain ⟨P, Q, hP, hQ, hbound⟩ :=
    exists_cross_error_le_of_forall_pos hab ff ff.continuous hnear
  have hQ0 : Q ≠ 0 := by
    intro hzero
    have ha := (hbound a ⟨le_rfl, hab.le⟩).1
    simp [hzero] at ha
  let r := algebraMap ℝ[X] (RatFunc ℝ) P / algebraMap ℝ[X] (RatFunc ℝ) Q
  let hr := isPoleFreeRationalApproximation_div P Q hP hQ hQ0 (fun x hx => (hbound x hx).1)
  have hnorm : ‖f - rationalContinuousMap (Icc a b) r hr.2.2‖ ≤ E := by
    apply (ContinuousMap.norm_le _ (rationalMinimaxError_nonneg m n f)).mpr
    intro x
    have hval : ff x = f x := ContinuousMap.IccExtendCM_of_mem x.property
    have heval := rationalContinuousMap_div_apply_eq P Q hP hQ hQ0
      (fun x hx => (hbound x hx).1) x
    change |f x - rationalContinuousMap (Icc a b) r hr.2.2 x| ≤ E
    rw [heval, ← hval]
    have hb := (hbound x x.property).2
    have heq : ff x * Q.eval (x : ℝ) - P.eval (x : ℝ) =
        Q.eval (x : ℝ) * (ff x - P.eval (x : ℝ) / Q.eval (x : ℝ)) := by
      field_simp [(hbound x x.property).1]
    rw [heq, abs_mul] at hb
    apply le_of_mul_le_mul_left (a := |Q.eval (x : ℝ)|)
      (by nlinarith [hb]) (abs_pos.mpr (hbound x x.property).1)
  exact ⟨r, hr, le_antisymm hnorm
    (rationalMinimaxError_le_norm_sub m n f ⟨r, hr, rfl⟩)⟩

end NLAlib
