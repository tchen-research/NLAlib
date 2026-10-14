import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Ring.GeomSum

/-!
# Finite even-moment recurrence comparison

A factorial moment recurrence is bounded by a square-root plus linear barrier.
The terminal-order barrier gives the sharp logarithmic order without optimizing
the numerical Gaussian pairing constants. Source: Heidary, *The Sharp Logarithmic
Cost of Khatri--Rao Subspace Embeddings*, Appendix `closed:thm:moment`.
Atlas: `khatri-rao-sharp-growth`.
-/

noncomputable section

open Finset Set MeasureTheory

namespace NLAlib

/-- Cauchy--Schwarz interpolation between neighboring even moments.
Source: Heidary, Appendix `closed:thm:moment`.
Atlas: `khatri-rao-sharp-growth`. -/
def evenMomentInterpolation (u : ℕ → ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (u (k / 2) * u ((k + 1) / 2))

/-- The factorial update for even moments, with variance `ν` and radius `R`.
Source: Heidary, equation `closed:eq:update`.
Atlas: `khatri-rao-sharp-growth`. -/
def finiteMomentUpdate (ν R : ℝ) (u : ℕ → ℝ) (p : ℕ) : ℝ :=
  ∑ k ∈ range (2 * p - 1),
    ((2 * p).choose (k + 2) : ℝ) * ((k + 2).factorial : ℝ) / 2 *
      ν * R ^ k * evenMomentInterpolation u (2 * p - (k + 2))

/-- A common even-power barrier bounds the interpolated odd powers as well.
Source: Cauchy--Schwarz and monotonicity of the square root.
Atlas: `khatri-rao-sharp-growth`. -/
theorem evenMomentInterpolation_le_pow {u : ℕ → ℝ} {q k : ℕ} {x : ℝ}
    (hu : ∀ p, 0 ≤ u p) (hx : 0 ≤ x) (hk : k ≤ 2 * q)
    (hbound : ∀ p ≤ q, u p ≤ x ^ (2 * p)) :
    evenMomentInterpolation u k ≤ x ^ k := by
  unfold evenMomentInterpolation
  apply (Real.sqrt_le_left (pow_nonneg hx _)).2
  have h1 : k / 2 ≤ q := by omega
  have h2 : (k + 1) / 2 ≤ q := by omega
  calc
    u (k / 2) * u ((k + 1) / 2) ≤
        x ^ (2 * (k / 2)) * x ^ (2 * ((k + 1) / 2)) :=
      mul_le_mul (hbound _ h1) (hbound _ h2) (hu _) (pow_nonneg hx _)
    _ = (x ^ k) ^ 2 := by
      rw [← pow_add, ← pow_mul]
      congr 1
      omega

/-- The factorial binomial coefficient is bounded using the terminal moment order.
Source: descending factorial bounded by a power.
Atlas: `khatri-rao-sharp-growth`. -/
theorem choose_mul_factorial_le_mul_pow {p q k : ℕ} (hpq : p ≤ q) :
    (2 * p).choose (k + 2) * (k + 2).factorial ≤
      (2 * p) * (2 * q) ^ (k + 1) := by
  rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
  rw [show k + 2 = (k + 1) + 1 by omega, Nat.descFactorial_succ]
  exact Nat.mul_le_mul (Nat.sub_le _ _)
    ((Nat.descFactorial_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) _))

/-- A positive finite geometric convolution is bounded by its infinite envelope.
Source: the finite geometric identity.
Atlas: `khatri-rao-sharp-growth`. -/
theorem sum_pow_mul_pow_le_div {a x : ℝ} (ha : 0 ≤ a) (hax : a < x) (n : ℕ) :
    (∑ k ∈ range n, a ^ k * x ^ (n - 1 - k)) ≤ x ^ n / (x - a) := by
  apply (le_div_iff₀ (sub_pos.mpr hax)).2
  have hgeom := geom_sum₂_mul a x n
  have hpow := pow_nonneg ha n
  nlinarith

/-- The factorial update is bounded by the derivative of a common power barrier.
Source: Heidary, Appendix `closed:thm:moment`, using a coarser terminal-order
barrier instead of Gaussian pairing coefficients.
Atlas: `khatri-rao-sharp-growth`. -/
theorem finiteMomentUpdate_le {ν R x : ℝ} {u : ℕ → ℝ} {p q : ℕ}
    (hν : 0 ≤ ν) (hR : 0 ≤ R) (hp : 1 ≤ p) (hpq : p ≤ q)
    (hx : 2 * (q : ℝ) * R < x)
    (hu : ∀ i, 0 ≤ u i) (hbound : ∀ i ≤ q, u i ≤ x ^ (2 * i)) :
    finiteMomentUpdate ν R u p ≤
      (2 * (p : ℝ)) * x ^ (2 * p - 1) * ((q : ℝ) * ν / (x - 2 * q * R)) := by
  have hx0 : 0 ≤ x := le_trans (by positivity) hx.le
  have ha : 0 ≤ 2 * (q : ℝ) * R := by positivity
  have hcoeff (k : ℕ) :
      ((2 * p).choose (k + 2) : ℝ) * ((k + 2).factorial : ℝ) ≤
        (2 * (p : ℝ)) * (2 * (q : ℝ)) ^ (k + 1) := by
    exact_mod_cast choose_mul_factorial_le_mul_pow (k := k) hpq
  calc
    finiteMomentUpdate ν R u p ≤
        ∑ k ∈ range (2 * p - 1),
          ((2 * (p : ℝ)) * (2 * (q : ℝ)) ^ (k + 1)) / 2 * ν * R ^ k *
            x ^ (2 * p - (k + 2)) := by
      unfold finiteMomentUpdate
      apply sum_le_sum
      intro k hk
      have hi : 2 * p - (k + 2) ≤ 2 * q := by omega
      have hcdiv := div_le_div_of_nonneg_right (hcoeff k) (by norm_num : (0 : ℝ) ≤ 2)
      have hcv := mul_le_mul_of_nonneg_right hcdiv hν
      have hcvR := mul_le_mul_of_nonneg_right hcv (pow_nonneg hR k)
      exact mul_le_mul hcvR
        (evenMomentInterpolation_le_pow hu hx0 hi hbound)
        (Real.sqrt_nonneg _) (by positivity)
    _ = (2 * (p : ℝ)) * (q : ℝ) * ν *
        ∑ k ∈ range (2 * p - 1),
          (2 * (q : ℝ) * R) ^ k * x ^ (2 * p - 1 - 1 - k) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      rw [mul_pow, pow_succ]
      have he : 2 * p - (k + 2) = 2 * p - 1 - 1 - k := by omega
      rw [he]
      ring
    _ ≤ (2 * (p : ℝ)) * (q : ℝ) * ν *
        (x ^ (2 * p - 1) / (x - 2 * q * R)) :=
      mul_le_mul_of_nonneg_left (sum_pow_mul_pow_le_div ha hx _) (by positivity)
    _ = _ := by ring

/-- A terminal-order square-root plus linear barrier for factorial recurrences.
The shift by one removes the square-root derivative singularity at the origin.
Source: Heidary, Appendix `closed:thm:moment`.
Atlas: `khatri-rao-sharp-growth`. -/
def finiteMomentBarrier (q : ℕ) (ν R t : ℝ) : ℝ :=
  Real.sqrt (2 * (q : ℝ) * ν * (t + 1)) + 2 * (q : ℝ) * R

/-- The factorial recurrence barrier increases with time.
Source: monotonicity of the square root.
Atlas: `khatri-rao-sharp-growth`. -/
theorem finiteMomentBarrier_mono {q : ℕ} {ν R : ℝ} (hν : 0 ≤ ν) :
    Monotone (finiteMomentBarrier q ν R) := by
  intro a b hab
  unfold finiteMomentBarrier
  gcongr

/-- The shifted barrier has the derivative used to compare the finite recurrence.
Source: the chain rule.
Atlas: `khatri-rao-sharp-growth`. -/
theorem hasDerivAt_finiteMomentBarrier {q : ℕ} {ν R t : ℝ}
    (hq : 1 ≤ q) (hν : 0 < ν) (ht : 0 ≤ t) :
    HasDerivAt (finiteMomentBarrier q ν R)
      ((q : ℝ) * ν / Real.sqrt (2 * (q : ℝ) * ν * (t + 1))) t := by
  have hpos : 0 < 2 * (q : ℝ) * ν * (t + 1) := by
    have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    positivity
  have h := ((((hasDerivAt_id t).add_const 1).const_mul (2 * (q : ℝ) * ν)).sqrt hpos.ne').add_const
    (2 * (q : ℝ) * R)
  convert! h using 1
  simp only [id_eq, mul_one]
  ring

/-- A common power barrier dominates one discrete factorial moment update.
Source: Heidary, Appendix `closed:thm:moment`, with a shifted terminal-order
barrier and coarser explicit numerical constants.
Atlas: `khatri-rao-sharp-growth`. -/
theorem finiteMomentUpdate_le_barrier_sub {ν R : ℝ} {u : ℕ → ℝ} {p q n : ℕ}
    (hν : 0 < ν) (hR : 0 ≤ R) (hp : 1 ≤ p) (hpq : p ≤ q)
    (hu : ∀ i, 0 ≤ u i)
    (hbound : ∀ i ≤ q, u i ≤ finiteMomentBarrier q ν R n ^ (2 * i)) :
    finiteMomentUpdate ν R u p ≤
      finiteMomentBarrier q ν R (n + 1) ^ (2 * p) -
        finiteMomentBarrier q ν R n ^ (2 * p) := by
  have hq : 1 ≤ q := hp.trans hpq
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hpos (t : ℝ) (ht : 0 ≤ t) : 0 < 2 * (q : ℝ) * ν * (t + 1) := by positivity
  have hbar (t : ℝ) (ht : 0 ≤ t) :
      2 * (q : ℝ) * R < finiteMomentBarrier q ν R t := by
    dsimp only [finiteMomentBarrier]
    linarith [Real.sqrt_pos.2 (hpos t ht)]
  let D : ℝ → ℝ := fun t => (2 * (p : ℝ)) *
    finiteMomentBarrier q ν R t ^ (2 * p - 1) *
      ((q : ℝ) * ν / Real.sqrt (2 * (q : ℝ) * ν * (t + 1)))
  have hd (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt (fun t => finiteMomentBarrier q ν R t ^ (2 * p)) (D t) t := by
    convert! (hasDerivAt_finiteMomentBarrier hq hν ht).pow (2 * p) using 1
    simp only [D, Nat.cast_mul, Nat.cast_ofNat]
  have hcont : Continuous (fun t => finiteMomentBarrier q ν R t ^ (2 * p)) := by
    unfold finiteMomentBarrier
    fun_prop
  have hDcont : ContinuousOn D (Icc (n : ℝ) (n + 1)) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.pow
      unfold finiteMomentBarrier
      fun_prop
    · apply ContinuousOn.div continuousOn_const
      · fun_prop
      · intro t ht
        exact (Real.sqrt_pos.2 (hpos t (le_trans (by positivity) ht.1))).ne'
  have hle : (n : ℝ) ≤ n + 1 := by linarith
  have hint : IntervalIntegrable D volume (n : ℝ) (n + 1) :=
    hDcont.intervalIntegrable_of_Icc hle
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcont.continuousOn
    (fun t ht => hd t (le_trans (by positivity) ht.1.le)) hint
  have hcmp (t : ℝ) (ht : t ∈ Icc (n : ℝ) (n + 1)) :
      finiteMomentUpdate ν R u p ≤ D t := by
    have ht0 : 0 ≤ t := le_trans (by positivity) ht.1
    have hboundt (i : ℕ) (hiq : i ≤ q) :
        u i ≤ finiteMomentBarrier q ν R t ^ (2 * i) := by
      apply (hbound i hiq).trans
      apply pow_le_pow_left₀
      · exact le_trans (by positivity) (hbar n (by positivity)).le
      · exact finiteMomentBarrier_mono hν.le ht.1
    convert finiteMomentUpdate_le hν.le hR hp hpq (hbar t ht0) hu hboundt using 1
    simp only [D, finiteMomentBarrier, add_sub_cancel_right]
  have hmono := intervalIntegral.integral_mono_on hle
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => finiteMomentUpdate ν R u p)
      volume (n : ℝ) (n + 1)) hint hcmp
  rw [hftc] at hmono
  simpa using hmono

/-- Every nonnegative even-moment sequence satisfying the factorial recurrence
is bounded by an explicit square-root plus linear terminal-order barrier.
Source: Heidary, Appendix `closed:thm:moment`; numerical constants are coarsened
to avoid optimizing Gaussian pairing coefficients.
Atlas: `khatri-rao-sharp-growth`. -/
theorem le_finiteMomentBarrier_pow {ν R : ℝ} {q : ℕ} {M : ℕ → ℕ → ℝ}
    (hν : 0 < ν) (hR : 0 ≤ R) (hq : 1 ≤ q)
    (hM : ∀ n p, 0 ≤ M n p) (hzero : ∀ n, M n 0 = 1)
    (hinit : ∀ p, 1 ≤ p → p ≤ q → M 0 p = 0)
    (hstep : ∀ n p, 1 ≤ p → p ≤ q →
      M (n + 1) p ≤ M n p + finiteMomentUpdate ν R (M n) p) :
    ∀ n p, p ≤ q → M n p ≤ finiteMomentBarrier q ν R n ^ (2 * p) := by
  intro n
  induction n with
  | zero =>
    intro p hp
    by_cases hp0 : p = 0
    · simp [hp0, hzero]
    · rw [hinit p (by omega) hp]
      exact pow_nonneg (by unfold finiteMomentBarrier; positivity) _
  | succ n ih =>
    intro p hp
    by_cases hp0 : p = 0
    · simp [hp0, hzero]
    have hp1 : 1 ≤ p := by omega
    have hdiff := finiteMomentUpdate_le_barrier_sub hν hR hp1 hp (hM n) ih
    have hrec := hstep n p hp1 hp
    have hind := ih p hp
    push_cast at hdiff ⊢
    linarith

/-- At a positive integer time the shifted barrier has the usual
`2 √(q ν m) + 2 q R` form. Source: the terminal-order finite recurrence comparison.
Atlas: `khatri-rao-sharp-growth`. -/
theorem finiteMomentBarrier_le_sqrt_add_mul {ν R : ℝ} {q m : ℕ}
    (hν : 0 ≤ ν) (hm : 1 ≤ m) :
    finiteMomentBarrier q ν R m ≤
      2 * Real.sqrt ((q : ℝ) * ν * m) + 2 * (q : ℝ) * R := by
  unfold finiteMomentBarrier
  apply add_le_add _ le_rfl
  apply (Real.sqrt_le_left (by positivity)).2
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmul := mul_nonneg (show 0 ≤ (q : ℝ) * ν by positivity) (sub_nonneg.mpr hmR)
  nlinarith

/-- The explicit factorial recurrence bound at the terminal moment order.
Source: Heidary, Appendix `closed:thm:moment`; this gives the same square-root
and linear scales with coarser explicit numerical constants.
Atlas: `khatri-rao-sharp-growth`. -/
theorem le_sqrt_add_mul_pow_of_finiteMomentUpdate {ν R : ℝ} {q m : ℕ}
    {M : ℕ → ℕ → ℝ} (hν : 0 < ν) (hR : 0 ≤ R) (hq : 1 ≤ q) (hm : 1 ≤ m)
    (hM : ∀ n p, 0 ≤ M n p) (hzero : ∀ n, M n 0 = 1)
    (hinit : ∀ p, 1 ≤ p → p ≤ q → M 0 p = 0)
    (hstep : ∀ n p, 1 ≤ p → p ≤ q →
      M (n + 1) p ≤ M n p + finiteMomentUpdate ν R (M n) p) :
    M m q ≤ (2 * Real.sqrt ((q : ℝ) * ν * m) + 2 * (q : ℝ) * R) ^ (2 * q) := by
  apply (le_finiteMomentBarrier_pow hν hR hq hM hzero hinit hstep m q le_rfl).trans
  apply pow_le_pow_left₀
  · unfold finiteMomentBarrier
    positivity
  · exact finiteMomentBarrier_le_sqrt_add_mul hν.le hm

end NLAlib
