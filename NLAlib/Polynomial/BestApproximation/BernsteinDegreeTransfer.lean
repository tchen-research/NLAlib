import NLAlib.Polynomial.BestApproximation.BernsteinFiniteGrowth
import NLAlib.Polynomial.FunctionApproximation.AnalyticApproximation
import NLAlib.Polynomial.FunctionApproximation.EllipseImaginary

/-!
# Finite degree transfer for best absolute-value approximation

A finite scaled minimizer and ellipse truncation compare any target degree to
every sufficiently large even source degree. No limiting analytic function is
constructed. Source: the focused polynomial Bernstein reroute, Section 2.
-/

noncomputable section

open Polynomial Set Complex

namespace NLAlib

/-- The positive exponential decay coefficient in the finite degree-transfer
comparison for `0 < α < 1`. -/
def bernsteinDegreeTransferDecay (α : ℝ) : ℝ :=
  ((1 - α) / 2) * (1 - Real.exp (-((1 - α) / 2)))

/-- The explicit source-degree-independent remainder in Bernstein's finite
degree-transfer comparison. -/
def bernsteinDegreeTransferRemainder (α : ℝ) (N : ℕ) : ℝ :=
  let t := (1 - α) / 2
  12 * Real.exp 1 * (1 + (α * N * Real.cosh t)^2) /
    (Real.pi * α * (Real.exp t - 1)) *
      Real.exp (-bernsteinDegreeTransferDecay α * N)

/-- The degree-transfer decay coefficient is strictly positive for
`0 < α < 1`. -/
theorem bernsteinDegreeTransferDecay_pos {α : ℝ} (hα1 : α < 1) :
    0 < bernsteinDegreeTransferDecay α := by
  have ht : 0 < (1 - α) / 2 := by linarith
  exact mul_pos ht (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))

private theorem sinh_le_mul_exp (t : ℝ) : Real.sinh t ≤ t * Real.exp t := by
  have h := Real.one_sub_le_exp_neg (2 * t)
  have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos t).le
  have he : Real.exp (- (2 * t)) * Real.exp t = Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hmul
  rw [Real.sinh_eq]
  nlinarith

private theorem degree_transfer_exponent_le {α : ℝ} (hα1 : α < 1) :
    α * Real.sinh ((1 - α) / 2) - (1 - α) / 2 ≤ -bernsteinDegreeTransferDecay α := by
  let t := (1 - α) / 2
  have ht : 0 < t := by dsimp [t]; linarith
  have hα : α ≤ Real.exp (-(2 * t)) := by
    have h := Real.one_sub_le_exp_neg (2 * t)
    dsimp [t] at h
    linarith
  have hs := sinh_le_mul_exp t
  have h := mul_le_mul hα hs (Real.sinh_nonneg_iff.mpr ht.le)
    (Real.exp_pos (-(2 * t))).le
  have he : Real.exp (-(2 * t)) * (t * Real.exp t) = t * Real.exp (-t) := by
    rw [mul_left_comm, ← Real.exp_add]
    congr 1
    ring
  rw [he] at h
  change α * Real.sinh t - t ≤ -(t * (1 - Real.exp (-t)))
  nlinarith

/-- Any target degree compares to every sufficiently large even source degree
through the explicit exponentially decaying remainder. The error is the actual
native real minimax error for absolute value.
Source: the focused polynomial Bernstein reroute, finite degree-transfer theorem. -/
theorem mul_absoluteMinimaxError_le_degreeTransfer {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) {N m : ℕ} (hN : 1 ≤ N)
    (hthreshold : 2 * max 1 ((α * N * Real.cosh ((1 - α) / 2))^2) ≤
      ((2 * m : ℕ) : ℝ)) :
    (N : ℝ) * absoluteMinimaxError N ≤
      ((2 * m : ℕ) : ℝ) * absoluteMinimaxError (2 * m) / α +
        bernsteinDegreeTransferRemainder α N := by
  let t := (1 - α) / 2
  let A := α * (N : ℝ)
  let R := A * Real.cosh t
  let n : ℝ := (2 * m : ℕ)
  have ht : 0 < t := by dsimp [t]; linarith
  have hNp : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hA : 0 < A := mul_pos hα0 hNp
  have hR : 0 ≤ R := mul_nonneg hA.le (Real.cosh_pos t).le
  have hn2 : 2 ≤ n := by nlinarith [le_max_left (1 : ℝ) (R^2)]
  have hn : 0 < n := by linarith
  have hπ : 0 < Real.pi := Real.pi_pos
  have hRA : A ≤ R := le_mul_of_one_le_right hA.le (Real.one_le_cosh t)
  have hRmax : R ≤ max 1 (R^2) := by
    by_cases hR1 : R ≤ 1
    · exact hR1.trans (le_max_left _ _)
    · exact (by nlinarith : R ≤ R^2).trans (le_max_right _ _)
  have hAn : A ≤ n := by linarith
  obtain ⟨p, hp, hbest⟩ := exists_degree_le_absoluteMinimaxError (2 * m)
  have herr : ∀ x ∈ Icc (-1 : ℝ) 1,
      |(|x|) - p.eval x| ≤ 2 / (Real.pi * (2 * m + 1)) :=
    fun x hx => (hbest x hx).trans (absoluteMinimaxError_even_le m)
  let r := (n / A) • p.comp (C (A / n) * X)
  let M := 6 * (1 + R^2) / (Real.pi * A) * Real.exp (A * Real.sinh t + 1)
  have hF : ∀ z ∈ openBernsteinEllipse (Real.exp t),
      ‖(r.map Complex.ofRealHom).eval z‖ ≤ M := by
    intro z hz
    obtain ⟨hznorm, hzim⟩ := norm_le_cosh_and_abs_im_le_sinh_of_mem_openBernsteinEllipse ht hz
    have haznorm : ‖(A : ℂ) * z‖ ≤ R := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA]
      exact mul_le_mul_of_nonneg_left hznorm hA.le
    have hazim : |((A : ℂ) * z).im| ≤ A * Real.sinh t := by
      simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, abs_mul, abs_of_pos hA] using
        mul_le_mul_of_nonneg_left hzim hA.le
    have hg := norm_scaled_absolute_approximant_le hp herr hR hthreshold haznorm
    have heval : (r.map Complex.ofRealHom).eval z = (A : ℂ)⁻¹ *
        (((2 * m : ℕ) : ℂ) * (p.map Complex.ofRealHom).eval
          ((A : ℂ) * z / ((2 * m : ℕ) : ℂ))) := by
      simp only [r, smul_eq_C_mul, Polynomial.map_mul, Polynomial.map_comp,
        Polynomial.map_C, Polynomial.map_X, eval_mul, eval_C, eval_comp, eval_X,
        Complex.ofRealHom_eq_coe, Complex.ofReal_div]
      have harg : ((A : ℂ) / (n : ℂ)) * z = (A : ℂ) * z / ((2 * m : ℕ) : ℂ) := by
        simp only [n, Complex.ofReal_natCast]
        ring
      rw [harg]
      simp only [n, Complex.ofReal_natCast]
      ring
    rw [heval, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA]
    refine (mul_le_mul_of_nonneg_left hg (inv_nonneg.mpr hA.le)).trans ?_
    change A⁻¹ * (6 * (1 + R^2) / Real.pi * Real.exp (|((A : ℂ) * z).im| + 1)) ≤ M
    calc
      A⁻¹ * (6 * (1 + R^2) / Real.pi * Real.exp (|((A : ℂ) * z).im| + 1)) =
          (6 * (1 + R^2) / (Real.pi * A)) * Real.exp (|((A : ℂ) * z).im| + 1) := by ring
      _ ≤ M := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by linarith : |((A : ℂ) * z).im| + 1 ≤ A * Real.sinh t + 1))
        (by positivity)
  have hmatch : ∀ x ∈ Icc (-1 : ℝ) 1,
      (r.map Complex.ofRealHom).eval (x : ℂ) = ((r.eval x : ℝ) : ℂ) := by
    intro x _
    rw [show (x : ℂ) = Complex.ofRealHom x by rfl, eval_map_apply]
    rfl
  obtain ⟨q, hq, hrq⟩ := exists_degree_le_abs_sub_eval_le_of_open_bernsteinEllipse
    (Real.one_lt_exp_iff.mpr ht) (r.map Complex.ofRealHom).differentiable.differentiableOn hF
    (f := fun x : ℝ => r.eval x) hmatch N
  have hscaled : ∀ x ∈ Icc (-1 : ℝ) 1,
      |(|x|) - r.eval x| ≤ n / A * absoluteMinimaxError (2 * m) := by
    intro x hx
    have hy : A / n * x ∈ Icc (-1 : ℝ) 1 := by
      have hc : 0 ≤ A / n := div_nonneg hA.le hn.le
      have hc1 : A / n ≤ 1 := (div_le_one hn).mpr hAn
      constructor <;> nlinarith [hx.1, hx.2]
    have h := mul_le_mul_of_nonneg_left (hbest (A / n * x) hy)
      (div_nonneg hn.le hA.le)
    have he : |(|x|) - r.eval x| = n / A * |(|A / n * x|) - p.eval (A / n * x)| := by
      simp only [r, eval_smul, smul_eq_mul, eval_comp, eval_mul, eval_C, eval_X,
        abs_mul, abs_of_pos (div_pos hA hn)]
      have he : |x| - n / A * p.eval (A / n * x) =
          n / A * (A / n * |x| - p.eval (A / n * x)) := by field_simp
      rw [he, abs_mul, abs_of_pos (div_pos hn hA)]
    rw [he]
    exact h
  have hEN : absoluteMinimaxError N ≤ n / A * absoluteMinimaxError (2 * m) +
      2 * M / (Real.exp t)^N / (Real.exp t - 1) := by
    apply absoluteMinimaxError_le_of_degree_le hq
    intro x hx
    exact (abs_sub_le |x| (r.eval x) (q.eval x)).trans (add_le_add (hscaled x hx) (hrq x hx))
  have hNbound := mul_le_mul_of_nonneg_left hEN hNp.le
  have hρ : 0 < Real.exp t - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)
  have hmain : (N : ℝ) * (n / A * absoluteMinimaxError (2 * m)) =
      n * absoluteMinimaxError (2 * m) / α := by dsimp [A]; field_simp
  have htail : (N : ℝ) * (2 * M / (Real.exp t)^N / (Real.exp t - 1)) =
      12 * Real.exp 1 * (1 + R^2) / (Real.pi * α * (Real.exp t - 1)) *
        Real.exp ((α * Real.sinh t - t) * (N : ℝ)) := by
    have he : Real.exp (A * Real.sinh t + 1) / Real.exp ((N : ℝ) * t) =
        Real.exp 1 * Real.exp ((α * Real.sinh t - t) * (N : ℝ)) := by
      rw [← Real.exp_sub, ← Real.exp_add]
      dsimp [A]
      congr 1
      ring
    calc
      (N : ℝ) * (2 * M / (Real.exp t)^N / (Real.exp t - 1)) =
          (12 * N * (1 + R^2) / (Real.pi * A * (Real.exp t - 1))) *
            (Real.exp (A * Real.sinh t + 1) / Real.exp ((N : ℝ) * t)) := by
        dsimp only [M]
        rw [← Real.exp_nat_mul]
        field_simp
        ring
      _ = _ := by
        rw [he]
        dsimp only [A]
        field_simp
  rw [mul_add, hmain, htail] at hNbound
  have hexp := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (degree_transfer_exponent_le hα1) hNp.le)
  have htailBound :
      12 * Real.exp 1 * (1 + R^2) / (Real.pi * α * (Real.exp t - 1)) *
          Real.exp ((α * Real.sinh t - t) * (N : ℝ)) ≤
        bernsteinDegreeTransferRemainder α N := by
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  exact hNbound.trans (add_le_add le_rfl htailBound)

end NLAlib
