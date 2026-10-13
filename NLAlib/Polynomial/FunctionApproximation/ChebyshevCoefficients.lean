import NLAlib.Polynomial.FunctionApproximation.Basic
import NLAlib.Polynomial.FunctionApproximation.AnalyticFourier
import NLAlib.Polynomial.Chebyshev.CosineBasis
import NLAlib.ForMathlib.Analysis.FourierConvolution

/-!
# Chebyshev coefficient functionals

The canonical arcsine-measure coefficients agree with the weighted, cosine, and Joukowski
contour interfaces. Linearity, orthogonality, exact polynomial reconstruction, and sharp
individual coefficient bounds use that one coefficient function.
Atlas: `chebyshev-coefficients-def`.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Finset Real MeasureTheory Set
open scoped NLAlib.TwoPi

namespace NLAlib

/-- Reflection of the cosine pullback halves its full-period integral. Source: the
symmetry `cos (2π - θ) = cos θ` and adjacent interval additivity. -/
theorem integral_chebyshev_cosine_full_period {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1) 1)) (k : ℕ) :
    (∫ θ in 0..2 * Real.pi, f (Real.cos θ) * (T ℝ (k : ℤ)).eval (Real.cos θ)) =
      2 * ∫ θ in 0..Real.pi, f (Real.cos θ) * (T ℝ (k : ℤ)).eval (Real.cos θ) := by
  let g : ℝ → ℝ := fun θ => f (Real.cos θ) * (T ℝ (k : ℤ)).eval (Real.cos θ)
  have hfc : Continuous (fun θ => f (Real.cos θ)) :=
    hf.comp_continuous Real.continuous_cos (fun θ => ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩)
  have hg : Continuous g := hfc.mul ((T ℝ (k : ℤ)).continuous.comp Real.continuous_cos)
  have hreflect := intervalIntegral.integral_comp_sub_left (f := g)
    (a := Real.pi) (b := 2 * Real.pi) (2 * Real.pi)
  have hsym : ∀ θ, g (2 * Real.pi - θ) = g θ := by
    intro θ
    simp only [g, Real.cos_two_pi_sub]
  simp_rw [hsym] at hreflect
  have heq : (∫ θ in Real.pi..2 * Real.pi, g θ) = ∫ θ in 0..Real.pi, g θ := by
    simpa only [sub_self, show 2 * Real.pi - Real.pi = Real.pi by ring] using hreflect
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hg.intervalIntegrable 0 Real.pi) (hg.intervalIntegrable Real.pi (2 * Real.pi))
  change (∫ θ in 0..2 * Real.pi, g θ) = 2 * ∫ θ in 0..Real.pi, g θ
  rw [← hadd, heq]
  ring

/-- A continuous real restriction identifies the real contour coefficient with the
weighted real Chebyshev coefficient. No holomorphic extension is needed for this equality.
Source: Trefethen, ATAP, Chapters 3 and 8. -/
theorem chebyshevAnalyticCoeff_eq_chebyshevCoeff {F : ℂ → ℂ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1) 1))
    (hF : ∀ x ∈ Icc (-1 : ℝ) 1, F x = (f x : ℂ)) (k : ℕ) :
    chebyshevAnalyticCoeff F k = chebyshevCoeff f k := by
  have hfc : Continuous (fun θ => f (Real.cos θ)) :=
    hf.comp_continuous Real.continuous_cos (fun θ => ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩)
  have hcircle : ∀ θ : ℝ, chebyshevCircleFunction F (θ : AddCircle (2 * Real.pi)) =
      (f (Real.cos θ) : ℂ) := by
    intro θ
    rw [chebyshevCircleFunction_coe_eq_cos]
    exact hF _ ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hI : IntervalIntegrable (fun θ : ℝ =>
      fourier (-(k : ℤ)) (θ : AddCircle (2 * Real.pi)) * (f (Real.cos θ) : ℂ))
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    exact ((fourier (-(k : ℤ))).continuous.comp (AddCircle.continuous_mk' (2 * Real.pi))).mul
      (Complex.continuous_ofReal.comp hfc)
  have hreal := Complex.reCLM.intervalIntegral_comp_comm hI
  change (∫ θ in 0..2 * Real.pi,
      (fourier (-(k : ℤ)) (θ : AddCircle (2 * Real.pi)) * (f (Real.cos θ) : ℂ)).re) =
    (∫ θ in 0..2 * Real.pi,
      fourier (-(k : ℤ)) (θ : AddCircle (2 * Real.pi)) * (f (Real.cos θ) : ℂ)).re at hreal
  have hterm : ∀ θ : ℝ,
      (fourier (-(k : ℤ)) (θ : AddCircle (2 * Real.pi)) * (f (Real.cos θ) : ℂ)).re =
        f (Real.cos θ) * (T ℝ (k : ℤ)).eval (Real.cos θ) := by
    intro θ
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, fourier_neg, Complex.conj_re, re_fourier_nat_coe_eq_cos,
      T_real_cos, Int.cast_natCast]
    ring
  simp_rw [hterm] at hreal
  rw [chebyshevAnalyticCoeff, chebyshevComplexCoeff_eq_fourierCoeff,
    fourierCoeff_eq_intervalIntegral _ _ 0, zero_add]
  simp_rw [hcircle]
  have hnormal (z : ℂ) :
      ((if k = 0 then (1 : ℂ) else 2) * ((1 / (2 * Real.pi) : ℝ) • z)).re =
        (if k = 0 then (1 : ℝ) else 2) * (1 / (2 * Real.pi)) * z.re := by
    split_ifs <;> simp [Complex.mul_re, Complex.real_smul]
    ring
  rw [hnormal]
  simp only [smul_eq_mul]
  rw [← hreal, integral_chebyshev_cosine_full_period hf k, chebyshevCoeff,
    integral_measureT_eq_integral_cos]
  split_ifs <;> ring

/-- The complex contour coefficient itself is the real weighted coefficient when the
restriction is real and continuous. Source: even-real Fourier symmetry and the contour bridge. -/
theorem chebyshevComplexCoeff_eq_ofReal_chebyshevCoeff {F : ℂ → ℂ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1) 1))
    (hF : ∀ x ∈ Icc (-1 : ℝ) 1, F x = (f x : ℂ)) (k : ℕ) :
    chebyshevComplexCoeff F k = (chebyshevCoeff f k : ℂ) := by
  let g : AddCircle (2 * Real.pi) → ℝ := fun θ => (chebyshevCircleFunction F θ).re
  have hreal : chebyshevCircleFunction F = fun θ => (g θ : ℂ) := by
    funext θ
    induction θ using QuotientAddGroup.induction_on with
    | H θ =>
      change chebyshevCircleFunction F (θ : AddCircle (2 * Real.pi)) =
        ((chebyshevCircleFunction F (θ : AddCircle (2 * Real.pi))).re : ℂ)
      rw [chebyshevCircleFunction_coe_eq_cos, hF _ ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩]
      simp
  have heven : ∀ θ, g (-θ) = g θ := by
    intro θ
    simp only [g, chebyshevCircleFunction_neg]
  have him := im_fourierCoeff_of_even_real g heven (k : ℤ)
  apply Complex.ext
  · simpa only [Complex.ofReal_re, chebyshevAnalyticCoeff] using
      chebyshevAnalyticCoeff_eq_chebyshevCoeff hf hF k
  · rw [chebyshevComplexCoeff_eq_fourierCoeff, hreal]
    split_ifs <;> simp [Complex.mul_im, him]

/-- Chebyshev coefficient functionals preserve addition of continuous functions.
Source: Trefethen, ATAP, Chapter 3.
atlas: chebyshev-coefficients-def (partial) -/
theorem chebyshevCoeff_add {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) (hg : ContinuousOn g (Icc (-1 : ℝ) 1))
    (k : ℕ) : chebyshevCoeff (fun x => f x + g x) k = chebyshevCoeff f k + chebyshevCoeff g k := by
  simp only [chebyshevCoeff, add_mul]
  rw [integral_add (f := fun x => f x * (T ℝ (k : ℤ)).eval x)
    (g := fun x => g x * (T ℝ (k : ℤ)).eval x)
    (integrable_measureT (hf.mul (by fun_prop)))
    (integrable_measureT (hg.mul (by fun_prop))), mul_add]

/-- Chebyshev coefficient functionals preserve scalar multiplication.
Source: Trefethen, ATAP, Chapter 3.
atlas: chebyshev-coefficients-def (partial) -/
theorem chebyshevCoeff_const_mul (f : ℝ → ℝ) (c : ℝ) (k : ℕ) :
    chebyshevCoeff (fun x => c * f x) k = c * chebyshevCoeff f k := by
  simp only [chebyshevCoeff]
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  ring

/-- Chebyshev coefficient functionals preserve subtraction of continuous functions.
Source: Trefethen, ATAP, Chapter 3; helper for `chebyshev-series-convergence`. -/
theorem chebyshevCoeff_sub {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) (hg : ContinuousOn g (Icc (-1 : ℝ) 1))
    (k : ℕ) : chebyshevCoeff (fun x => f x - g x) k = chebyshevCoeff f k - chebyshevCoeff g k := by
  have h := chebyshevCoeff_add (g := fun x => (-1 : ℝ) * g x) hf
    (continuousOn_const.mul hg) k
  rw [chebyshevCoeff_const_mul] at h
  simpa only [neg_one_mul, ← sub_eq_add_neg] using h

/-- The coefficient of a Chebyshev basis polynomial is its Kronecker delta.
Source: Trefethen, ATAP, Chapter 3; Mathlib Chebyshev orthogonality.
atlas: chebyshev-coefficients-def (partial) -/
@[simp] theorem chebyshevCoeff_eval_T (j k : ℕ) :
    chebyshevCoeff (fun x => (T ℝ (j : ℤ)).eval x) k = if j = k then 1 else 0 := by
  rw [chebyshevCoeff]
  by_cases hjk : j = k
  · subst j
    by_cases hk : k = 0
    · subst k
      simp only [Nat.cast_zero]
      rw [integral_eval_T_real_mul_self_measureT_zero]
      simp [Real.pi_ne_zero]
    · rw [if_neg hk, integral_T_real_mul_self_measureT_of_ne_zero hk, if_pos rfl]
      field_simp
  · rw [integral_eval_T_real_mul_eval_T_real_measureT_of_ne hjk, if_neg hjk, mul_zero]

/-- The Chebyshev coefficient of a finite Chebyshev expansion is its corresponding entry.
Source: finite orthogonal projection, Trefethen ATAP, Chapter 3.
Helper for `chebyshev-coefficients-def`. -/
theorem chebyshevCoeff_eval_sum_smul_T (c : ℕ → ℝ) (n k : ℕ) :
    chebyshevCoeff (fun x => (∑ j ∈ range (n + 1), c j • T ℝ (j : ℤ)).eval x) k =
      if k ≤ n then c k else 0 := by
  simp only [chebyshevCoeff, eval_finsetSum, eval_smul,
    smul_eq_mul, Finset.sum_mul]
  rw [integral_finsetSum _ (fun j hj =>
    integrable_measureT (by fun_prop))]
  simp_rw [mul_assoc, integral_const_mul]
  rw [Finset.mul_sum]
  have hterm : ∀ j, (if k = 0 then 1 else 2) / Real.pi *
      (c j * ∫ x, (T ℝ (j : ℤ)).eval x * (T ℝ (k : ℤ)).eval x ∂measureT) =
        c j * (if j = k then 1 else 0) := by
    intro j
    rw [← mul_assoc, mul_comm ((if k = 0 then 1 else 2) / Real.pi) (c j), mul_assoc,
      ← chebyshevCoeff, chebyshevCoeff_eval_T]
  simp_rw [hterm]
  simp [Finset.sum_ite_eq']

/-- Coefficients above the degree of a polynomial vanish.
Source: Trefethen, ATAP, Chapter 3, finite Chebyshev basis.
atlas: chebyshev-coefficients-def (partial) -/
theorem chebyshevCoeff_eval_eq_zero_of_degree_lt {p : ℝ[X]} {n k : ℕ}
    (hp : p.degree ≤ n) (hnk : n < k) : chebyshevCoeff p.eval k = 0 := by
  obtain ⟨c, hc⟩ := exists_sum_smul_T_eq_of_degree_le hp
  rw [← hc, chebyshevCoeff_eval_sum_smul_T, if_neg (by omega)]

/-- Chebyshev truncation reproduces every polynomial of degree at most its cutoff.
Source: Trefethen, ATAP, Chapter 3, finite Chebyshev basis.
atlas: chebyshev-coefficients-def (partial) -/
theorem chebyshevTrunc_eval_eq_of_degree_le {p : ℝ[X]} {n : ℕ}
    (hp : p.degree ≤ n) : chebyshevTrunc p.eval n = p := by
  obtain ⟨c, hc⟩ := exists_sum_smul_T_eq_of_degree_le hp
  unfold chebyshevTrunc
  rw [← hc]
  apply Finset.sum_congr rfl
  intro k hk
  rw [chebyshevCoeff_eval_sum_smul_T, if_pos (Nat.le_of_lt_succ (mem_range.mp hk)), C_mul']

/-- Every Chebyshev truncation has degree at most its cutoff.
Source: Trefethen, ATAP, Chapter 3; helper for `chebyshev-coefficients-def`. -/
theorem degree_chebyshevTrunc_le (f : ℝ → ℝ) (n : ℕ) : (chebyshevTrunc f n).degree ≤ n := by
  unfold chebyshevTrunc
  refine (degree_sum_le _ _).trans (Finset.sup_le fun k hk => ?_)
  rw [C_mul']
  refine (degree_smul_le _ _).trans ?_
  rw [degree_T, Int.natAbs_natCast]
  exact_mod_cast Nat.le_of_lt_succ (mem_range.mp hk)

/-- The undoubled constant coefficient is bounded by the function bound on the interval.
Source: Trefethen, ATAP, Chapter 3.
atlas: chebyshev-coefficients-def (partial) -/
theorem abs_chebyshevCoeff_zero_le {f : ℝ → ℝ} {M : ℝ}
    (hM : ∀ x ∈ Icc (-1 : ℝ) 1, |f x| ≤ M) : |chebyshevCoeff f 0| ≤ M := by
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := Real.pi) (f := fun θ => f (cos θ) * cos ((0 : ℝ) * θ))
    (C := M) (fun θ hθ => by
      simpa only [zero_mul, cos_zero, mul_one, Real.norm_eq_abs] using
        hM (cos θ) ⟨neg_one_le_cos θ, cos_le_one θ⟩)
  simp only [chebyshevCoeff_eq_cosine_integral, if_true, Nat.cast_zero, zero_mul, cos_zero, mul_one]
  rw [abs_mul, abs_of_pos (by positivity : 0 < (1 : ℝ) / Real.pi)]
  simp only [sub_zero, abs_of_pos Real.pi_pos, Real.norm_eq_abs, zero_mul, cos_zero,
    mul_one] at hI
  calc 1 / Real.pi * |∫ θ in 0..Real.pi, f (cos θ)| ≤ 1 / Real.pi * (M * Real.pi) :=
      mul_le_mul_of_nonneg_left hI (by positivity)
    _ = M := by field_simp

/-- Every positive Chebyshev coefficient is bounded by twice the function bound.
Source: Trefethen, ATAP, Chapter 3.
atlas: chebyshev-coefficients-def -/
theorem abs_chebyshevCoeff_le_two_mul {f : ℝ → ℝ} {M : ℝ}
    (hM : ∀ x ∈ Icc (-1 : ℝ) 1, |f x| ≤ M) {k : ℕ} (hk : 0 < k) :
    |chebyshevCoeff f k| ≤ 2 * M := by
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := Real.pi) (f := fun θ => f (cos θ) * cos ((k : ℝ) * θ))
    (C := M) (fun θ hθ => by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul_of_nonneg_left (abs_cos_le_one _) (abs_nonneg _)).trans
        (by simpa only [mul_one] using hM (cos θ) ⟨neg_one_le_cos θ, cos_le_one θ⟩))
  simp only [chebyshevCoeff_eq_cosine_integral, if_neg hk.ne']
  rw [abs_mul, abs_of_pos (by positivity : 0 < (2 : ℝ) / Real.pi)]
  simp only [sub_zero, abs_of_pos Real.pi_pos, Real.norm_eq_abs] at hI
  calc 2 / Real.pi * |∫ θ in 0..Real.pi, f (cos θ) * cos ((k : ℝ) * θ)| ≤
      2 / Real.pi * (M * Real.pi) := mul_le_mul_of_nonneg_left hI (by positivity)
    _ = 2 * M := by field_simp

end NLAlib
