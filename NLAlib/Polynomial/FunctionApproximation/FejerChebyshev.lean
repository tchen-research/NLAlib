import NLAlib.ForMathlib.Analysis.FejerKernel
import NLAlib.Polynomial.FunctionApproximation.ChebyshevSeries
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Positive Fejér means of Chebyshev series

The finite Cesàro means are convolution with the genuine positive Fejér kernel.
They preserve positivity, contract the uniform norm, and converge uniformly for
every continuous unit-interval function by polynomial density.
Atlas: `fejer-chebyshev-means`.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Finset Real Set Filter MeasureTheory
open scoped Topology ComplexConjugate

namespace NLAlib

open scoped NLAlib.TwoPi

/-- The genuine Cesàro mean has the triangular Chebyshev coefficient weights
`1-k/(n+1)`, including the constant coefficient with weight one.
Source: Trefethen, ATAP, Exercise 6.6; the finite Cesàro sum.
atlas: fejer-chebyshev-means (partial) -/
theorem fejerChebyshevMean_eq_sum_smul_T (f : ℝ → ℝ) (n : ℕ) :
    fejerChebyshevMean f n = ∑ k ∈ range (n + 1),
      (1 - (k : ℝ) / (n + 1)) • (C (chebyshevCoeff f k) * T ℝ (k : ℤ)) := by
  let b : ℕ → ℝ[X] := fun k => C (chebyshevCoeff f k) * T ℝ (k : ℤ)
  have hsum : ∀ n : ℕ, (∑ m ∈ range (n + 1), chebyshevTrunc f m) =
      ∑ k ∈ range (n + 1), ((n + 1 - k : ℕ) : ℝ) • b k := by
    intro n
    induction n with
    | zero => simp [chebyshevTrunc, b]
    | succ n ih =>
      rw [sum_range_succ, ih]
      change (∑ k ∈ range (n + 1), ((n + 1 - k : ℕ) : ℝ) • b k) +
        (∑ k ∈ range (n + 2), b k) =
          ∑ k ∈ range (n + 2), ((n + 2 - k : ℕ) : ℝ) • b k
      rw [sum_range_succ (f := b) (n + 1),
        sum_range_succ (f := fun k => ((n + 2 - k : ℕ) : ℝ) • b k) (n + 1)]
      simp only [show n + 2 - (n + 1) = 1 by omega, Nat.cast_one, one_smul]
      rw [← add_assoc, ← sum_add_distrib]
      congr 1
      apply sum_congr rfl
      intro k hk
      have hcount : ((n + 1 - k : ℕ) : ℝ) + 1 = ((n + 2 - k : ℕ) : ℝ) := by
        norm_cast
        have := mem_range.mp hk
        omega
      calc
        ((n + 1 - k : ℕ) : ℝ) • b k + b k =
            ((n + 1 - k : ℕ) : ℝ) • b k + (1 : ℝ) • b k := by rw [one_smul]
        _ = (((n + 1 - k : ℕ) : ℝ) + 1) • b k := (add_smul _ _ _).symm
        _ = ((n + 2 - k : ℕ) : ℝ) • b k := by rw [hcount]
  unfold fejerChebyshevMean
  rw [hsum, smul_sum]
  apply sum_congr rfl
  intro k hk
  rw [smul_smul]
  have hk_le : k ≤ n + 1 := (mem_range.mp hk).le
  rw [Nat.cast_sub hk_le]
  simp only [Nat.cast_add, Nat.cast_one]
  change ((n + 1 : ℝ)⁻¹ * ((n + 1 : ℝ) - (k : ℝ))) • b k = _
  congr 1
  have hn0 : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp

/-- Every Fejér Chebyshev mean has degree at most its cutoff.
Source: Trefethen, ATAP, Exercise 6.6; helper for `fejer-chebyshev-means`. -/
theorem degree_fejerChebyshevMean_le (f : ℝ → ℝ) (n : ℕ) :
    (fejerChebyshevMean f n).degree ≤ n := by
  unfold fejerChebyshevMean
  refine (degree_smul_le _ _).trans ((degree_sum_le _ _).trans (Finset.sup_le fun m hm => ?_))
  exact (degree_chebyshevTrunc_le f m).trans (by exact_mod_cast Nat.le_of_lt_succ (mem_range.mp hm))

/-- Fejér means preserve every constant function, so the contraction bound has norm exactly one.
Source: Trefethen, ATAP, Exercise 6.6.
atlas: fejer-chebyshev-means (partial) -/
@[simp] theorem fejerChebyshevMean_const (c : ℝ) (n : ℕ) :
    fejerChebyshevMean (fun _ => c) n = C c := by
  have htrunc : ∀ m, chebyshevTrunc (fun _ => c) m = C c := by
    intro m
    simpa only [eval_C] using chebyshevTrunc_eval_eq_of_degree_le
      (p := C c) (n := m) (degree_C_le.trans (by exact_mod_cast Nat.zero_le m))
  unfold fejerChebyshevMean
  simp_rw [htrunc]
  rw [sum_const, card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have hn0 : (n + 1 : ℝ) ≠ 0 := by positivity
  simp only [Nat.cast_add, Nat.cast_one]
  rw [inv_mul_cancel₀ hn0, one_smul]

/-- Dirichlet-kernel convolution is the genuine finite Chebyshev truncation.
Source: Trefethen, ATAP, Exercise 6.6; finite Fourier convolution.
Helper for `fejer-chebyshev-means`. -/
theorem integral_dirichletCircleKernel_mul_realChebyshevCircleFunction {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) (n : ℕ) (a : AddCircle (2 * Real.pi)) :
    (∫ t : AddCircle (2 * Real.pi), dirichletCircleKernel n t * realChebyshevCircleFunction f (a - t)
      ∂AddCircle.haarAddCircle) = (chebyshevTrunc f n).eval ((fourier 1 a).re) := by
  let g := realChebyshevCircleFunction f
  have hg : Continuous g := continuous_realChebyshevCircleFunction hf
  have hgi : Integrable (fun t : AddCircle (2 * Real.pi) => g (a - t)) AddCircle.haarAddCircle :=
    (hg.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hki : ∀ k, Integrable (fun t : AddCircle (2 * Real.pi) =>
      (fourier ((k + 1 : ℕ) : ℤ) t).re * g (a - t)) AddCircle.haarAddCircle := by
    intro k
    exact ((Complex.continuous_re.comp (fourier ((k + 1 : ℕ) : ℤ)).continuous).mul
      (hg.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hterm : ∀ t : AddCircle (2 * Real.pi), dirichletCircleKernel n t * g (a - t) =
      (fourier 0 t).re * g (a - t) +
        2 * ∑ k ∈ range n, (fourier ((k + 1 : ℕ) : ℤ) t).re * g (a - t) := by
    intro t
    simp only [dirichletCircleKernel, add_mul, mul_assoc, sum_mul]
    simp
  change (∫ t : AddCircle (2 * Real.pi), dirichletCircleKernel n t * g (a - t)
    ∂AddCircle.haarAddCircle) = _
  simp_rw [hterm]
  rw [integral_add (by simpa using hgi) (by
    exact (integrable_finsetSum _ (fun k hk => hki k)).const_mul 2), integral_const_mul,
    integral_finsetSum _ (fun k hk => hki k),
    integral_re_fourier_mul_comp_sub_eq_re_fourier_mul_coeff hg (even_realChebyshevCircleFunction f)]
  simp_rw [integral_re_fourier_mul_comp_sub_eq_re_fourier_mul_coeff hg
    (even_realChebyshevCircleFunction f)]
  simp only [chebyshevTrunc, eval_finsetSum, eval_mul, eval_C]
  rw [sum_range_succ']
  simp only [Nat.cast_zero, T_zero, eval_one, mul_one]
  rw [chebyshevCoeff_eq_re_fourierCoeff hf]
  simp only [if_true, one_mul, fourier_zero,
    Complex.one_re]
  rw [mul_sum]
  conv_rhs => rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro k hk
  rw [chebyshevCoeff_eq_re_fourierCoeff hf, if_neg (by omega), eval_T_re_fourier_one]
  ring

/-- Fejér Chebyshev means are convolution with the actual positive Fejér kernel.
Source: Trefethen, ATAP, Exercise 6.6; operator rederivations `polyseries:fejeroperator`.
atlas: fejer-chebyshev-means (partial) -/
theorem eval_fejerChebyshevMean_eq_integral {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) (n : ℕ) (a : AddCircle (2 * Real.pi)) :
    (fejerChebyshevMean f n).eval ((fourier 1 a).re) =
      ∫ t : AddCircle (2 * Real.pi), fejerCircleKernel n t * realChebyshevCircleFunction f (a - t)
        ∂AddCircle.haarAddCircle := by
  simp only [fejerChebyshevMean, eval_smul, smul_eq_mul, eval_finsetSum]
  simp_rw [fejerCircleKernel_eq_avg_dirichlet]
  have hterm : ∀ t, (n + 1 : ℝ)⁻¹ * (∑ m ∈ range (n + 1), dirichletCircleKernel m t) *
      realChebyshevCircleFunction f (a - t) = (n + 1 : ℝ)⁻¹ *
        ∑ m ∈ range (n + 1), dirichletCircleKernel m t * realChebyshevCircleFunction f (a - t) := by
    intro t
    rw [mul_assoc, sum_mul]
  simp_rw [hterm]
  rw [integral_const_mul, integral_finsetSum (f := fun m t =>
    dirichletCircleKernel m t * realChebyshevCircleFunction f (a - t)) _ (fun m hm =>
    ((continuous_dirichletCircleKernel m).mul
      ((continuous_realChebyshevCircleFunction hf).comp
        (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))]
  simp_rw [integral_dirichletCircleKernel_mul_realChebyshevCircleFunction hf]

/-- Fejér means preserve nonnegativity throughout the unit interval.
Source: Trefethen, ATAP, Exercise 6.6; positive Fejér convolution.
atlas: fejer-chebyshev-means (partial) -/
theorem eval_fejerChebyshevMean_nonneg {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ f x) (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 ≤ (fejerChebyshevMean f n).eval x := by
  have hxcos : (fourier 1 (Real.arccos x : AddCircle (2 * Real.pi))).re = x := by
    rw [show (fourier 1 (Real.arccos x : AddCircle (2 * Real.pi))).re = Real.cos (Real.arccos x) by
      simpa using re_fourier_nat_coe_eq_cos 1 (Real.arccos x), Real.cos_arccos hx.1 hx.2]
  rw [← hxcos, eval_fejerChebyshevMean_eq_integral hf]
  apply integral_nonneg
  intro t
  exact mul_nonneg (fejerCircleKernel_nonneg _ _)
    (hpos _ (re_fourier_one_mem_Icc _))

/-- Fejér means contract every uniform bound on the unit interval.
Source: Trefethen, ATAP, Exercise 6.6; positive normalized Fejér convolution.
atlas: fejer-chebyshev-means (partial) -/
theorem abs_eval_fejerChebyshevMean_le {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) {M : ℝ}
    (hM : ∀ x ∈ Icc (-1 : ℝ) 1, |f x| ≤ M) (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |(fejerChebyshevMean f n).eval x| ≤ M := by
  have hxcos : (fourier 1 (Real.arccos x : AddCircle (2 * Real.pi))).re = x := by
    rw [show (fourier 1 (Real.arccos x : AddCircle (2 * Real.pi))).re = Real.cos (Real.arccos x) by
      simpa using re_fourier_nat_coe_eq_cos 1 (Real.arccos x), Real.cos_arccos hx.1 hx.2]
  rw [← hxcos, eval_fejerChebyshevMean_eq_integral hf, ← Real.norm_eq_abs]
  have hki : Integrable (fun t : AddCircle (2 * Real.pi) => M * fejerCircleKernel n t)
      AddCircle.haarAddCircle :=
    (continuous_const.mul (continuous_fejerCircleKernel n)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine (norm_integral_le_of_norm_le hki (Filter.Eventually.of_forall (fun t => ?_))).trans_eq ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (fejerCircleKernel_nonneg _ _)]
    exact (mul_le_mul_of_nonneg_left (hM _ (re_fourier_one_mem_Icc _))
      (fejerCircleKernel_nonneg _ _)).trans_eq (mul_comm _ _)
  · rw [integral_const_mul, integral_fejerCircleKernel_eq_one, mul_one]

/-- Fejér means preserve subtraction of continuous functions.
Source: finite Chebyshev coefficient linearity; helper for `fejer-chebyshev-means`. -/
theorem fejerChebyshevMean_sub {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) (hg : ContinuousOn g (Icc (-1 : ℝ) 1)) (n : ℕ) :
    fejerChebyshevMean (fun x => f x - g x) n = fejerChebyshevMean f n - fejerChebyshevMean g n := by
  simp only [fejerChebyshevMean, chebyshevTrunc, chebyshevCoeff_sub hf hg, C_sub,
    sub_mul, sum_sub_distrib, smul_sub]

/-- The Fejér means of every polynomial converge uniformly to that polynomial.
Source: finite exact Chebyshev projection and Cesàro convergence;
helper for `fejer-chebyshev-means`. -/
theorem tendstoUniformlyOn_fejerChebyshevMean_eval (p : ℝ[X]) :
    TendstoUniformlyOn (fun n x => (fejerChebyshevMean p.eval n).eval x) p.eval atTop
      (Icc (-1 : ℝ) 1) := by
  let s : Set ℝ := Icc (-1 : ℝ) 1
  let pc : C(s, ℝ) := p.toContinuousMapOn s
  let u : ℕ → C(s, ℝ) := fun n => (chebyshevTrunc p.eval n).toContinuousMapOn s
  have hexact : ∀ᶠ n in atTop, u n = pc := by
    filter_upwards [eventually_ge_atTop p.natDegree] with n hn
    have hp : p.degree ≤ n := p.degree_le_natDegree.trans (by exact_mod_cast hn)
    dsimp [u, pc]
    rw [chebyshevTrunc_eval_eq_of_degree_le hp]
  have hu : Tendsto u atTop (𝓝 pc) := tendsto_const_nhds.congr'
    (hexact.mono (fun n hn => hn.symm))
  have hcesaro := hu.cesaro_smul.comp (tendsto_add_atTop_nat 1)
  have hmean : Tendsto (fun n => (fejerChebyshevMean p.eval n).toContinuousMapOn s) atTop (𝓝 pc) := by
    convert hcesaro using 1
    funext n
    ext x
    simp [fejerChebyshevMean, u, eval_smul, eval_finsetSum]
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hnorm : ∀ᶠ n in atTop, ‖pc - (fejerChebyshevMean p.eval n).toContinuousMapOn s‖ < ε := by
    filter_upwards [(Metric.tendsto_nhds.mp hmean) ε hε] with n hn
    rw [_root_.dist_eq_norm] at hn
    simpa only [norm_sub_rev] using hn
  filter_upwards [hnorm] with n hn x hx
  have h := ContinuousMap.norm_coe_le_norm
    (pc - (fejerChebyshevMean p.eval n).toContinuousMapOn s) ⟨x, hx⟩
  exact lt_of_le_of_lt (by simpa only [pc, ContinuousMap.sub_apply, Polynomial.toContinuousMapOn_apply,
    Polynomial.toContinuousMap_apply, Real.norm_eq_abs, Real.dist_eq] using h) hn

/-- Fejér Cesàro means of the genuine Chebyshev series converge uniformly for every
continuous function on the full closed interval. Together with the positive contraction
and exact normalization, this proves the original Fejér assertion.
Source: Trefethen, ATAP, Exercise 6.6; positive contractions and polynomial density.
atlas: fejer-chebyshev-means -/
theorem tendstoUniformlyOn_fejerChebyshevMean {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    TendstoUniformlyOn (fun n x => (fejerChebyshevMean f n).eval x) f atTop
      (Icc (-1 : ℝ) 1) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-1) 1 f hf (ε / 3) (by positivity)
  have hpoly := (Metric.tendstoUniformlyOn_iff.mp (tendstoUniformlyOn_fejerChebyshevMean_eval p))
    (ε / 3) (by positivity)
  filter_upwards [hpoly] with n hn x hx
  have herr : ∀ y ∈ Icc (-1 : ℝ) 1, |f y - p.eval y| ≤ ε / 3 := by
    intro y hy
    rw [abs_sub_comm]
    exact (hp y hy).le
  have hmean := abs_eval_fejerChebyshevMean_le (hf.sub p.continuous.continuousOn) herr n hx
  change |(fejerChebyshevMean (fun y => f y - p.eval y) n).eval x| ≤ ε / 3 at hmean
  rw [fejerChebyshevMean_sub hf p.continuous.continuousOn, eval_sub] at hmean
  have h1 := hp x hx
  have h2 := hn x hx
  rw [Real.dist_eq] at h2 ⊢
  have ht1 := abs_sub_le (f x) (p.eval x) ((fejerChebyshevMean f n).eval x)
  have ht2 := abs_sub_le (p.eval x) ((fejerChebyshevMean p.eval n).eval x)
    ((fejerChebyshevMean f n).eval x)
  rw [abs_sub_comm (p.eval x) (f x)] at h1
  rw [abs_sub_comm ((fejerChebyshevMean f n).eval x) ((fejerChebyshevMean p.eval n).eval x)] at hmean
  linarith

end NLAlib
