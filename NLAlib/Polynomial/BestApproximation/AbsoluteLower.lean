import NLAlib.Polynomial.BestApproximation.Absolute
import NLAlib.Polynomial.FunctionApproximation.ChebyshevFourier
import NLAlib.ForMathlib.Analysis.FejerModulation

/-! # A positive finite lower bound for the absolute-value minimax error

The actual modulated Fejér integral annihilates every polynomial below its finite
frequency band and has norm at most one. Its explicit absolute-value Fourier
coefficients give a positive order-`1/n` lower bound, without a numerical Bernstein
constant or an assumed dual certificate.
-/

noncomputable section
set_option maxHeartbeats 600000
open Polynomial Finset MeasureTheory Set Real
open scoped NLAlib.TwoPi

namespace NLAlib

/-- The actual finite Fejér dual at the absolute-value cusp. -/
def absoluteFejerDual (K : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∫ t : AddCircle (2 * Real.pi), modulatedFejerCircleKernel K t *
    realChebyshevCircleFunction f ((Real.pi / 2 : ℝ) - t) ∂AddCircle.haarAddCircle

/-- A real cosine character convolved with the cosine pullback at the cusp angle. -/
def cuspCosineMoment (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∫ t : AddCircle (2 * Real.pi), (fourier (k : ℤ) t).re *
    realChebyshevCircleFunction f ((Real.pi / 2 : ℝ) - t) ∂AddCircle.haarAddCircle

private theorem cuspCosineMoment_eq {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1 : ℝ) 1))
    {k : ℕ} (hk : 0 < k) : cuspCosineMoment f k =
      (fourier (k : ℤ) ((Real.pi / 2 : ℝ) : AddCircle (2 * Real.pi))).re * chebyshevCoeff f k / 2 := by
  rw [cuspCosineMoment, integral_re_fourier_mul_comp_sub_eq_re_fourier_mul_coeff
    (continuous_realChebyshevCircleFunction hf) (even_realChebyshevCircleFunction f)]
  rw [chebyshevCoeff_eq_re_fourierCoeff hf, if_neg hk.ne']
  ring

private theorem cuspCosineMoment_abs_even {j : ℕ} (hj : 0 < j) :
    cuspCosineMoment (fun x : ℝ => |x|) (2 * j) = - (2 / (Real.pi * (4 * (j : ℝ) ^ 2 - 1))) := by
  rw [cuspCosineMoment_eq (by fun_prop) (by omega), re_fourier_nat_coe_eq_cos,
    show ((2 * j : ℕ) : ℝ) * (Real.pi / 2) = (j : ℝ) * Real.pi by push_cast; ring,
    Real.cos_nat_mul_pi, chebyshevCoeff_abs_even hj]
  have hpow : (-1 : ℝ) ^ j * (-1 : ℝ) ^ (j + 1) = -1 := by
    rw [← pow_add, show j + (j + 1) = 2 * j + 1 by omega, pow_add, pow_mul]
    simp
  calc _ = (4 / Real.pi / (4 * (j : ℝ) ^ 2 - 1) / 2) *
      ((-1 : ℝ) ^ j * (-1 : ℝ) ^ (j + 1)) := by ring
       _ = _ := by rw [hpow]; simp only [div_eq_mul_inv, mul_inv_rev]; ring

private theorem cusp_integrable {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) (k : ℕ) :
    Integrable (fun t : AddCircle (2 * Real.pi) => (fourier (k : ℤ) t).re *
      realChebyshevCircleFunction f ((Real.pi / 2 : ℝ) - t)) AddCircle.haarAddCircle :=
  ((Complex.continuous_re.comp (fourier (k : ℤ)).continuous).mul
    ((continuous_realChebyshevCircleFunction hf).comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- The actual dual has its finite band-frequency expression. -/
theorem absoluteFejerDual_eq_sum {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) (K : ℕ) :
    absoluteFejerDual K f = (K + 1 : ℝ)⁻¹ * ∑ m ∈ range (K + 1),
      (cuspCosineMoment f (4 * K) + ∑ j ∈ range m,
        (cuspCosineMoment f (4 * K + 2 * (j + 1)) +
          cuspCosineMoment f (4 * K - 2 * (j + 1)))) := by
  let g : AddCircle (2 * Real.pi) → ℝ := fun t => realChebyshevCircleFunction f ((Real.pi / 2 : ℝ) - t)
  let S : ℕ → AddCircle (2 * Real.pi) → ℝ := fun m t =>
    (fourier ((4 * K : ℕ) : ℤ) t).re * g t + ∑ j ∈ range m,
      ((fourier ((4 * K + 2 * (j + 1) : ℕ) : ℤ) t).re * g t +
        (fourier ((4 * K - 2 * (j + 1) : ℕ) : ℤ) t).re * g t)
  have hterm (t : AddCircle (2 * Real.pi)) : modulatedFejerCircleKernel K t * g t =
      (K + 1 : ℝ)⁻¹ * ∑ m ∈ range (K + 1), S m t := by
    rw [modulatedFejerCircleKernel_eq_sum, mul_assoc, sum_mul]
    congr 1
    apply sum_congr rfl
    intro m hm
    simp only [S, add_mul, sum_mul]
  have hS (m : ℕ) : Integrable (S m) AddCircle.haarAddCircle :=
    (cusp_integrable hf _).add (integrable_finsetSum _ (fun j hj =>
      (cusp_integrable hf _).add (cusp_integrable hf _)))
  change (∫ t : AddCircle (2 * Real.pi), modulatedFejerCircleKernel K t * g t ∂AddCircle.haarAddCircle) = _
  simp_rw [hterm]
  rw [integral_const_mul, integral_finsetSum _ (fun m hm => hS m)]
  congr 1
  apply sum_congr rfl
  intro m hm
  dsimp only [S, g]
  have his : Integrable (fun t : AddCircle (2 * Real.pi) => ∑ j ∈ range m,
      ((fourier ((4 * K + 2 * (j + 1) : ℕ) : ℤ) t).re * realChebyshevCircleFunction f ((Real.pi / 2 : ℝ) - t) +
        (fourier ((4 * K - 2 * (j + 1) : ℕ) : ℤ) t).re * realChebyshevCircleFunction f ((Real.pi / 2 : ℝ) - t)))
      AddCircle.haarAddCircle := integrable_finsetSum _ (fun j hj =>
        (cusp_integrable hf _).add (cusp_integrable hf _))
  rw [integral_add (cusp_integrable hf (4 * K)) his,
    integral_finsetSum (f := fun (j : ℕ) (t : AddCircle (2 * Real.pi)) =>
      (fourier ((4 * K + 2 * (j + 1) : ℕ) : ℤ) t).re * realChebyshevCircleFunction f ((Real.pi / 2 : ℝ) - t) +
        (fourier ((4 * K - 2 * (j + 1) : ℕ) : ℤ) t).re * realChebyshevCircleFunction f ((Real.pi / 2 : ℝ) - t))
      _ (fun j hj => (cusp_integrable hf _).add (cusp_integrable hf _))]
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [integral_add (cusp_integrable hf _) (cusp_integrable hf _)]
  rfl

/-- The genuine finite Fejér dual annihilates every polynomial below its frequency
band. Source: focused reroutes, Section 2, finite positivity certificate.
atlas: abs-best-approx-asymptotics (partial) -/
theorem absoluteFejerDual_eval_eq_zero {n K : ℕ} (hK : n < 2 * K)
    {p : ℝ[X]} (hp : p.degree ≤ n) : absoluteFejerDual K p.eval = 0 := by
  have hmoment (k : ℕ) (hk : n < k) : cuspCosineMoment p.eval k = 0 := by
    rw [cuspCosineMoment_eq p.continuous.continuousOn (by omega),
      chebyshevCoeff_eval_eq_zero_of_degree_lt hp hk, mul_zero, zero_div]
  rw [absoluteFejerDual_eq_sum p.continuous.continuousOn]
  have hterm (m : ℕ) (hm : m ∈ range (K + 1)) :
      cuspCosineMoment p.eval (4 * K) + ∑ j ∈ range m,
        (cuspCosineMoment p.eval (4 * K + 2 * (j + 1)) +
          cuspCosineMoment p.eval (4 * K - 2 * (j + 1))) = 0 := by
    rw [hmoment _ (by omega)]
    apply zero_add _ |>.trans
    apply sum_eq_zero
    intro j hj
    have := mem_range.mp hm
    have := mem_range.mp hj
    rw [hmoment _ (by omega), hmoment _ (by omega), add_zero]
  rw [sum_eq_zero hterm, mul_zero]

/-- The actual dual is a contraction for every continuous function bounded on the
unit interval. The bound follows from a positive kernel of normalized integral one.
Source: focused reroutes, Section 2, finite positivity certificate.
atlas: abs-best-approx-asymptotics (partial) -/
theorem abs_absoluteFejerDual_le {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (K : ℕ) {E : ℝ} (hbound : ∀ x ∈ Icc (-1 : ℝ) 1, |f x| ≤ E) :
    |absoluteFejerDual K f| ≤ E := by
  have hg : Continuous (fun t : AddCircle (2 * Real.pi) =>
      realChebyshevCircleFunction f ((Real.pi / 2 : ℝ) - t)) :=
    (continuous_realChebyshevCircleFunction hf).comp (by fun_prop)
  have hi : Integrable (fun t : AddCircle (2 * Real.pi) => |modulatedFejerCircleKernel K t *
      realChebyshevCircleFunction f ((Real.pi / 2 : ℝ) - t)|) AddCircle.haarAddCircle :=
    ((continuous_modulatedFejerCircleKernel K).mul hg).abs.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hF : Integrable (fun t : AddCircle (2 * Real.pi) => fejerCircleKernel K (2 • t) * E)
      AddCircle.haarAddCircle := (((continuous_fejerCircleKernel K).comp (continuous_id.nsmul 2)).mul
    continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply (abs_integral_le_integral_abs).trans
  have hm := integral_mono hi hF (fun t => ?_)
  · rw [integral_mul_const, integral_fejerCircleKernel_two_nsmul_eq_one, one_mul] at hm
    exact hm
  · rw [abs_mul]
    exact mul_le_mul (abs_modulatedFejerCircleKernel_le K t)
      (hbound _ (re_fourier_one_mem_Icc _)) (abs_nonneg _) (fejerCircleKernel_nonneg _ _)

private theorem sum_one_add_two_mul (N : ℕ) :
    (∑ m ∈ range N, (1 + 2 * (m : ℝ))) = (N : ℝ) ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

private theorem cuspCosineMoment_abs_even_le_neg {K j : ℕ}
    (hK : 0 < K) (hj : 0 < j) (hjK : j ≤ 3 * K) :
    cuspCosineMoment (fun x : ℝ => |x|) (2 * j) ≤ -(1 / (18 * Real.pi * (K : ℝ) ^ 2)) := by
  rw [cuspCosineMoment_abs_even hj]
  apply neg_le_neg
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hjKR : (j : ℝ) ≤ 3 * K := by exact_mod_cast hjK
  have hDj : 0 < Real.pi * (4 * (j : ℝ) ^ 2 - 1) :=
    mul_pos Real.pi_pos (by nlinarith)
  have hDK : 0 < 18 * Real.pi * (K : ℝ) ^ 2 := by positivity
  apply (div_le_div_iff₀ hDK hDj).mpr
  have hsmall : 4 * (j : ℝ) ^ 2 - 1 ≤ 36 * (K : ℝ) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsmall Real.pi_pos.le
  nlinarith

/-- The actual modulated positive Fejér integral of absolute value has a quantitative
negative value of order `1/K`. Source: focused reroutes, Section 2, finite dual certificate.
atlas: abs-best-approx-asymptotics (partial) -/
theorem div_le_neg_absoluteFejerDual_abs {K : ℕ} (hK : 0 < K) :
    (K + 1 : ℝ) / (18 * Real.pi * (K : ℝ) ^ 2) ≤ -absoluteFejerDual K (fun x : ℝ => |x|) := by
  let c : ℝ := 1 / (18 * Real.pi * (K : ℝ) ^ 2)
  have hb : cuspCosineMoment (fun x : ℝ => |x|) (4 * K) ≤ -c := by
    simpa only [show 2 * (2 * K) = 4 * K by omega] using
      cuspCosineMoment_abs_even_le_neg hK (by omega : 0 < 2 * K) (by omega : 2 * K ≤ 3 * K)
  have hm (m : ℕ) (hm : m ∈ range (K + 1)) :
      cuspCosineMoment (fun x : ℝ => |x|) (4 * K) + ∑ j ∈ range m,
        (cuspCosineMoment (fun x : ℝ => |x|) (4 * K + 2 * (j + 1)) +
          cuspCosineMoment (fun x : ℝ => |x|) (4 * K - 2 * (j + 1))) ≤ -c * (1 + 2 * (m : ℝ)) := by
    have hterm (j : ℕ) (hj : j ∈ range m) :
        cuspCosineMoment (fun x : ℝ => |x|) (4 * K + 2 * (j + 1)) +
          cuspCosineMoment (fun x : ℝ => |x|) (4 * K - 2 * (j + 1)) ≤ -2 * c := by
      have hmK := mem_range.mp hm
      have hjm := mem_range.mp hj
      have hp := cuspCosineMoment_abs_even_le_neg hK
        (by omega : 0 < 2 * K + (j + 1)) (by omega : 2 * K + (j + 1) ≤ 3 * K)
      have hn := cuspCosineMoment_abs_even_le_neg hK
        (by omega : 0 < 2 * K - (j + 1)) (by omega : 2 * K - (j + 1) ≤ 3 * K)
      rw [show 2 * (2 * K + (j + 1)) = 4 * K + 2 * (j + 1) by omega] at hp
      rw [show 2 * (2 * K - (j + 1)) = 4 * K - 2 * (j + 1) by omega] at hn
      change _ ≤ -c at hp hn
      linarith
    have hsum := sum_le_sum hterm
    simp only [sum_const, card_range, nsmul_eq_mul] at hsum
    linarith
  have hsum := sum_le_sum hm
  rw [← mul_sum, sum_one_add_two_mul] at hsum
  have h := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ (K + 1 : ℝ)⁻¹)
  rw [← absoluteFejerDual_eq_sum (by fun_prop) K] at h
  have heq : (K + 1 : ℝ)⁻¹ * (-c * ((K + 1 : ℕ) : ℝ) ^ 2) = -(K + 1 : ℝ) * c := by
    push_cast
    field_simp
  rw [heq] at h
  change (K + 1 : ℝ) / (18 * Real.pi * (K : ℝ) ^ 2) ≤ _
  dsimp only [c] at h
  simp only [mul_one_div, neg_div] at h
  linarith

private theorem absoluteFejerDual_sub {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) (hg : ContinuousOn g (Icc (-1 : ℝ) 1)) (K : ℕ) :
    absoluteFejerDual K (fun x => f x - g x) = absoluteFejerDual K f - absoluteFejerDual K g := by
  have hi (h : ℝ → ℝ) (hh : ContinuousOn h (Icc (-1 : ℝ) 1)) :
      Integrable (fun t : AddCircle (2 * Real.pi) => modulatedFejerCircleKernel K t *
        realChebyshevCircleFunction h ((Real.pi / 2 : ℝ) - t)) AddCircle.haarAddCircle :=
    ((continuous_modulatedFejerCircleKernel K).mul ((continuous_realChebyshevCircleFunction hh).comp
      (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [absoluteFejerDual, realChebyshevCircleFunction, mul_sub]
  exact integral_sub (hi f hf) (hi g hg)

/-- Every degree-`n` polynomial competitor leaves absolute-value error at least
`1/(18π(n+1))`. The bound follows from the actual finite integral certificate.
Source: focused mathematical reroutes, Section 2, finite dual positivity bound.
atlas: abs-best-approx-asymptotics (partial) -/
theorem one_div_eighteen_pi_mul_succ_le_absoluteMinimaxError (n : ℕ) :
    1 / (18 * Real.pi * (n + 1)) ≤ absoluteMinimaxError n := by
  let K := n / 2 + 1
  have hK : 0 < K := by dsimp only [K]; omega
  have hKn : n < 2 * K := by dsimp only [K]; omega
  obtain ⟨p, hp, he⟩ := exists_degree_le_absoluteMinimaxError n
  have hd := abs_absoluteFejerDual_le (by fun_prop : ContinuousOn (fun x : ℝ => |x| - p.eval x) (Icc (-1 : ℝ) 1)) K he
  rw [absoluteFejerDual_sub (by fun_prop) p.continuous.continuousOn K,
    absoluteFejerDual_eval_eq_zero hKn hp, sub_zero] at hd
  have hl := (div_le_neg_absoluteFejerDual_abs hK).trans ((neg_le_abs _).trans hd)
  apply le_trans _ hl
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKN : (K : ℝ) ≤ n + 1 := by exact_mod_cast (show K ≤ n + 1 by dsimp only [K]; omega)
  have hD₁ : 0 < 18 * Real.pi * (n + 1) := by positivity
  have hD₂ : 0 < 18 * Real.pi * (K : ℝ) ^ 2 := by positivity
  apply (div_le_div_iff₀ hD₁ hD₂).mpr
  have hpoly : (K : ℝ) ^ 2 ≤ (K + 1) * (n + 1) := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hpoly (by positivity : 0 ≤ 18 * Real.pi)
  nlinarith

end NLAlib
