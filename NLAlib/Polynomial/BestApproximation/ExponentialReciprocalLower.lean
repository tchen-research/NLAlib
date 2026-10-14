import NLAlib.Polynomial.BestApproximation.WeightedMinimax
import NLAlib.Polynomial.BestApproximation.LaguerreProjection
import NLAlib.Polynomial.Interpolation.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The finite weighted-minimax lower certificate for reciprocal exponentials

The finite Laguerre Gram lower bound is transferred to every pole-free reciprocal
polynomial through a positive weighted minimizer on a finite interval. Its
exponential interpolant has a nonnegative tail remainder.
Source: the retained reciprocal lower-bound appendix of the focused re-derivations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial MeasureTheory Set
namespace NLAlib

private def expQuarterOn (a : ℝ) : C(Icc 0 a, ℝ) :=
  ⟨fun x => Real.exp ((x : ℝ)/4), by fun_prop⟩

private def expHalfWeightOn (a : ℝ) : C(Icc 0 a, ℝ) :=
  ⟨fun x => Real.exp (-(x : ℝ)/2), by fun_prop⟩

/-- The finite-interval weighted polynomial error used by the reciprocal
exponential certificate. Source: retained lower-bound appendix. -/
def expQuarterWeightedError (a : ℝ) (p : ℝ[X]) : ℝ :=
  ‖expHalfWeightOn a * (expQuarterOn a - p.toContinuousMapOn (Icc 0 a))‖

/-- A positive weighted minimizer for the growing exponential exists, and its
extrapolated values stay positive and below that exponential after the interval.
Source: retained lower-bound appendix, weighted minimax and Rolle interpolation. -/
theorem exists_expQuarterWeightedError_minimizer {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ∃ q : ℝ[X], q.degree ≤ n ∧
      (∀ p : ℝ[X], p.degree ≤ n → expQuarterWeightedError a q ≤ expQuarterWeightedError a p) ∧
      ∀ x : ℝ, a ≤ x →
        0 < q.eval x ∧ q.eval x ≤ Real.exp (x/4) ∧ 0 ≤ q.derivative.eval x := by
  obtain ⟨q, hq, hbest⟩ :=
    exists_degree_le_weighted_norm_sub_minimal n (expQuarterOn a) (expHalfWeightOn a)
  have hw : ∀ x : Icc 0 a, 0 < expHalfWeightOn a x := fun x => Real.exp_pos _
  obtain ⟨c, hc, hval, _⟩ := exists_interpolate_eq_of_weighted_norm_sub_minimal
    ha (expQuarterOn a) (expHalfWeightOn a) hw hq hbest
  refine ⟨q, hq, hbest, fun x hx => ?_⟩
  have h := eval_pos_le_exp_and_derivative_nonneg_of_interpolation hq hc
    (by norm_num : 0 < (1:ℝ)/4) (fun i => (c i).property)
    (by intro i; simpa [expQuarterOn, div_eq_mul_inv, mul_comm] using (hval i).symm) hx
  simpa [div_eq_mul_inv, mul_comm] using h

private theorem expQuarterWeightedError_le_iff {a : ℝ}
    (p : ℝ[X]) {E : ℝ} (hE : 0 ≤ E) :
    expQuarterWeightedError a p ≤ E ↔
      ∀ x : ℝ, 0 ≤ x → x ≤ a →
        |Real.exp (-x/2) * (Real.exp (x/4) - p.eval x)| ≤ E := by
  unfold expQuarterWeightedError
  rw [ContinuousMap.norm_le _ hE]
  constructor
  · intro h x hx hxa
    exact h ⟨x, hx, hxa⟩
  · intro h x
    exact h x x.property.1 x.property.2

private theorem reciprocal_polynomial_pos {p : ℝ[X]} {E : ℝ} (hE : E < 1)
    (hpole : ∀ x : ℝ, 0 ≤ x → p.eval x ≠ 0)
    (herr : ∀ x : ℝ, 0 ≤ x → |Real.exp (-x/4) - (p.eval x)⁻¹| ≤ E) :
    ∀ x : ℝ, 0 ≤ x → 0 < p.eval x := by
  have h0 := (abs_le.mp (herr 0 le_rfl)).2
  simp only [neg_zero, zero_div, Real.exp_zero] at h0
  have hinv : 0 < (p.eval 0)⁻¹ := by linarith
  have hp0 : 0 < p.eval 0 := inv_pos.mp hinv
  intro x hx
  by_contra hnot
  have hpx : p.eval x < 0 := lt_of_le_of_ne (le_of_not_gt hnot) (hpole x hx)
  obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc' hx p.continuous.continuousOn
    ⟨hpx.le, hp0.le⟩
  exact hpole y hy.1 hy0

private theorem abs_exp_quarter_sub_eval_le_of_reciprocal_error
    {p : ℝ[X]} {E a x : ℝ} (hE : 0 ≤ E) (hp : 0 < p.eval x)
    (hxa : x ≤ a)
    (hsmall : E * Real.exp (a/4) < 1/2)
    (herr : |Real.exp (-x/4) - (p.eval x)⁻¹| ≤ E) :
    |Real.exp (x/4) - p.eval x| ≤ 2*E*Real.exp (x/2) := by
  let f := Real.exp (x/4)
  have hf : 0 < f := Real.exp_pos _
  have hsmallx : E*f < 1/2 := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hE) hsmall
  have hexp : Real.exp (-x/4) = f⁻¹ := by
    rw [show -x/4 = -(x/4) by ring, Real.exp_neg]
  rw [hexp] at herr
  have hlower := (abs_le.mp herr).2
  have hm := mul_le_mul_of_nonneg_right hlower (mul_pos hf hp).le
  have hc1 : f⁻¹ * (f * p.eval x) = p.eval x := by rw [← mul_assoc, inv_mul_cancel₀ hf.ne', one_mul]
  have hc2 : (p.eval x)⁻¹ * (f * p.eval x) = f := by
    rw [mul_comm f, ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
  rw [sub_mul, hc1, hc2] at hm
  have hsmallmul := mul_le_mul_of_nonneg_right hsmallx.le hp.le
  have hpf : p.eval x ≤ 2*f := by nlinarith
  have hinv : f⁻¹ - (p.eval x)⁻¹ = (p.eval x - f) / (f*p.eval x) := by
    field_simp
  rw [hinv, abs_div, abs_of_pos (mul_pos hf hp)] at herr
  have habs := (div_le_iff₀ (mul_pos hf hp)).mp herr
  have hright := mul_le_mul_of_nonneg_left hpf (mul_nonneg hE hf.le)
  have hsq : f^2 = Real.exp (x/2) := by
    dsimp [f]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [abs_sub_comm]
  calc
    |p.eval x - f| ≤ E * (f*p.eval x) := habs
    _ ≤ 2*E*f^2 := by nlinarith
    _ = 2*E*Real.exp (x/2) := by rw [hsq]

private theorem integral_exp_quarter_sub_eval_sq_le {a M : ℝ} (ha : 0 < a)
    (hM : 0 ≤ M) {q : ℝ[X]} (hq : expQuarterWeightedError a q ≤ M)
    (htail : ∀ x : ℝ, a ≤ x → 0 < q.eval x ∧ q.eval x ≤ Real.exp (x/4)) :
    (∫ x : ℝ in Ioi 0, (Real.exp (x/4) - q.eval x)^2 * Real.exp (-x)) ≤
      a*M^2 + 2*Real.exp (-a/2) := by
  have hweighted := (expQuarterWeightedError_le_iff q hM).mp hq
  have hsq := integrableOn_exp_quarter_sub_eval_sq_mul_exp_neg q
  have hIoc := hsq.mono_set (show Ioc 0 a ⊆ Ioi 0 from Ioc_subset_Ioi_self)
  have hIoi := hsq.mono_set (Ioi_subset_Ioi ha.le)
  have hconst : IntegrableOn (fun _ : ℝ => M^2) (Ioc 0 a) :=
    integrableOn_const (by simp)
  have hleft : (∫ x : ℝ in Ioc 0 a,
      (Real.exp (x/4) - q.eval x)^2 * Real.exp (-x)) ≤ a*M^2 := by
    have h := setIntegral_mono_on hIoc hconst measurableSet_Ioc (fun x hx => by
      have hw := hweighted x hx.1.le hx.2
      have hs := (sq_le_sq₀ (abs_nonneg _) hM).mpr hw
      have hexp : (Real.exp (-x/2))^2 = Real.exp (-x) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      rw [sq_abs, mul_pow, hexp] at hs
      simpa only [mul_comm] using hs)
    simpa only [setIntegral_const, measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal ha.le, sub_zero, smul_eq_mul] using h
  have hexpInt : IntegrableOn (fun x : ℝ => Real.exp (-x/2)) (Ioi a) := by
    convert! integrableOn_exp_mul_Ioi (by norm_num : (-1/2 : ℝ) < 0) a using 1
    funext x
    congr 1
    ring
  have hright : (∫ x : ℝ in Ioi a,
      (Real.exp (x/4) - q.eval x)^2 * Real.exp (-x)) ≤ 2*Real.exp (-a/2) := by
    have h := setIntegral_mono_on hIoi hexpInt measurableSet_Ioi (fun x hx => by
      obtain ⟨hpos, hle⟩ := htail x hx.le
      have hf := Real.exp_pos (x/4)
      have hs : (Real.exp (x/4) - q.eval x)^2 ≤ (Real.exp (x/4))^2 :=
        (sq_le_sq₀ (sub_nonneg.mpr hle) hf.le).mpr (by linarith)
      have hm := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-x)).le
      have he : (Real.exp (x/4))^2 * Real.exp (-x) = Real.exp (-x/2) := by
        rw [pow_two, mul_assoc, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rwa [he] at hm)
    have hint : (∫ x : ℝ in Ioi a, Real.exp (-x/2)) = 2*Real.exp (-a/2) := by
      have heq : (fun x : ℝ => Real.exp (-x/2)) = (fun x => Real.exp ((-1/2)*x)) := by
        funext x
        congr 1
        ring
      rw [heq, integral_exp_mul_Ioi (by norm_num : (-1/2 : ℝ) < 0)]
      rw [show (-1/2 : ℝ)*a = -a/2 by ring]
      ring
    rwa [hint] at h
  have hsplit : (∫ x : ℝ in Ioi 0, (Real.exp (x/4) - q.eval x)^2 * Real.exp (-x)) =
      (∫ x : ℝ in Ioc 0 a, (Real.exp (x/4) - q.eval x)^2 * Real.exp (-x)) +
        ∫ x : ℝ in Ioi a, (Real.exp (x/4) - q.eval x)^2 * Real.exp (-x) := by
    rw [← Ioc_union_Ioi_eq_Ioi ha.le]
    exact setIntegral_union
      (disjoint_left.mpr (fun x hx hy => not_lt_of_ge hx.2 hy))
      measurableSet_Ioi hIoc hIoi
  rw [hsplit]
  exact add_le_add hleft hright

/-- Every pole-free reciprocal polynomial satisfies the finite Laguerre lower
certificate whenever its uniform error is small on the truncation interval.
The degree and uniform-error hypotheses refer to the actual reciprocal.
Source: retained reciprocal lower-bound appendix.
atlas: exp-rational-halfline (partial) -/
theorem laguerreResidual_le_reciprocal_error_truncation_bound
    {n : ℕ} {p : ℝ[X]} (hp : p.degree ≤ n) {a E : ℝ} (ha : 0 < a)
    (hpole : ∀ x : ℝ, 0 ≤ x → p.eval x ≠ 0)
    (herr : ∀ x : ℝ, 0 ≤ x → |Real.exp (-x/4) - (p.eval x)⁻¹| ≤ E)
    (hsmall : E*Real.exp (a/4) < 1/2) :
    2 / 3^(2*n+2) ≤ 4*a*E^2 + 2*Real.exp (-a/2) := by
  have hE : 0 ≤ E := (abs_nonneg _).trans (herr 0 le_rfl)
  have hExp : 1 ≤ Real.exp (a/4) := Real.one_le_exp_iff.mpr (by positivity)
  have hE1 : E < 1 := by have hm := mul_le_mul_of_nonneg_left hExp hE; nlinarith
  have hpos := reciprocal_polynomial_pos hE1 hpole herr
  have hpweighted : expQuarterWeightedError a p ≤ 2*E := by
    apply (expQuarterWeightedError_le_iff p (by positivity)).mpr
    intro x hx hxa
    have habs := abs_exp_quarter_sub_eval_le_of_reciprocal_error hE (hpos x hx)
      hxa hsmall (herr x hx)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-x/2) * Real.exp (x/2) = 1 := by
      rw [← Real.exp_add, show -x/2+x/2 = 0 by ring, Real.exp_zero]
    calc
      _ ≤ Real.exp (-x/2) * (2*E*Real.exp (x/2)) :=
        mul_le_mul_of_nonneg_left habs (Real.exp_pos _).le
      _ = 2*E * (Real.exp (-x/2) * Real.exp (x/2)) := by ring
      _ = 2*E := by rw [he, mul_one]
  obtain ⟨q, hq, hmin, htail⟩ := exists_expQuarterWeightedError_minimizer ha n
  have hqweighted := (hmin p hp).trans hpweighted
  have hupper := integral_exp_quarter_sub_eval_sq_le ha (by positivity : 0 ≤ 2*E)
    hqweighted (fun x hx => ⟨(htail x hx).1, (htail x hx).2.1⟩)
  have hlower := laguerreResidual_le_integral_exp_quarter_sub_eval_sq hq
  have h := hlower.trans hupper
  nlinarith

/-- The finite truncation length in the reciprocal exponential lower certificate.
Source: retained lower-bound appendix. -/
def reciprocalExponentialLowerCutoff (n : ℕ) : ℝ :=
  (4*(n : ℝ)+4)*Real.log 3 + Real.log 4

/-- The explicit reciprocal lower-bound truncation length exceeds two in every
degree, including order zero. Source: focused reciprocal reroute appendix. -/
theorem reciprocalExponentialLowerCutoff_gt_two (n : ℕ) :
    2 < reciprocalExponentialLowerCutoff n := by
  have h3 : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  dsimp [reciprocalExponentialLowerCutoff]
  nlinarith

private theorem exp_half_reciprocalExponentialLowerCutoff (n : ℕ) :
    Real.exp (reciprocalExponentialLowerCutoff n / 2) = 2 * (3 : ℝ)^(2*n+2) := by
  have h4 : Real.exp (Real.log 4 / 2) = 2 := by
    have hs : (Real.exp (Real.log 4 / 2))^2 = 4 := by
      rw [pow_two, ← Real.exp_add, show Real.log 4/2+Real.log 4/2 = Real.log 4 by ring,
        Real.exp_log (by norm_num)]
    nlinarith [Real.exp_pos (Real.log 4/2)]
  rw [show reciprocalExponentialLowerCutoff n / 2 =
      ((2*n+2 : ℕ) : ℝ)*Real.log 3 + Real.log 4/2 by
        dsimp [reciprocalExponentialLowerCutoff]; push_cast; ring,
    Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num), h4, mul_comm]

/-- Every actual pole-free reciprocal degree-`n` polynomial has uniform
half-line error at least the geometric Laguerre lower certificate.
Source: retained reciprocal lower-bound appendix.
atlas: exp-rational-halfline (partial) -/
theorem reciprocal_exp_quarter_error_ge_laguerre_lower_bound
    {n : ℕ} {p : ℝ[X]} (hp : p.degree ≤ n) {E : ℝ}
    (hpole : ∀ x : ℝ, 0 ≤ x → p.eval x ≠ 0)
    (herr : ∀ x : ℝ, 0 ≤ x → |Real.exp (-x/4) - (p.eval x)⁻¹| ≤ E) :
    1 / (2 * Real.sqrt (reciprocalExponentialLowerCutoff n) * 3^(n+1)) ≤ E := by
  let a := reciprocalExponentialLowerCutoff n
  have ha2 : 2 < a := reciprocalExponentialLowerCutoff_gt_two n
  have ha : 0 < a := by linarith
  have hE : 0 ≤ E := (abs_nonneg _).trans (herr 0 le_rfl)
  have hP : 0 < (3 : ℝ)^(n+1) := by positivity
  have hpow : (3 : ℝ)^(2*n+2) = ((3 : ℝ)^(n+1))^2 := by
    rw [← pow_mul]
    congr 1
    omega
  have hexp : (Real.exp (a/4))^2 = 2 * ((3 : ℝ)^(n+1))^2 := by
    rw [pow_two, ← Real.exp_add, show a/4+a/4 = a/2 by ring,
      exp_half_reciprocalExponentialLowerCutoff, hpow]
  have htail : 2*Real.exp (-a/2) = 1 / (3 : ℝ)^(2*n+2) := by
    rw [show -a/2 = -(a/2) by ring, Real.exp_neg,
      exp_half_reciprocalExponentialLowerCutoff]
    field_simp
  by_contra hnot
  have hlt : E < 1 / (2 * Real.sqrt a * (3 : ℝ)^(n+1)) := lt_of_not_ge hnot
  have hden : 0 < 2 * Real.sqrt a * (3 : ℝ)^(n+1) := by positivity
  have hEprod := (lt_div_iff₀ hden).mp hlt
  have hExpLt : Real.exp (a/4) < Real.sqrt a * (3 : ℝ)^(n+1) := by
    apply (sq_lt_sq₀ (Real.exp_pos _).le (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt ha.le, hexp]
    exact mul_lt_mul_of_pos_right ha2 (sq_pos_of_pos hP)
  have hsmall : E*Real.exp (a/4) < 1/2 := by
    have h := mul_le_mul_of_nonneg_left hExpLt.le hE
    nlinarith
  have hGram := laguerreResidual_le_reciprocal_error_truncation_bound hp ha hpole herr hsmall
  rw [htail] at hGram
  have hE2 : E^2 < (1 / (2 * Real.sqrt a * (3 : ℝ)^(n+1)))^2 :=
    (sq_lt_sq₀ hE (by positivity)).mpr hlt
  have h4 : 4*a*E^2 < 1 / (3 : ℝ)^(2*n+2) := by
    calc
      _ < 4*a*(1 / (2 * Real.sqrt a * (3 : ℝ)^(n+1)))^2 :=
        mul_lt_mul_of_pos_left hE2 (by positivity)
      _ = _ := by
        rw [hpow]
        field_simp
        rw [Real.sq_sqrt ha.le]
        ring
  rw [show (2 : ℝ) / 3^(2*n+2) = 2 * (1 / 3^(2*n+2)) by ring] at hGram
  linarith

/-- Every actual pole-free reciprocal polynomial of degree at most `n` has
uniform error at least `3^(-n)/(6*sqrt((4n+4)log 3+log 4))` against the
decaying exponential on the positive half-line.
Source: retained reciprocal lower-bound appendix.
atlas: exp-rational-halfline (partial) -/
theorem reciprocal_exp_neg_error_ge_geometric_lower_bound
    {n : ℕ} {p : ℝ[X]} (hp : p.degree ≤ n) {E : ℝ}
    (hpole : ∀ x : ℝ, 0 ≤ x → p.eval x ≠ 0)
    (herr : ∀ x : ℝ, 0 ≤ x → |Real.exp (-x) - (p.eval x)⁻¹| ≤ E) :
    1 / (6 * Real.sqrt (reciprocalExponentialLowerCutoff n) * 3^n) ≤ E := by
  let q := p.comp (C (1/4) * X)
  have hq : q.degree ≤ n := by
    apply degree_le_of_natDegree_le
    have h := natDegree_comp_le (p := p) (q := C (1/4) * X)
    have hlin : (C (1/4 : ℝ) * X).natDegree = 1 := by
      rw [natDegree_C_mul (by norm_num), natDegree_X]
    rw [hlin, mul_one] at h
    exact h.trans (natDegree_le_of_degree_le hp)
  have heval (x : ℝ) : q.eval x = p.eval (x/4) := by
    simp only [q, eval_comp, eval_mul, eval_C, eval_X]
    congr 1
    ring
  have h := reciprocal_exp_quarter_error_ge_laguerre_lower_bound hq
    (by intro x hx; rw [heval]; exact hpole (x/4) (by positivity))
    (by intro x hx; rw [heval]; simpa [show -(x/4) = -x/4 by ring] using herr (x/4) (by positivity))
  have heq : 1 / (2 * Real.sqrt (reciprocalExponentialLowerCutoff n) * (3 : ℝ)^(n+1)) =
      1 / (6 * Real.sqrt (reciprocalExponentialLowerCutoff n) * (3 : ℝ)^n) := by
    rw [pow_succ]
    congr 1
    ring
  rwa [heq] at h

end NLAlib
