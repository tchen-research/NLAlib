import NLAlib.ForMathlib.Analysis.ExpBounds
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual even Lp bounds from paired sub-gamma exponential moments

The finite Taylor terms of cosh convert genuine two-sign exponential
moment bounds into a square-root plus linear Lp estimate. Arbitrarily
small positive slack in the scale includes both zero parameters directly.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace NLAlib

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

private theorem lpNorm_two_mul_le_four_mul_scale
    {X : Ω → ℝ} {p : ℕ} (hp : 0<p) (hX : MemLp X ((2*p : ℕ) : ℝ≥0∞) μ)
    {V c D : ℝ} (hD : 0<D)
    (hsmall : c*((p : ℝ)/D) ≤ 1/2)
    (hquad : V*((p : ℝ)/D)^2 ≤ p)
    (hexp : ∀ s : ℝ, 0≤s → c*s<1 → ∀ e : ℝ, e=1 ∨ e= -1 →
      Integrable (fun ω => Real.exp (s*(e*X ω))) μ)
    (hmgf : ∀ s : ℝ, 0≤s → c*s<1 → ∀ e : ℝ, e=1 ∨ e= -1 →
      (∫ ω, Real.exp (s*(e*X ω)) ∂μ) ≤ Real.exp (V*s^2/(2*(1-c*s)))) :
    lpNorm X ((2*p : ℕ) : ℝ≥0∞) μ ≤ 4*D := by
  have hpr : (0 : ℝ)<p := by exact_mod_cast hp
  have hn : (2*p : ℕ)≠0 := by omega
  let s : ℝ := p/D
  have hs : 0<s := div_pos hpr hD
  have hdom : c*s<1 := by dsimp only [s]; linarith
  have hden : 1≤2*(1-c*s) := by dsimp only [s]; linarith
  have hpar : V*s^2/(2*(1-c*s)) ≤ p := by
    apply (div_le_iff₀ (by linarith : 0<2*(1-c*s))).mpr
    have hh : (p : ℝ)≤(p : ℝ)*(2*(1-c*s)) :=
      le_mul_of_one_le_right hpr.le hden
    exact hquad.trans hh
  have hpos : Integrable (fun ω => Real.exp (s*X ω)) μ := by
    simpa only [one_mul] using hexp s hs.le hdom 1 (Or.inl rfl)
  have hneg : Integrable (fun ω => Real.exp (-(s*X ω))) μ := by
    simpa only [neg_one_mul,mul_neg] using hexp s hs.le hdom (-1) (Or.inr rfl)
  have hposb : (∫ ω, Real.exp (s*X ω) ∂μ) ≤ Real.exp (p : ℝ) := by
    have hh := (hmgf s hs.le hdom 1 (Or.inl rfl)).trans (Real.exp_le_exp.mpr hpar)
    simpa only [one_mul] using hh
  have hnegb : (∫ ω, Real.exp (-(s*X ω)) ∂μ) ≤ Real.exp (p : ℝ) := by
    have hh := (hmgf s hs.le hdom (-1) (Or.inr rfl)).trans (Real.exp_le_exp.mpr hpar)
    simpa only [neg_one_mul,mul_neg] using hh
  have hcosh : Integrable (fun ω => Real.cosh (s*X ω)) μ := by
    convert (hpos.add hneg).div_const 2 using 1
    funext ω
    exact Real.cosh_eq (s*X ω)
  have hcoshb : (∫ ω, Real.cosh (s*X ω) ∂μ) ≤ Real.exp (p : ℝ) := by
    have he : (∫ ω, Real.cosh (s*X ω) ∂μ) =
        ((∫ ω, Real.exp (s*X ω) ∂μ)+(∫ ω, Real.exp (-(s*X ω)) ∂μ))/2 := by
      simp_rw [Real.cosh_eq]
      rw [integral_div,integral_add hpos hneg]
    rw [he]
    linarith
  have heven (x : ℝ) : ‖x‖^(2*p)=x^(2*p) := by
    simp only [Real.norm_eq_abs,pow_mul,sq_abs]
  have hiPow : Integrable (fun ω => X ω^(2*p)) μ := by
    simpa only [heven] using hX.integrable_norm_pow hn
  have hiTerm : Integrable
      (fun ω => (s*X ω)^(2*p)/(Nat.factorial (2*p) : ℝ)) μ := by
    simpa only [mul_pow] using (hiPow.const_mul (s^(2*p))).div_const (Nat.factorial (2*p) : ℝ)
  have hterm : (∫ ω, (s*X ω)^(2*p)/(Nat.factorial (2*p) : ℝ) ∂μ) ≤
      Real.exp (p : ℝ) :=
    (integral_mono_ae hiTerm hcosh (Eventually.of_forall fun ω =>
      cosh_taylor_term_le (s*X ω) p)).trans hcoshb
  have hscale : (∫ ω, (s*X ω)^(2*p)/(Nat.factorial (2*p) : ℝ) ∂μ) =
      (s^(2*p)/(Nat.factorial (2*p) : ℝ))*(∫ ω, X ω^(2*p) ∂μ) := by
    simp_rw [mul_pow,div_eq_mul_inv]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => by ring
  rw [hscale] at hterm
  have hcoef : 0<s^(2*p)/(Nat.factorial (2*p) : ℝ) := by positivity
  have hm : (∫ ω, X ω^(2*p) ∂μ) ≤
      (Nat.factorial (2*p) : ℝ)/s^(2*p)*Real.exp (p : ℝ) := by
    have hh : (∫ ω, X ω^(2*p) ∂μ) ≤
        Real.exp (p : ℝ)/(s^(2*p)/(Nat.factorial (2*p) : ℝ)) := by
      apply (le_div_iff₀ hcoef).mpr
      nlinarith [hterm]
    apply hh.trans_eq
    field_simp [hs.ne',Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2*p))]
  have hfac : (Nat.factorial (2*p) : ℝ) ≤ ((2*p : ℕ) : ℝ)^(2*p) := by
    exact_mod_cast Nat.factorial_le_pow (2*p)
  have he : Real.exp (p : ℝ) ≤ (2 : ℝ)^(2*p) := by
    calc
      _ = (Real.exp 1)^p := by rw [← Real.exp_nat_mul]; simp
      _ ≤ (4 : ℝ)^p := pow_le_pow_left₀ (Real.exp_pos _).le
        (by linarith [Real.exp_one_lt_three]) p
      _ = _ := by rw [pow_mul]; norm_num
  have hm' : (∫ ω, X ω^(2*p) ∂μ) ≤ (4*(p : ℝ)/s)^(2*p) := by
    calc
      _ ≤ (Nat.factorial (2*p) : ℝ)/s^(2*p)*Real.exp (p : ℝ) := hm
      _ ≤ (((2*p : ℕ) : ℝ)^(2*p)/s^(2*p))*(2 : ℝ)^(2*p) := by gcongr
      _ = ((((2*p : ℕ) : ℝ)/s)*2)^(2*p) := by simp only [mul_pow,div_pow]
      _ = _ := by congr 1; push_cast; ring
  have hlp : lpNorm X ((2*p : ℕ) : ℝ≥0∞) μ ≤ 4*(p : ℝ)/s := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) (by finiteness)
      hX.aestronglyMeasurable]
    simp only [ENNReal.toReal_natCast,Real.rpow_natCast]
    simp_rw [heven]
    calc
      _ ≤ ((4*(p : ℝ)/s)^(2*p))^(((2*p : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow (integral_nonneg fun ω =>
          Even.pow_nonneg (even_two.mul_right p) (X ω)) hm' (by positivity)
      _ = _ := Real.pow_rpow_inv_natCast (by positivity) hn
  have heq : 4*(p : ℝ)/s=4*D := by
    dsimp only [s]
    field_simp [hpr.ne',hD.ne']
  rwa [heq] at hlp

/-- Actual paired sub-gamma exponential moments imply an explicit even
Lp bound. The variables, measure, exponential integrals, and moment norm
are native objects; both zero variance and zero scale are included.
The constants are obtained from the cosh Taylor term and a factorial
bound, as in the scalar moment step for resolvent concentration. -/
theorem lpNorm_two_mul_le_sqrt_add_of_subgamma_mgf
    {X : Ω → ℝ} {p : ℕ} (hp : 0<p) (hX : MemLp X ((2*p : ℕ) : ℝ≥0∞) μ)
    {V c : ℝ} (hV : 0≤V) (hc : 0≤c)
    (hexp : ∀ s : ℝ, 0≤s → c*s<1 → ∀ e : ℝ, e=1 ∨ e= -1 →
      Integrable (fun ω => Real.exp (s*(e*X ω))) μ)
    (hmgf : ∀ s : ℝ, 0≤s → c*s<1 → ∀ e : ℝ, e=1 ∨ e= -1 →
      (∫ ω, Real.exp (s*(e*X ω)) ∂μ) ≤ Real.exp (V*s^2/(2*(1-c*s)))) :
    lpNorm X ((2*p : ℕ) : ℝ≥0∞) μ ≤ 4*Real.sqrt (V*p)+8*c*p := by
  have hpr : (0 : ℝ)<p := by exact_mod_cast hp
  apply le_of_forall_pos_le_add
  intro ε hε
  let q := Real.sqrt (V*p)
  let D := q+2*c*p+ε/4
  have hq : 0≤q := Real.sqrt_nonneg _
  have hqsq : q^2=V*p := Real.sq_sqrt (mul_nonneg hV hpr.le)
  have hD : 0<D := by dsimp only [D]; positivity
  have hsmall : c*((p : ℝ)/D) ≤ 1/2 := by
    rw [← mul_div_assoc,div_le_iff₀ hD]
    dsimp only [D]
    nlinarith
  have hquad : V*((p : ℝ)/D)^2 ≤ p := by
    rw [div_pow,← mul_div_assoc,div_le_iff₀ (sq_pos_of_pos hD)]
    have hDq : q≤D := by dsimp only [D]; nlinarith [mul_nonneg hc hpr.le]
    have hqsqD : q^2≤D^2 := pow_le_pow_left₀ hq hDq 2
    nlinarith
  have hh := lpNorm_two_mul_le_four_mul_scale hp hX hD hsmall hquad hexp hmgf
  calc
    _ ≤ 4*D := hh
    _ = 4*Real.sqrt (V*p)+8*c*p+ε := by dsimp only [D,q]; ring

end NLAlib
