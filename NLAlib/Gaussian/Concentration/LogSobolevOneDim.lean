import NLAlib.Gaussian.Concentration.OrnsteinUhlenbeckEntropy
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Gross's Gaussian logarithmic Sobolev inequality in dimension one

For the standard Gaussian `γ = N(0,1)` and `Ent_γ(F) = ∫ F log F dγ - (∫ F dγ) log ∫ F dγ`:

* `entropy_le_half_integral_sq_deriv_div_gaussianReal`: `Ent_γ(f) ≤ ½ ∫ f'²/f dγ` for
  `f ∈ C¹` with `δ ≤ f ≤ C`, `|f'| ≤ C` (`δ > 0`). Proof: along the Ornstein–Uhlenbeck
  semigroup, `Ent_γ(P_t f) - ½ e^{-2t} ∫ f'²/f` is nondecreasing (entropy dissipation,
  commutation, Cauchy–Schwarz and invariance) and tends to `0` as `t → ∞`;
* `entropy_sq_le_two_mul_integral_sq_deriv_gaussianReal_of_hasCompactSupport`:
  `Ent_γ(g²) ≤ 2 ∫ g'² dγ` for compactly supported `g ∈ C¹` (apply the first to `g² + ε`);
* `entropy_sq_le_two_mul_integral_sq_deriv_gaussianReal`: the same for every `g ∈ C¹` with
  `g², g² log g², g'² ∈ L¹(γ)` (smooth truncation and dominated convergence).

Source: Gross 1975; Ledoux, *The Concentration of Measure Phenomenon*, Thm 5.1 (`n = 1`);
Bakry–Gentil–Ledoux 2014, Prop 5.5.1. Atlas: `gaussian-log-sobolev`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open Filter Topology Set

namespace NLAlib

/-! ### Elementary inequalities -/

/-- `|s log s| ≤ s² + 1` for `s ≥ 0`. Atlas: `gaussian-log-sobolev` (helper). Ported from
Prove2me solution `GaussianMatrix.gaussian_logsobolev_bounded_below`. -/
theorem abs_mul_log_le_sq_add_one (s : ℝ) (hs : 0 ≤ s) : |s * Real.log s| ≤ s ^ 2 + 1 := by
  rcases hs.eq_or_lt with h | hs'
  · subst h; simp
  rcases le_or_gt s 1 with h1 | h1
  · have := Real.abs_log_mul_self_lt s hs' h1
    rw [mul_comm]; nlinarith [sq_nonneg s]
  · have hl : 0 ≤ Real.log s := Real.log_nonneg h1.le
    have hl2 : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs'
    rw [abs_of_nonneg (mul_nonneg hs hl)]
    nlinarith

/-- Cauchy–Schwarz in the form `(∫ a)² ≤ (∫ a²/b) (∫ b)` for `b ≥ δ > 0` on a probability
space. Atlas: `gaussian-log-sobolev` (helper). Ported from Prove2me solution
`GaussianMatrix.gaussian_logsobolev_bounded_below`. -/
theorem sq_integral_le_integral_div_mul_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (a b : α → ℝ) (δ : ℝ) (hδ : 0 < δ) (hb : ∀ x, δ ≤ b x)
    (ha : Integrable a μ) (hbi : Integrable b μ) (hab : Integrable (fun x => a x ^ 2 / b x) μ) :
    (∫ x, a x ∂μ) ^ 2 ≤ (∫ x, a x ^ 2 / b x ∂μ) * (∫ x, b x ∂μ) := by
  set A := ∫ x, a x ∂μ
  set B := ∫ x, b x ∂μ
  set Q := ∫ x, a x ^ 2 / b x ∂μ
  have hB : δ ≤ B := by
    have := integral_mono (integrable_const δ) hbi hb
    simpa using this
  have hBpos : 0 < B := lt_of_lt_of_le hδ hB
  set l := A / B
  have hpt : ∀ x, (a x - l * b x) ^ 2 / b x = a x ^ 2 / b x - 2 * l * a x + l ^ 2 * b x := by
    intro x
    have : b x ≠ 0 := (lt_of_lt_of_le hδ (hb x)).ne'
    field_simp
    ring
  have hnonneg : 0 ≤ ∫ x, (a x - l * b x) ^ 2 / b x ∂μ := by
    refine integral_nonneg (fun x => div_nonneg (sq_nonneg _) (hδ.le.trans (hb x)))
  have hcalc : ∫ x, (a x - l * b x) ^ 2 / b x ∂μ = Q - 2 * l * A + l ^ 2 * B := by
    simp_rw [hpt]
    have h1 : Integrable (fun x => a x ^ 2 / b x - 2 * l * a x) μ := hab.sub (ha.const_mul _)
    have h2 : Integrable (fun x => l ^ 2 * b x) μ := hbi.const_mul _
    have h3 : Integrable (fun x => 2 * l * a x) μ := ha.const_mul _
    rw [integral_add h1 h2, integral_sub hab h3, integral_const_mul, integral_const_mul]
  rw [hcalc] at hnonneg
  have : Q - 2 * l * A + l ^ 2 * B = Q - A ^ 2 / B := by
    simp only [l]; field_simp; ring
  rw [this, sub_nonneg, div_le_iff₀ hBpos] at hnonneg
  exact hnonneg

/-! ### Functions bounded below -/

/-- **Gaussian log-Sobolev inequality for functions bounded below** (one dimension): for
`f ∈ C¹` with `δ ≤ f ≤ C` (`δ > 0`) and `|f'| ≤ C`,
`∫ f log f dγ - (∫ f dγ) log ∫ f dγ ≤ ½ ∫ f'²/f dγ`.
Source: Bakry–Gentil–Ledoux 2014, Prop 5.5.1 (semigroup proof); Ledoux, *Concentration of
Measure*, §5.1. Atlas: `gaussian-log-sobolev`. Ported from Prove2me solution
`GaussianMatrix.gaussian_logsobolev_bounded_below`. -/
theorem entropy_le_half_integral_sq_deriv_div_gaussianReal (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (δ C : ℝ) (hδ : 0 < δ) (hlow : ∀ x, δ ≤ f x) (hup : ∀ x, f x ≤ C)
    (hdf : ∀ x, |deriv f x| ≤ C) :
    ∫ x, f x * Real.log (f x) ∂(gaussianReal 0 1)
      - (∫ x, f x ∂(gaussianReal 0 1)) * Real.log (∫ x, f x ∂(gaussianReal 0 1))
      ≤ (1 / 2) * ∫ x, deriv f x ^ 2 / f x ∂(gaussianReal 0 1) := by
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hfc : Continuous f := hf.continuous
  have hdfc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hC : δ ≤ C := (hlow 0).trans (hup 0)
  have hC0 : 0 < C := lt_of_lt_of_le hδ hC
  have hfabs : ∀ x, |f x| ≤ C := fun x => by
    rw [abs_of_pos (lt_of_lt_of_le hδ (hlow x))]; exact hup x
  -- integrability of bounded continuous functions composed with affine maps
  have hint_aff : ∀ (h : ℝ → ℝ), Measurable h → (∀ z, |h z| ≤ C ^ 2 / δ + C) →
      ∀ a b : ℝ, Integrable (fun y => h (a + b * y)) (gaussianReal 0 1) := by
    intro h hm hb a b
    refine Integrable.mono' (integrable_const (C ^ 2 / δ + C))
      (hm.comp (by fun_prop)).aestronglyMeasurable (Eventually.of_forall (fun y => ?_))
    rw [Real.norm_eq_abs]; exact hb _
  have hδC : 0 ≤ C ^ 2 / δ := by positivity
  have hf_int : ∀ a b : ℝ, Integrable (fun y => f (a + b * y)) (gaussianReal 0 1) :=
    hint_aff f hfc.measurable (fun z => by linarith [hfabs z])
  -- basic bounds on the semigroup
  have hP_low : ∀ t x, δ ≤ ornsteinUhlenbeck t f x := by
    intro t x
    have := integral_mono (integrable_const δ)
      (hf_int (Real.exp (-t) * x) (Real.sqrt (1 - Real.exp (-(2 * t))))) (fun y => hlow _)
    simpa [ornsteinUhlenbeck] using this
  have hP_up : ∀ t x, ornsteinUhlenbeck t f x ≤ C := by
    intro t x
    have := integral_mono (hf_int (Real.exp (-t) * x) (Real.sqrt (1 - Real.exp (-(2 * t)))))
      (integrable_const C) (fun y => hup _)
    simpa [ornsteinUhlenbeck] using this
  have hP_pos : ∀ t x, 0 < ornsteinUhlenbeck t f x := fun t x => lt_of_lt_of_le hδ (hP_low t x)
  have hP0 : ∀ x, ornsteinUhlenbeck 0 f x = f x := by intro x; simp [ornsteinUhlenbeck]
  -- differentiability (hence continuity, measurability) in `x`
  have hP_hasDeriv : ∀ t x, HasDerivAt (ornsteinUhlenbeck t f)
      (Real.exp (-t) * ornsteinUhlenbeck t (deriv f) x) x :=
    fun t x => hasDerivAt_ornsteinUhlenbeck f hf C hdf t x
  have hP_cont : ∀ t, Continuous (ornsteinUhlenbeck t f) := fun t =>
    continuous_iff_continuousAt.2 (fun x => (hP_hasDeriv t x).continuousAt)
  -- continuity in `t`
  have hP_cont_t : ∀ x, Continuous (fun t => ornsteinUhlenbeck t f x) := by
    intro x
    refine continuous_of_dominated (bound := fun _ => C) (fun t => ?_)
      (fun t => Eventually.of_forall (fun y => ?_)) (integrable_const C)
      (Eventually.of_forall (fun y => ?_))
    · exact (hfc.comp (by fun_prop)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hfabs _
    · exact hfc.comp (by fun_prop)
  -- the entropy functional along the semigroup
  set H : ℝ → ℝ := fun t =>
    ∫ x, ornsteinUhlenbeck t f x * Real.log (ornsteinUhlenbeck t f x) ∂(gaussianReal 0 1)
    with hHdef
  have hΦbound : ∀ t x,
      |ornsteinUhlenbeck t f x * Real.log (ornsteinUhlenbeck t f x)| ≤ C ^ 2 + 1 := by
    intro t x
    refine (abs_mul_log_le_sq_add_one _ (hP_pos t x).le).trans ?_
    have := pow_le_pow_left₀ (hP_pos t x).le (hP_up t x) 2
    linarith
  have hH_cont : Continuous H := by
    refine continuous_of_dominated (bound := fun _ => C ^ 2 + 1) (fun t => ?_)
      (fun t => Eventually.of_forall (fun x => ?_)) (integrable_const _)
      (Eventually.of_forall (fun x => ?_))
    · exact ((hP_cont t).measurable.mul (hP_cont t).measurable.log).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hΦbound t x
    · exact Real.continuous_mul_log.comp (hP_cont_t x)
  -- Fisher information and its decay
  set J := ∫ x, deriv f x ^ 2 / f x ∂(gaussianReal 0 1) with hJdef
  set I : ℝ → ℝ := fun t =>
    ∫ x, deriv (ornsteinUhlenbeck t f) x ^ 2 / ornsteinUhlenbeck t f x ∂(gaussianReal 0 1)
    with hIdef
  have hH_deriv : ∀ t, 0 < t → HasDerivAt H (-I t) t := fun t ht =>
    hasDerivAt_integral_ornsteinUhlenbeck_mul_log f hf δ C hδ hlow hup hdf t ht
  set q : ℝ → ℝ := fun z => deriv f z ^ 2 / f z with hqdef
  have hq_meas : Measurable q := ((measurable_deriv f).pow_const 2).div hfc.measurable
  have hq_bound : ∀ z, |q z| ≤ C ^ 2 / δ + C := by
    intro z
    have hfz := lt_of_lt_of_le hδ (hlow z)
    rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hfz.le)]
    have h1 : deriv f z ^ 2 ≤ C ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hdf z) 2
    have h2 : deriv f z ^ 2 / f z ≤ C ^ 2 / δ := by
      rw [div_le_div_iff₀ hfz hδ]
      nlinarith [hlow z, sq_nonneg (deriv f z)]
    linarith
  have hq_int : Integrable q (gaussianReal 0 1) := by
    simpa using hint_aff q hq_meas hq_bound 0 1
  have hI_le : ∀ t, 0 ≤ t → I t ≤ Real.exp (-(2 * t)) * J := by
    intro t ht
    have hinv : ∫ x, ornsteinUhlenbeck t q x ∂(gaussianReal 0 1) = J :=
      integral_ornsteinUhlenbeck q hq_int t ht
    -- pointwise Cauchy–Schwarz
    have hpt : ∀ x, deriv (ornsteinUhlenbeck t f) x ^ 2 / ornsteinUhlenbeck t f x
        ≤ Real.exp (-(2 * t)) * ornsteinUhlenbeck t q x := by
      intro x
      rw [(hP_hasDeriv t x).deriv]
      have hCS := sq_integral_le_integral_div_mul_integral (gaussianReal 0 1)
        (fun y => deriv f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-(2 * t))) * y))
        (fun y => f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-(2 * t))) * y)) δ hδ
        (fun y => hlow _)
        (hint_aff (deriv f) (measurable_deriv f) (fun z => by
          linarith [hdf z, show C ≤ C ^ 2 / δ + C by linarith]) _ _)
        (hf_int _ _) (hint_aff q hq_meas hq_bound _ _)
      have hP := hP_pos t x
      rw [div_le_iff₀ hP, mul_pow, ← Real.exp_nat_mul]
      have e : ((2 : ℕ) : ℝ) * -t = -(2 * t) := by push_cast; ring
      rw [e, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      exact hCS
    have hmeas_q : Integrable (ornsteinUhlenbeck t q) (gaussianReal 0 1) := by
      refine Integrable.mono' (integrable_const (C ^ 2 / δ + C)) ?_
        (Eventually.of_forall (fun x => ?_))
      · refine (StronglyMeasurable.integral_prod_right'
          (f := fun p : ℝ × ℝ => q (Real.exp (-t) * p.1
            + Real.sqrt (1 - Real.exp (-(2 * t))) * p.2)) ?_).aestronglyMeasurable
        exact (hq_meas.comp (by fun_prop)).stronglyMeasurable
      · rw [Real.norm_eq_abs]
        refine (abs_integral_le_integral_abs).trans ?_
        have := integral_mono (hint_aff q hq_meas hq_bound (Real.exp (-t) * x)
          (Real.sqrt (1 - Real.exp (-(2 * t))))).abs
          (integrable_const (C ^ 2 / δ + C)) (fun y => hq_bound _)
        simpa using this
    calc I t ≤ ∫ x, Real.exp (-(2 * t)) * ornsteinUhlenbeck t q x ∂(gaussianReal 0 1) := by
          refine integral_mono_of_nonneg (Eventually.of_forall (fun x => ?_))
            (hmeas_q.const_mul _) (Eventually.of_forall hpt)
          exact div_nonneg (sq_nonneg _) (hP_pos t x).le
      _ = Real.exp (-(2 * t)) * J := by rw [integral_const_mul, hinv]
  -- monotonicity of `Ψ(t) = H(t) - e^{-2t} J / 2` on `[0, ∞)`
  set Ψ : ℝ → ℝ := fun t => H t - (1 / 2) * Real.exp (-(2 * t)) * J with hΨdef
  have hΨ_mono : MonotoneOn Ψ (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => -I t + Real.exp (-(2 * t)) * J)
      (convex_Ici 0) (by fun_prop) (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Ici] at ht
      have h1 := hH_deriv t ht
      have h2 : HasDerivAt (fun t : ℝ => (1 / 2) * Real.exp (-(2 * t)) * J)
          (-(Real.exp (-(2 * t)) * J)) t := by
        have := (((hasDerivAt_id t).const_mul 2).neg.exp.const_mul (1 / 2)).mul_const J
        refine this.congr_deriv ?_
        simp only [Pi.neg_apply, id]; ring
      exact (h1.sub h2).hasDerivWithinAt.congr_deriv (by ring)
    · rw [interior_Ici] at ht
      have := hI_le t (le_of_lt ht)
      linarith
  -- behaviour at infinity
  set m := ∫ x, f x ∂(gaussianReal 0 1) with hmdef
  have hP_lim : ∀ x, Tendsto (fun t => ornsteinUhlenbeck t f x) atTop (𝓝 m) := by
    intro x
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => C)
      (Eventually.of_forall (fun t => (hfc.comp (by fun_prop)).aestronglyMeasurable))
      (Eventually.of_forall (fun t => Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs]; exact hfabs _))) (integrable_const C)
      (Eventually.of_forall (fun y => ?_))
    have h1 : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero
    have h2 : Tendsto (fun t : ℝ => Real.exp (-(2 * t))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    have h3 : Tendsto (fun t : ℝ => Real.sqrt (1 - Real.exp (-(2 * t)))) atTop (𝓝 1) := by
      have := ((tendsto_const_nhds (x := (1 : ℝ))).sub h2).sqrt
      simpa using this
    have h4 : Tendsto (fun t : ℝ => Real.exp (-t) * x
        + Real.sqrt (1 - Real.exp (-(2 * t))) * y) atTop (𝓝 y) := by
      have := (h1.mul_const x).add (h3.mul_const y)
      simpa using this
    exact (hfc.tendsto y).comp h4
  have hH_lim : Tendsto H atTop (𝓝 (m * Real.log m)) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := gaussianReal 0 1)
      (F := fun t x => ornsteinUhlenbeck t f x * Real.log (ornsteinUhlenbeck t f x))
      (f := fun _ => m * Real.log m)
      (l := atTop) (fun _ => C ^ 2 + 1)
      (Eventually.of_forall (fun t =>
        ((hP_cont t).measurable.mul (hP_cont t).measurable.log).aestronglyMeasurable))
      (Eventually.of_forall (fun t => Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs]; exact hΦbound t x))) (integrable_const _)
      (Eventually.of_forall (fun x => (Real.continuous_mul_log.tendsto _).comp (hP_lim x)))
    simpa using this
  have hΨ_lim : Tendsto Ψ atTop (𝓝 (m * Real.log m)) := by
    have h2 : Tendsto (fun t : ℝ => Real.exp (-(2 * t))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    have := hH_lim.sub ((h2.const_mul (1 / 2)).mul_const J)
    simpa [Ψ, mul_assoc] using this
  have hΨ0 : Ψ 0 ≤ m * Real.log m := by
    refine ge_of_tendsto hΨ_lim ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact hΨ_mono (self_mem_Ici) ht ht
  have hH0 : H 0 = ∫ x, f x * Real.log (f x) ∂(gaussianReal 0 1) := by
    simp only [H, hP0]
  have : Ψ 0 = ∫ x, f x * Real.log (f x) ∂(gaussianReal 0 1) - (1 / 2) * J := by
    simp only [Ψ, hH0]; simp
  rw [this] at hΨ0
  linarith

/-! ### Compactly supported functions -/

/-- **Gaussian log-Sobolev inequality** for compactly supported `g ∈ C¹` (one dimension):
`∫ g² log g² dγ - (∫ g² dγ) log ∫ g² dγ ≤ 2 ∫ g'² dγ`.
Source: Gross 1975; Ledoux, *Concentration of Measure*, Thm 5.1 (`n = 1`). Atlas:
`gaussian-log-sobolev`. Ported from Prove2me solution
`GaussianMatrix.gaussian_logsobolev_one_dim_compact_support`. -/
theorem entropy_sq_le_two_mul_integral_sq_deriv_gaussianReal_of_hasCompactSupport (g : ℝ → ℝ)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    ∫ t, g t ^ 2 * Real.log (g t ^ 2) ∂(gaussianReal 0 1)
      - (∫ t, g t ^ 2 ∂(gaussianReal 0 1)) * Real.log (∫ t, g t ^ 2 ∂(gaussianReal 0 1))
      ≤ 2 * ∫ t, deriv g t ^ 2 ∂(gaussianReal 0 1) := by
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hgcont : Continuous g := hg.continuous
  have hdcont : Continuous (deriv g) := hg.continuous_deriv le_rfl
  obtain ⟨M1, hM1⟩ := hgcont.bounded_above_of_compact_support hgc
  obtain ⟨M2, hM2⟩ := hdcont.bounded_above_of_compact_support hgc.deriv
  set M := max M1 M2 with hMdef
  have hgM : ∀ x, |g x| ≤ M := fun x => by
    have := hM1 x; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  have hdM : ∀ x, |deriv g x| ≤ M := fun x => by
    have := hM2 x; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_right _ _)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hgM 0)
  have hg2M : ∀ x, g x ^ 2 ≤ M ^ 2 := fun x => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hgM x) 2
  have hd2M : ∀ x, deriv g x ^ 2 ≤ M ^ 2 := fun x => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hdM x) 2
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun n => by positivity
  have hε1 : ∀ n, ε n ≤ 1 := fun n => by
    simp only [ε]; rw [div_le_one (by positivity)]
    linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let f : ℕ → ℝ → ℝ := fun n x => g x ^ 2 + ε n
  have hf_deriv : ∀ n x, deriv (f n) x = 2 * g x * deriv g x := by
    intro n x
    have := (((hgd x).hasDerivAt.pow 2).add_const (ε n))
    exact this.deriv.trans (by simp)
  have hf_contDiff : ∀ n, ContDiff ℝ 1 (f n) := fun n => (hg.pow 2).add contDiff_const
  have hfcont : ∀ n, Continuous (f n) := fun n => (hf_contDiff n).continuous
  -- the bounded-below inequality for `f n`
  have hineq : ∀ n, ∫ x, f n x * Real.log (f n x) ∂(gaussianReal 0 1)
      - (∫ x, f n x ∂(gaussianReal 0 1)) * Real.log (∫ x, f n x ∂(gaussianReal 0 1))
      ≤ 2 * ∫ t, deriv g t ^ 2 ∂(gaussianReal 0 1) := by
    intro n
    have h := entropy_le_half_integral_sq_deriv_div_gaussianReal (f n) (hf_contDiff n) (ε n)
      (3 * M ^ 2 + 1)
      (hε n) (fun x => by simp only [f]; linarith [sq_nonneg (g x)])
      (fun x => by simp only [f]; linarith [hg2M x, hε1 n, sq_nonneg M])
      (fun x => by
        rw [hf_deriv, abs_mul, abs_mul, abs_two]
        have := mul_le_mul (hgM x) (hdM x) (abs_nonneg _) hM0
        nlinarith [sq_nonneg M])
    refine h.trans ?_
    have hle : ∫ x, deriv (f n) x ^ 2 / f n x ∂(gaussianReal 0 1)
        ≤ ∫ x, 4 * deriv g x ^ 2 ∂(gaussianReal 0 1) := by
      refine integral_mono_of_nonneg (Eventually.of_forall (fun x => ?_)) ?_
        (Eventually.of_forall (fun x => ?_))
      · exact div_nonneg (sq_nonneg _) (by simp only [f]; linarith [sq_nonneg (g x), hε n])
      · refine Integrable.mono' (integrable_const (4 * M ^ 2))
          ((hdcont.pow 2).const_mul 4).aestronglyMeasurable
          (Eventually.of_forall (fun x => ?_))
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        linarith [hd2M x]
      · simp only
        rw [hf_deriv, div_le_iff₀ (by simp only [f]; linarith [sq_nonneg (g x), hε n])]
        simp only [f]
        nlinarith [mul_nonneg (sq_nonneg (deriv g x)) (hε n).le]
    rw [integral_const_mul] at hle
    linarith
  -- limits as `n → ∞`
  have hpt : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x ^ 2)) := fun x => by
    simpa using (tendsto_const_nhds (x := g x ^ 2)).add hεlim
  have hfb : ∀ n x, 0 ≤ f n x ∧ f n x ≤ M ^ 2 + 1 := fun n x => by
    simp only [f]; constructor <;> linarith [sq_nonneg (g x), hg2M x, hε n, hε1 n]
  have L1 : Tendsto (fun n => ∫ x, f n x ∂(gaussianReal 0 1)) atTop
      (𝓝 (∫ t, g t ^ 2 ∂(gaussianReal 0 1))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => M ^ 2 + 1)
      (fun n => (hfcont n).aestronglyMeasurable) (integrable_const _) (fun n => ?_)
      (Eventually.of_forall hpt)
    refine Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hfb n x).1]; exact (hfb n x).2
  have L2 : Tendsto (fun n => ∫ x, f n x * Real.log (f n x) ∂(gaussianReal 0 1)) atTop
      (𝓝 (∫ t, g t ^ 2 * Real.log (g t ^ 2) ∂(gaussianReal 0 1))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (M ^ 2 + 1) ^ 2 + 1)
      (fun n => ((hfcont n).measurable.mul (hfcont n).measurable.log).aestronglyMeasurable)
      (integrable_const _) (fun n => ?_) ?_
    · refine Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs]
      refine (abs_mul_log_le_sq_add_one _ (hfb n x).1).trans ?_
      have := pow_le_pow_left₀ (hfb n x).1 (hfb n x).2 2
      linarith
    · exact Eventually.of_forall (fun x => (Real.continuous_mul_log.tendsto _).comp (hpt x))
  have L4 : Tendsto (fun n => (∫ x, f n x ∂(gaussianReal 0 1))
        * Real.log (∫ x, f n x ∂(gaussianReal 0 1))) atTop
      (𝓝 ((∫ t, g t ^ 2 ∂(gaussianReal 0 1)) * Real.log (∫ t, g t ^ 2 ∂(gaussianReal 0 1)))) :=
    (Real.continuous_mul_log.tendsto _).comp L1
  exact le_of_tendsto' (L2.sub L4) hineq

/-! ### The general one-dimensional inequality -/

/-- `|(G s) log (G s)| ≤ |G log G| + G` for `G ≥ 0` and `s ∈ [0,1]`. -/
private lemma abs_mul_mul_log_le (G s : ℝ) (hG : 0 ≤ G) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |G * s * Real.log (G * s)| ≤ |G * Real.log G| + G := by
  rcases hG.eq_or_lt with h | hG'
  · subst h; simp
  rcases hs0.eq_or_lt with h | hs'
  · subst h; simp; positivity
  rw [Real.log_mul hG'.ne' hs'.ne']
  have e : G * s * (Real.log G + Real.log s) = s * (G * Real.log G) + G * (Real.log s * s) := by
    ring
  rw [e]
  have h1 := Real.abs_log_mul_self_lt s hs' hs1
  calc |s * (G * Real.log G) + G * (Real.log s * s)|
      ≤ |s * (G * Real.log G)| + |G * (Real.log s * s)| := abs_add_le _ _
    _ = s * |G * Real.log G| + G * |Real.log s * s| := by
        rw [abs_mul s (G * Real.log G), abs_mul G (Real.log s * s), abs_of_nonneg hs0,
          abs_of_nonneg hG]
    _ ≤ 1 * |G * Real.log G| + G * 1 := by
        gcongr
    _ = |G * Real.log G| + G := by ring

/-- **Gross's Gaussian logarithmic Sobolev inequality** in dimension one: for `g ∈ C¹` with
`g², g² log g², g'² ∈ L¹(γ)`,
`∫ g² log g² dγ - (∫ g² dγ) log ∫ g² dγ ≤ 2 ∫ g'² dγ`.
Source: Gross 1975, Thm 5; Ledoux, *Concentration of Measure*, Thm 5.1 (`n = 1`). Atlas:
`gaussian-log-sobolev`. Ported from Prove2me solution
`GaussianMatrix.gaussian_logsobolev_one_dim`. -/
theorem entropy_sq_le_two_mul_integral_sq_deriv_gaussianReal (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun t => g t ^ 2) (gaussianReal 0 1))
    (hglog : Integrable (fun t => g t ^ 2 * Real.log (g t ^ 2)) (gaussianReal 0 1))
    (hdg : Integrable (fun t => deriv g t ^ 2) (gaussianReal 0 1)) :
    ∫ t, g t ^ 2 * Real.log (g t ^ 2) ∂(gaussianReal 0 1)
      - (∫ t, g t ^ 2 ∂(gaussianReal 0 1)) * Real.log (∫ t, g t ^ 2 ∂(gaussianReal 0 1))
      ≤ 2 * ∫ t, deriv g t ^ 2 ∂(gaussianReal 0 1) := by
  -- a fixed smooth cutoff `χ`, equal to `1` on `[-1,1]` and supported in `[-2,2]`
  let χ : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  have hχc : ContDiff ℝ 1 (fun x => χ x) := χ.contDiff
  have hχd : Continuous (deriv (fun x => χ x)) := hχc.continuous_deriv le_rfl
  have hχs : HasCompactSupport (deriv (fun x => χ x)) := χ.hasCompactSupport.deriv
  obtain ⟨K, hK⟩ := hχd.bounded_above_of_compact_support hχs
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0)
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hgc : Continuous g := hg.continuous
  -- the truncations `g_n = g · χ(·/(n+1))`
  let c : ℕ → ℝ → ℝ := fun n x => χ (x / ((n : ℝ) + 1))
  let gn : ℕ → ℝ → ℝ := fun n x => g x * c n x
  have hnpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hc_contDiff : ∀ n, ContDiff ℝ 1 (c n) := fun n =>
    hχc.comp (contDiff_id.div_const _)
  have hc01 : ∀ n x, 0 ≤ c n x ∧ c n x ≤ 1 := fun n x => ⟨χ.nonneg, χ.le_one⟩
  have hc_one : ∀ (n : ℕ) (x : ℝ), |x| < (n : ℝ) + 1 → c n x = 1 := by
    intro n x hx
    apply χ.one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_div,
      abs_of_pos (hnpos n), div_le_one (hnpos n)]
    exact hx.le
  have hgn_contDiff : ∀ n, ContDiff ℝ 1 (gn n) := fun n => hg.mul (hc_contDiff n)
  have hgn_supp : ∀ n, HasCompactSupport (gn n) := by
    intro n
    apply HasCompactSupport.mul_left
    apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (2 * ((n : ℝ) + 1)))
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hx
    apply χ.zero_of_le_dist
    rw [dist_zero_right, Real.norm_eq_abs, abs_div, abs_of_pos (hnpos n),
      le_div_iff₀ (hnpos n)]
    exact hx.le
  -- derivative of the truncation
  have hc_deriv : ∀ n x, deriv (c n) x = deriv (fun x => χ x) (x / ((n : ℝ) + 1))
      / ((n : ℝ) + 1) := by
    intro n x
    have h1 : HasDerivAt (fun x : ℝ => x / ((n : ℝ) + 1)) (1 / ((n : ℝ) + 1)) x :=
      (hasDerivAt_id x).div_const _
    have h2 := ((hχc.differentiable one_ne_zero) (x / ((n : ℝ) + 1))).hasDerivAt.comp x h1
    exact h2.deriv.trans (by ring)
  have hc_deriv_bound : ∀ n x, |deriv (c n) x| ≤ K := by
    intro n x
    rw [hc_deriv, abs_div, abs_of_pos (hnpos n)]
    have := hK (x / ((n : ℝ) + 1))
    rw [Real.norm_eq_abs] at this
    calc |deriv (fun x => χ x) (x / (↑n + 1))| / (↑n + 1) ≤ K / 1 := by
          gcongr
          · linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
      _ = K := div_one K
  have hgn_deriv : ∀ n x, deriv (gn n) x = deriv g x * c n x + g x * deriv (c n) x := by
    intro n x
    exact ((hgd x).hasDerivAt.mul
      (((hc_contDiff n).differentiable one_ne_zero) x).hasDerivAt).deriv
  have hgn_deriv_sq : ∀ n x, deriv (gn n) x ^ 2 ≤ 2 * deriv g x ^ 2 + 2 * K ^ 2 * g x ^ 2 := by
    intro n x
    rw [hgn_deriv]
    obtain ⟨h0, h1⟩ := hc01 n x
    have hb := hc_deriv_bound n x
    have hc2 : c n x ^ 2 ≤ 1 := by nlinarith
    have e1 : (deriv g x * c n x) ^ 2 ≤ deriv g x ^ 2 := by
      rw [mul_pow]; nlinarith [mul_le_mul_of_nonneg_left hc2 (sq_nonneg (deriv g x))]
    have hd2 : deriv (c n) x ^ 2 ≤ K ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    have e2 : (g x * deriv (c n) x) ^ 2 ≤ K ^ 2 * g x ^ 2 := by
      rw [mul_pow, mul_comm]
      exact mul_le_mul_of_nonneg_right hd2 (sq_nonneg _)
    nlinarith [sq_nonneg (deriv g x * c n x - g x * deriv (c n) x)]
  -- pointwise eventual equality
  have hev : ∀ x, ∀ᶠ n in atTop, gn n x = g x ∧ deriv (gn n) x = deriv g x := by
    intro x
    refine eventually_atTop.2 ⟨⌈|x|⌉₊, fun n hn => ?_⟩
    have hx : |x| < (n : ℝ) + 1 := by
      have := Nat.le_ceil |x|
      have : (⌈|x|⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    refine ⟨by show g x * c n x = g x; rw [hc_one n x hx, mul_one], ?_⟩
    have : gn n =ᶠ[𝓝 x] g := by
      have hopen : IsOpen {y : ℝ | |y| < (n : ℝ) + 1} :=
        isOpen_lt continuous_abs continuous_const
      filter_upwards [hopen.mem_nhds hx] with y hy
      show g y * c n y = g y; rw [hc_one n y hy, mul_one]
    exact this.deriv_eq
  -- apply the compactly supported inequality to `g_n`
  have hineq : ∀ n, ∫ t, gn n t ^ 2 * Real.log (gn n t ^ 2) ∂(gaussianReal 0 1)
      - (∫ t, gn n t ^ 2 ∂(gaussianReal 0 1)) * Real.log (∫ t, gn n t ^ 2 ∂(gaussianReal 0 1))
      ≤ 2 * ∫ t, deriv (gn n) t ^ 2 ∂(gaussianReal 0 1) := fun n =>
    entropy_sq_le_two_mul_integral_sq_deriv_gaussianReal_of_hasCompactSupport (gn n)
      (hgn_contDiff n) (hgn_supp n)
  have hgn_cont : ∀ n, Continuous (gn n) := fun n => (hgn_contDiff n).continuous
  -- limits
  have L1 : Tendsto (fun n => ∫ t, gn n t ^ 2 ∂(gaussianReal 0 1)) atTop
      (𝓝 (∫ t, g t ^ 2 ∂(gaussianReal 0 1))) := by
    refine tendsto_integral_of_dominated_convergence (fun t => g t ^ 2)
      (fun n => ((hgn_cont n).pow 2).aestronglyMeasurable) hg2 (fun n => ?_) ?_
    · refine Eventually.of_forall (fun x => ?_)
      obtain ⟨h0, h1⟩ := hc01 n x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simp only [gn, mul_pow]
      have hc2 : c n x ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hc2 (sq_nonneg (g x))]
    · refine Eventually.of_forall (fun x => ?_)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x] with n hn
      rw [hn.1]
  have L2 : Tendsto (fun n => ∫ t, gn n t ^ 2 * Real.log (gn n t ^ 2) ∂(gaussianReal 0 1)) atTop
      (𝓝 (∫ t, g t ^ 2 * Real.log (g t ^ 2) ∂(gaussianReal 0 1))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun t => |g t ^ 2 * Real.log (g t ^ 2)| + g t ^ 2)
      (fun n => (((hgn_cont n).pow 2).measurable.mul
        ((hgn_cont n).pow 2).measurable.log).aestronglyMeasurable) (hglog.abs.add hg2)
      (fun n => ?_) ?_
    · refine Eventually.of_forall (fun x => ?_)
      obtain ⟨h0, h1⟩ := hc01 n x
      rw [Real.norm_eq_abs]
      have e : gn n x ^ 2 = g x ^ 2 * c n x ^ 2 := by simp only [gn, mul_pow]
      rw [e]
      exact abs_mul_mul_log_le _ _ (sq_nonneg _) (sq_nonneg _) (by nlinarith)
    · refine Eventually.of_forall (fun x => ?_)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x] with n hn
      rw [hn.1]
  have L3 : Tendsto (fun n => ∫ t, deriv (gn n) t ^ 2 ∂(gaussianReal 0 1)) atTop
      (𝓝 (∫ t, deriv g t ^ 2 ∂(gaussianReal 0 1))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun t => 2 * deriv g t ^ 2 + 2 * K ^ 2 * g t ^ 2)
      (fun n => ((measurable_deriv _).pow_const 2).aestronglyMeasurable)
      ((hdg.const_mul 2).add (hg2.const_mul _)) (fun n => ?_) ?_
    · refine Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hgn_deriv_sq n x
    · refine Eventually.of_forall (fun x => ?_)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x] with n hn
      rw [hn.2]
  have L4 : Tendsto (fun n => (∫ t, gn n t ^ 2 ∂(gaussianReal 0 1))
        * Real.log (∫ t, gn n t ^ 2 ∂(gaussianReal 0 1))) atTop
      (𝓝 ((∫ t, g t ^ 2 ∂(gaussianReal 0 1)) * Real.log (∫ t, g t ^ 2 ∂(gaussianReal 0 1)))) :=
    (Real.continuous_mul_log.tendsto _).comp L1
  exact le_of_tendsto_of_tendsto' (L2.sub L4) (L3.const_mul 2) hineq

end NLAlib
