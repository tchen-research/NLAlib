import NLAlib.Gaussian.Concentration.LogSobolevOneDim
import NLAlib.Concentration.Scalar.EntropyTensorization
import NLAlib.ForMathlib.Analysis.Real
import Mathlib.Analysis.Calculus.Deriv.Pi

/-!
# Gross's Gaussian logarithmic Sobolev inequality

For the standard Gaussian measure `γₙ = ⊗ᵢ N(0,1)` on `ι → ℝ` and `g ∈ C¹` with
`g², g² log g², |∇g|² ∈ L¹(γₙ)`,

  `∫ g² log g² dγₙ - (∫ g² dγₙ) log ∫ g² dγₙ ≤ 2 ∫ |∇g|² dγₙ`

(`entropy_sq_le_two_mul_integral_sum_sq_fderiv_gaussian`), with `|∇g|² = ∑ᵢ (∂ᵢ g)²` written as
`∑ i, fderiv ℝ g x (Pi.single i 1) ^ 2`. Proof: apply tensorization of entropy to `g² + δ`,
bound each one-coordinate entropy by the one-dimensional inequality applied to `√(g² + δ)`
along that coordinate, and let `δ → 0`.

Source: Gross 1975; Ledoux, *The Concentration of Measure Phenomenon*, Thm 5.1;
Boucheron–Lugosi–Massart 2013, Thm 5.4. Atlas: `gaussian-log-sobolev`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace NLAlib

/-- One-dimensional step: the `i`-th local entropy of `g ^ 2 + δ` is bounded by the
`i`-th partial energy, whenever the relevant sections are integrable. -/
private lemma local_step {ι : Type*} [Fintype ι] [DecidableEq ι] (g : (ι → ℝ) → ℝ)
    (hg : ContDiff ℝ 1 g) (δ : ℝ) (hδ : 0 < δ) (x : ι → ℝ) (i : ι)
    (h1 : Integrable (fun t => g (Function.update x i t) ^ 2) (gaussianReal 0 1))
    (h2 : Integrable (fun t => (g (Function.update x i t) ^ 2 + δ)
      * Real.log (g (Function.update x i t) ^ 2 + δ)) (gaussianReal 0 1))
    (h3 : Integrable (fun t => fderiv ℝ g (Function.update x i t) (Pi.single i 1) ^ 2)
      (gaussianReal 0 1)) :
    ∫ t, (g (Function.update x i t) ^ 2 + δ) * Real.log (g (Function.update x i t) ^ 2 + δ)
        ∂(gaussianReal 0 1)
      - (∫ t, (g (Function.update x i t) ^ 2 + δ) ∂(gaussianReal 0 1))
        * Real.log (∫ t, (g (Function.update x i t) ^ 2 + δ) ∂(gaussianReal 0 1))
      ≤ 2 * ∫ t, fderiv ℝ g (Function.update x i t) (Pi.single i 1) ^ 2 ∂(gaussianReal 0 1) := by
  set u : ℝ → ℝ := fun t => g (Function.update x i t) with hu_def
  set D : ℝ → ℝ := fun t => fderiv ℝ g (Function.update x i t) (Pi.single i 1) with hD_def
  set φ : ℝ → ℝ := fun t => Real.sqrt (u t ^ 2 + δ) with hφ_def
  have hpos : ∀ t, 0 < u t ^ 2 + δ := fun t => by positivity
  have hu : ∀ t, HasDerivAt u (D t) t := fun t =>
    ((hg.differentiable one_ne_zero) (Function.update x i t)).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_update x i t)
  have hφd : ∀ t, HasDerivAt φ ((2 * u t * D t) / (2 * Real.sqrt (u t ^ 2 + δ))) t := by
    intro t
    have h2 : HasDerivAt (fun y => u y ^ 2 + δ) (2 * u t * D t) t := by
      simpa using ((hu t).pow 2).add_const δ
    exact h2.sqrt (hpos t).ne'
  have hsq : ∀ t, φ t ^ 2 = u t ^ 2 + δ := fun t => Real.sq_sqrt (hpos t).le
  have hderiv_sq : ∀ t, deriv φ t ^ 2 ≤ D t ^ 2 := by
    intro t
    rw [(hφd t).deriv, div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (hpos t).le]
    rw [div_le_iff₀ (by have := hpos t; positivity)]
    have := sq_nonneg (D t)
    nlinarith [sq_nonneg (u t * D t), mul_nonneg hδ.le this]
  have hφC : ContDiff ℝ 1 φ :=
    (((hg.comp (contDiff_update 1 x i)).pow 2).add contDiff_const).sqrt (fun t => (hpos t).ne')
  have hφ2 : Integrable (fun t => φ t ^ 2) (gaussianReal 0 1) := by
    simp only [hsq]; exact h1.add (integrable_const δ)
  have hφlog : Integrable (fun t => φ t ^ 2 * Real.log (φ t ^ 2)) (gaussianReal 0 1) := by
    simp only [hsq]; exact h2
  have hφd2 : Integrable (fun t => deriv φ t ^ 2) (gaussianReal 0 1) := by
    refine h3.mono' ((hφC.continuous_deriv le_rfl).pow 2).aestronglyMeasurable
      (ae_of_all _ fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hderiv_sq t
  have key := entropy_sq_le_two_mul_integral_sq_deriv_gaussianReal φ hφC hφ2 hφlog hφd2
  simp only [hsq] at key
  refine key.trans ?_
  gcongr
  intro t
  exact hderiv_sq t

private lemma integrable_shift_mul_log {ι : Type*} [Fintype ι] (g : (ι → ℝ) → ℝ)
    (hg : Continuous g)
    (hg2 : Integrable (fun x => g x ^ 2) (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hglog : Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2))
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Integrable (fun x => (g x ^ 2 + δ) * Real.log (g x ^ 2 + δ))
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  refine Integrable.mono' ((hglog.abs.add hg2).add (integrable_const (2 : ℝ)))
    ((Real.continuous_mul_log.comp ((hg.pow 2).add continuous_const)).aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  exact abs_add_mul_log_add_le (g x ^ 2) δ (sq_nonneg _) hδ hδ1

/-- The regularized inequality: `Ent(g² + δ) ≤ 2 ∫ |∇g|²` for `0 < δ ≤ 1`. -/
private lemma ent_delta_le {ι : Type*} [Fintype ι] [DecidableEq ι] (g : (ι → ℝ) → ℝ)
    (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2) (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hglog : Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2))
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hdg : Integrable (fun x => ∑ i, fderiv ℝ g x (Pi.single i 1) ^ 2)
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∫ x, (g x ^ 2 + δ) * Real.log (g x ^ 2 + δ) ∂(Measure.pi fun _ : ι => gaussianReal 0 1)
      - (∫ x, g x ^ 2 ∂(Measure.pi fun _ : ι => gaussianReal 0 1) + δ)
        * Real.log (∫ x, g x ^ 2 ∂(Measure.pi fun _ : ι => gaussianReal 0 1) + δ)
      ≤ 2 * ∫ x, ∑ i, fderiv ℝ g x (Pi.single i 1) ^ 2
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  set P := Measure.pi fun _ : ι => gaussianReal 0 1 with hP
  have hgc : Continuous g := hg.continuous
  have hmeas : Measurable (fun x => g x ^ 2 + δ) :=
    ((hgc.pow 2).add continuous_const).measurable
  have hpos : ∀ x, 0 < g x ^ 2 + δ := fun x => by positivity
  have hint : Integrable (fun x => g x ^ 2 + δ) P := hg2.add (integrable_const δ)
  have hlogI := integrable_shift_mul_log g hgc hg2 hglog δ hδ hδ1
  have htens := entropy_pi_le_sum_integral_entropy_update (fun _ : ι => gaussianReal 0 1)
    (fun x => g x ^ 2 + δ)
    hmeas hpos hint hlogI
  have hintc : ∫ x, (g x ^ 2 + δ) ∂P = ∫ x, g x ^ 2 ∂P + δ := by
    rw [integral_add hg2 (integrable_const δ)]
    simp
  rw [← hP, hintc] at htens
  refine htens.trans ?_
  -- partial derivatives
  have hDc : ∀ i, Continuous (fun x => fderiv ℝ g x (Pi.single i 1)) := fun i =>
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDi : ∀ i, Integrable (fun x => fderiv ℝ g x (Pi.single i 1) ^ 2) P := by
    intro i
    refine hdg.mono' ((hDc i).pow 2).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact Finset.single_le_sum (f := fun j => fderiv ℝ g x (Pi.single j 1) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hterm : ∀ i, ∫ x, (∫ t, (g (Function.update x i t) ^ 2 + δ)
        * Real.log (g (Function.update x i t) ^ 2 + δ) ∂(gaussianReal 0 1)
      - (∫ t, (g (Function.update x i t) ^ 2 + δ) ∂(gaussianReal 0 1))
        * Real.log (∫ t, (g (Function.update x i t) ^ 2 + δ) ∂(gaussianReal 0 1))) ∂P
      ≤ 2 * ∫ x, fderiv ℝ g x (Pi.single i 1) ^ 2 ∂P := by
    intro i
    have hae : ∀ᵐ x ∂P, (∫ t, (g (Function.update x i t) ^ 2 + δ)
          * Real.log (g (Function.update x i t) ^ 2 + δ) ∂(gaussianReal 0 1)
        - (∫ t, (g (Function.update x i t) ^ 2 + δ) ∂(gaussianReal 0 1))
          * Real.log (∫ t, (g (Function.update x i t) ^ 2 + δ) ∂(gaussianReal 0 1)))
        ≤ 2 * ∫ t, fderiv ℝ g (Function.update x i t) (Pi.single i 1) ^ 2
          ∂(gaussianReal 0 1) := by
      filter_upwards [ae_integrable_comp_update_pi (fun _ : ι => gaussianReal 0 1) i hg2,
        ae_integrable_comp_update_pi (fun _ : ι => gaussianReal 0 1) i hlogI,
        ae_integrable_comp_update_pi (fun _ : ι => gaussianReal 0 1) i (hDi i)] with x h1 h2 h3
      exact local_step g hg δ hδ x i h1 h2 h3
    have hR : Integrable (fun x => 2 * ∫ t, fderiv ℝ g (Function.update x i t) (Pi.single i 1) ^ 2
        ∂(gaussianReal 0 1)) P :=
      (integrable_integral_update_pi (fun _ : ι => gaussianReal 0 1) i (hDi i)).const_mul 2
    calc _ ≤ ∫ x, 2 * ∫ t, fderiv ℝ g (Function.update x i t) (Pi.single i 1) ^ 2
          ∂(gaussianReal 0 1) ∂P := by
          by_cases hE : Integrable (fun x => ∫ t, (g (Function.update x i t) ^ 2 + δ)
              * Real.log (g (Function.update x i t) ^ 2 + δ) ∂(gaussianReal 0 1)
            - (∫ t, (g (Function.update x i t) ^ 2 + δ) ∂(gaussianReal 0 1))
              * Real.log (∫ t, (g (Function.update x i t) ^ 2 + δ) ∂(gaussianReal 0 1))) P
          · exact integral_mono_ae hE hR hae
          · rw [integral_undef hE]
            exact integral_nonneg fun x =>
              mul_nonneg zero_le_two (integral_nonneg fun t => sq_nonneg _)
      _ = 2 * ∫ x, fderiv ℝ g x (Pi.single i 1) ^ 2 ∂P := by
          rw [integral_const_mul,
            integral_integral_update_pi (fun _ : ι => gaussianReal 0 1) i (hDi i)]
  refine (Finset.sum_le_sum fun i _ => hterm i).trans_eq ?_
  rw [← Finset.mul_sum, integral_finsetSum _ fun i _ => hDi i]

/-- **Gross's Gaussian logarithmic Sobolev inequality**: for the standard Gaussian measure
`γₙ` on `ι → ℝ` and `g ∈ C¹` with `g², g² log g², |∇g|² ∈ L¹(γₙ)`,
`∫ g² log g² dγₙ - (∫ g² dγₙ) log ∫ g² dγₙ ≤ 2 ∫ |∇g|² dγₙ`, where
`|∇g(x)|² = ∑ i, fderiv ℝ g x (Pi.single i 1) ^ 2`.
Source: Gross 1975, Thm 5; Ledoux, *The Concentration of Measure Phenomenon*, Thm 5.1;
Boucheron–Lugosi–Massart 2013, Thm 5.4. Atlas: `gaussian-log-sobolev`. Ported from Prove2me
solution `GaussianMatrix.gaussian_logsobolev`. -/
theorem entropy_sq_le_two_mul_integral_sum_sq_fderiv_gaussian {ι : Type*} [Fintype ι]
    [DecidableEq ι] (g : (ι → ℝ) → ℝ) (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2) (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hglog : Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2))
      (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hdg : Integrable (fun x => ∑ i, fderiv ℝ g x (Pi.single i 1) ^ 2)
      (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    ∫ x, g x ^ 2 * Real.log (g x ^ 2) ∂(Measure.pi fun _ : ι => gaussianReal 0 1)
      - (∫ x, g x ^ 2 ∂(Measure.pi fun _ : ι => gaussianReal 0 1))
        * Real.log (∫ x, g x ^ 2 ∂(Measure.pi fun _ : ι => gaussianReal 0 1))
      ≤ 2 * ∫ x, ∑ i, fderiv ℝ g x (Pi.single i 1) ^ 2
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  set P := Measure.pi fun _ : ι => gaussianReal 0 1 with hP
  set c := ∫ x, g x ^ 2 ∂P with hc
  set δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hδ_def
  have hδpos : ∀ n, 0 < δ n := fun n => by positivity
  have hδle : ∀ n, δ n ≤ 1 := fun n => by
    simp only [hδ_def]
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have hδlim : Filter.Tendsto δ Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hgc : Continuous g := hg.continuous
  -- first term: dominated convergence
  have hT1 : Filter.Tendsto (fun n => ∫ x, (g x ^ 2 + δ n) * Real.log (g x ^ 2 + δ n) ∂P)
      Filter.atTop (nhds (∫ x, g x ^ 2 * Real.log (g x ^ 2) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => |g x ^ 2 * Real.log (g x ^ 2)| + g x ^ 2 + 2)
      (fun n => (Real.continuous_mul_log.comp
        ((hgc.pow 2).add continuous_const)).aestronglyMeasurable)
      ((hglog.abs.add hg2).add (integrable_const (2 : ℝ)))
      (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · rw [Real.norm_eq_abs]
      exact abs_add_mul_log_add_le (g x ^ 2) (δ n) (sq_nonneg _) (hδpos n) (hδle n)
    · have h1 : Filter.Tendsto (fun n => g x ^ 2 + δ n) Filter.atTop (nhds (g x ^ 2)) := by
        simpa using (tendsto_const_nhds (x := g x ^ 2)).add hδlim
      exact (Real.continuous_mul_log.tendsto (g x ^ 2)).comp h1
  have hT2 : Filter.Tendsto (fun n => (c + δ n) * Real.log (c + δ n))
      Filter.atTop (nhds (c * Real.log c)) := by
    have h1 : Filter.Tendsto (fun n => c + δ n) Filter.atTop (nhds c) := by
      simpa using (tendsto_const_nhds (x := c)).add hδlim
    exact (Real.continuous_mul_log.tendsto c).comp h1
  exact le_of_tendsto' (hT1.sub hT2) fun n =>
    ent_delta_le g hg hg2 hglog hdg (δ n) (hδpos n) (hδle n)

end NLAlib
