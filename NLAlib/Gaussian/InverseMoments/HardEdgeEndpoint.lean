import NLAlib.Gaussian.InverseMoments.Probe
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Scalar endpoint bounds for an antitone hard-edge density

The scalar Mellin endpoint argument in the operator derivation. The density
and its antitonicity are explicit hypotheses; this file does not assume that
a Gaussian smallest eigenvalue has such a density.
Atlas: `wishart-lambda-min-tail`, `pinv-spectral-tail`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology Matrix Matrix.Norms.L2Operator

namespace NLAlib

/-- An antitone Gamma-weighted density forces a lower bound on every
subcritical negative Mellin moment. Source: operator rederivations, Section 5;
atlas `wishart-lambda-min-tail` (scalar endpoint helper). -/
theorem ofReal_mellin_lower_le_lintegral_of_antitone_density
    (μ : Measure ℝ) (α : ℝ) (h : ℝ → ℝ) (hh : Measurable h)
    (hnn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ h x) (hanti : AntitoneOn h (Ioi 0))
    (hdens : μ.restrict (Ioi 0) = (volume.restrict (Ioi 0)).withDensity
      (fun x : ℝ => ENNReal.ofReal (x ^ (α - 1) * Real.exp (-x / 2) * h x)))
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ENNReal.ofReal (h δ * Real.exp (-δ / 2) * δ ^ ε / ε)
      ≤ ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (x ^ (-α + ε)) ∂μ := by
  have hint : IntegrableOn (fun x : ℝ => x ^ (ε - 1)) (Ioc 0 δ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hδ.le).1
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < ε - 1))
  have hlow : (∫⁻ x in Ioc (0 : ℝ) δ,
      ENNReal.ofReal (h δ * Real.exp (-δ / 2) * x ^ (ε - 1)))
      = ENNReal.ofReal (h δ * Real.exp (-δ / 2) * δ ^ ε / ε) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)]
    · rw [integral_const_mul, ← intervalIntegral.integral_of_le hδ.le,
        integral_rpow (Or.inl (by linarith : -1 < ε - 1))]
      simp only [sub_add_cancel, Real.zero_rpow hε.ne', sub_zero]
      congr 1
      ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact mul_nonneg (mul_nonneg (hnn δ hδ) (Real.exp_nonneg _))
        (Real.rpow_nonneg hx.1.le _)
  have hident : (∫⁻ x in Ioi (0 : ℝ),
      ENNReal.ofReal (x ^ (ε - 1) * Real.exp (-x / 2) * h x))
      = ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (x ^ (-α + ε)) ∂μ := by
    rw [hdens, lintegral_withDensity_eq_lintegral_mul]
    · apply setLIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only [Pi.mul_apply]
      rw [← ENNReal.ofReal_mul (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_nonneg _)) (hnn x hx))]
      congr 1
      rw [show x ^ (α - 1) * Real.exp (-x / 2) * h x * x ^ (-α + ε)
          = (x ^ (α - 1) * x ^ (-α + ε)) * Real.exp (-x / 2) * h x by ring,
        ← Real.rpow_add hx]
      rw [show α - 1 + (-α + ε) = ε - 1 by ring]
    · fun_prop
    · fun_prop
  rw [← hlow]
  calc (∫⁻ x in Ioc (0 : ℝ) δ,
      ENNReal.ofReal (h δ * Real.exp (-δ / 2) * x ^ (ε - 1)))
      ≤ ∫⁻ x in Ioc (0 : ℝ) δ,
        ENNReal.ofReal (x ^ (ε - 1) * Real.exp (-x / 2) * h x) := by
          apply setLIntegral_mono' measurableSet_Ioc
          intro x hx
          apply ENNReal.ofReal_le_ofReal
          have hhδ : h δ ≤ h x := hanti hx.1 hδ hx.2
          have heδ : Real.exp (-δ / 2) ≤ Real.exp (-x / 2) :=
            Real.exp_le_exp.2 (by linarith [hx.2])
          have hxpow : 0 ≤ x ^ (ε - 1) := Real.rpow_nonneg hx.1.le _
          nlinarith [mul_le_mul hhδ heδ (Real.exp_nonneg _) (hnn x hx.1)]
    _ ≤ ∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal (x ^ (ε - 1) * Real.exp (-x / 2) * h x) :=
      lintegral_mono' (Measure.restrict_mono (fun x hx => hx.1) le_rfl) le_rfl
    _ = _ := hident

/-- Subcritical Mellin bounds with a finite endpoint residue bound an antitone
Gamma-weighted density uniformly. Source: operator rederivations, Section 5;
atlas `wishart-lambda-min-tail`. The two limits are elementary and require no
Tauberian theorem. -/
theorem antitone_density_le_of_mellin_endpoint
    (μ : Measure ℝ) (α : ℝ) (hα : 0 < α) (h : ℝ → ℝ) (hh : Measurable h)
    (hnn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ h x) (hanti : AntitoneOn h (Ioi 0))
    (hdens : μ.restrict (Ioi 0) = (volume.restrict (Ioi 0)).withDensity
      (fun x : ℝ => ENNReal.ofReal (x ^ (α - 1) * Real.exp (-x / 2) * h x)))
    (M : ℝ → ℝ) (C : ℝ)
    (hMom : ∀ ε : ℝ, 0 < ε → ε < α →
      Integrable (fun x : ℝ => x ^ (-α + ε)) (μ.restrict (Ioi 0)) ∧
      (∫ x in Ioi (0 : ℝ), x ^ (-α + ε) ∂μ) ≤ M ε)
    (hlim : Tendsto (fun ε : ℝ => ε * M ε) (𝓝[>] 0) (𝓝 C)) :
    ∀ x ∈ Ioi (0 : ℝ), h x ≤ C := by
  intro x hx
  have hsmall (δ : ℝ) (hδ : 0 < δ) (hδx : δ ≤ x) :
      h x * Real.exp (-δ / 2) ≤ C := by
    have hineq : ∀ ε : ℝ, 0 < ε → ε < α →
        h x * Real.exp (-δ / 2) * δ ^ ε ≤ ε * M ε := by
      intro ε hε hεα
      obtain ⟨hint, hbound⟩ := hMom ε hε hεα
      have hlower := ofReal_mellin_lower_le_lintegral_of_antitone_density
        μ α h hh hnn hanti hdens ε δ hε hδ
      have hpos : 0 ≤ᵐ[μ.restrict (Ioi 0)] (fun x : ℝ => x ^ (-α + ε)) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        exact Real.rpow_nonneg hy.le _
      rw [← ofReal_integral_eq_lintegral_ofReal hint hpos] at hlower
      have hleft : h δ * Real.exp (-δ / 2) * δ ^ ε / ε ≤ M ε := by
        have hM : 0 ≤ M ε := (integral_nonneg_of_ae hpos).trans hbound
        exact (ENNReal.ofReal_le_ofReal_iff hM).1
          (hlower.trans (ENNReal.ofReal_le_ofReal hbound))
      have hhδ : h x ≤ h δ := hanti hδ hx hδx
      have hscaled := (div_le_iff₀ hε).1 hleft
      have hfac : 0 ≤ Real.exp (-δ / 2) * δ ^ ε := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hhδ hfac]
    have hp : Tendsto (fun ε : ℝ => δ ^ ε) (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
      simpa using (Real.continuousAt_const_rpow hδ.ne' :
        ContinuousAt (fun ε : ℝ => δ ^ ε) 0).tendsto.mono_left nhdsWithin_le_nhds
    have hleftlim : Tendsto (fun ε : ℝ => h x * Real.exp (-δ / 2) * δ ^ ε)
        (𝓝[>] 0) (𝓝 (h x * Real.exp (-δ / 2))) := by
      simpa using tendsto_const_nhds.mul hp
    apply le_of_tendsto_of_tendsto hleftlim hlim
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hα)] with ε hε hεα
    exact hineq ε hε hεα
  have hexp : Tendsto (fun δ : ℝ => Real.exp (-δ / 2)) (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
    simpa [Function.comp_def] using ((Real.continuous_exp.comp ((continuous_id : Continuous (fun δ : ℝ => δ)).neg.div_const 2)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds : Tendsto (fun δ : ℝ => Real.exp (-δ / 2)) (𝓝[>] 0) _)
  have hleftlim : Tendsto (fun δ : ℝ => h x * Real.exp (-δ / 2))
      (𝓝[>] 0) (𝓝 (h x)) := by simpa using tendsto_const_nhds.mul hexp
  apply le_of_tendsto hleftlim
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hx)] with δ hδ hδx
  exact hsmall δ hδ hδx.le

/-- A uniform bound on the antitone density gives the exact Gamma-weighted
small-ball bound. Source: operator rederivations, Section 5; atlas
`wishart-lambda-min-tail` (scalar integration helper). -/
theorem measure_Ioc_le_lintegral_of_antitone_density_bound
    (μ : Measure ℝ) (α : ℝ) (h : ℝ → ℝ)
    (hdens : μ.restrict (Ioi 0) = (volume.restrict (Ioi 0)).withDensity
      (fun x : ℝ => ENNReal.ofReal (x ^ (α - 1) * Real.exp (-x / 2) * h x)))
    (C : ℝ) (hbound : ∀ x ∈ Ioi (0 : ℝ), h x ≤ C) (t : ℝ) :
    μ (Ioc 0 t) ≤ ∫⁻ x in Ioc (0 : ℝ) t,
      ENNReal.ofReal (C * x ^ (α - 1) * Real.exp (-x / 2)) := by
  have hset : Ioc (0 : ℝ) t ∩ Ioi 0 = Ioc 0 t := by
    ext x
    simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
    tauto
  have hμ : μ (Ioc 0 t) = (μ.restrict (Ioi 0)) (Ioc 0 t) := by
    rw [Measure.restrict_apply measurableSet_Ioc, hset]
  rw [hμ, hdens, withDensity_apply _ measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, hset]
  apply setLIntegral_mono' measurableSet_Ioc
  intro x hx
  apply ENNReal.ofReal_le_ofReal
  have hp : 0 ≤ x ^ (α - 1) * Real.exp (-x / 2) :=
    mul_nonneg (Real.rpow_nonneg hx.1.le _) (Real.exp_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left (hbound x hx.1) hp]

/-- Real Gamma is continuous at every positive argument.
Source: Mathlib Gamma differentiability; atlas `wishart-lambda-min-tail`
(scalar endpoint helper). -/
theorem continuousAt_Gamma_of_pos {x : ℝ} (hx : 0 < x) : ContinuousAt Real.Gamma x :=
  (Real.differentiableAt_Gamma (fun n => by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)).continuousAt

/-- The residue of the real Gamma pole from the positive side is one.
Source: Gamma recurrence and continuity at one; atlas
`wishart-lambda-min-tail` (scalar endpoint helper). -/
theorem tendsto_self_mul_Gamma_nhdsWithin_zero_pos :
    Tendsto (fun ε : ℝ => ε * Real.Gamma ε) (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
  have hcont : ContinuousAt (fun ε : ℝ => Real.Gamma (ε + 1)) 0 :=
    (continuousAt_Gamma_of_pos (by norm_num : (0 : ℝ) < 1)).comp_of_eq
      (continuousAt_id.add continuousAt_const) (by simp)
  apply Tendsto.congr' ?_ (by simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact Real.Gamma_add_one (ne_of_gt hε)

/-- The exact pole residue of the operator master moment formula.
Source: operator rederivations, Section 5; atlas `wishart-lambda-min-tail`.
Only Gamma recurrence and continuity of positive scalar factors are used. -/
theorem tendsto_gamma_probe_mellin_endpoint (x α : ℝ) (hx : 0 < x) (hα : 0 < α) :
    Tendsto (fun ε : ℝ => ε *
      (Real.Gamma (x + α - ε) * Real.Gamma ε * Real.sqrt Real.pi /
        (2 ^ (α - ε) * Real.Gamma x * Real.Gamma α * Real.Gamma (α + 1 / 2 - ε))))
      (𝓝[>] 0)
      (𝓝 (Real.Gamma (x + α) * Real.sqrt Real.pi /
        (2 ^ α * Real.Gamma x * Real.Gamma α * Real.Gamma (α + 1 / 2)))) := by
  have hG1 : Tendsto (fun ε : ℝ => Real.Gamma (x + α - ε)) (𝓝[>] 0)
      (𝓝 (Real.Gamma (x + α))) := by
    have hh := (continuousAt_Gamma_of_pos (add_pos hx hα)).comp_of_eq
      (continuousAt_const.sub continuousAt_id : ContinuousAt (fun ε : ℝ => x + α - ε) 0)
      (by simp)
    simpa only [Function.comp_def, Pi.sub_apply, sub_zero] using hh.tendsto.mono_left nhdsWithin_le_nhds
  have hG2 : Tendsto (fun ε : ℝ => Real.Gamma (α + 1 / 2 - ε)) (𝓝[>] 0)
      (𝓝 (Real.Gamma (α + 1 / 2))) := by
    have hh := (continuousAt_Gamma_of_pos (by linarith : 0 < α + 1 / 2)).comp_of_eq
      (continuousAt_const.sub continuousAt_id : ContinuousAt (fun ε : ℝ => α + 1 / 2 - ε) 0)
      (by simp)
    simpa only [Function.comp_def, Pi.sub_apply, sub_zero] using hh.tendsto.mono_left nhdsWithin_le_nhds
  have hpow : Tendsto (fun ε : ℝ => (2 : ℝ) ^ (α - ε)) (𝓝[>] 0) (𝓝 (2 ^ α)) := by
    have hh := (Real.continuousAt_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).comp'
      (continuousAt_const.sub continuousAt_id : ContinuousAt (fun ε : ℝ => α - ε) 0)
    simpa using hh.tendsto.mono_left nhdsWithin_le_nhds
  have hden : 2 ^ α * Real.Gamma x * Real.Gamma α * Real.Gamma (α + 1 / 2) ≠ 0 := by
    have hgx := Real.Gamma_pos_of_pos hx
    have hga := Real.Gamma_pos_of_pos hα
    have hgh := Real.Gamma_pos_of_pos (by linarith : 0 < α + 1 / 2)
    positivity
  have ht := ((hG1.mul tendsto_self_mul_Gamma_nhdsWithin_zero_pos).mul
    (tendsto_const_nhds (x := Real.sqrt Real.pi))).div
    (((hpow.mul_const (Real.Gamma x)).mul_const (Real.Gamma α)).mul hG2) hden
  convert ht using 1
  · funext ε
    dsimp
    ring
  · simp

/-- Duplication turns the operator Mellin residue into the hard-edge density constant.
Source: Legendre duplication, operator rederivations Section 5; atlas
`wishart-lambda-min-tail` (exact constant helper). -/
theorem gamma_probe_mellin_residue_eq (x α : ℝ) (hx : 0 < x) (hα : 0 < α) :
    Real.Gamma (x + α) * Real.sqrt Real.pi /
        (2 ^ α * Real.Gamma x * Real.Gamma α * Real.Gamma (α + 1 / 2))
      = 2 ^ (α - 1) * Real.Gamma (x + α) / (Real.Gamma x * Real.Gamma (2 * α)) := by
  have hdup := Real.Gamma_mul_Gamma_add_half α
  have hgx : Real.Gamma x ≠ 0 := (Real.Gamma_pos_of_pos hx).ne'
  have hga2 : Real.Gamma (2 * α) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hp2 : (2 : ℝ) ^ α ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have hp2' : (2 : ℝ) ^ (1 - 2 * α) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  rw [show 2 ^ α * Real.Gamma x * Real.Gamma α * Real.Gamma (α + 1 / 2)
      = 2 ^ α * Real.Gamma x * (Real.Gamma α * Real.Gamma (α + 1 / 2)) by ring, hdup]
  have htwo : (2 : ℝ) ^ (α - 1) * (2 ^ α * 2 ^ (1 - 2 * α)) = 1 := by
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num),
      show α - 1 + (α + (1 - 2 * α)) = 0 by ring, Real.rpow_zero]
  field_simp
  simpa only [mul_assoc, mul_comm, mul_left_comm] using htwo.symm

/-- The exact hard-edge CDF density bound follows from an antitone Gamma-weighted
density and the operator master moment inequalities. Source: operator rederivations
Section 5, equation (20); atlas `wishart-lambda-min-tail`. The hypotheses are the
scalar density interface and real moment interface, and are supplied separately by
the Gaussian operator argument. -/
theorem measure_Ioc_le_lintegral_of_antitone_density_of_probe_moments
    (μ : Measure ℝ) (x α : ℝ) (hx : 0 < x) (hα : 0 < α)
    (h : ℝ → ℝ) (hh : Measurable h) (hnn : ∀ y ∈ Ioi (0 : ℝ), 0 ≤ h y)
    (hanti : AntitoneOn h (Ioi 0))
    (hdens : μ.restrict (Ioi 0) = (volume.restrict (Ioi 0)).withDensity
      (fun y : ℝ => ENNReal.ofReal (y ^ (α - 1) * Real.exp (-y / 2) * h y)))
    (hMom : ∀ s : ℝ, 0 < s → s < α →
      Integrable (fun y : ℝ => y ^ (-s)) (μ.restrict (Ioi 0)) ∧
      (∫ y in Ioi (0 : ℝ), y ^ (-s) ∂μ) ≤
        Real.Gamma (x + s) * Real.Gamma (α - s) * Real.sqrt Real.pi /
          (2 ^ s * Real.Gamma x * Real.Gamma α * Real.Gamma (s + 1 / 2)))
    (t : ℝ) :
    μ (Ioc 0 t) ≤ ∫⁻ y in Ioc (0 : ℝ) t,
      ENNReal.ofReal ((2 ^ (α - 1) * Real.Gamma (x + α) /
        (Real.Gamma x * Real.Gamma (2 * α))) * y ^ (α - 1) * Real.exp (-y / 2)) := by
  let M : ℝ → ℝ := fun ε => Real.Gamma (x + α - ε) * Real.Gamma ε * Real.sqrt Real.pi /
    (2 ^ (α - ε) * Real.Gamma x * Real.Gamma α * Real.Gamma (α + 1 / 2 - ε))
  have hM : ∀ ε : ℝ, 0 < ε → ε < α →
      Integrable (fun y : ℝ => y ^ (-α + ε)) (μ.restrict (Ioi 0)) ∧
      (∫ y in Ioi (0 : ℝ), y ^ (-α + ε) ∂μ) ≤ M ε := by
    intro ε hε hεα
    obtain ⟨hint, hbound⟩ := hMom (α - ε) (by linarith) (by linarith)
    have hp : -(α - ε) = -α + ε := by ring
    have harg1 : x + (α - ε) = x + α - ε := by ring
    have harg2 : α - (α - ε) = ε := by ring
    have harg3 : α - ε + 1 / 2 = α + 1 / 2 - ε := by ring
    simpa only [hp, harg1, harg2, harg3, M] using And.intro hint hbound
  have hlim := tendsto_gamma_probe_mellin_endpoint x α hx hα
  rw [gamma_probe_mellin_residue_eq x α hx hα] at hlim
  have hbound := antitone_density_le_of_mellin_endpoint μ α hα h hh hnn hanti hdens M _ hM hlim
  exact measure_Ioc_le_lintegral_of_antitone_density_bound μ α h hdens _ hbound t

/-- The squared smallest singular value is measurable via the total inverse-Gram
operator norm. Source: reciprocal singular-value identity; atlas
`wishart-lambda-min-tail` (scalar law helper). -/
theorem measurable_sigmaMin_transpose_sq {r k : ℕ} :
    Measurable (fun G : Fin r → Fin k → ℝ => sigmaMin (Matrix.of G)ᵀ ^ 2) := by
  convert measurable_specNorm_inv_self_mul_transpose.inv using 1
  funext G
  change sigmaMin (Matrix.of G)ᵀ ^ 2 = (specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹)⁻¹
  rw [specNorm_inv_self_mul_transpose_eq, one_div, inv_inv]

/-- The scalar smallest-eigenvalue law inherits every subcritical negative
moment bound from the operator quadratic probe, also after restriction to the
positive half-line. Source: operator master inverse moment; atlas
`wishart-lambda-min-tail` (scalar Mellin input). -/
theorem integrable_and_integral_rpow_neg_map_sigmaMin_transpose_sq_gaussianMatrix_le
    {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) (s : ℝ) (hs : 0 < s)
    (hsα : s < ((k : ℝ) - r + 1) / 2) :
    Integrable (fun y : ℝ => y ^ (-s))
      (((gaussianMatrix r k).map (fun G => sigmaMin (Matrix.of G)ᵀ ^ 2)).restrict (Ioi 0)) ∧
    (∫ y in Ioi (0 : ℝ), y ^ (-s)
      ∂((gaussianMatrix r k).map (fun G => sigmaMin (Matrix.of G)ᵀ ^ 2))) ≤
      Real.Gamma ((r : ℝ) / 2 + s) * Real.Gamma (((k : ℝ) - r + 1) / 2 - s) *
        Real.sqrt Real.pi /
        (2 ^ s * Real.Gamma ((r : ℝ) / 2) * Real.Gamma (((k : ℝ) - r + 1) / 2) *
          Real.Gamma (s + 1 / 2)) := by
  let X : (Fin r → Fin k → ℝ) → ℝ := fun G => sigmaMin (Matrix.of G)ᵀ ^ 2
  let μ := (gaussianMatrix r k).map X
  have hXm : Measurable X := measurable_sigmaMin_transpose_sq
  have hsm : Measurable (fun y : ℝ => y ^ (-s)) := by fun_prop
  have hpow : (fun G : Fin r → Fin k → ℝ => X G ^ (-s))
      = (fun G => specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ s) := by
    funext G
    rw [specNorm_inv_self_mul_transpose_eq, one_div, Real.inv_rpow (sq_nonneg _),
      Real.rpow_neg (sq_nonneg _)]
  obtain ⟨hint, hbound⟩ :=
    integrable_and_integral_rpow_specNorm_inv_self_mul_transpose_gaussianMatrix_le hr hrk s hs hsα
  have hint' : Integrable (fun y : ℝ => y ^ (-s)) μ := by
    apply (integrable_map_measure hsm.aestronglyMeasurable hXm.aemeasurable).mpr
    change Integrable (fun G => X G ^ (-s)) (gaussianMatrix r k)
    rw [hpow]
    exact hint
  have hval : (∫ y : ℝ, y ^ (-s) ∂μ) =
      ∫ G : Fin r → Fin k → ℝ, specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ s
        ∂(gaussianMatrix r k) := by
    rw [integral_map hXm.aemeasurable hsm.aestronglyMeasurable]
    exact congrArg (integral (gaussianMatrix r k)) hpow
  have hnn : 0 ≤ᵐ[μ] (fun y : ℝ => y ^ (-s)) := by
    apply (ae_map_iff hXm.aemeasurable (measurableSet_le measurable_const hsm)).2
    exact ae_of_all _ fun G => Real.rpow_nonneg (sq_nonneg _) _
  exact ⟨hint'.restrict, (setIntegral_le_integral hint' hnn).trans (hval ▸ hbound)⟩

/-- An antitone Gamma-weighted density for the squared smallest Gaussian
singular value implies the exact Edelman CDF bound. Source: operator
rederivations Section 5; atlas `wishart-lambda-min-tail`. All moment and
endpoint hypotheses are discharged by the operator probe; only the scalar
density representation remains as the explicit input. -/
theorem gaussianMatrix_map_sigmaMin_transpose_sq_Ioc_le_of_antitone_density
    {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k)
    (h : ℝ → ℝ) (hh : Measurable h) (hnn : ∀ y ∈ Ioi (0 : ℝ), 0 ≤ h y)
    (hanti : AntitoneOn h (Ioi 0))
    (hdens : ((gaussianMatrix r k).map
        (fun G => sigmaMin (Matrix.of G)ᵀ ^ 2)).restrict (Ioi 0) =
      (volume.restrict (Ioi 0)).withDensity (fun y : ℝ => ENNReal.ofReal
        (y ^ (((k : ℝ) - r - 1) / 2) * Real.exp (-y / 2) * h y)))
    (t : ℝ) :
    ((gaussianMatrix r k).map (fun G => sigmaMin (Matrix.of G)ᵀ ^ 2)) (Ioc 0 t)
      ≤ ∫⁻ y in Ioc (0 : ℝ) t, ENNReal.ofReal
        ((2 ^ (((k : ℝ) - r - 1) / 2) * Real.Gamma (((k : ℝ) + 1) / 2) /
          (Real.Gamma ((r : ℝ) / 2) * Real.Gamma ((k : ℝ) - r + 1))) *
          y ^ (((k : ℝ) - r - 1) / 2) * Real.exp (-y / 2)) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hrkR : (r : ℝ) ≤ k := by exact_mod_cast hrk
  have hα : 0 < ((k : ℝ) - r + 1) / 2 := by linarith
  have he1 : ((k : ℝ) - r + 1) / 2 - 1 = ((k : ℝ) - r - 1) / 2 := by ring
  have he2 : (r : ℝ) / 2 + ((k : ℝ) - r + 1) / 2 = ((k : ℝ) + 1) / 2 := by ring
  have he3 : 2 * (((k : ℝ) - r + 1) / 2) = (k : ℝ) - r + 1 := by ring
  have h := measure_Ioc_le_lintegral_of_antitone_density_of_probe_moments
    ((gaussianMatrix r k).map (fun G => sigmaMin (Matrix.of G)ᵀ ^ 2))
    ((r : ℝ) / 2) (((k : ℝ) - r + 1) / 2) (by positivity) hα h hh hnn hanti
    (by simpa only [he1] using hdens)
    (fun s hs hsα => integrable_and_integral_rpow_neg_map_sigmaMin_transpose_sq_gaussianMatrix_le
      hr hrk s hs hsα) t
  simpa only [he1, he2, he3] using h

/-- A Gaussian matrix of positive row dimension and at least as many columns
has positive squared smallest singular value almost surely. Source: Gaussian
full row rank and the reciprocal inverse-Gram norm; atlas
`wishart-lambda-min-tail` (null-boundary helper). -/
theorem ae_sigmaMin_transpose_sq_pos_gaussianMatrix {r k : ℕ}
    (hr : 1 ≤ r) (hrk : r ≤ k) :
    ∀ᵐ G ∂(gaussianMatrix r k), 0 < sigmaMin (Matrix.of G)ᵀ ^ 2 := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  filter_upwards [gaussianMatrix_ae_rank_eq r k] with G hG
  have hdet : IsUnit (Matrix.of G * (Matrix.of G)ᵀ).det :=
    isUnit_iff_ne_zero.mpr (det_ne_zero_of_rank_eq _ (by
      rw [Matrix.rank_self_mul_transpose, hG, Fintype.card_fin, Nat.min_eq_left hrk]))
  have hinv : (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ≠ 0 := by
    intro hz
    have hmul := Matrix.mul_nonsing_inv (Matrix.of G * (Matrix.of G)ᵀ) hdet
    rw [hz, Matrix.mul_zero] at hmul
    exact one_ne_zero hmul.symm
  have hnorm : 0 < specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ := by
    exact norm_pos_iff.mpr hinv
  have hXne : sigmaMin (Matrix.of G)ᵀ ^ 2 ≠ 0 := by
    intro hzero
    rw [specNorm_inv_self_mul_transpose_eq, hzero, div_zero] at hnorm
    exact (lt_irrefl 0) hnorm
  exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm hXne)

/-- The exact Gaussian hard-edge CDF bound follows from the scalar antitone
density interface. Source: operator rederivations Section 5; atlas
`wishart-lambda-min-tail`. The density input is explicit, and all spectral
moments and endpoint limiting arguments are kernel-checked here. -/
theorem gaussianMatrix_sigmaMin_transpose_sq_le_le_lintegral_of_antitone_density
    {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k)
    (h : ℝ → ℝ) (hh : Measurable h) (hnn : ∀ y ∈ Ioi (0 : ℝ), 0 ≤ h y)
    (hanti : AntitoneOn h (Ioi 0))
    (hdens : ((gaussianMatrix r k).map
        (fun G => sigmaMin (Matrix.of G)ᵀ ^ 2)).restrict (Ioi 0) =
      (volume.restrict (Ioi 0)).withDensity (fun y : ℝ => ENNReal.ofReal
        (y ^ (((k : ℝ) - r - 1) / 2) * Real.exp (-y / 2) * h y)))
    (t : ℝ) :
    (gaussianMatrix r k) {G | sigmaMin (Matrix.of G)ᵀ ^ 2 ≤ t}
      ≤ ∫⁻ y in Ioc (0 : ℝ) t, ENNReal.ofReal
        ((2 ^ (((k : ℝ) - r - 1) / 2) * Real.Gamma (((k : ℝ) + 1) / 2) /
          (Real.Gamma ((r : ℝ) / 2) * Real.Gamma ((k : ℝ) - r + 1))) *
          y ^ (((k : ℝ) - r - 1) / 2) * Real.exp (-y / 2)) := by
  have hset : (gaussianMatrix r k) {G | sigmaMin (Matrix.of G)ᵀ ^ 2 ≤ t}
      = (gaussianMatrix r k) ((fun G => sigmaMin (Matrix.of G)ᵀ ^ 2) ⁻¹' Ioc 0 t) := by
    apply measure_congr
    filter_upwards [ae_sigmaMin_transpose_sq_pos_gaussianMatrix hr hrk] with G hG
    change (sigmaMin (Matrix.of G)ᵀ ^ 2 ≤ t) =
      (0 < sigmaMin (Matrix.of G)ᵀ ^ 2 ∧ sigmaMin (Matrix.of G)ᵀ ^ 2 ≤ t)
    apply propext
    simp only [hG, true_and]
  rw [hset, ← Measure.map_apply measurable_sigmaMin_transpose_sq measurableSet_Ioc]
  exact gaussianMatrix_map_sigmaMin_transpose_sq_Ioc_le_of_antitone_density
    hr hrk h hh hnn hanti hdens t

end NLAlib
