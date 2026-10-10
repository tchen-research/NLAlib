import NLAlib.ForMathlib.MeasureTheory.LocalWeakDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Gamma-weighted density from a weak scalar inequality

This file applies the proved weak-density infrastructure to the scalar Gamma
integrating factor. Source: operator rederivations, Section 5,
atlas wishart-lambda-min-tail.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal

namespace NLAlib

/-- A density continuous on a half-line gives a Radon reweighted measure after
restriction to every smaller half-line. Clamping the weight at the smaller endpoint
reduces the statement to Mathlib's continuous-density local finiteness theorem.
Source: operator rederivations, Section 5; atlas wishart-lambda-min-tail (helper). -/
theorem withDensity_restrict_regular_of_continuousOn_Ioi
    (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] (g : ℝ → ℝ)
    (ℓ a : ℝ) (ha : ℓ < a) (hg : ContinuousOn g (Ioi ℓ)) :
    ((μ.withDensity (fun x => ENNReal.ofReal (g x))).restrict (Ioi a)).Regular := by
  let g' : ℝ → ℝ := fun x => g (max a x)
  have hg' : Continuous g' := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((hg (max a x) (ha.trans_le (le_max_left a x))).continuousAt
      (isOpen_Ioi.mem_nhds (ha.trans_le (le_max_left a x)))).comp
      (continuous_const.max continuous_id).continuousAt
  let ν : Measure ℝ := (μ.restrict (Ioi a)).withDensity (fun x => ENNReal.ofReal (g' x))
  let : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hg'
  have hν : ν.Regular := inferInstance
  have heq : (μ.withDensity (fun x => ENNReal.ofReal (g x))).restrict (Ioi a) = ν := by
    rw [restrict_withDensity measurableSet_Ioi]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change a < x at hx
    simp [g', max_eq_right hx.le]
  exact heq ▸ hν

/-- An antitone representative on a real half-line has a globally measurable
extension agreeing with it on that half-line. Source: operator rederivations,
Section 5, density API; atlas wishart-lambda-min-tail (helper). -/
theorem exists_measurable_extension_of_antitoneOn_Ioi
    (ℓ : ℝ) (h : ℝ → ℝ) (hh : AntitoneOn h (Ioi ℓ)) :
    ∃ h' : ℝ → ℝ, Measurable h' ∧ EqOn h' h (Ioi ℓ) := by
  have hsub : Antitone (fun x : Ioi ℓ => h x) := fun x y hxy => hh x.property y.property hxy
  obtain ⟨h', hmeas, heq⟩ :=
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi).exists_measurable_extend
      hsub.measurable (fun _ => inferInstance)
  refine ⟨h', hmeas, ?_⟩
  intro x hx
  exact congrFun heq ⟨x, hx⟩

/-- The weak scalar Wishart inequality produces an actual Gamma-weighted density
with a nonnegative antitone measurable factor. No density premise is assumed.
The original finite measure may have an atom at zero, which is removed by the
explicit restriction to the positive half-line.
Source: operator rederivations, Section 5; atlas wishart-lambda-min-tail (helper).
atlas: gamma-weighted-antitone-density -/
theorem exists_gamma_weighted_antitone_density_of_weak_inequality
    (μ : Measure ℝ) [IsFiniteMeasure μ] (m : ℝ)
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioi 0 → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x in Ioi 0, 4 * x * deriv ψ x + 2 * (m - x) * ψ x ∂μ) :
    ∃ h : ℝ → ℝ, Measurable h ∧ AntitoneOn h (Ioi 0) ∧
      (∀ x ∈ Ioi 0, 0 ≤ h x) ∧
      μ.restrict (Ioi 0) = (volume.restrict (Ioi 0)).withDensity
        (fun x => ENNReal.ofReal (x ^ (m / 2 - 1) * Real.exp (-x / 2) * h x)) := by
  let g : ℝ → ℝ := fun x => x ^ (1 - m / 2) * Real.exp (x / 2)
  let w : ℝ → ℝ := fun x => x ^ (m / 2 - 1) * Real.exp (-x / 2)
  have hgmeas : Measurable g := by fun_prop
  have hgpos (x : ℝ) (hx : 0 < x) : 0 < g x :=
    mul_pos (Real.rpow_pos_of_pos hx _) (Real.exp_pos _)
  have hgcont : ContinuousOn g (Ioi 0) := by
    intro x hx
    exact ((Real.contDiffAt_rpow_const_of_ne (p := 1 - m / 2) (n := 1)
      (ne_of_gt hx)).continuousAt.mul
      (Real.continuous_exp.continuousAt.comp
        (continuousAt_id.div_const 2))).continuousWithinAt
  let τ : Measure ℝ := (μ.restrict (Ioi 0)).withDensity (fun x => ENNReal.ofReal (g x))
  have hτweak : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ Ioi 0 → (∀ x, 0 ≤ η x) → 0 ≤ ∫ x, deriv η x ∂τ := by
    intro η hη hηc hηs hη0
    have hh := integral_rpow_exp_mul_deriv_nonneg_of_weak_gamma μ m hweak η hη hηc hηs hη0
    have hi : (∫ x, deriv η x ∂τ) = ∫ x in Ioi 0, g x * deriv η x ∂μ := by
      rw [integral_withDensity_eq_integral_toReal_smul hgmeas.ennreal_ofReal
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [ENNReal.toReal_ofReal (hgpos x hx).le, smul_eq_mul]
    rw [hi]
    exact hh
  have hτloc : ∀ a : ℝ, 0 < a → (τ.restrict (Ioi a)).Regular := by
    intro a ha
    exact withDensity_restrict_regular_of_continuousOn_Ioi (μ.restrict (Ioi 0)) g 0 a ha hgcont
  obtain ⟨h, hh, hh0, hτeq⟩ :=
    exists_antitoneOn_withDensity_eq_of_locally_regular_weak_deriv_nonneg τ 0 hτloc hτweak
  obtain ⟨h', h'meas, h'eq⟩ := exists_measurable_extension_of_antitoneOn_Ioi 0 h hh
  have h'anti : AntitoneOn h' (Ioi 0) := by
    intro x hx y hy hxy
    rw [h'eq hx, h'eq hy]
    exact hh hx hy hxy
  have h'0 : ∀ x ∈ Ioi 0, 0 ≤ h' x := fun x hx => by rw [h'eq hx]; exact hh0 x hx
  have hτr : τ.restrict (Ioi 0) = τ := by
    rw [restrict_withDensity measurableSet_Ioi]
    dsimp [τ]
    rw [Measure.restrict_restrict measurableSet_Ioi, inter_self]
  rw [hτr] at hτeq
  have hτeq' : τ = (volume.restrict (Ioi 0)).withDensity (fun x => ENNReal.ofReal (h' x)) := by
    rw [hτeq]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [h'eq hx]
  have hginv : ∀ x ∈ Ioi 0, (ENNReal.ofReal (g x))⁻¹ = ENNReal.ofReal (w x) := by
    intro x hx
    have hmul : g x * w x = 1 := by
      dsimp [g, w]
      rw [mul_mul_mul_comm, ← Real.rpow_add hx, ← Real.exp_add]
      rw [show (1 - m / 2) + (m / 2 - 1) = 0 by ring,
        show x / 2 + -x / 2 = 0 by ring]
      simp
    have hwreal : w x = (g x)⁻¹ := by
      apply mul_left_cancel₀ (hgpos x hx).ne'
      rw [hmul, mul_inv_cancel₀ (hgpos x hx).ne']
    rw [hwreal, ENNReal.ofReal_inv_of_pos (hgpos x hx)]
  have hinverse : τ.withDensity (fun x => (ENNReal.ofReal (g x))⁻¹) = μ.restrict (Ioi 0) := by
    apply withDensity_inv_same hgmeas.ennreal_ofReal
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact (ENNReal.ofReal_pos.mpr (hgpos x hx)).ne'
    · exact Eventually.of_forall fun _ => ENNReal.ofReal_ne_top
  refine ⟨h', h'meas, h'anti, h'0, ?_⟩
  rw [← hinverse, hτeq']
  have heqmul : ((volume.restrict (Ioi 0)).withDensity
      (fun x => ENNReal.ofReal (h' x))).withDensity
      (fun x => (ENNReal.ofReal (g x))⁻¹) =
      (volume.restrict (Ioi 0)).withDensity
        (fun x => ENNReal.ofReal (h' x) * (ENNReal.ofReal (g x))⁻¹) :=
    (withDensity_mul (volume.restrict (Ioi 0)) h'meas.ennreal_ofReal
      hgmeas.ennreal_ofReal.inv).symm
  rw [heqmul]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [hginv x hx, ← ENNReal.ofReal_mul (h'0 x hx)]
  congr 1
  dsimp [w]
  ring

end NLAlib
