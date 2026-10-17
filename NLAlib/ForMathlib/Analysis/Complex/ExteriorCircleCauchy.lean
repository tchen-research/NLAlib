import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Field.Lemmas

/-! # Cauchy integrals for functions holomorphic near infinity

The exterior Cauchy formula computes a positively oriented circle integral from
the value of a holomorphic function at infinity. These lemmas supply the atomic
term in Stahl's trace-exponential integral representation (Stahl 2013, Theorem 2),
toward atlas item `trace-exponential-stahl`. No global eigenvalue
branch continuation or spectral-surface positivity is assumed here.
-/

noncomputable section

open Set Metric Filter Bornology Complex
open scoped Topology

namespace NLAlib

/-- A holomorphic function on an exterior domain has equal contour integrals
on any two positive-radius circles in that domain. This is the radius
independence needed to fix one density in `trace-exponential-stahl`. -/
theorem circleIntegral_eq_of_differentiableOn_exterior
    {f : ℂ → ℂ} {R r s : ℝ} (hf : DifferentiableOn ℂ f {z | R < ‖z‖})
    (hr : 0 < r) (hs : 0 < s) (hRr : R < r) (hRs : R < s) :
    (∮ z in C(0, r), f z) = ∮ z in C(0, s), f z := by
  suffices haux : ∀ {u v : ℝ}, 0 < u → R < u → u ≤ v →
      (∮ z in C(0, v), f z) = ∮ z in C(0, u), f z by
    rcases le_total r s with hrs | hsr
    · exact (haux hr hRr hrs).symm
    · exact haux hs hRs hsr
  intro u v hu hRu huv
  have hsub : closedBall (0 : ℂ) v \ ball 0 u ⊆ {z | R < ‖z‖} := by
    intro z hz
    have hz' : u ≤ ‖z‖ := by simpa [mem_ball, dist_zero_right] using hz.2
    exact hRu.trans_le hz'
  have hopen : IsOpen {z : ℂ | R < ‖z‖} := isOpen_lt continuous_const continuous_norm
  exact Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    hu huv (s := (∅ : Set ℂ)) countable_empty (hf.continuousOn.mono hsub)
    (fun z hz => hf.differentiableAt (hopen.mem_nhds (by
      have hz' : u < ‖z‖ := by
        simpa only [mem_closedBall, dist_zero_right, not_le] using hz.1.2
      exact hRu.trans hz')))

/-- The normalized exterior Cauchy kernel has the same integral on two circles
lying in an exterior holomorphy domain. Both circles are counterclockwise.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem circleIntegral_inv_mul_eq_of_differentiableOn_exterior
    {f : ℂ → ℂ} {R r s : ℝ} (hf : DifferentiableOn ℂ f {z | R < ‖z‖})
    (hr : 0 < r) (hRr : R < r) (hrs : r ≤ s) :
    (∮ z in C(0, s), z⁻¹ * f z) = ∮ z in C(0, r), z⁻¹ * f z := by
  have hsub : closedBall (0 : ℂ) s \ ball 0 r ⊆ {z | R < ‖z‖} := by
    intro z hz
    have hz' : r ≤ ‖z‖ := by simpa [mem_ball, dist_zero_right] using hz.2
    exact hRr.trans_le hz'
  have hopen : IsOpen {z : ℂ | R < ‖z‖} := isOpen_lt continuous_const continuous_norm
  simpa only [sub_zero, smul_eq_mul] using
    circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable
      hr hrs (s := (∅ : Set ℂ)) countable_empty (hf.continuousOn.mono hsub)
      (fun z hz => hf.differentiableAt (hopen.mem_nhds (by
        have hz' : r < ‖z‖ := by
          simpa only [mem_closedBall, dist_zero_right, not_le] using hz.1.2
        exact hRr.trans hz')))

/-- A function holomorphic near infinity and vanishing there has zero exterior
circle integral against `1 / z`. This is proved by enlarging the circle and a
uniform norm estimate, rather than by assuming a residue at infinity.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem two_pi_i_inv_mul_circleIntegral_inv_mul_eq_zero_of_tendsto
    {f : ℂ → ℂ} {R r : ℝ} (hf : DifferentiableOn ℂ f {z | R < ‖z‖})
    (hr : 0 < r) (hRr : R < r) (hlim : Tendsto f (cobounded ℂ) (𝓝 0)) :
    (2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, r), z⁻¹ * f z) = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  have hev : ∀ᶠ z in cobounded ℂ, ‖f z‖ < ε := by
    simpa only [dist_zero_right] using (Metric.tendsto_nhds.mp hlim ε hε)
  obtain ⟨K, _, hK⟩ := hasBasis_cobounded_norm.eventually_iff.mp hev
  let s := max r K
  have hrs : r ≤ s := le_max_left _ _
  have hKs : K ≤ s := le_max_right _ _
  have hs : 0 < s := hr.trans_le hrs
  rw [← circleIntegral_inv_mul_eq_of_differentiableOn_exterior hf hr hRr hrs]
  have hb : ∀ z ∈ sphere (0 : ℂ) s, ‖z⁻¹ * f z‖ ≤ ε / s := by
    intro z hz
    have hz' : ‖z‖ = s := by simpa only [mem_sphere, dist_zero_right] using hz
    rw [norm_mul, norm_inv, hz']
    calc
      s⁻¹ * ‖f z‖ ≤ s⁻¹ * ε :=
        mul_le_mul_of_nonneg_left (hK (hKs.trans_eq hz'.symm)).le (inv_nonneg.mpr hs.le)
      _ = ε / s := by ring
  have hbound := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hs.le hb
  simpa only [smul_eq_mul, mul_div_cancel₀ _ hs.ne', zero_add] using hbound

/-- The counterclockwise exterior Cauchy integral of a function holomorphic near
infinity equals its finite limit at infinity.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem two_pi_i_inv_mul_circleIntegral_inv_mul_eq_of_tendsto
    {f : ℂ → ℂ} {a : ℂ} {R r : ℝ}
    (hf : DifferentiableOn ℂ f {z | R < ‖z‖}) (hr : 0 < r) (hRr : R < r)
    (hlim : Tendsto f (cobounded ℂ) (𝓝 a)) :
    (2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, r), z⁻¹ * f z) = a := by
  have hsub : sphere (0 : ℂ) r ⊆ {z | R < ‖z‖} := by
    intro z hz
    have hz' : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right] using hz
    exact hRr.trans_eq hz'.symm
  have hne (z : ℂ) (hz : z ∈ sphere (0 : ℂ) r) : z ≠ 0 := by
    have hz' : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right] using hz
    intro h
    exact hr.ne' (by simpa [h] using hz'.symm)
  have hci : CircleIntegrable (fun z => z⁻¹ * f z) 0 r :=
    ((continuousOn_id.inv₀ hne).mul (hf.continuousOn.mono hsub)).circleIntegrable hr.le
  have hca : CircleIntegrable (fun z : ℂ => z⁻¹ * a) 0 r :=
    ((continuousOn_id.inv₀ hne).mul continuousOn_const).circleIntegrable hr.le
  have hz := two_pi_i_inv_mul_circleIntegral_inv_mul_eq_zero_of_tendsto
    (hf.sub_const a) hr hRr (by simpa using hlim.sub_const a)
  have heq : (∮ z in C(0, r), z⁻¹ * (f z - a)) =
      (∮ z in C(0, r), z⁻¹ * f z) - (2 * Real.pi * I : ℂ) * a := by
    simp_rw [mul_sub]
    rw [circleIntegral.integral_sub hci hca]
    congr 1
    simp_rw [mul_comm _ a]
    rw [circleIntegral.integral_const_mul]
    have hk : (∮ z in C(0, r), z⁻¹) = (2 * Real.pi * I : ℂ) := by
      simpa only [sub_zero, smul_eq_mul] using
        circleIntegral.integral_sub_center_inv (0 : ℂ) hr.ne'
    rw [hk]
  rw [heq] at hz
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [mul_sub, inv_mul_cancel_left₀ hpi] at hz
  exact sub_eq_zero.mp hz

/-- The exterior Cauchy formula evaluates the circle kernel at every point
inside the circle, even if the holomorphic function is not defined there. Its
value is the function's limit at infinity, not its value at the enclosed point.
This is the atomic Cauchy term in Stahl's representation (Stahl 2013, Theorem 2).
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem two_pi_i_inv_mul_circleIntegral_div_sub_eq_of_tendsto
    {f : ℂ → ℂ} {a t : ℂ} {R r : ℝ}
    (hf : DifferentiableOn ℂ f {z | R < ‖z‖}) (hr : 0 < r) (hRr : R < r)
    (htr : ‖t‖ < r) (hlim : Tendsto f (cobounded ℂ) (𝓝 a)) :
    (2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, r), f z / (z - t)) = a := by
  let g : ℂ → ℂ := fun z => (1 - t * z⁻¹)⁻¹ * f z
  have hzero (z : ℂ) (hz : max R ‖t‖ < ‖z‖) : z ≠ 0 := by
    intro h
    have h' := (le_max_right R ‖t‖).trans_lt hz
    simpa [h] using (norm_nonneg t).trans_lt h'
  have hsub (z : ℂ) (hz : max R ‖t‖ < ‖z‖) : z - t ≠ 0 := by
    intro h
    have h' := (le_max_right R ‖t‖).trans_lt hz
    simp [sub_eq_zero.mp h] at h'
  have hden (z : ℂ) (hz : max R ‖t‖ < ‖z‖) : 1 - t * z⁻¹ ≠ 0 := by
    intro h
    apply hsub z hz
    have hh := congrArg (fun w : ℂ => w * z) h
    simpa only [sub_mul, one_mul, mul_assoc, inv_mul_cancel₀ (hzero z hz), mul_one,
      zero_mul] using hh
  have hg : DifferentiableOn ℂ g {z | max R ‖t‖ < ‖z‖} := by
    have hf' : DifferentiableOn ℂ f {z | max R ‖t‖ < ‖z‖} :=
      hf.mono (fun _ hz => (le_max_left R ‖t‖).trans_lt hz)
    intro z hz
    have hi : DifferentiableAt ℂ (fun w : ℂ => w⁻¹) z :=
      differentiableAt_id.inv (hzero z hz)
    have hd : DifferentiableAt ℂ (fun w : ℂ => (1 - t * w⁻¹)⁻¹) z :=
      ((hi.const_mul t).const_sub 1).inv (hden z hz)
    exact hd.differentiableWithinAt.mul (hf' z hz)
  have hg_lim : Tendsto g (cobounded ℂ) (𝓝 a) := by
    have hinv : Tendsto (fun z : ℂ => (1 - t * z⁻¹)⁻¹) (cobounded ℂ) (𝓝 1) := by
      have hh : Tendsto (fun z : ℂ => 1 - t * z⁻¹) (cobounded ℂ) (𝓝 (1 : ℂ)) := by
        simpa using (tendsto_const_nhds (x := (1 : ℂ))).sub
          (tendsto_inv₀_cobounded.const_mul t)
      simpa using hh.inv₀ one_ne_zero
    simpa [g] using hinv.mul hlim
  have hg_eq : (∮ z in C(0, r), z⁻¹ * g z) =
      ∮ z in C(0, r), f z / (z - t) := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    have hz' : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right] using hz
    have hzext : max R ‖t‖ < ‖z‖ := by rw [hz']; exact max_lt hRr htr
    dsimp [g]
    field_simp [hzero z hzext, hsub z hzext, hden z hzext]
  rw [← hg_eq]
  exact two_pi_i_inv_mul_circleIntegral_inv_mul_eq_of_tendsto hg hr
    (max_lt hRr htr) hg_lim

end NLAlib
