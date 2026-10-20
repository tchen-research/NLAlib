import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! # Uniform propagation from one boundary of a bounded holomorphic strip

Hadamard's three-lines theorem propagates a vanishing uniform bound on the
upper boundary to every closed interior substrip. This quantitative route
needs neither a normal-family theorem nor a subsequence selection.
-/

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Complex.HadamardThreeLines

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A uniform upper-boundary error propagates into a bounded holomorphic
strip with its exact positive Hadamard exponent. The lower edge of the
target substrip is strictly above the original lower boundary. -/
theorem norm_le_mul_boundary_error_rpow
    {f : ℂ → E} {l h u B ε : ℝ} (hlh : l<h) (hhu : h≤u)
    (hd : DiffContOnCl ℂ f (verticalStrip l u))
    (hB : 1≤B) (hbound : ∀ z∈verticalClosedStrip l u, ‖f z‖≤B)
    (hε0 : 0≤ε) (hε1 : ε≤1) (hupper : ∀ z : ℂ, z.re=u → ‖f z‖≤ε)
    {z : ℂ} (hz : z∈verticalClosedStrip h u) :
    ‖f z‖≤B*ε^((h-l)/(u-l)) := by
  have hlu : l<u := hlh.trans_le hhu
  have hz' : z∈verticalClosedStrip l u := ⟨hlh.le.trans hz.1,hz.2⟩
  have hu0 : 0<u-l := sub_pos.mpr hlu
  have ht0 : 0≤(z.re-l)/(u-l) := div_nonneg (sub_nonneg.mpr hz'.1) hu0.le
  have ht1 : (z.re-l)/(u-l)≤1 := (div_le_one hu0).mpr (by linarith [hz'.2])
  have hθ0 : 0≤(h-l)/(u-l) := div_nonneg (sub_nonneg.mpr hlh.le) hu0.le
  have hθ : (h-l)/(u-l)≤(z.re-l)/(u-l) :=
    div_le_div_of_nonneg_right (by linarith [hz.1]) hu0.le
  have hbdd : BddAbove ((norm ∘ f) '' verticalClosedStrip l u) := by
    refine ⟨B,?_⟩
    rintro _ ⟨w,hw,rfl⟩
    exact hbound w hw
  have ha : ∀ w∈re ⁻¹' {l}, ‖f w‖≤B := by
    intro w hw
    apply hbound w
    have he : w.re=l := hw
    exact ⟨he.ge,he.trans_le hlu.le⟩
  have hb : ∀ w∈re ⁻¹' {u}, ‖f w‖≤ε := fun w hw => hupper w hw
  have hh := norm_le_interp_of_mem_verticalClosedStrip' hlu hz' hd hbdd ha hb
  apply hh.trans
  have hpowB : B^(1-(z.re-l)/(u-l))≤B := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hB (show 1-(z.re-l)/(u-l)≤1 by linarith)
  have hpowε : ε^((z.re-l)/(u-l))≤ε^((h-l)/(u-l)) :=
    Real.rpow_le_rpow_of_exponent_ge' hε0 hε1 hθ0 hθ
  exact mul_le_mul hpowB hpowε (Real.rpow_nonneg hε0 _) (zero_le_one.trans hB)

/-- A family bounded on one closed holomorphic strip converges uniformly
to zero on every closed interior substrip if its uniform error on the
upper boundary tends to zero. The indexing filter is arbitrary. -/
theorem tendstoUniformlyOn_zero_of_upper_boundary_error
    (F : ι → ℂ → E) (p : Filter ι) {l h u B : ℝ} (hlh : l<h) (hhu : h≤u)
    (hd : ∀ i, DiffContOnCl ℂ (F i) (verticalStrip l u))
    (hB : 1≤B) (hbound : ∀ i z, z∈verticalClosedStrip l u → ‖F i z‖≤B)
    (ε : ι → ℝ) (hε0 : ∀ i, 0≤ε i) (hε : Tendsto ε p (𝓝 0))
    (hupper : ∀ i z, z.re=u → ‖F i z‖≤ε i) :
    TendstoUniformlyOn F (fun _ => 0) p (verticalClosedStrip h u) := by
  have hθ : 0<(h-l)/(u-l) := div_pos (sub_pos.mpr hlh) (sub_pos.mpr (hlh.trans_le hhu))
  have hlim : Tendsto (fun i => B*ε i^((h-l)/(u-l))) p (𝓝 0) := by
    simpa only [mul_zero] using (hε.rpow_const_nhds_zero hθ).const_mul B
  have hsmall : ∀ᶠ i in p, ε i≤1 := hε.eventually (eventually_le_nhds zero_lt_one)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro δ hδ
  have hlt : ∀ᶠ i in p, B*ε i^((h-l)/(u-l))<δ :=
    hlim.eventually (eventually_lt_nhds hδ)
  filter_upwards [hsmall,hlt] with i hi hilt
  intro z hz
  simpa only [dist_zero_left] using
    (norm_le_mul_boundary_error_rpow hlh hhu (hd i) hB (hbound i)
      (hε0 i) hi (hupper i) hz).trans_lt hilt

end Complex.HadamardThreeLines
