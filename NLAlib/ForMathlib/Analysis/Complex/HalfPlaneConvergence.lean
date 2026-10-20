import NLAlib.ForMathlib.Analysis.Complex.StripConvergence

/-!
# Boundary convergence propagates throughout a half-plane

A holomorphic family with a common reciprocal-height bound and vanishing
uniform error on every sufficiently high line converges locally uniformly
on the entire half-plane. The proof uses actual quantitative three-lines
bounds on neighborhoods, including zero boundary errors and arbitrary nets.
-/

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Complex.HadamardThreeLines
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Vanishing high-line errors and a common reciprocal-real-part bound
give locally uniform convergence throughout the right half-plane. -/
theorem tendstoLocallyUniformlyOn_zero_of_right_boundary_error
    (F : ι → ℂ → E) (p : Filter ι) (C u₀ : ℝ) (hC : 0≤C)
    (hd : ∀ i, DifferentiableOn ℂ (F i) {z : ℂ | 0<z.re})
    (hb : ∀ i z, 0<z.re → ‖F i z‖≤C/z.re)
    (hu : ∀ u, u₀≤u → ∃ ε : ι → ℝ,
      (∀ i, 0≤ε i) ∧ Tendsto ε p (𝓝 0) ∧
        ∀ i z, z.re=u → ‖F i z‖≤ε i) :
    TendstoLocallyUniformlyOn F (fun _ => 0) p {z : ℂ | 0<z.re} := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro z hz
  change 0<z.re at hz
  let l : ℝ := z.re/4
  let h : ℝ := z.re/2
  let u : ℝ := max u₀ (z.re+1)
  have hl : 0<l := by dsimp [l]; linarith
  have hlh : l<h := by dsimp [l,h]; linarith
  have hhz : h<z.re := by dsimp [h]; linarith
  have hzu : z.re<u := (by linarith : z.re<z.re+1).trans_le (le_max_right _ _)
  have hhu : h≤u := hhz.le.trans hzu.le
  let B : ℝ := max 1 (C/l)
  have hB : 1≤B := le_max_left _ _
  have hbound (i : ι) (w : ℂ) (hw : w∈verticalClosedStrip l u) : ‖F i w‖≤B := by
    exact (hb i w (hl.trans_le hw.1)).trans
      ((div_le_div_of_nonneg_left hC hl hw.1).trans (le_max_right _ _))
  have hcl : closure (verticalStrip l u) ⊆ {w : ℂ | 0<w.re} := by
    have he : closure (verticalStrip l u) ⊆ {w : ℂ | l≤w.re} :=
      closure_minimal (fun _ hw => hw.1.le) (isClosed_le continuous_const continuous_re)
    exact fun w hw => hl.trans_le (he hw)
  have hdiff (i : ι) : DiffContOnCl ℂ (F i) (verticalStrip l u) :=
    ((hd i).mono hcl).diffContOnCl
  obtain ⟨ε,hε0,hε,hupper⟩ := hu u (le_max_left _ _)
  have hf := tendstoUniformlyOn_zero_of_upper_boundary_error F p hlh hhu hdiff hB hbound
    ε hε0 hε hupper
  refine ⟨verticalClosedStrip h u,?_,hf⟩
  apply mem_nhdsWithin_of_mem_nhds
  apply mem_of_superset ((isOpen_Ioo.preimage continuous_re).mem_nhds ⟨hhz,hzu⟩)
  intro w hw
  exact ⟨hw.1.le,hw.2.le⟩

end Complex.HadamardThreeLines

namespace Complex
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Vanishing high horizontal-line errors and a common reciprocal-height bound
give locally uniform convergence throughout the upper half-plane. -/
theorem tendstoLocallyUniformlyOn_zero_of_upper_boundary_error
    (F : ι → ℂ → E) (p : Filter ι) (C u₀ : ℝ) (hC : 0≤C)
    (hd : ∀ i, DifferentiableOn ℂ (F i) {z : ℂ | 0<z.im})
    (hb : ∀ i z, 0<z.im → ‖F i z‖≤C/z.im)
    (hu : ∀ u, u₀≤u → ∃ ε : ι → ℝ,
      (∀ i, 0≤ε i) ∧ Tendsto ε p (𝓝 0) ∧
        ∀ i z, z.im=u → ‖F i z‖≤ε i) :
    TendstoLocallyUniformlyOn F (fun _ => 0) p {z : ℂ | 0<z.im} := by
  let G : ι → ℂ → E := fun i w => F i (I*w)
  have hm : MapsTo (fun w : ℂ => I*w) {w | 0<w.re} {z | 0<z.im} := by
    intro w hw
    simpa only [mem_ofPred_eq,mul_im,I_re,zero_mul,I_im,one_mul,zero_add] using hw
  have hdG (i : ι) : DifferentiableOn ℂ (G i) {w : ℂ | 0<w.re} :=
    (hd i).comp (by fun_prop) hm
  have hbG (i : ι) (w : ℂ) (hw : 0<w.re) : ‖G i w‖≤C/w.re := by
    simpa only [mul_im,I_re,zero_mul,I_im,one_mul,zero_add] using hb i (I*w) (hm hw)
  have huG (u : ℝ) (hu₀ : u₀≤u) : ∃ ε : ι → ℝ,
      (∀ i, 0≤ε i) ∧ Tendsto ε p (𝓝 0) ∧
        ∀ i w, w.re=u → ‖G i w‖≤ε i := by
    obtain ⟨ε,hε0,hε,hεu⟩ := hu u hu₀
    refine ⟨ε,hε0,hε,?_⟩
    intro i w hw
    exact hεu i (I*w) (by simpa only [mul_im,I_re,zero_mul,I_im,one_mul,zero_add] using hw)
  have hg := HadamardThreeLines.tendstoLocallyUniformlyOn_zero_of_right_boundary_error
    G p C u₀ hC hdG hbG huG
  have hmi : MapsTo (fun z : ℂ => -I*z) {z | 0<z.im} {w | 0<w.re} := by
    intro z hz
    simpa only [mem_ofPred_eq,mul_re,neg_re,I_re,neg_zero,zero_mul,
      neg_im,I_im,neg_mul,one_mul,zero_sub,neg_neg] using hz
  have hc := hg.comp (fun z : ℂ => -I*z) hmi
    (continuous_const.mul continuous_id).continuousOn
  simpa only [G,Function.comp_def,← mul_assoc,mul_neg,I_mul_I,neg_neg,one_mul] using hc

end Complex
