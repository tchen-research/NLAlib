import NLAlib.ForMathlib.Analysis.CStarAlgebra.ResolventParameter
import NLAlib.ForMathlib.Analysis.CStarAlgebra.SpectrumPerturbation

/-!
# Actual spectral comparison across complex C-star algebras

The scalar functional calculus attains a self-adjoint resolvent norm on the
actual spectrum, including continuous spectra. Two elements may belong to
different algebras. Exact parameter continuity then lifts a finite-grid
resolvent comparison to a genuine directed spectral inclusion.
Source: deterministic extension of arXiv:2201.05142v3, Lemma 7.1.
-/

noncomputable section
set_option autoImplicit false
open scoped ContinuousFunctionalCalculus

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

private theorem nonreal_sub_ne_zero {a : A} (ha : IsSelfAdjoint a)
    {z : ℂ} (hz : z.im ≠ 0) {x : ℂ} (hx : x ∈ spectrum ℂ a) : z - x ≠ 0 := by
  intro h
  have he := congrArg Complex.im (sub_eq_zero.mp h)
  have hr := ha.mem_spectrum_eq_re hx
  rw [hr] at he
  exact hz (by simpa using he)

/-- An actual real spectral point attains a nonreal self-adjoint resolvent norm in any nontrivial complex C-star algebra. -/
theorem IsSelfAdjoint.exists_mem_spectrum_real_norm_resolvent_eq [Nontrivial A]
    {a : A} (ha : IsSelfAdjoint a) {z : ℂ} (hz : z.im ≠ 0) :
    ∃ β ∈ spectrum ℝ a, ‖resolvent a z‖ = ‖z - (β : ℂ)‖⁻¹ := by
  have hf : ContinuousOn (fun x : ℂ => (z - x)⁻¹) (spectrum ℂ a) :=
    (continuous_const.sub continuous_id).continuousOn.inv₀
      (fun x hx => nonreal_sub_ne_zero ha hz hx)
  obtain ⟨x, hx, he⟩ := (IsGreatest.norm_cfc (fun x : ℂ => (z - x)⁻¹) a hf ha.isStarNormal).1
  have hr := ha.mem_spectrum_eq_re hx
  refine ⟨x.re, spectrum.of_algebraMap_mem ℂ (hr ▸ hx), ?_⟩
  rw [ha.resolvent_eq_cfc_of_im_ne_zero hz, ← he]
  change ‖(z - x)⁻¹‖ = ‖z - (x.re : ℂ)‖⁻¹
  rw [norm_inv, ← hr]

/-- Directly above an actual real spectral point the native self-adjoint resolvent norm is exactly inverse height. -/
theorem IsSelfAdjoint.norm_resolvent_eq_inv_of_mem_spectrum_real
    {a : A} (ha : IsSelfAdjoint a) {ξ η : ℝ}
    (hξ : ξ ∈ spectrum ℝ a) (hη : 0 < η) :
    ‖resolvent a ((ξ : ℂ) + (η : ℂ) * Complex.I)‖ = η⁻¹ := by
  let z : ℂ := (ξ : ℂ) + (η : ℂ) * Complex.I
  have hz : z.im ≠ 0 := by simpa only [z, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
    mul_one, mul_zero, add_zero, zero_add] using hη.ne'
  apply le_antisymm
  · simpa only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
      add_zero, zero_add, abs_of_pos hη] using ha.norm_resolvent_le hz
  · have hf : ContinuousOn (fun x : ℂ => (z - x)⁻¹) (spectrum ℂ a) :=
      (continuous_const.sub continuous_id).continuousOn.inv₀
        (fun x hx => nonreal_sub_ne_zero ha hz hx)
    have hb := norm_apply_le_norm_cfc (fun x : ℂ => (z - x)⁻¹) a
      (spectrum.algebraMap_mem ℂ hξ) hf ha.isStarNormal
    rw [← ha.resolvent_eq_cfc_of_im_ne_zero hz] at hb
    change ‖(z - (ξ : ℂ))⁻¹‖ ≤ ‖resolvent a z‖ at hb
    have he : ‖(z - (ξ : ℂ))⁻¹‖ = η⁻¹ := by
      dsimp only [z]
      rw [show (ξ : ℂ) + (η : ℂ) * Complex.I - (ξ : ℂ) = (η : ℂ) * Complex.I by ring]
      rw [norm_inv, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, abs_of_pos hη]
    rwa [he] at hb

/-- A genuine resolvent comparison produces a nearby actual target spectral point, even in a different C-star algebra. -/
theorem IsSelfAdjoint.exists_mem_spectrum_real_dist_le_of_resolvent_comparison
    [Nontrivial B] {a : A} {b : B} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    {ξ η C δ : ℝ} (hξ : ξ ∈ spectrum ℝ a) (hη : 0 < η)
    (hδ : δ ≤ (2 * η)⁻¹)
    (hcmp : ‖resolvent a ((ξ : ℂ) + (η : ℂ) * Complex.I)‖ ≤
      C * ‖resolvent b ((ξ : ℂ) + (η : ℂ) * Complex.I)‖ + δ) :
    ∃ β ∈ spectrum ℝ b, dist ξ β ≤ 2 * C * η := by
  have hz : ((ξ : ℂ) + (η : ℂ) * Complex.I).im ≠ 0 := by simpa using hη.ne'
  obtain ⟨β, hβ, hn⟩ := hb.exists_mem_spectrum_real_norm_resolvent_eq hz
  rw [ha.norm_resolvent_eq_inv_of_mem_spectrum_real hξ hη, hn] at hcmp
  have hdpos : 0 < ‖(ξ : ℂ) + (η : ℂ) * Complex.I - (β : ℂ)‖ := by
    apply norm_pos_iff.mpr
    intro he
    exact hz (by simpa using congrArg Complex.im he)
  have hhalf : (2 * η)⁻¹ ≤ C * ‖(ξ : ℂ) + (η : ℂ) * Complex.I - (β : ℂ)‖⁻¹ := by
    have hs : η⁻¹ = 2 * (2 * η)⁻¹ := by field_simp
    linarith
  have hnormle : ‖(ξ : ℂ) + (η : ℂ) * Complex.I - (β : ℂ)‖ ≤ 2 * C * η := by
    have hs := mul_le_mul_of_nonneg_right hhalf hdpos.le
    rw [mul_assoc, inv_mul_cancel₀ hdpos.ne', mul_one] at hs
    have hm := mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ 2 * η)
    have he : ((2 * η)⁻¹ * ‖(ξ : ℂ) + (η : ℂ) * Complex.I - (β : ℂ)‖) * (2 * η) =
        ‖(ξ : ℂ) + (η : ℂ) * Complex.I - (β : ℂ)‖ := by field_simp
    rw [he] at hm
    nlinarith
  refine ⟨β, hβ, le_trans ?_ hnormle⟩
  simpa only [Real.dist_eq, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero,
    mul_one, sub_zero, add_zero] using
      Complex.abs_re_le_norm ((ξ : ℂ) + (η : ℂ) * Complex.I - (β : ℂ))

/-- A finite covering net and native resolvent comparisons give actual directed spectral inclusion across different C-star algebras.
Source: arXiv:2201.05142v3, Lemma 7.1 and Proposition 7.7.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem IsSelfAdjoint.forall_exists_mem_spectrum_real_dist_le_of_resolvent_net
    [Nontrivial B] {a : A} {b : B} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (N : Set ℝ) {η C δ ε : ℝ} (hη : 0 < η) (hC : 0 ≤ C)
    (hcover : ∀ ξ ∈ spectrum ℝ a, ∃ u ∈ N, |ξ-u| ≤ ε)
    (hcmp : ∀ u ∈ N,
      ‖resolvent a ((u : ℂ)+(η : ℂ)*Complex.I)‖ ≤
        C*‖resolvent b ((u : ℂ)+(η : ℂ)*Complex.I)‖+δ)
    (herror : δ+(C+1)*ε/η^2 ≤ (2*η)⁻¹) :
    ∀ ξ ∈ spectrum ℝ a, ∃ β ∈ spectrum ℝ b, dist ξ β ≤ 2*C*η := by
  intro ξ hξ
  obtain ⟨u, hu, hdist⟩ := hcover ξ hξ
  have hl := ha.abs_norm_resolvent_real_sub_le ξ u hη.ne'
  have hr := hb.abs_norm_resolvent_real_sub_le u ξ hη.ne'
  rw [abs_sub_comm u ξ] at hr
  have hd := div_le_div_of_nonneg_right hdist (sq_nonneg η)
  have hl' := (le_abs_self _).trans (hl.trans hd)
  have hr' := (le_abs_self _).trans (hr.trans hd)
  have hg := hcmp u hu
  have hm := mul_le_mul_of_nonneg_left hr' hC
  apply ha.exists_mem_spectrum_real_dist_le_of_resolvent_comparison hb hξ hη herror
  rw [show δ+(C+1)*ε/η^2 = δ+ε/η^2+C*(ε/η^2) by ring]
  linear_combination hl' + hg + hm
