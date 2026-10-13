import NLAlib.Polynomial.BestApproximation.InterpolationPeakSmoothness

/-!
# Implicit charts for actual interpolation gap peaks

The ordinary scalar implicit function theorem tracks the unique nondegenerate
critical point. The maximum value is therefore continuously differentiable.
-/

noncomputable section
open Polynomial Real Set Filter
open scoped Topology ContDiff
namespace NLAlib

private theorem isInvertible_smulRight_one {c : ℝ} (hc : c ≠ 0) :
    ((1 : ℝ →L[ℝ] ℝ).smulRight c).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := (1 : ℝ →L[ℝ] ℝ).smulRight c⁻¹)
  · ext
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self, smul_eq_mul, ContinuousLinearMap.id_apply]
    field_simp
  · ext
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self, smul_eq_mul, ContinuousLinearMap.id_apply]
    field_simp

/-- The unique critical point of each actual node gap admits a local `C¹`
implicit chart, and the actual peak equals its polynomial value on that chart.
Source: ordinary implicit function theorem at a nondegenerate scalar maximum;
focused reroutes, peak charts. -/
theorem exists_contDiffAt_interpolationGapPeak_chart {n : ℕ} (hn : 0 < n)
    {t : Fin n → ℝ} (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) :
    ∃ τ : (Fin n → ℝ) → ℝ, ContDiffAt ℝ 1 τ t ∧
      τ t ∈ Ioo (canonicalIntervalNodes n t i.castSucc) (canonicalIntervalNodes n t i.succ) ∧
      (interpolationGapPolynomial n t i).derivative.eval (τ t) = 0 ∧
      ∀ᶠ s in 𝓝 t, s ∈ interiorNodeSimplex n ∧
        τ s ∈ Ioo (canonicalIntervalNodes n s i.castSucc) (canonicalIntervalNodes n s i.succ) ∧
        (interpolationGapPolynomial n s i).derivative.eval (τ s) = 0 ∧
        interpolationGapPeak n s i = (interpolationGapPolynomial n s i).eval (τ s) := by
  obtain ⟨τ₀, hτ₀, hc, hcc, _, _, _⟩ := exists_interpolationGapPeak_nondegenerate hn ht i
  let G : (Fin n → ℝ) × ℝ → ℝ := fun u => (interpolationGapPolynomial n u.1 i).derivative.eval u.2
  have hG : ContDiffAt ℝ 1 G (t, τ₀) := contDiffAt_eval_derivative_interpolationGapPolynomial ht i τ₀ 1
  have hinr : HasFDerivAt (fun y : ℝ => (t, y)) (ContinuousLinearMap.inr ℝ (Fin n → ℝ) ℝ) τ₀ := by
    have hd := (hasFDerivAt_const (𝕜 := ℝ) t τ₀).prodMk (hasFDerivAt_id (𝕜 := ℝ) τ₀)
    have heq : (0 : ℝ →L[ℝ] (Fin n → ℝ)).prod (ContinuousLinearMap.id ℝ ℝ) =
        ContinuousLinearMap.inr ℝ (Fin n → ℝ) ℝ := by ext y <;> simp
    rw [heq] at hd
    exact hd
  have hpartial := hG.differentiableAt_one.hasFDerivAt.comp τ₀ hinr
  have heq : fderiv ℝ G (t, τ₀) ∘L ContinuousLinearMap.inr ℝ (Fin n → ℝ) ℝ =
      (1 : ℝ →L[ℝ] ℝ).smulRight ((interpolationGapPolynomial n t i).derivative.derivative.eval τ₀) :=
    hpartial.unique ((interpolationGapPolynomial n t i).derivative.hasFDerivAt τ₀)
  have hinvert : (fderiv ℝ G (t, τ₀) ∘L ContinuousLinearMap.inr ℝ (Fin n → ℝ) ℝ).IsInvertible := by
    rw [heq]
    exact isInvertible_smulRight_one hcc.ne
  let τ := hG.implicitFunction (by norm_num : (1 : ℕ∞ω) ≠ 0) hinvert
  have hτself : τ t = τ₀ := hG.implicitFunction_apply_self (by norm_num) hinvert
  have hτdiff : ContDiffAt ℝ 1 τ t := hG.contDiffAt_implicitFunction (by norm_num) hinvert
  have hτcrit : ∀ᶠ s in 𝓝 t, (interpolationGapPolynomial n s i).derivative.eval (τ s) = 0 := by
    have h := hG.eventually_apply_implicitFunction (by norm_num) hinvert
    change ∀ᶠ s in 𝓝 t, G (s, τ s) = G (t, τ₀) at h
    simpa only [G, hc] using h
  have hs : ∀ᶠ s in 𝓝 t, s ∈ interiorNodeSimplex n := (isOpen_interiorNodeSimplex n).mem_nhds ht
  have hl : ∀ᶠ s in 𝓝 t, canonicalIntervalNodes n s i.castSucc < τ s :=
    (continuous_canonicalIntervalNodes n i.castSucc).continuousAt.eventually_lt hτdiff.continuousAt
      (by rw [hτself]; exact hτ₀.1)
  have hr : ∀ᶠ s in 𝓝 t, τ s < canonicalIntervalNodes n s i.succ :=
    hτdiff.continuousAt.eventually_lt (continuous_canonicalIntervalNodes n i.succ).continuousAt
      (by rw [hτself]; exact hτ₀.2)
  refine ⟨τ, hτdiff, by rwa [hτself], by rwa [hτself], ?_⟩
  filter_upwards [hs, hl, hr, hτcrit] with s hs hl hr hc
  obtain ⟨ξ, hξ, _, _, _, hpeak, huniq⟩ := exists_interpolationGapPeak_nondegenerate hn hs i
  have hτξ : τ s = ξ := huniq (τ s) ⟨hl, hr⟩ hc
  exact ⟨hs, ⟨hl, hr⟩, hc, by rw [hτξ]; exact hpeak⟩

/-- Each actual interpolation gap peak is `C¹` on the ordered node simplex.
Source: the unique nondegenerate critical-point chart and the smooth signed
cardinal formula; focused reroutes, the peak map. -/
theorem contDiffAt_interpolationGapPeak {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) :
    ContDiffAt ℝ 1 (fun s => interpolationGapPeak n s i) t := by
  obtain ⟨τ, hτdiff, _, _, hevent⟩ := exists_contDiffAt_interpolationGapPeak_chart hn ht i
  have heval := contDiffAt_eval_interpolationGapPolynomial ht i (τ t) 1
  have hinput : ContDiffAt ℝ 1 (fun s : Fin n → ℝ => (s, τ s)) t := contDiffAt_id.prodMk hτdiff
  have hcomp : ContDiffAt ℝ 1 (fun s => (interpolationGapPolynomial n s i).eval (τ s)) t := by
    exact heval.comp t hinput
  exact hcomp.congr_of_eventuallyEq (hevent.mono (fun s hs => hs.2.2.2))

end NLAlib
