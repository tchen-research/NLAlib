import NLAlib.Polynomial.Quadrature.ComplexConvergence
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.Equicontinuity

/-! # Locally uniform Markov convergence

All Gauss transforms have the same support-distance continuity modulus because
their positive weights have the original mass. Compactness upgrades the native
pointwise Markov theorem to convergence uniformly on every compact set outside
the support interval. Source: Gautschi (2004), Chapter 1, Markov theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial MeasureTheory Set Finset Filter
open scoped Topology
namespace NLAlib

private theorem norm_sum_gaussWeights_div_sub_le
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn0 : 0 < n)
    (hn : (n : ℕ∞) ≤ μ.support.encard) {z w : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hz : ∀ x ∈ Icc a b, δ ≤ ‖z-(x:ℂ)‖)
    (hw : ∀ x ∈ Icc a b, δ ≤ ‖w-(x:ℂ)‖) :
    ‖(∑ i : Fin n, (gaussWeights μ hμ n i : ℂ)/(z-(gaussNodes μ hμ n i:ℂ))) -
      (∑ i : Fin n, (gaussWeights μ hμ n i : ℂ)/(w-(gaussNodes μ hμ n i:ℂ)))‖ ≤
        μ.real univ / δ^2 * ‖z-w‖ := by
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin n, ‖(gaussWeights μ hμ n i : ℂ)/(z-(gaussNodes μ hμ n i:ℂ)) -
        (gaussWeights μ hμ n i : ℂ)/(w-(gaussNodes μ hμ n i:ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n, gaussWeights μ hμ n i * (‖z-w‖/δ^2) := by
      apply sum_le_sum
      intro i _
      let t := gaussNodes μ hμ n i
      have ht := gaussNodes_mem_Icc hμ hs hn i
      have hz0 : z-(t:ℂ) ≠ 0 := norm_pos_iff.mp (hδ.trans_le (hz t ht))
      have hw0 : w-(t:ℂ) ≠ 0 := norm_pos_iff.mp (hδ.trans_le (hw t ht))
      rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_sub, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (gaussWeights_pos hμ hn i)]
      apply mul_le_mul_of_nonneg_left _ (gaussWeights_pos hμ hn i).le
      change ‖(z-(t:ℂ))⁻¹-(w-(t:ℂ))⁻¹‖ ≤ _
      rw [← dist_eq_norm, dist_inv_inv₀ hz0 hw0, dist_sub_right, dist_eq_norm]
      apply div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hδ)
      simpa only [pow_two] using mul_le_mul (hz t ht) (hw t ht) hδ.le (norm_nonneg _)
    _ = _ := by
      rw [← sum_mul, sum_gaussWeights_eq_measure_univ hμ hn0 hn]
      simp only [measureReal_def, div_mul_eq_mul_div, mul_div_assoc]

/-- Actual second-kind ratios converge uniformly on every compact set of
complex points outside the real support enclosure. Infinite support makes all
orders available; finite-support terminal rules are already exactly atomic.
Source: Gautschi (2004), Markov theorem; operator derivations AQ20.
atlas: jacobi-fraction-second-kind (partial) -/
theorem tendstoUniformlyOn_secondKindPolynomial_div_stieltjesTransform
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) (hinf : μ.support.Infinite) {K : Set ℂ}
    (hK : IsCompact K) (hoff : ∀ z ∈ K, ∀ x ∈ Icc a b, z ≠ (x : ℂ)) :
    TendstoUniformlyOn (fun n z =>
      ((secondKindPolynomial (polynomialIntegral μ hμ) (n+1)).map Complex.ofRealHom).eval z /
        ((monicOrthogonalPolynomial (polynomialIntegral μ hμ) (n+1)).map Complex.ofRealHom).eval z)
      (stieltjesTransform μ) atTop K := by
  let : IsFiniteMeasure μ := hμ.isFiniteMeasure
  by_cases hKne : K.Nonempty
  · have hI : (Icc a b).Nonempty := by
      obtain ⟨x, hx⟩ := hinf.nonempty
      exact ⟨x, Measure.support_subset_of_isClosed isClosed_Icc hs hx⟩
    have hcompact := hK.prod (isCompact_Icc (a:=a) (b:=b))
    obtain ⟨u, hu, hmin⟩ := hcompact.exists_isMinOn (hKne.prod hI)
      (show ContinuousOn (fun zx : ℂ × ℝ => ‖zx.1-(zx.2:ℂ)‖) (K ×ˢ Icc a b) by fun_prop)
    let δ := ‖u.1-(u.2:ℂ)‖
    have hδ : 0 < δ := norm_pos_iff.mpr (sub_ne_zero.mpr (hoff u.1 hu.1 u.2 hu.2))
    have hgap (z : K) (x : ℝ) (hx : x ∈ Icc a b) : δ ≤ ‖(z:ℂ)-(x:ℂ)‖ :=
      (isMinOn_iff.mp hmin) ((z:ℂ),x) ⟨z.2,hx⟩
    let F : ℕ → K → ℂ := fun n z =>
      ∑ i : Fin (n+1), (gaussWeights μ hμ (n+1) i : ℂ) /
        ((z:ℂ)-(gaussNodes μ hμ (n+1) i:ℂ))
    let C := μ.real univ/δ^2
    have hbound (z w : K) (n : ℕ) : dist (F n z) (F n w) ≤ C * dist z w := by
      simpa only [F, C, dist_eq_norm, Subtype.dist_eq] using
        norm_sum_gaussWeights_div_sub_le hμ hs (Nat.zero_lt_succ n)
          (by rw [hinf.encard_eq]; simp) hδ (hgap z) (hgap w)
    have hequi : Equicontinuous F := Metric.equicontinuous_of_continuity_modulus
      (fun t : ℝ => C*t)
      (by simpa only [mul_zero] using
        (show Continuous (fun t : ℝ => C*t) from continuous_const.mul continuous_id).tendsto (0:ℝ)) F hbound
    let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    have hpoint : Tendsto F atTop (𝓝 (fun z : K => stieltjesTransform μ z)) := by
      apply tendsto_pi_nhds.mpr
      intro z
      have h := tendsto_secondKindPolynomial_div_stieltjesTransform hμ hs hinf (hoff z z.2)
      convert! h using 1
      funext n
      exact (eval_map_secondKindPolynomial_div_eq_sum_gaussWeights_div hμ hs (Nat.zero_lt_succ n)
        (by rw [hinf.encard_eq]; simp) (hoff z z.2)).symm
    have huniform := (hequi.tendsto_uniformFun_iff_pi atTop
      (fun z : K => stieltjesTransform μ z)).mpr hpoint
    have huniform' := UniformFun.tendsto_iff_tendstoUniformly.mp huniform
    rw [tendstoUniformlyOn_iff_restrict]
    convert! huniform' using 1
    funext n z
    exact eval_map_secondKindPolynomial_div_eq_sum_gaussWeights_div hμ hs (Nat.zero_lt_succ n)
      (by rw [hinf.encard_eq]; simp) (hoff z z.2)
  · rw [Set.not_nonempty_iff_eq_empty.mp hKne]
    exact tendstoUniformlyOn_empty

end NLAlib
