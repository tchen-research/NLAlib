import NLAlib.Polynomial.Quadrature.GaussCubicalContour
import NLAlib.ForMathlib.MeasureTheory.CompactSupportContinuity
import NLAlib.ForMathlib.MeasureTheory.IntervalSupport

/-! # Continuity of the actual Gauss remainder kernel on compact contours

Compact-support dominated continuity gives the native Stieltjes transform's
continuity on a compact pole-free set. The actual finite atomic transform
identity then gives continuity of `rho_n/pi_n` without an assumed analytic
kernel certificate. Source: Gautschi (2004), Theorem 2.48.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial MeasureTheory Set Finset
namespace NLAlib

/-- The actual Stieltjes transform is continuous on any compact set disjoint
from the finite measure's compact support enclosure. -/
theorem continuousOn_stieltjesTransform_of_compact_off_Icc
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {K : Set ℂ} (hK : IsCompact K)
    (hoff : ∀ z ∈ K, ∀ x ∈ Icc a b, z ≠ (x : ℂ)) :
    ContinuousOn (stieltjesTransform μ) K := by
  have hsupport : μ.support ⊆ Icc a b := μ.support_subset_of_isClosed isClosed_Icc hs
  apply continuousOn_integral_of_continuousOn_compact_support μ
    (μ.isCompact_support_of_subset_Icc hsupport) hK
  exact (continuous_fst.continuousOn.sub
    (Complex.continuous_ofReal.comp continuous_snd).continuousOn).inv₀
      (fun p hp => sub_ne_zero.mpr (hoff p.1 hp.1 p.2 (hsupport hp.2)))

/-- The actual `rho_n/pi_n` remainder kernel is continuous on each compact
set disjoint from the support interval, including the zero-order rule. -/
theorem continuousOn_gaussRemainderKernel_of_compact_off_Icc
    {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : HasPolynomialMoments μ) {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn : (n : ℕ∞) ≤ μ.support.encard)
    {K : Set ℂ} (hK : IsCompact K)
    (hoff : ∀ z ∈ K, ∀ x ∈ Icc a b, z ≠ (x : ℂ)) :
    ContinuousOn (gaussRemainderKernel μ hμ n) K := by
  have hS := continuousOn_stieltjesTransform_of_compact_off_Icc hs hK hoff
  have hG : ContinuousOn (fun z => ∑ i : Fin n, (gaussWeights μ hμ n i : ℂ) /
      (z - (gaussNodes μ hμ n i : ℂ))) K := by
    apply continuousOn_finsetSum
    intro i _
    exact continuousOn_const.div (continuousOn_id.sub continuousOn_const)
      (fun z hz => sub_ne_zero.mpr (hoff z hz _ (gaussNodes_mem_Icc hμ hs hn i)))
  apply (hS.sub hG).congr
  intro z hz
  exact (stieltjesTransform_sub_sum_gaussWeights_eq_gaussRemainderKernel hμ hs hn (hoff z hz)).symm

end NLAlib
