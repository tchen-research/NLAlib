import NLAlib.Polynomial.OrthogonalPolynomials.StieltjesTransform
import NLAlib.ForMathlib.Analysis.Complex.CubicalCauchyFormula
import NLAlib.ForMathlib.Analysis.Complex.CubicalIntegralAlgebra
import NLAlib.ForMathlib.Analysis.Complex.CubicalIntegralBounds

/-! # General null-homologous-contour Gauss remainder

A finite signed C1 contour which is an actual continuous singular cubical
boundary in the holomorphy domain, and has winding one on the support,
represents the canonical Gauss error. The domain may be multiply connected.
Compact-support Fubini and the actual Cauchy theorem supply the analytic
identity; neither is assumed. Source: Gautschi (2004), Theorem 2.48.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial MeasureTheory Set Finset Complex
open scoped unitInterval
namespace NLAlib

/-- The source's actual Gauss remainder kernel `rho_n / pi_n`, using the
canonical monic orthogonal polynomial and its actual Cauchy integral. -/
def gaussRemainderKernel (μ : Measure ℝ) (hμ : HasPolynomialMoments μ) (n : ℕ) (z : ℂ) : ℂ :=
  (∫ x : ℝ, ((monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).map
    Complex.ofRealHom).eval (x : ℂ) / (z - (x : ℂ)) ∂μ) /
      ((monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom).eval z

/-- The actual Gauss remainder kernel equals the native transform error at
every point outside the support interval, including the zero-order rule. -/
theorem stieltjesTransform_sub_sum_gaussWeights_eq_gaussRemainderKernel
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn : (n : ℕ∞) ≤ μ.support.encard)
    {z : ℂ} (hz : ∀ x ∈ Icc a b, z ≠ (x : ℂ)) :
    stieltjesTransform μ z - ∑ i : Fin n, (gaussWeights μ hμ n i : ℂ) /
      (z - (gaussNodes μ hμ n i : ℂ)) = gaussRemainderKernel μ hμ n z := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp [gaussRemainderKernel, stieltjesTransform]
  · rw [← eval_map_secondKindPolynomial_div_eq_sum_gaussWeights_div hμ hs hn0 hn hz]
    exact stieltjesTransform_sub_secondKind_div_eq_integral hμ hs hn0 hn hz

/-- The canonical Gauss transform-error formula on an actual finite
null-homologous C1 contour. Its winding and domain hypotheses supply Cauchy;
the Cauchy formula itself is not a premise. -/
theorem integral_sub_gauss_eq_cubicalCurveIntegral_transform_kernel
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn : (n : ℕ∞) ≤ μ.support.encard)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω)
    (hI : ∀ x ∈ Icc a b, (x : ℂ) ∈ Ω) (Γ : Cubical.OneChain Ω)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    (hoff : ∀ γ ∈ Γ.support, ∀ r, ∀ x ∈ Icc a b, (γ r : ℂ) ≠ (x : ℂ))
    (hnull : Cubical.IsNullHomologous Γ)
    (hw : ∀ x ∈ Icc a b, cubicalWindingIntegral Γ (x : ℂ) = 1) :
    (∫ x : ℝ, f (x : ℂ) ∂μ) - ∑ i : Fin n, (gaussWeights μ hμ n i : ℂ) *
        f (gaussNodes μ hμ n i : ℂ) =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ * cubicalCurveIntegral
        (fun z => f z * (stieltjesTransform μ z - ∑ i : Fin n,
          (gaussWeights μ hμ n i : ℂ) / (z - (gaussNodes μ hμ n i : ℂ)))) Γ := by
  let : IsFiniteMeasure μ := hμ.isFiniteMeasure
  have hC (x : ℝ) (hx : x ∈ Icc a b) :=
    two_pi_i_inv_mul_cubicalCurveIntegral_div_sub_eq_of_isNullHomologous
      hΩ hf (hI x hx) Γ hΓ (fun γ hγ r => hoff γ hγ r x hx) hnull (hw x hx)
  have hμformula : (2 * Real.pi * Complex.I : ℂ)⁻¹ * cubicalCurveIntegral
      (fun z => f z * stieltjesTransform μ z) Γ = ∫ x : ℝ, f (x : ℂ) ∂μ := by
    change (2 * Real.pi * Complex.I : ℂ)⁻¹ * cubicalCurveIntegral
      (fun z => f z * (∫ x : ℝ, (z - (x : ℂ))⁻¹ ∂μ)) Γ = _
    rw [← integral_cubicalCurveIntegral_div_sub hs Γ hΓ hoff hf.continuousOn,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hs] with x hx
    exact hC x hx
  have hnode (γ : C(I, Ω)) (hγ : γ ∈ Γ.support) (i : Fin n) :
      CurveIntegrable (fun z => (f z / (z - (gaussNodes μ hμ n i : ℂ))) •
        ContinuousLinearMap.id ℂ ℂ) (cubicalPath γ) := by
    have hne (z : ℂ) (hz : z ∈ range (cubicalPath γ)) :
        z - (gaussNodes μ hμ n i : ℂ) ≠ 0 := by
      obtain ⟨r, rfl⟩ := hz
      exact sub_ne_zero.mpr (hoff γ hγ r _ (gaussNodes_mem_Icc hμ hs hn i))
    exact ((hf.continuousOn.mono (by rintro z ⟨r, rfl⟩; exact (γ r).property)).div
      (continuousOn_id.sub continuousOn_const) hne).smul continuousOn_const
      |>.curveIntegrable_of_contDiffOn (hΓ γ hγ) (fun r => mem_range_self r)
  have hweighted (γ : C(I, Ω)) (hγ : γ ∈ Γ.support) (i : Fin n) :
      CurveIntegrable (fun z => ((gaussWeights μ hμ n i : ℂ) *
        (f z / (z - (gaussNodes μ hμ n i : ℂ)))) • ContinuousLinearMap.id ℂ ℂ) (cubicalPath γ) := by
    have he : (fun z => ((gaussWeights μ hμ n i : ℂ) *
        (f z / (z - (gaussNodes μ hμ n i : ℂ)))) • ContinuousLinearMap.id ℂ ℂ) =
        (gaussWeights μ hμ n i : ℂ) • (fun z =>
          (f z / (z - (gaussNodes μ hμ n i : ℂ))) • ContinuousLinearMap.id ℂ ℂ) := by
      funext z
      exact mul_smul _ _ _
    rw [he]
    exact (hnode γ hγ i).smul
  have hsum : (fun z => f z * ∑ i : Fin n, (gaussWeights μ hμ n i : ℂ) /
      (z - (gaussNodes μ hμ n i : ℂ))) =
      fun z => ∑ i : Fin n, (gaussWeights μ hμ n i : ℂ) *
        (f z / (z - (gaussNodes μ hμ n i : ℂ))) := by
    funext z
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  have hGformula : (2 * Real.pi * Complex.I : ℂ)⁻¹ * cubicalCurveIntegral
      (fun z => f z * ∑ i : Fin n, (gaussWeights μ hμ n i : ℂ) /
        (z - (gaussNodes μ hμ n i : ℂ))) Γ =
      ∑ i : Fin n, (gaussWeights μ hμ n i : ℂ) * f (gaussNodes μ hμ n i : ℂ) := by
    rw [hsum, cubicalCurveIntegral_sum Γ _ hweighted]
    simp_rw [cubicalCurveIntegral_const_mul]
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    calc
      _ = (gaussWeights μ hμ n i : ℂ) * ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          cubicalCurveIntegral (fun z => f z / (z - (gaussNodes μ hμ n i : ℂ))) Γ) := by ring
      _ = _ := by rw [hC _ (gaussNodes_mem_Icc hμ hs hn i)]
  have hFint (γ : C(I, Ω)) (hγ : γ ∈ Γ.support) :
      CurveIntegrable (fun z => (f z * stieltjesTransform μ z) • ContinuousLinearMap.id ℂ ℂ)
        (cubicalPath γ) :=
    (curveIntegrable_and_integral_curveIntegral_div_sub hs (cubicalPath γ) (hΓ γ hγ)
      (fun t ht x hx => by rw [(cubicalPath γ).extend_apply ht]; exact hoff γ hγ ⟨t, ht⟩ x hx)
      (hf.continuousOn.mono (by rintro z ⟨r, rfl⟩; exact (γ r).property))).1
  have hGint (γ : C(I, Ω)) (hγ : γ ∈ Γ.support) :
      CurveIntegrable (fun z => (f z * ∑ i : Fin n, (gaussWeights μ hμ n i : ℂ) /
        (z - (gaussNodes μ hμ n i : ℂ))) • ContinuousLinearMap.id ℂ ℂ) (cubicalPath γ) := by
    have hne (z : ℂ) (hz : z ∈ range (cubicalPath γ)) (i : Fin n) :
        z - (gaussNodes μ hμ n i : ℂ) ≠ 0 := by
      obtain ⟨r, rfl⟩ := hz
      exact sub_ne_zero.mpr (hoff γ hγ r _ (gaussNodes_mem_Icc hμ hs hn i))
    have hc : ContinuousOn (fun z => f z * ∑ i : Fin n, (gaussWeights μ hμ n i : ℂ) /
        (z - (gaussNodes μ hμ n i : ℂ))) (range (cubicalPath γ)) :=
      (hf.continuousOn.mono (by rintro z ⟨r, rfl⟩; exact (γ r).property)).mul
        (continuousOn_finsetSum _ (fun i _ => continuousOn_const.div
          (continuousOn_id.sub continuousOn_const) (fun z hz => hne z hz i)))
    exact (hc.smul continuousOn_const).curveIntegrable_of_contDiffOn (hΓ γ hγ)
      (fun r => mem_range_self r)
  have heq : (fun z => f z * (stieltjesTransform μ z - ∑ i : Fin n,
      (gaussWeights μ hμ n i : ℂ) / (z - (gaussNodes μ hμ n i : ℂ)))) =
      fun z => f z * stieltjesTransform μ z - f z * ∑ i : Fin n,
        (gaussWeights μ hμ n i : ℂ) / (z - (gaussNodes μ hμ n i : ℂ)) := by
    funext z
    ring
  rw [heq, cubicalCurveIntegral_sub Γ _ _ hFint hGint, mul_sub, hμformula, hGformula]

/-- The actual `rho_n / pi_n` Gauss remainder formula for an arbitrary finite
null-homologous C1 cycle with winding one on the real support. Polynomial
moments follow from the stated compact support and finite mass. The actual
continuous filling, scalar Cauchy formula and Fubini interchange are all
proved, and no simple-connectedness is required of the holomorphy domain.
Source: Gautschi (2004), Theorem 2.48, null-homologous-cycle alternative.
atlas: gauss-remainder-contour-kernel (partial) -/
theorem integral_sub_gauss_eq_cubicalCurveIntegral_gaussRemainderKernel
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn : (n : ℕ∞) ≤ μ.support.encard)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω)
    (hI : ∀ x ∈ Icc a b, (x : ℂ) ∈ Ω) (Γ : Cubical.OneChain Ω)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    (hoff : ∀ γ ∈ Γ.support, ∀ r, ∀ x ∈ Icc a b, (γ r : ℂ) ≠ (x : ℂ))
    (hnull : Cubical.IsNullHomologous Γ)
    (hw : ∀ x ∈ Icc a b, cubicalWindingIntegral Γ (x : ℂ) = 1) :
    let hμ := hasPolynomialMoments_of_ae_mem_Icc hs
    (∫ x : ℝ, f (x : ℂ) ∂μ) - ∑ i : Fin n, (gaussWeights μ hμ n i : ℂ) *
        f (gaussNodes μ hμ n i : ℂ) =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ * cubicalCurveIntegral
        (fun z => f z * gaussRemainderKernel μ hμ n z) Γ := by
  dsimp only
  rw [integral_sub_gauss_eq_cubicalCurveIntegral_transform_kernel
    (hasPolynomialMoments_of_ae_mem_Icc hs) hs hn hΩ hf hI Γ hΓ hoff hnull hw]
  congr 1
  apply cubicalCurveIntegral_congr
  intro γ hγ r
  rw [stieltjesTransform_sub_sum_gaussWeights_eq_gaussRemainderKernel _ hs hn (hoff γ hγ r)]

/-- The actual general-cycle Gauss error obeys the standard total-length
bound with any nonnegative uniform bounds for the kernel and integrand.
In particular, their actual maxima on the compact contour may be used.
Source: Gautschi (2004), Theorem 2.48, null-homologous-cycle alternative.
atlas: gauss-remainder-contour-kernel (partial) -/
theorem norm_integral_sub_gauss_le_cubicalLength_mul_bounds
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn : (n : ℕ∞) ≤ μ.support.encard)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω)
    (hI : ∀ x ∈ Icc a b, (x : ℂ) ∈ Ω) (Γ : Cubical.OneChain Ω)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    (hoff : ∀ γ ∈ Γ.support, ∀ r, ∀ x ∈ Icc a b, (γ r : ℂ) ≠ (x : ℂ))
    (hnull : Cubical.IsNullHomologous Γ)
    (hw : ∀ x ∈ Icc a b, cubicalWindingIntegral Γ (x : ℂ) = 1)
    {K F : ℝ} (hF0 : 0 ≤ F)
    (hK : ∀ γ ∈ Γ.support, ∀ r,
      ‖gaussRemainderKernel μ (hasPolynomialMoments_of_ae_mem_Icc hs) n (γ r : ℂ)‖ ≤ K)
    (hF : ∀ γ ∈ Γ.support, ∀ r, ‖f (γ r : ℂ)‖ ≤ F) :
    let hμ := hasPolynomialMoments_of_ae_mem_Icc hs
    ‖(∫ x : ℝ, f (x : ℂ) ∂μ) - ∑ i : Fin n, (gaussWeights μ hμ n i : ℂ) *
      f (gaussNodes μ hμ n i : ℂ)‖ ≤ cubicalLength Γ / (2 * Real.pi) * K * F := by
  dsimp only
  rw [integral_sub_gauss_eq_cubicalCurveIntegral_gaussRemainderKernel hs hn hΩ hf hI Γ hΓ hoff hnull hw]
  have h := norm_two_pi_i_inv_mul_cubicalCurveIntegral_le_length_mul Γ
    (fun z => f z * gaussRemainderKernel μ (hasPolynomialMoments_of_ae_mem_Icc hs) n z) hΓ
    (C := F * K) (fun γ hγ r => by
      rw [norm_mul]
      exact mul_le_mul (hF γ hγ r) (hK γ hγ r) (norm_nonneg _) hF0)
  convert h using 1
  ring

end NLAlib
