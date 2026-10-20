import NLAlib.Probability.Gaussian.Calculus.ParameterDerivativeEvaluation
import NLAlib.ForMathlib.MeasureTheory.AffineDifferentiation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Exact variance-weighted Gaussian interpolation

The actual square-root interpolation of two independent native Gaussian
laws differentiates into the full difference of their covariance matrices.
Source: Bandeira--Boedihardjo--van Handel, arXiv:2108.06312v2, Lemma 4.11.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter
namespace NLAlib
variable {κ F : Type*} [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
local notation "E" => κ → ℝ

/-- The exact source Gaussian variance interpolation derivative for bounded
C² Banach-valued tests. Both centered Gaussian laws are the native measures,
their independent coupling is their literal product, and every covariance
entry is the actual real-coordinate covariance. Singular laws and empty
coordinate types are included. The formula holds at every interior time;
bounded tests also have continuous expectations at both endpoints.
Source: Bandeira--Boedihardjo--van Handel, arXiv:2108.06312v2, Lemma 4.11. -/
theorem hasDerivAt_integral_gaussian_sqrt_interpolation
    (γY γZ : Measure E) [IsGaussian γY] [IsGaussian γZ]
    (hYmean : (∫ y : E, y ∂γY)=0) (hZmean : (∫ z : E, z ∂γZ)=0)
    (f : E → F) (df : E → E →L[ℝ] F) (ddf : E → E →L[ℝ] E →L[ℝ] F)
    (hf : ∀ x, HasFDerivAt f (df x) x)
    (hdf : ∀ x, HasFDerivAt df (ddf x) x) (hddfc : Continuous ddf)
    (C₀ C₁ C₂ : ℝ) (hfb : ∀ x, ‖f x‖≤C₀)
    (hdfb : ∀ x, ‖df x‖≤C₁) (hddfb : ∀ x, ‖ddf x‖≤C₂)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    HasDerivAt
      (fun s : ℝ => ∫ q : E×E, f (Real.sqrt s•q.1+Real.sqrt (1-s)•q.2) ∂γY.prod γZ)
      ((1/2 : ℝ) • ∑ i, ∑ j,
        (cov[(fun z : E => z i),(fun z : E => z j);γY]-
          cov[(fun z : E => z i),(fun z : E => z j);γZ]) •
          ∫ q : E×E, ddf (Real.sqrt t•q.1+Real.sqrt (1-t)•q.2)
            (Pi.single j 1) (Pi.single i 1) ∂γY.prod γZ) t := by
  have hdfc : Continuous df := continuous_iff_continuousAt.mpr fun x => (hdf x).continuousAt
  have hC₁ : 0≤C₁ := (norm_nonneg (df 0)).trans (hdfb 0)
  let a := Real.sqrt t
  let b := Real.sqrt (1-t)
  let W (q : E×E) := a•q.1+b•q.2
  let G (i j : κ) (q : E×E) := ddf (W q) (Pi.single j 1) (Pi.single i 1)
  have hYint : Integrable (fun q : E×E => q.1) (γY.prod γZ) :=
    (IsGaussian.integrable_id (μ := γY)).comp_fst γZ
  have hZint : Integrable (fun q : E×E => q.2) (γY.prod γZ) :=
    (IsGaussian.integrable_id (μ := γZ)).comp_snd γY
  have hiY : Integrable (fun q : E×E => df (W q) q.1) (γY.prod γZ) := by
    have hc : Continuous (fun q : E×E => df (W q) q.1) := by dsimp only [W]; fun_prop
    apply Integrable.mono' (hYint.norm.const_mul C₁) hc.aestronglyMeasurable
    exact Eventually.of_forall fun q => ((df _).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hdfb _) (norm_nonneg _))
  have hiZ : Integrable (fun q : E×E => df (W q) q.2) (γY.prod γZ) := by
    have hc : Continuous (fun q : E×E => df (W q) q.2) := by dsimp only [W]; fun_prop
    apply Integrable.mono' (hZint.norm.const_mul C₁) hc.aestronglyMeasurable
    exact Eventually.of_forall fun q => ((df _).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hdfb _) (norm_nonneg _))
  have hZ : (∫ q : E×E, df (W q) q.2 ∂γY.prod γZ) =
      b • ∑ i, ∑ j, cov[(fun z : E => z i),(fun z : E => z j);γZ] •
        ∫ q, G i j q ∂γY.prod γZ :=
    integral_apply_gaussian_affine γY γZ hZmean a b df ddf hdf hddfc C₁ C₂ hdfb hddfb
  have hY : (∫ q : E×E, df (W q) q.1 ∂γY.prod γZ) =
      a • ∑ i, ∑ j, cov[(fun z : E => z i),(fun z : E => z j);γY] •
        ∫ q, G i j q ∂γY.prod γZ := by
    have hh := integral_apply_gaussian_affine γZ γY hYmean b a df ddf hdf hddfc
      C₁ C₂ hdfb hddfb
    have he : (∫ q : E×E, df (b•q.1+a•q.2) q.2 ∂γZ.prod γY) =
        ∫ q : E×E, df (W q) q.1 ∂γY.prod γZ := by
      simpa only [W,Prod.swap,add_comm] using
        (integral_prod_swap (μ := γY) (ν := γZ) (fun q : E×E => df (W q) q.1))
    have hG (i j : κ) :
        (∫ q : E×E, ddf (b•q.1+a•q.2) (Pi.single j 1) (Pi.single i 1) ∂γZ.prod γY) =
          ∫ q, G i j q ∂γY.prod γZ := by
      simpa only [G,W,Prod.swap,add_comm] using
        (integral_prod_swap (μ := γY) (ν := γZ) (G i j))
    rw [he] at hh
    simp_rw [hG] at hh
    exact hh
  have hchain := hasDerivAt_integral_sqrt_affine_path
    (fun q : E×E => q.1) (fun q : E×E => q.2) hYint hZint 0 f df hf hdfc
      C₀ C₁ hC₁ hfb hdfb ht ht1
  simp only [zero_add] at hchain
  have hcancelA : (1/(2*a))*a=(1/2 : ℝ) := by
    have ha : a≠0 := (Real.sqrt_pos.mpr ht).ne'
    field_simp [ha]
  have hcancelB : (1/(2*b))*b=(1/2 : ℝ) := by
    have hb : b≠0 := (Real.sqrt_pos.mpr (by linarith : 0<1-t)).ne'
    field_simp [hb]
  have he : (∫ q : E×E, df (W q) ((1/(2*a))•q.1-(1/(2*b))•q.2) ∂γY.prod γZ) =
      (1/2 : ℝ) • ∑ i, ∑ j,
        (cov[(fun z : E => z i),(fun z : E => z j);γY]-
          cov[(fun z : E => z i),(fun z : E => z j);γZ]) •
          ∫ q, G i j q ∂γY.prod γZ := by
    simp_rw [map_sub,map_smul]
    have hiYs : Integrable (fun q : E×E => (1/(2*a)) • df (W q) q.1) (γY.prod γZ) :=
      hiY.smul _
    have hiZs : Integrable (fun q : E×E => (1/(2*b)) • df (W q) q.2) (γY.prod γZ) :=
      hiZ.smul _
    rw [integral_sub hiYs hiZs,integral_smul,integral_smul,hY,hZ,
      smul_smul,smul_smul,hcancelA,hcancelB]
    simp only [sub_smul,Finset.sum_sub_distrib,smul_sub]
  exact hchain.congr_deriv he

/-- Integrating the exact native Gaussian variance derivative gives the
actual difference of the endpoint expectations. Every integrability and
endpoint continuity premise follows from the bounded C² test, including
degenerate Gaussian laws. Source: Bandeira--Boedihardjo--van Handel,
arXiv:2108.06312v2, Lemma 4.11. -/
theorem integral_sub_integral_eq_gaussian_covariance_difference_integral
    (γY γZ : Measure E) [IsGaussian γY] [IsGaussian γZ]
    (hYmean : (∫ y : E, y ∂γY)=0) (hZmean : (∫ z : E, z ∂γZ)=0)
    (f : E → F) (df : E → E →L[ℝ] F) (ddf : E → E →L[ℝ] E →L[ℝ] F)
    (hf : ∀ x, HasFDerivAt f (df x) x)
    (hdf : ∀ x, HasFDerivAt df (ddf x) x) (hddfc : Continuous ddf)
    (C₀ C₁ C₂ : ℝ) (hfb : ∀ x, ‖f x‖≤C₀)
    (hdfb : ∀ x, ‖df x‖≤C₁) (hddfb : ∀ x, ‖ddf x‖≤C₂) :
    (∫ y : E, f y ∂γY)-(∫ z : E, f z ∂γZ) =
      (1/2 : ℝ) • ∫ t : ℝ in (0 : ℝ)..1, ∑ i, ∑ j,
        (cov[(fun z : E => z i),(fun z : E => z j);γY]-
          cov[(fun z : E => z i),(fun z : E => z j);γZ]) •
          ∫ q : E×E, ddf (Real.sqrt t•q.1+Real.sqrt (1-t)•q.2)
            (Pi.single j 1) (Pi.single i 1) ∂γY.prod γZ := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  let H (t : ℝ) := ∫ q : E×E, f (Real.sqrt t•q.1+Real.sqrt (1-t)•q.2) ∂γY.prod γZ
  let D (t : ℝ) := ∑ i, ∑ j,
    (cov[(fun z : E => z i),(fun z : E => z j);γY]-
      cov[(fun z : E => z i),(fun z : E => z j);γZ]) •
      ∫ q : E×E, ddf (Real.sqrt t•q.1+Real.sqrt (1-t)•q.2)
        (Pi.single j 1) (Pi.single i 1) ∂γY.prod γZ
  have hYint : Integrable (fun q : E×E => q.1) (γY.prod γZ) :=
    (IsGaussian.integrable_id (μ := γY)).comp_fst γZ
  have hZint : Integrable (fun q : E×E => q.2) (γY.prod γZ) :=
    (IsGaussian.integrable_id (μ := γZ)).comp_snd γY
  have hHc : Continuous H := by
    simpa only [zero_add,H] using continuous_integral_affine_path
      (fun q : E×E => q.1) (fun q : E×E => q.2)
      hYint.aestronglyMeasurable hZint.aestronglyMeasurable 0
      Real.sqrt (fun t : ℝ => Real.sqrt (1-t)) Real.continuous_sqrt
      (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)) f hfc C₀ hfb
  have hDc : Continuous D := by
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    have hcont : Continuous (fun t : ℝ => ∫ q : E×E,
        ddf (Real.sqrt t•q.1+Real.sqrt (1-t)•q.2)
          (Pi.single j 1) (Pi.single i 1) ∂γY.prod γZ) := by
      apply continuous_of_dominated (bound := fun _ : E×E => C₂)
      · intro t
        have hc : Continuous (fun q : E×E =>
            ddf (Real.sqrt t•q.1+Real.sqrt (1-t)•q.2)
              (Pi.single j 1) (Pi.single i 1)) := by fun_prop
        exact hc.aestronglyMeasurable
      · intro t
        exact Eventually.of_forall fun q => by
          have hd : ‖ddf (Real.sqrt t•q.1+Real.sqrt (1-t)•q.2) (Pi.single j 1)‖≤C₂ := by
            simpa only [Pi.norm_single,norm_one,mul_one] using
              ((ddf _).le_opNorm (Pi.single j 1)).trans
                (mul_le_mul_of_nonneg_right (hddfb _) (norm_nonneg _))
          simpa only [Pi.norm_single,norm_one,mul_one] using
            ((ddf _ (Pi.single j 1)).le_opNorm (Pi.single i 1)).trans
              (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
      · exact integrable_const _
      · exact Eventually.of_forall fun q => by fun_prop
    exact hcont.const_smul _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (show (0 : ℝ)≤1 by norm_num) hHc.continuousOn
    (fun t ht => hasDerivAt_integral_gaussian_sqrt_interpolation γY γZ hYmean hZmean
      f df ddf hf hdf hddfc C₀ C₁ C₂ hfb hdfb hddfb ht.1 ht.2)
    ((hDc.const_smul (1/2 : ℝ)).intervalIntegrable 0 1)
  have h0 : H 0=(∫ z : E, f z ∂γZ) := by
    simpa only [H,Real.sqrt_zero,sub_zero,Real.sqrt_one,zero_smul,one_smul,zero_add,
      Function.comp_def] using
      (measurePreserving_snd (μ := γY) (ν := γZ)).hasLaw.integral_comp hfc.aestronglyMeasurable
  have h1 : H 1=(∫ y : E, f y ∂γY) := by
    simpa only [H,sub_self,Real.sqrt_zero,Real.sqrt_one,zero_smul,one_smul,add_zero,
      Function.comp_def] using
      (measurePreserving_fst (μ := γY) (ν := γZ)).hasLaw.integral_comp hfc.aestronglyMeasurable
  rw [intervalIntegral.integral_smul,h0,h1] at hFTC
  exact hFTC.symm

end NLAlib
