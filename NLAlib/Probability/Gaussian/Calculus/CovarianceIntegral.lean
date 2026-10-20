import NLAlib.ForMathlib.MeasureTheory.BilinearRotationDifferentiation
import NLAlib.Probability.Gaussian.Calculus.ParameterIntegrationByParts
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

/-! # Exact native Gaussian covariance rotation derivatives

Actual product-Gaussian rotation and Gaussian Stein contraction produce
the cross derivative underlying source arXiv:2108.06312v2, Corollary 4.12.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace NLAlib
variable {κ F G : Type*} [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
local notation "E" => κ → ℝ

omit [DecidableEq κ] in
private theorem rotation_inverse_fst (θ : ℝ) (q : E×E) :
    Real.cos θ • (ContinuousLinearMap.rotation (-θ) q).1+
      Real.sin θ • (ContinuousLinearMap.rotation (-θ) q).2=q.1 := by
  funext i
  change Real.cos θ*(Real.cos (-θ)*q.1 i+Real.sin (-θ)*q.2 i)+
    Real.sin θ*(-Real.sin (-θ)*q.1 i+Real.cos (-θ)*q.2 i)=q.1 i
  rw [Real.cos_neg,Real.sin_neg]
  linear_combination (q.1 i)*(Real.cos_sq_add_sin_sq θ)

omit [DecidableEq κ] in
private theorem rotation_inverse_snd (θ : ℝ) (q : E×E) :
    -Real.sin θ • (ContinuousLinearMap.rotation (-θ) q).1+
      Real.cos θ • (ContinuousLinearMap.rotation (-θ) q).2=q.2 := by
  funext i
  change -Real.sin θ*(Real.cos (-θ)*q.1 i+Real.sin (-θ)*q.2 i)+
    Real.cos θ*(-Real.sin (-θ)*q.1 i+Real.cos (-θ)*q.2 i)=q.2 i
  rw [Real.cos_neg,Real.sin_neg]
  linear_combination (q.2 i)*(Real.cos_sq_add_sin_sq θ)

omit [DecidableEq κ] in
private theorem integral_comp_gaussian_rotation
    (γ : Measure E) [IsGaussian γ] (hmean : (∫ z : E, z ∂γ)=0)
    (h : E×E → ℂ) (hh : Continuous h) (θ : ℝ) :
    (∫ q, h (ContinuousLinearMap.rotation θ q) ∂γ.prod γ)=∫ q, h q ∂γ.prod γ := by
  calc
    _ = ∫ q, h q ∂(γ.prod γ).map (ContinuousLinearMap.rotation θ) :=
      (integral_map (ContinuousLinearMap.rotation θ).continuous.measurable.aemeasurable
        hh.aestronglyMeasurable).symm
    _ = _ := by rw [IsGaussian.map_rotation_eq_self hmean θ]

/-- Actual centered Gaussian rotation differentiates the genuine bilinear
expectation into its full native covariance contraction. Only bounded C¹
tests with bounded continuous derivatives are needed. Gaussian rotation
invariance and Stein in the independent rotated noise supply the identity;
no covariance cancellation is assumed.
Source: Bandeira--Boedihardjo--van Handel, arXiv:2108.06312v2, Corollary 4.12. -/
theorem hasDerivAt_integral_bilin_gaussian_rotation
    (γ : Measure E) [IsGaussian γ] (hmean : (∫ z : E, z ∂γ)=0)
    (f : E → F) (df : E → E →L[ℝ] F)
    (g : E → G) (dg : E → E →L[ℝ] G)
    (hf : ∀ x, HasFDerivAt f (df x) x) (hdfc : Continuous df)
    (hg : ∀ x, HasFDerivAt g (dg x) x) (hdgc : Continuous dg)
    (Cf Cd Cg Ce : ℝ) (hfb : ∀ x, ‖f x‖≤Cf) (hdfb : ∀ x, ‖df x‖≤Cd)
    (hgb : ∀ x, ‖g x‖≤Cg) (hdgb : ∀ x, ‖dg x‖≤Ce)
    (B : F →L[ℝ] G →L[ℝ] ℂ) (θ : ℝ) :
    HasDerivAt
      (fun t : ℝ => ∫ q : E×E, B (f q.1)
        (g (Real.cos t•q.1+Real.sin t•q.2)) ∂γ.prod γ)
      (-Real.sin θ • ∑ i, ∑ j, cov[(fun z : E => z i),(fun z : E => z j);γ] •
        ∫ q : E×E, B (df q.1 (Pi.single i 1))
          (dg (Real.cos θ•q.1+Real.sin θ•q.2) (Pi.single j 1)) ∂γ.prod γ) θ := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hCe : 0≤Ce := (norm_nonneg (dg 0)).trans (hdgb 0)
  let K (w : E) : E →L[ℝ] F →L[ℝ] ℂ := B.flip.comp (dg w)
  have hK : Continuous K :=
    (ContinuousLinearMap.compL ℝ E G (F →L[ℝ] ℂ) B.flip).continuous.comp hdgc
  have hKb (w : E) : ‖K w‖≤‖B‖*Ce := by
    exact (ContinuousLinearMap.opNorm_comp_le B.flip (dg w)).trans (by
      rw [ContinuousLinearMap.opNorm_flip]
      exact mul_le_mul_of_nonneg_left (hdgb w) (norm_nonneg B))
  have hs := integral_parameter_bilin_gaussian_affine γ γ hmean
    (Real.cos θ) (-Real.sin θ) f df hf hdfc Cf Cd hfb hdfb K hK (‖B‖*Ce) hKb
  simp only [K,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply] at hs
  let H' (q : E×E) : ℂ := B (f q.1)
    (dg (Real.cos θ•q.1+Real.sin θ•q.2) (-Real.sin θ•q.1+Real.cos θ•q.2))
  let H0 (q : E×E) : ℂ := B (f (Real.cos θ•q.1-Real.sin θ•q.2)) (dg q.1 q.2)
  have hH'c : Continuous H' := by dsimp only [H']; fun_prop
  have hHchange : (∫ q, H' q ∂γ.prod γ)=(∫ q, H0 q ∂γ.prod γ) := by
    rw [← integral_comp_gaussian_rotation γ hmean H' hH'c (-θ)]
    apply integral_congr_ae
    exact Eventually.of_forall fun q => by
      dsimp only [H']
      rw [rotation_inverse_fst θ q,rotation_inverse_snd θ q]
      simp only [H0,ContinuousLinearMap.rotation_apply,Real.cos_neg,Real.sin_neg,neg_smul,
        sub_eq_add_neg]
  have hGchange (i j : κ) :
      (∫ q : E×E, B (df (Real.cos θ•q.1-Real.sin θ•q.2) (Pi.single j 1))
        (dg q.1 (Pi.single i 1)) ∂γ.prod γ) =
      ∫ q : E×E, B (df q.1 (Pi.single j 1))
        (dg (Real.cos θ•q.1+Real.sin θ•q.2) (Pi.single i 1)) ∂γ.prod γ := by
    let h (q : E×E) := B (df (Real.cos θ•q.1-Real.sin θ•q.2) (Pi.single j 1))
      (dg q.1 (Pi.single i 1))
    have hc : Continuous h := by dsimp only [h]; fun_prop
    rw [← integral_comp_gaussian_rotation γ hmean h hc θ]
    apply integral_congr_ae
    exact Eventually.of_forall fun q => by
      have he := rotation_inverse_fst (-θ) q
      simp only [neg_neg,Real.cos_neg,Real.sin_neg,neg_smul,← sub_eq_add_neg] at he
      dsimp only [h]
      rw [he]
      rfl
  have hval : (∫ q, H' q ∂γ.prod γ) =
      -Real.sin θ • ∑ i, ∑ j, cov[(fun z : E => z i),(fun z : E => z j);γ] •
        ∫ q : E×E, B (df q.1 (Pi.single i 1))
          (dg (Real.cos θ•q.1+Real.sin θ•q.2) (Pi.single j 1)) ∂γ.prod γ := by
    rw [hHchange]
    change (∫ q : E×E, B (f (Real.cos θ•q.1-Real.sin θ•q.2)) (dg q.1 q.2) ∂γ.prod γ)=_
    have hss : (∫ q : E×E, B (f (Real.cos θ•q.1-Real.sin θ•q.2)) (dg q.1 q.2) ∂γ.prod γ) =
        -Real.sin θ • ∑ i, ∑ j, cov[(fun z : E => z i),(fun z : E => z j);γ] •
          ∫ q : E×E, B (df (Real.cos θ•q.1-Real.sin θ•q.2) (Pi.single j 1))
            (dg q.1 (Pi.single i 1)) ∂γ.prod γ := by
      simpa only [neg_smul,← sub_eq_add_neg] using hs
    rw [hss]
    congr 1
    simp_rw [hGchange]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [covariance_comm]
  have hY : Integrable (fun q : E×E => q.1) (γ.prod γ) :=
    (IsGaussian.integrable_id (μ := γ)).comp_fst γ
  have hZ : Integrable (fun q : E×E => q.2) (γ.prod γ) :=
    (IsGaussian.integrable_id (μ := γ)).comp_snd γ
  have hh := hasDerivAt_integral_bilin_rotation (fun q : E×E => q.1) (fun q : E×E => q.2)
    hY hZ f hfc g dg hg hdgc Cf Cg Ce hfb hgb hdgb B θ
  exact hh.congr_deriv hval

/-- The actual Gaussian covariance integral for bounded C¹ Banach-valued
tests and a continuous real bilinear complex-valued observation. The
independent copy is the literal product law, and the interpolation is
the source correlation path `t*y+sqrt(1-t²)*z` on the closed unit interval.
Singular Gaussian covariance and empty coordinate types are included.
Source: Bandeira--Boedihardjo--van Handel, arXiv:2108.06312v2, Corollary 4.12. -/
theorem integral_bilin_sub_bilin_integrals_eq_gaussian_covariance_integral
    [CompleteSpace F] [CompleteSpace G]
    (γ : Measure E) [IsGaussian γ] (hmean : (∫ z : E, z ∂γ)=0)
    (f : E → F) (df : E → E →L[ℝ] F)
    (g : E → G) (dg : E → E →L[ℝ] G)
    (hf : ∀ x, HasFDerivAt f (df x) x) (hdfc : Continuous df)
    (hg : ∀ x, HasFDerivAt g (dg x) x) (hdgc : Continuous dg)
    (Cf Cd Cg Ce : ℝ) (hfb : ∀ x, ‖f x‖≤Cf) (hdfb : ∀ x, ‖df x‖≤Cd)
    (hgb : ∀ x, ‖g x‖≤Cg) (hdgb : ∀ x, ‖dg x‖≤Ce)
    (B : F →L[ℝ] G →L[ℝ] ℂ) :
    (∫ y : E, B (f y) (g y) ∂γ)-B (∫ y : E, f y ∂γ) (∫ y : E, g y ∂γ) =
      ∫ t : ℝ in (0 : ℝ)..1, ∑ i, ∑ j,
        cov[(fun z : E => z i),(fun z : E => z j);γ] •
          ∫ q : E×E, B (df q.1 (Pi.single i 1))
            (dg (t•q.1+Real.sqrt (1-t^2)•q.2) (Pi.single j 1)) ∂γ.prod γ := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt
  have hCf : 0≤Cf := (norm_nonneg (f 0)).trans (hfb 0)
  have hCd : 0≤Cd := (norm_nonneg (df 0)).trans (hdfb 0)
  have hCg : 0≤Cg := (norm_nonneg (g 0)).trans (hgb 0)
  have hCe : 0≤Ce := (norm_nonneg (dg 0)).trans (hdgb 0)
  let H (θ : ℝ) : ℂ := ∫ q : E×E, B (f q.1)
    (g (Real.cos θ•q.1+Real.sin θ•q.2)) ∂γ.prod γ
  let D (t : ℝ) : ℂ := ∑ i, ∑ j,
    cov[(fun z : E => z i),(fun z : E => z j);γ] •
      ∫ q : E×E, B (df q.1 (Pi.single i 1))
        (dg (t•q.1+Real.sqrt (1-t^2)•q.2) (Pi.single j 1)) ∂γ.prod γ
  have hcoef (i j : κ) (t : ℝ) (q : E×E) :
      ‖B (df q.1 (Pi.single i 1))
        (dg (t•q.1+Real.sqrt (1-t^2)•q.2) (Pi.single j 1))‖≤‖B‖*Cd*Ce := by
    have hdf : ‖df q.1 (Pi.single i 1)‖≤Cd := by
      simpa only [Pi.norm_single,norm_one,mul_one] using
        ((df q.1).le_opNorm (Pi.single i 1)).trans
          (mul_le_mul_of_nonneg_right (hdfb q.1) (norm_nonneg _))
    have hdg : ‖dg (t•q.1+Real.sqrt (1-t^2)•q.2) (Pi.single j 1)‖≤Ce := by
      simpa only [Pi.norm_single,norm_one,mul_one] using
        ((dg (t•q.1+Real.sqrt (1-t^2)•q.2)).le_opNorm (Pi.single j 1)).trans
          (mul_le_mul_of_nonneg_right (hdgb (t•q.1+Real.sqrt (1-t^2)•q.2)) (norm_nonneg _))
    exact (B.le_opNorm₂ _ _).trans (by gcongr)
  have hDc : Continuous D := by
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    have hcont : Continuous (fun t : ℝ => ∫ q : E×E,
        B (df q.1 (Pi.single i 1))
          (dg (t•q.1+Real.sqrt (1-t^2)•q.2) (Pi.single j 1)) ∂γ.prod γ) := by
      apply continuous_of_dominated (bound := fun _ : E×E => ‖B‖*Cd*Ce)
      · intro t
        have hc : Continuous (fun q : E×E => B (df q.1 (Pi.single i 1))
            (dg (t•q.1+Real.sqrt (1-t^2)•q.2) (Pi.single j 1))) := by fun_prop
        exact hc.aestronglyMeasurable
      · intro t
        exact Eventually.of_forall fun q => hcoef i j t q
      · exact integrable_const _
      · exact Eventually.of_forall fun q => by fun_prop
    exact hcont.const_smul (cov[(fun z : E => z i),(fun z : E => z j);γ])
  have hHd (θ : ℝ) : HasDerivAt H
      (-Real.sin θ • ∑ i, ∑ j, cov[(fun z : E => z i),(fun z : E => z j);γ] •
        ∫ q : E×E, B (df q.1 (Pi.single i 1))
          (dg (Real.cos θ•q.1+Real.sin θ•q.2) (Pi.single j 1)) ∂γ.prod γ) θ :=
    hasDerivAt_integral_bilin_gaussian_rotation γ hmean f df g dg hf hdfc hg hdgc
      Cf Cd Cg Ce hfb hdfb hgb hdgb B θ
  have hHc : Continuous H := continuous_iff_continuousAt.mpr fun θ => (hHd θ).continuousAt
  have hπ : (0 : ℝ)≤Real.pi/2 := by linarith [Real.pi_pos]
  have htheta (θ : ℝ) (hθ : θ∈Icc (0 : ℝ) (Real.pi/2)) :
      HasDerivAt H (-Real.sin θ • D (Real.cos θ)) θ := by
    have hsin : 0≤Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
      (by linarith [hθ.2,Real.pi_pos])
    have hsqrt : Real.sqrt (1-(Real.cos θ)^2)=Real.sin θ := by
      have he : 1-(Real.cos θ)^2=(Real.sin θ)^2 := by nlinarith [Real.sin_sq_add_cos_sq θ]
      rw [he,Real.sqrt_sq_eq_abs,abs_of_nonneg hsin]
    simpa only [D,hsqrt] using hHd θ
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hπ hHc.continuousOn
    (fun θ hθ => htheta θ ⟨hθ.1.le,hθ.2.le⟩)
    ((Real.continuous_sin.neg.smul (hDc.comp Real.continuous_cos)).intervalIntegrable 0 (Real.pi/2))
  have hchange := intervalIntegral.integral_deriv_smul_comp
    (a := (0 : ℝ)) (b := Real.pi/2) (f := Real.cos) (f' := fun θ => -Real.sin θ) (g := D)
    (fun θ _ => Real.hasDerivAt_cos θ) Real.continuous_sin.neg.continuousOn hDc
  simp only [Real.cos_zero,Real.cos_pi_div_two,Function.comp_def] at hchange
  have heq : (∫ t : ℝ in (0 : ℝ)..1, D t)=H 0-H (Real.pi/2) := by
    have hh : -(∫ t : ℝ in (0 : ℝ)..1, D t)=H (Real.pi/2)-H 0 := by
      rw [← intervalIntegral.integral_symm,← hchange]
      exact hFTC
    exact neg_injective (by simpa only [neg_sub,neg_neg] using hh)
  have h0 : H 0=(∫ y : E, B (f y) (g y) ∂γ) := by
    have hc : Continuous (fun y : E => B (f y) (g y)) := by fun_prop
    simpa only [H,Real.cos_zero,Real.sin_zero,one_smul,zero_smul,add_zero,Function.comp_def] using
      (measurePreserving_fst (μ := γ) (ν := γ)).hasLaw.integral_comp hc.aestronglyMeasurable
  have hfint : Integrable f γ := Integrable.of_bound hfc.aestronglyMeasurable Cf
    (Eventually.of_forall hfb)
  have hgint : Integrable g γ := Integrable.of_bound hgc.aestronglyMeasurable Cg
    (Eventually.of_forall hgb)
  have h1 : H (Real.pi/2)=B (∫ y : E, f y ∂γ) (∫ y : E, g y ∂γ) := by
    have hc : Continuous (fun q : E×E => B (f q.1) (g q.2)) := by fun_prop
    have hi : Integrable (fun q : E×E => B (f q.1) (g q.2)) (γ.prod γ) := by
      apply Integrable.of_bound hc.aestronglyMeasurable (‖B‖*Cf*Cg)
      exact Eventually.of_forall fun q => (B.le_opNorm₂ _ _).trans
        (by gcongr <;> first | exact hfb _ | exact hgb _)
    simp only [H,Real.cos_pi_div_two,Real.sin_pi_div_two,zero_smul,one_smul,zero_add]
    rw [integral_prod _ hi]
    have hinner (y : E) : (∫ z : E, B (f y) (g z) ∂γ)=B (f y) (∫ z : E, g z ∂γ) :=
      (B (f y)).integral_comp_comm hgint
    simp_rw [hinner]
    exact (B.flip (∫ z : E, g z ∂γ)).integral_comp_comm hfint
  rw [h0,h1] at heq
  exact heq.symm

end NLAlib
