import NLAlib.Probability.Gaussian.Calculus.AffineBilinearIntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr

/-! # Actual Gaussian Stein contraction with a varying independent bilinear map -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter
namespace NLAlib
variable {κ F : Type*} [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
local notation "E" => κ → ℝ

/-- Stein's exact covariance contraction permits a bounded continuous
bilinear map depending on an independently sampled parameter. The two
actual laws form their product measure, and every integrability premise
is proved from the displayed native bounds and Gaussian first moments. -/
theorem integral_parameter_bilin_gaussian_affine
    (P : Measure E) [IsProbabilityMeasure P]
    (γ : Measure E) [IsGaussian γ] (hmean : (∫ z : E, z ∂γ)=0)
    (a b : ℝ) (f : E → F) (df : E → E →L[ℝ] F)
    (hf : ∀ x, HasFDerivAt f (df x) x) (hdf : Continuous df)
    (Cf Cd : ℝ) (hfb : ∀ x, ‖f x‖≤Cf) (hdfb : ∀ x, ‖df x‖≤Cd)
    (K : E → E →L[ℝ] F →L[ℝ] ℂ) (hK : Continuous K)
    (Ck : ℝ) (hKb : ∀ x, ‖K x‖≤Ck) :
    (∫ q : E×E, K q.1 q.2 (f (a•q.1+b•q.2)) ∂P.prod γ) =
      b • ∑ i, ∑ j, cov[(fun z : E => z i),(fun z : E => z j);γ] •
        ∫ q : E×E, K q.1 (Pi.single i 1)
          (df (a•q.1+b•q.2) (Pi.single j 1)) ∂P.prod γ := by
  have hγ := IsGaussian.hasGaussianLaw_id (μ := γ)
  have hCf : 0≤Cf := (norm_nonneg (f 0)).trans (hfb 0)
  have hCd : 0≤Cd := (norm_nonneg (df 0)).trans (hdfb 0)
  have hCk : 0≤Ck := (norm_nonneg (K 0)).trans (hKb 0)
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hmc (i : κ) : (∫ z : E, z i ∂γ)=0 := by
    have hh := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) i).integral_comp_comm
      (IsGaussian.integrable_id (μ := γ))
    change (∫ z : E, z i ∂γ)=(∫ z : E, z ∂γ) i at hh
    simpa only [hmean,Pi.zero_apply] using hh
  let H (q : E×E) := K q.1 q.2 (f (a•q.1+b•q.2))
  let G (i j : κ) (q : E×E) := K q.1 (Pi.single i 1)
    (df (a•q.1+b•q.2) (Pi.single j 1))
  have hHc : Continuous H := by dsimp only [H]; fun_prop
  have hGc (i j : κ) : Continuous (G i j) := by dsimp only [G]; fun_prop
  have hHi : Integrable H (P.prod γ) := by
    have hZi : Integrable (fun q : E×E => q.2) (P.prod γ) :=
      (IsGaussian.integrable_id (μ := γ)).comp_snd P
    apply Integrable.mono' (hZi.norm.const_mul (Ck*Cf)) hHc.aestronglyMeasurable
    exact Eventually.of_forall fun q => by
      dsimp only [H]
      calc
        _ ≤ ‖K q.1‖*‖q.2‖*‖f (a•q.1+b•q.2)‖ := (K q.1).le_opNorm₂ _ _
        _ ≤ Ck*‖q.2‖*Cf := by gcongr <;> first | exact hKb _ | exact hfb _
        _ = _ := by ring
  have hGi (i j : κ) : Integrable (G i j) (P.prod γ) := by
    apply Integrable.of_bound (hGc i j).aestronglyMeasurable (Ck*Cd)
    exact Eventually.of_forall fun q => by
      dsimp only [G]
      have hd : ‖df (a•q.1+b•q.2) (Pi.single j 1)‖≤Cd := by
        have hh := ((df (a•q.1+b•q.2)).le_opNorm (Pi.single j 1)).trans
          (mul_le_mul_of_nonneg_right (hdfb (a•q.1+b•q.2)) (norm_nonneg _))
        simpa only [Pi.norm_single,norm_one,mul_one] using hh
      have hh := (K q.1).le_opNorm₂ (Pi.single i 1) (df (a•q.1+b•q.2) (Pi.single j 1))
      simp only [Pi.norm_single,norm_one,mul_one] at hh
      exact hh.trans (mul_le_mul (hKb _) hd (norm_nonneg _) hCk)
  let c (i j : κ) : ℝ := cov[(fun z : E => z i),(fun z : E => z j);γ]
  have hterm (i j : κ) : Integrable (fun w : E => c i j • ∫ z : E, G i j (w,z) ∂γ) P :=
    ((hGi i j).integral_prod_left).smul (c i j)
  have hsum (i : κ) : Integrable (fun w : E => ∑ j, c i j • ∫ z : E, G i j (w,z) ∂γ) P :=
    integrable_finsetSum Finset.univ fun j _ => hterm i j
  calc
    _ = ∫ w, ∫ z, H (w,z) ∂γ ∂P := integral_prod _ hHi
    _ = ∫ w, b • ∑ i, ∑ j, c i j • ∫ z, G i j (w,z) ∂γ ∂P := by
      apply integral_congr_ae
      exact Eventually.of_forall fun w => by
        simpa only [H,G,c,zero_add,sub_zero] using
          integral_bilin_gaussian_affine γ hγ hmc 0 w a b f df hf hdf Cf Cd hfb hdfb (K w)
    _ = _ := by
      rw [integral_smul,integral_finsetSum _ (fun i _ => hsum i)]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ => hterm i j)]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_smul,← integral_prod _ (hGi i j)]

end NLAlib
