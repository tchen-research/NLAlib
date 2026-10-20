import NLAlib.Probability.Gaussian.Calculus.ParameterIntegrationByParts
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! # Native Banach-valued Gaussian derivative evaluation -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter
namespace NLAlib
variable {κ F : Type*} [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
local notation "E" => κ → ℝ

/-- An actual independent Gaussian coordinate vector can be contracted
against a Banach-valued derivative field. Scalar Gaussian Stein and the
separating continuous dual give the exact vector identity; the displayed
native bounds imply every Bochner integrability requirement.
Source: the Stein contraction in Bandeira--Boedihardjo--van Handel,
arXiv:2108.06312v2, Lemma 4.11. -/
theorem integral_apply_gaussian_affine
    (P : Measure E) [IsProbabilityMeasure P]
    (γ : Measure E) [IsGaussian γ] (hmean : (∫ z : E, z ∂γ)=0)
    (a b : ℝ) (Ψ : E → E →L[ℝ] F) (DΨ : E → E →L[ℝ] E →L[ℝ] F)
    (hΨ : ∀ x, HasFDerivAt Ψ (DΨ x) x) (hDc : Continuous DΨ)
    (C₀ C₁ : ℝ) (hΨb : ∀ x, ‖Ψ x‖≤C₀) (hDb : ∀ x, ‖DΨ x‖≤C₁) :
    (∫ q : E×E, Ψ (a•q.1+b•q.2) q.2 ∂P.prod γ) =
      b • ∑ i, ∑ j, cov[(fun z : E => z i),(fun z : E => z j);γ] •
        ∫ q : E×E, DΨ (a•q.1+b•q.2) (Pi.single j 1) (Pi.single i 1) ∂P.prod γ := by
  have hΨc : Continuous Ψ := continuous_iff_continuousAt.mpr fun x => (hΨ x).continuousAt
  let H (q : E×E) := Ψ (a•q.1+b•q.2) q.2
  let G (i j : κ) (q : E×E) := DΨ (a•q.1+b•q.2) (Pi.single j 1) (Pi.single i 1)
  have hHi : Integrable H (P.prod γ) := by
    have hZi : Integrable (fun q : E×E => q.2) (P.prod γ) :=
      (IsGaussian.integrable_id (μ := γ)).comp_snd P
    have hc : Continuous H := by dsimp only [H]; fun_prop
    apply Integrable.mono' (hZi.norm.const_mul C₀) hc.aestronglyMeasurable
    exact Eventually.of_forall fun q => ((Ψ _).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hΨb _) (norm_nonneg _))
  have hGi (i j : κ) : Integrable (G i j) (P.prod γ) := by
    have hc : Continuous (G i j) := by dsimp only [G]; fun_prop
    apply Integrable.of_bound hc.aestronglyMeasurable C₁
    exact Eventually.of_forall fun q => by
      dsimp only [G]
      have hd : ‖DΨ (a•q.1+b•q.2) (Pi.single j 1)‖≤C₁ := by
        simpa only [Pi.norm_single,norm_one,mul_one] using
          ((DΨ _).le_opNorm (Pi.single j 1)).trans
            (mul_le_mul_of_nonneg_right (hDb _) (norm_nonneg _))
      simpa only [Pi.norm_single,norm_one,mul_one] using
        ((DΨ _ (Pi.single j 1)).le_opNorm (Pi.single i 1)).trans
          (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro ℓ
  let L : F →L[ℝ] ℂ := Complex.ofRealCLM.comp ℓ
  let C : (E →L[ℝ] F) →L[ℝ] E →L[ℝ] ℂ :=
    ContinuousLinearMap.compL ℝ E F ℂ L
  let Ψc (x : E) := C (Ψ x)
  let DΨc (x : E) := C.comp (DΨ x)
  have hΨc (x : E) : HasFDerivAt Ψc (DΨc x) x :=
    C.hasFDerivAt.comp x (hΨ x)
  have hDcc : Continuous DΨc :=
    (ContinuousLinearMap.compL ℝ E (E →L[ℝ] F) (E →L[ℝ] ℂ) C).continuous.comp hDc
  have hΨcb (x : E) : ‖Ψc x‖≤‖L‖*C₀ :=
    (ContinuousLinearMap.opNorm_comp_le L (Ψ x)).trans
      (mul_le_mul_of_nonneg_left (hΨb x) (norm_nonneg L))
  have hC₁ : 0≤C₁ := (norm_nonneg (DΨ 0)).trans (hDb 0)
  have hDΨcb (x : E) : ‖DΨc x‖≤‖L‖*C₁ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg L) hC₁)
    intro v
    change ‖L.comp (DΨ x v)‖≤(‖L‖*C₁)*‖v‖
    calc
      _ ≤ ‖L‖*‖DΨ x v‖ := ContinuousLinearMap.opNorm_comp_le L (DΨ x v)
      _ ≤ ‖L‖*(C₁*‖v‖) := mul_le_mul_of_nonneg_left
        (((DΨ x).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (hDb x) (norm_nonneg v))) (norm_nonneg L)
      _ = _ := by ring
  let B : E →L[ℝ] (E →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ
  have hBb := B.opNorm_le_bound₂ (show (0 : ℝ)≤1 by norm_num)
    (fun x y => by simpa only [B,ContinuousLinearMap.apply_apply,one_mul,mul_comm]
      using y.le_opNorm x)
  have hs := integral_parameter_bilin_gaussian_affine (F := E →L[ℝ] ℂ)
    P γ hmean a b Ψc DΨc hΨc hDcc
    (‖L‖*C₀) (‖L‖*C₁) hΨcb hDΨcb (fun _ => B) continuous_const 1 (fun _ => hBb)
  change (∫ q : E×E, L (H q) ∂P.prod γ) =
    b • ∑ i, ∑ j, cov[(fun z : E => z i),(fun z : E => z j);γ] •
      ∫ q : E×E, L (G i j q) ∂P.prod γ at hs
  rw [L.integral_comp_comm hHi] at hs
  simp_rw [L.integral_comp_comm (hGi _ _)] at hs
  have he : L (∫ q, H q ∂P.prod γ) =
      L (b • ∑ i, ∑ j, cov[(fun z : E => z i),(fun z : E => z j);γ] •
        ∫ q, G i j q ∂P.prod γ) := by
    simpa only [map_smul,map_sum] using hs
  change ((ℓ (∫ q, H q ∂P.prod γ)) : ℂ) =
    ((ℓ (b • ∑ i, ∑ j, cov[(fun z : E => z i),(fun z : E => z j);γ] •
      ∫ q, G i j q ∂P.prod γ)) : ℂ) at he
  exact Complex.ofReal_injective he

end NLAlib
