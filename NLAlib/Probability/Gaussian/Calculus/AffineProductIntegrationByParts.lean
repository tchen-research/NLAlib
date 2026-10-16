import NLAlib.Probability.Gaussian.Calculus.AffineBilinearIntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Affine Gaussian Stein contraction with an independent parameter

Fubini's theorem applies the actual Gaussian identity at every value of an
independently sampled parameter. Global bounds prove product integrability.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib

variable {κ Ω F : Type*} [Fintype κ] [DecidableEq κ] [MeasurableSpace Ω]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Gaussian-affine bilinear test and every covariance-contraction
coefficient are integrable on the actual independent product space. -/
theorem integrable_bilin_gaussian_affine_product
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → κ → ℝ) (hX : AEMeasurable X P)
    (γ : Measure (κ → ℝ)) (hγ : HasGaussianLaw (id : (κ → ℝ) → κ → ℝ) γ)
    (μ : κ → ℝ) (a b : ℝ)
    (f : (κ → ℝ) → F) (hfc : Continuous f)
    (df : (κ → ℝ) → (κ → ℝ) →L[ℝ] F) (hdf : Continuous df)
    (C C' : ℝ) (hfb : ∀ y, ‖f y‖ ≤ C) (hdfb : ∀ y, ‖df y‖ ≤ C')
    (B : (κ → ℝ) →L[ℝ] F →L[ℝ] ℂ) :
    Integrable (fun q => B q.2 (f (μ + a • (X q.1 - μ) + b • q.2))) (P.prod γ) ∧
      ∀ i j, Integrable (fun q => B (Pi.single i 1)
        (df (μ + a • (X q.1 - μ) + b • q.2) (Pi.single j 1))) (P.prod γ) := by
  haveI := hγ.isProbabilityMeasure
  have hXa : AEStronglyMeasurable (fun q : Ω × (κ → ℝ) => X q.1) (P.prod γ) :=
    hX.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_fst (μ := P) (ν := γ))
  have hZi : Integrable (fun q : Ω × (κ → ℝ) => q.2) (P.prod γ) :=
    (hγ.memLp_two.integrable one_le_two).comp_snd P
  have hY : AEStronglyMeasurable
      (fun q : Ω × (κ → ℝ) => μ + a • (X q.1 - μ) + b • q.2) (P.prod γ) :=
    (aestronglyMeasurable_const.add
      ((hXa.sub aestronglyMeasurable_const).const_smul a)).add
        (hZi.aestronglyMeasurable.const_smul b)
  constructor
  · exact B.integrable_of_bilin_of_bdd_right C hZi
      (hfc.comp_aestronglyMeasurable hY) (Filter.Eventually.of_forall (fun q => hfb _))
  · intro i j
    have hcoef : Continuous (fun y : κ → ℝ => B (Pi.single i 1) (df y (Pi.single j 1))) :=
      (B _).continuous.comp (hdf.clm_apply continuous_const)
    refine Integrable.of_bound (hcoef.comp_aestronglyMeasurable hY)
      (‖B (Pi.single i 1)‖ * (C' * ‖(Pi.single j (1 : ℝ) : κ → ℝ)‖)) ?_
    filter_upwards [] with q
    exact ((B (Pi.single i 1)).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_left ((df _).le_opNorm _) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hdfb _) (norm_nonneg _)) (norm_nonneg _)))

/-- The exact affine Gaussian Stein identity after adjoining an arbitrary
independent parameter. The full coordinate covariance and the chain-rule
factor `b` are retained, and all product integrability is derived.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem integral_bilin_gaussian_affine_product
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → κ → ℝ) (hX : AEMeasurable X P)
    (γ : Measure (κ → ℝ)) (hγ : HasGaussianLaw (id : (κ → ℝ) → κ → ℝ) γ)
    (hmean : ∀ i, ∫ z, z i ∂γ = 0)
    (μ : κ → ℝ) (a b : ℝ)
    (f : (κ → ℝ) → F) (df : (κ → ℝ) → (κ → ℝ) →L[ℝ] F)
    (hf : ∀ y, HasFDerivAt f (df y) y) (hdf : Continuous df)
    (C C' : ℝ) (hfb : ∀ y, ‖f y‖ ≤ C) (hdfb : ∀ y, ‖df y‖ ≤ C')
    (B : (κ → ℝ) →L[ℝ] F →L[ℝ] ℂ) :
    (∫ q, B q.2 (f (μ + a • (X q.1 - μ) + b • q.2)) ∂P.prod γ) =
      b • ∑ i, ∑ j, cov[(fun z : κ → ℝ => z i), (fun z : κ → ℝ => z j); γ] •
        ∫ q, B (Pi.single i 1)
          (df (μ + a • (X q.1 - μ) + b • q.2) (Pi.single j 1)) ∂P.prod γ := by
  haveI := hγ.isProbabilityMeasure
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun y => (hf y).continuousAt)
  have hi := integrable_bilin_gaussian_affine_product P X hX γ hγ μ a b f hfc df hdf
    C C' hfb hdfb B
  let c (i j : κ) : ℝ := cov[(fun z : κ → ℝ => z i), (fun z : κ → ℝ => z j); γ]
  let G (i j : κ) (q : Ω × (κ → ℝ)) : ℂ :=
    B (Pi.single i 1) (df (μ + a • (X q.1 - μ) + b • q.2) (Pi.single j 1))
  have hinner (i j : κ) : Integrable (fun p => ∫ z, G i j (p, z) ∂γ) P :=
    (hi.2 i j).integral_prod_left
  have hterm (i j : κ) : Integrable (fun p => c i j • ∫ z, G i j (p, z) ∂γ) P := by
    refine ((hinner i j).smul (c i j)).congr ?_
    filter_upwards [] with p
    rfl
  have hsum (i : κ) : Integrable (fun p => ∑ j, c i j • ∫ z, G i j (p, z) ∂γ) P :=
    integrable_finsetSum Finset.univ (fun j _ => hterm i j)
  calc
    _ = ∫ p, ∫ z, B z (f (μ + a • (X p - μ) + b • z)) ∂γ ∂P :=
      integral_prod _ hi.1
    _ = ∫ p, b • ∑ i, ∑ j, c i j • ∫ z, G i j (p, z) ∂γ ∂P := by
      apply integral_congr_ae
      filter_upwards [] with p
      exact integral_bilin_gaussian_affine γ hγ hmean μ (X p) a b f df hf hdf C C' hfb hdfb B
    _ = b • ∑ i, ∑ j, c i j • ∫ q, G i j q ∂P.prod γ := by
      rw [integral_smul, integral_finsetSum _ (fun i _ => hsum i)]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi'
      rw [integral_finsetSum _ (fun j _ => hterm i j)]
      apply Finset.sum_congr rfl
      intro j hj'
      rw [integral_smul, ← integral_prod _ (hi.2 i j)]

end NLAlib
