import NLAlib.Probability.Gaussian.Comparison.ResamplingInterpolation
import NLAlib.ForMathlib.MeasureTheory.MatrixEntriesIntegral
import NLAlib.Matrix.Norms.Core
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Operator-valued resampling interpolation

No norm-sum of entries is used: entrywise Stein identities reconstruct a native
matrix derivative. Every matrix Bochner integral below is genuinely integrable.
Source: Brailovskaya–van Handel, arXiv:2201.05142v3, §6.4 Lemma 6.11.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib
variable {ι κ n F : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [Fintype κ] [DecidableEq κ] [Fintype n] [DecidableEq n]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
local notation "E" => κ → ℝ
local notation "M" => Matrix n n ℂ

open scoped Matrix.Norms.L2Operator in
/-- Exact full-covariance resampling derivative in the actual operator space.
The bounds are only analytic domination hypotheses of this generic bridge;
the resolvent consumer proves them from its actual Hermitian process.
Source: arXiv:2201.05142v3, §6.4 Lemma 6.11.
atlas: matrix-resolvent-gaussian-universality (partial) -/
theorem hasDerivAt_resamplingInterpolation_matrix
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : E → E) 2 (ν i))
    (γ : Measure E) (hγ : HasGaussianLaw (id : E → E) γ)
    (hmean : ∀ i, ∫ z, z i ∂γ = 0)
    (hcov : ∀ i j,
      cov[(fun z : E => z i), (fun z : E => z j); γ] =
        cov[(fun p : ι × ((ι × Fin 3) → E) => resamplingTripleOriginal p i),
          (fun p : ι × ((ι × Fin 3) → E) => resamplingTripleOriginal p j);
          resamplingTripleMeasure ν])
    (Φ : E → M) (f : E → F) (df : E → E →L[ℝ] F)
    (B : E →L[ℝ] F →L[ℝ] M)
    (hΦ : ∀ y, HasFDerivAt Φ (B.flip (f y)) y)
    (hf : ∀ y, HasFDerivAt f (df y) y) (hdf : Continuous df)
    (CΦ C C' : ℝ) (hΦb : ∀ y, specNorm (Φ y) ≤ CΦ)
    (hfb : ∀ y, ‖f y‖ ≤ C) (hdfb : ∀ y, ‖df y‖ ≤ C')
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    let μ := ∫ p, resamplingTripleOriginal p ∂resamplingTripleMeasure ν
    let a := Real.sqrt t
    let b := Real.sqrt (1 - t)
    HasDerivAt (resamplingInterpolation ν γ Φ)
      (((Fintype.card ι : ℝ) / (4 * a)) •
          (∫ q, B (resamplingTripleOriginal q.1 - resamplingTripleFirst q.1)
            (f (resamplingAffinePoint μ a b (resamplingTripleOriginal q.1) q.2) -
              f (resamplingAffinePoint μ a b (resamplingTripleFirst q.1) q.2))
            ∂(resamplingTripleMeasure ν).prod γ) -
        ((Fintype.card ι : ℝ) / 4) •
          ∫ q, B (resamplingTripleOriginal q.1 - resamplingTripleFirst q.1)
            (df (resamplingAffinePoint μ a b (resamplingTripleSecond q.1) q.2)
              (resamplingTripleOriginal q.1 - resamplingTripleFirst q.1))
            ∂(resamplingTripleMeasure ν).prod γ) t := by
  have := hγ.isProbabilityMeasure
  dsimp only
  let μ := ∫ p, resamplingTripleOriginal p ∂resamplingTripleMeasure ν
  let P := resamplingTripleMeasure ν
  let Q := P.prod γ
  let a := Real.sqrt t
  let b := Real.sqrt (1 - t)
  let Y (s : ℝ) (q : (ι × ((ι × Fin 3) → E)) × E) :=
    resamplingAffinePoint μ (Real.sqrt s) (Real.sqrt (1 - s))
      (resamplingTripleOriginal q.1) q.2
  let d (q : (ι × ((ι × Fin 3) → E)) × E) :=
    resamplingTripleOriginal q.1 - resamplingTripleFirst q.1
  let Lterm q := B (d q)
    (f (resamplingAffinePoint μ a b (resamplingTripleOriginal q.1) q.2) -
      f (resamplingAffinePoint μ a b (resamplingTripleFirst q.1) q.2))
  let Hterm q := B (d q)
    (df (resamplingAffinePoint μ a b (resamplingTripleSecond q.1) q.2) (d q))
  let Vt : M := ((Fintype.card ι : ℝ) / (4 * a)) • (∫ q, Lterm q ∂Q) -
    ((Fintype.card ι : ℝ) / 4) • ∫ q, Hterm q ∂Q
  let e (i j : n) : M →L[ℝ] ℂ :=
    ((Matrix.entryLinearMap ℂ ℂ i j).toContinuousLinearMap).restrictScalars ℝ
  let Be (i j : n) : E →L[ℝ] F →L[ℝ] ℂ :=
    (ContinuousLinearMap.compL ℝ F M ℂ (e i j)).comp B
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun y => (hf y).continuousAt
  have hΦc : Continuous Φ := continuous_iff_continuousAt.mpr fun y => (hΦ y).continuousAt
  have hX := ((memLp_resamplingTriple_sums ν hν).1.integrable one_le_two).comp_fst γ
  have hZ := (hγ.memLp_two.integrable one_le_two).comp_snd P
  have hY (s : ℝ) : AEStronglyMeasurable (Y s) Q :=
    (aestronglyMeasurable_const.add
      ((hX.aestronglyMeasurable.sub aestronglyMeasurable_const).const_smul (Real.sqrt s))).add
        (hZ.aestronglyMeasurable.const_smul (Real.sqrt (1 - s)))
  have hΦint (s : ℝ) : Integrable (fun q => Φ (Y s q)) Q := by
    apply Integrable.of_bound (hΦc.comp_aestronglyMeasurable (hY s)) CΦ
    exact ae_of_all _ fun q => by simpa only [specNorm_eq_norm] using hΦb (Y s q)
  have hLint : Integrable Lterm Q := by
    apply Matrix.integrable_iff_entries.mpr
    intro i j
    exact (integrable_bilin_resamplingAffine ν hν γ a b f hfc C hfb (Be i j)).2
  have hHint : Integrable Hterm Q := by
    apply Matrix.integrable_iff_entries.mpr
    intro i j
    exact integrable_bilin_quadratic_resamplingTriple_affine ν hν γ μ a b df hdf C' hdfb (Be i j)
  have heΦ (i j : n) (y : E) :
      HasFDerivAt (fun y => e i j (Φ y)) ((Be i j).flip (f y)) y := by
    have h := (e i j).hasFDerivAt.comp y (hΦ y)
    convert! h using 1
  have heΦb (i j : n) (y : E) : ‖e i j (Φ y)‖ ≤ ‖e i j‖ * CΦ :=
    ((e i j).le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (by simpa only [specNorm_eq_norm] using hΦb y) (norm_nonneg _))
  have hentry (i j : n) :
      HasDerivAt (fun s => resamplingInterpolation ν γ Φ s i j) (Vt i j) t := by
    have hs := hasDerivAt_resamplingInterpolation ν hν γ hγ hmean hcov
      (fun y => e i j (Φ y)) f df (Be i j) (heΦ i j) hf hdf
      (‖e i j‖ * CΦ) C C' (heΦb i j) hfb hdfb ht ht1
    have heF : resamplingInterpolation ν γ (fun y => e i j (Φ y)) =
        (fun s => resamplingInterpolation ν γ Φ s i j) := by
      funext s
      exact (Matrix.integral_apply (hΦint s) i j).symm
    rw [heF] at hs
    convert hs using 1
    simp only [Vt, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.integral_apply hLint, Matrix.integral_apply hHint]
    rfl
  have hpi : HasDerivAt
      (fun s : ℝ => (fun i j : n => resamplingInterpolation ν γ Φ s i j))
      (fun i j : n => Vt i j) t :=
    hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => hentry i j
  let T : (n → n → ℂ) ≃L[ℂ] M :=
    (Matrix.ofLinearEquiv ℂ).toContinuousLinearEquiv
  have hM := (T.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hpi
  convert hM using 1 <;> rfl

end NLAlib
