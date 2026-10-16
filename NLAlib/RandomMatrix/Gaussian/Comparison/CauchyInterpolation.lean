import NLAlib.Probability.Gaussian.Comparison.ResamplingInterpolation
import NLAlib.Probability.Moments.MatrixDifferenceTransport
import NLAlib.Probability.Moments.ResolventRemainder
import NLAlib.Matrix.Functions.ResolventCoordinateDifferences
import NLAlib.ForMathlib.Analysis.IntegralSpeed

/-!
# Sharp Cauchy comparison along the actual interpolation

The primitive and its derivatives are the actual reconstructed Hermitian
resolvents. Genuine discrete and Gaussian Stein identities cancel their
quadratic terms. The remaining six ordered words have actual third moments,
and integrating the square-root speed preserves the exact constant one.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open MeasureTheory ProbabilityTheory Set
namespace NLAlib
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ
local notation "J" => (n × n) ⊕ (n × n)
local notation "E" => J → ℝ
local notation "Ω" => (ι × ((ι × Fin 3) → E)) × E
local notation "L" => (hermitianMatrixFromRealCoordinates : E →L[ℝ] M)

open scoped Matrix.Norms.L2Operator in
/-- Sharp constant-one Cauchy comparison on the actual coordinate summand and
independent Gaussian laws. All summand third moments and the full real-entry
covariance match are explicit; no analytic cancellation or remainder estimate
is assumed. Source: supplied Cauchy-transform reroute, comparison-main.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem norm_resamplingInterpolation_trace_resolvent_sub_le_matrixDifferenceThirdMoment
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : E → E) 3 (ν i))
    (γ : Measure E) (hγ : HasGaussianLaw (id : E → E) γ)
    (hmean : ∀ i, ∫ z, z i ∂γ = 0)
    (hcov : ∀ i j,
      cov[(fun z : E => z i), (fun z : E => z j); γ] =
        cov[(fun p : ι × ((ι × Fin 3) → E) => resamplingTripleOriginal p i),
          (fun p : ι × ((ι × Fin 3) → E) => resamplingTripleOriginal p j);
          resamplingTripleMeasure ν])
    (ζ : ℂ) (hζ : ζ.im ≠ 0) :
    ‖resamplingInterpolation ν γ (hermitianCoordinateTraceResolvent ζ) 1 -
      resamplingInterpolation ν γ (hermitianCoordinateTraceResolvent ζ) 0‖ ≤
      matrixDifferenceThirdMoment (fun i => (ν i).map L) / |ζ.im|^4 := by
  letI := hγ.isProbabilityMeasure
  have hν₂ (i : ι) : MemLp (id : E → E) 2 (ν i) := (hν i).mono_exponent (by norm_num)
  let P := resamplingTripleMeasure ν
  let Q := P.prod γ
  let μ := ∫ p, resamplingTripleOriginal p ∂P
  let X₀ : Ω → E := fun q => resamplingTripleOriginal q.1
  let X₁ : Ω → E := fun q => resamplingTripleFirst q.1
  let X₂ : Ω → E := fun q => resamplingTripleSecond q.1
  let d : Ω → E := X₀-X₁
  let e : Ω → E := X₁-X₂
  let f : Ω → E := X₀-X₂
  let Y₀ : ℝ → Ω → E := fun t q =>
    resamplingAffinePoint μ (Real.sqrt t) (Real.sqrt (1-t)) (X₀ q) q.2
  let Y₁ : ℝ → Ω → E := fun t q =>
    resamplingAffinePoint μ (Real.sqrt t) (Real.sqrt (1-t)) (X₁ q) q.2
  let Y₂ : ℝ → Ω → E := fun t q =>
    resamplingAffinePoint μ (Real.sqrt t) (Real.sqrt (1-t)) (X₂ q) q.2
  let R : ℝ → Ω → ℂ := fun t q => normalizedTrace
    (L (d q) * resolventSquareSecondDifference ζ (L (Y₀ t q)) (L (Y₁ t q))
      (L (Y₂ t q)) (L (d q)) (L (e q)) +
     L (d q) * resolventSquareSecondDifference ζ (L (Y₀ t q)) (L (Y₂ t q))
      (L (Y₂ t q)) (L (f q)) (L (d q)))
  let N : ℝ := Fintype.card ι
  let m₃ := matrixDifferenceThirdMoment (fun i => (ν i).map L)
  let v : ℝ → ℂ := fun t => (N * Real.sqrt t / 4) • ∫ q, R t q ∂Q
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hdf := continuous_hermitianCoordinateSquaredResolventDerivative (n := n) ζ hζ
  have hΦ (y : E) : HasFDerivAt (hermitianCoordinateTraceResolvent ζ)
      (hermitianCoordinateTraceProduct.flip (hermitianCoordinateSquaredResolvent ζ y)) y := by
    have he : hermitianCoordinateTraceProduct.flip (hermitianCoordinateSquaredResolvent ζ y) =
        hermitianCoordinateTraceResolventDerivative ζ y := by
      apply ContinuousLinearMap.ext
      intro h
      exact (hermitianCoordinateTraceResolventDerivative_apply ζ y h).symm
    rw [he]
    exact hasFDerivAt_hermitianCoordinateTraceResolvent ζ hζ y
  have hΦc : Continuous (hermitianCoordinateTraceResolvent (n := n) ζ) :=
    continuous_iff_continuousAt.mpr (fun y => (hΦ y).continuousAt)
  have hm := memLp_resamplingTriple_sums ν hν₂
  have hX₀ : Integrable X₀ Q := (hm.1.integrable one_le_two).comp_fst γ
  have hX₁ : Integrable X₁ Q := (hm.2.1.integrable one_le_two).comp_fst γ
  have hX₂ : Integrable X₂ Q := (hm.2.2.integrable one_le_two).comp_fst γ
  have hZ : Integrable (fun q : Ω => q.2) Q :=
    (hγ.memLp_two.integrable one_le_two).comp_snd P
  have hX₀m := hX₀.aestronglyMeasurable.aemeasurable
  have hX₁m := hX₁.aestronglyMeasurable.aemeasurable
  have hX₂m := hX₂.aestronglyMeasurable.aemeasurable
  have hZm := hZ.aestronglyMeasurable.aemeasurable
  have hY₀ (t : ℝ) : AEMeasurable (fun q => L (Y₀ t q)) Q := by
    have hy : AEMeasurable (Y₀ t) Q :=
      (aemeasurable_const.add ((hX₀m.sub aemeasurable_const).const_smul (Real.sqrt t))).add
        (hZm.const_smul (Real.sqrt (1-t)))
    exact (L).continuous.measurable.comp_aemeasurable hy
  have hY₁ (t : ℝ) : AEMeasurable (fun q => L (Y₁ t q)) Q := by
    have hy : AEMeasurable (Y₁ t) Q :=
      (aemeasurable_const.add ((hX₁m.sub aemeasurable_const).const_smul (Real.sqrt t))).add
        (hZm.const_smul (Real.sqrt (1-t)))
    exact (L).continuous.measurable.comp_aemeasurable hy
  have hY₂ (t : ℝ) : AEMeasurable (fun q => L (Y₂ t q)) Q := by
    have hy : AEMeasurable (Y₂ t) Q :=
      (aemeasurable_const.add ((hX₂m.sub aemeasurable_const).const_smul (Real.sqrt t))).add
        (hZm.const_smul (Real.sqrt (1-t)))
    exact (L).continuous.measurable.comp_aemeasurable hy
  have hd : AEMeasurable (fun q => L (d q)) Q :=
    (L).continuous.measurable.comp_aemeasurable (hX₀m.sub hX₁m)
  have he : AEMeasurable (fun q => L (e q)) Q :=
    (L).continuous.measurable.comp_aemeasurable (hX₁m.sub hX₂m)
  have hf : AEMeasurable (fun q => L (f q)) Q :=
    (L).continuous.measurable.comp_aemeasurable (hX₀m.sub hX₂m)
  have h₃i := integrable_schattenNormReal_resamplingTriple_prod_differences ν hν L γ
  have h₃m := integral_schattenNormReal_resamplingTriple_prod_differences ν hν L γ
  have hR (t : ℝ) : Integrable (R t) Q ∧ ‖∫ q, R t q ∂Q‖ ≤ 6 * (m₃/N) / |ζ.im|^4 :=
    integrable_and_norm_integral_six_word_remainder_le ζ hζ
      (fun q => L (Y₀ t q)) (fun q => L (Y₁ t q)) (fun q => L (Y₂ t q))
      (fun q => L (d q)) (fun q => L (e q)) (fun q => L (f q))
      (hY₀ t) (hY₁ t) (hY₂ t) hd he hf
      (ae_of_all _ fun q => isHermitian_hermitianMatrixFromRealCoordinates _)
      (ae_of_all _ fun q => isHermitian_hermitianMatrixFromRealCoordinates _)
      (ae_of_all _ fun q => isHermitian_hermitianMatrixFromRealCoordinates _)
      h₃i.1 h₃i.2.1 h₃i.2.2 (m₃/N) h₃m.1 h₃m.2.1 h₃m.2.2
  have hv (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (resamplingInterpolation ν γ (hermitianCoordinateTraceResolvent ζ)) (v t) t := by
    let a := Real.sqrt t
    let b := Real.sqrt (1-t)
    have ha : 0 < a := Real.sqrt_pos.mpr ht.1
    let K : Ω → ℂ := fun q => hermitianCoordinateTraceProduct (d q)
      (hermitianCoordinateSquaredResolventDerivative ζ (Y₂ t q) (d q))
    have hK : Integrable K Q :=
      integrable_bilin_quadratic_resamplingTriple_affine ν hν₂ γ μ a b
        (hermitianCoordinateSquaredResolventDerivative ζ) hdf
        (2 * |ζ.im|⁻¹^3 * ‖L‖)
        (norm_hermitianCoordinateSquaredResolventDerivative_le ζ hζ) hermitianCoordinateTraceProduct
    have hp (q : Ω) : hermitianCoordinateTraceProduct (d q)
        (hermitianCoordinateSquaredResolvent ζ (Y₀ t q) -
          hermitianCoordinateSquaredResolvent ζ (Y₁ t q)) = a • K q + a^2 • R t q := by
      have h01 : Y₀ t q-Y₁ t q = a • d q := by dsimp [Y₀,Y₁,d,a,resamplingAffinePoint]; module
      have h12 : Y₁ t q-Y₂ t q = a • e q := by dsimp [Y₁,Y₂,e,a,resamplingAffinePoint]; module
      have h02 : Y₀ t q-Y₂ t q = a • f q := by dsimp [Y₀,Y₂,f,a,resamplingAffinePoint]; module
      simpa only [Matrix.mul_add] using
        hermitianCoordinateTraceProduct_squaredResolvent_affine_remainder ζ hζ
          (Y₀ t q) (Y₁ t q) (Y₂ t q) (d q) (e q) (f q) a h01 h12 h02
    have hfirst : (∫ q, hermitianCoordinateTraceProduct (d q)
        (hermitianCoordinateSquaredResolvent ζ (Y₀ t q) -
          hermitianCoordinateSquaredResolvent ζ (Y₁ t q)) ∂Q) =
        a • (∫ q, K q ∂Q) + a^2 • ∫ q, R t q ∂Q := by
      simp_rw [hp]
      have hKa : Integrable (fun q => a • K q) Q := by
        refine (hK.smul a).congr ?_
        filter_upwards [] with q
        rfl
      have hRa : Integrable (fun q => a^2 • R t q) Q := by
        refine ((hR t).1.smul (a^2)).congr ?_
        filter_upwards [] with q
        rfl
      rw [integral_add hKa hRa,integral_smul,integral_smul]
    have hderiv := hasDerivAt_resamplingInterpolation ν hν₂ γ hγ hmean hcov
      (hermitianCoordinateTraceResolvent ζ) (hermitianCoordinateSquaredResolvent ζ)
      (hermitianCoordinateSquaredResolventDerivative ζ) hermitianCoordinateTraceProduct hΦ
      (hasFDerivAt_hermitianCoordinateSquaredResolvent ζ hζ) hdf
      |ζ.im|⁻¹ (|ζ.im|⁻¹^2) (2 * |ζ.im|⁻¹^3 * ‖L‖)
      (norm_hermitianCoordinateTraceResolvent_le ζ hζ)
      (specNorm_hermitianCoordinateSquaredResolvent_le ζ hζ)
      (norm_hermitianCoordinateSquaredResolventDerivative_le ζ hζ) ht.1 ht.2
    change HasDerivAt _ ((N/(4*a)) • (∫ q, hermitianCoordinateTraceProduct (d q)
        (hermitianCoordinateSquaredResolvent ζ (Y₀ t q) -
          hermitianCoordinateSquaredResolvent ζ (Y₁ t q)) ∂Q) -
      (N/4) • ∫ q, K q ∂Q) t at hderiv
    apply hderiv.congr_deriv
    rw [hfirst,smul_add,smul_smul,smul_smul]
    have hca : N/(4*a)*a = N/4 := by field_simp [ha.ne']
    have hcb : N/(4*a)*a^2 = N*a/4 := by field_simp [ha.ne']
    rw [hca,hcb]
    dsimp [v,a]
    abel
  apply norm_sub_le_of_norm_deriv_le_sqrt _ v
    (continuous_resamplingInterpolation ν hν₂ γ _ hΦc |ζ.im|⁻¹
      (norm_hermitianCoordinateTraceResolvent_le ζ hζ)).continuousOn hv
    (m₃/|ζ.im|^4)
  intro t ht
  have hc : 0 ≤ N*Real.sqrt t/4 := by positivity
  calc
    ‖v t‖ = (N*Real.sqrt t/4) * ‖∫ q, R t q ∂Q‖ := by
      change ‖(N*Real.sqrt t/4) • (∫ q, R t q ∂Q)‖ = _
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hc]
    _ ≤ (N*Real.sqrt t/4) * (6*(m₃/N)/|ζ.im|^4) :=
      mul_le_mul_of_nonneg_left (hR t).2 hc
    _ = (3/2) * Real.sqrt t * (m₃/|ζ.im|^4) := by field_simp [hN.ne']; ring

end NLAlib
