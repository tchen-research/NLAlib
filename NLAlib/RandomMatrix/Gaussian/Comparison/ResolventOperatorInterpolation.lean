import NLAlib.Matrix.Functions.ResolventCoefficientFields
import NLAlib.Matrix.Functions.ResolventCancellation
import NLAlib.Probability.Gaussian.Comparison.MatrixResamplingInterpolation

/-!
# Actual operator-resolvent interpolation derivative

The native global bounds and derivatives of the actual Hermitian process
supply every analytic input of the genuine covariance-cancellation theorem.
The deterministic offset is carried independently of the summand laws.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
namespace NLAlib
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "J" => (n × n) ⊕ (n × n)
local notation "E" => J → ℝ
local notation "L" => (hermitianMatrixFromRealCoordinates : E →L[ℝ] M)

open scoped Matrix.Norms.L2Operator in
/-- Exact actual operator-resolvent derivative along square-root resampling.
Its quadratic cancellation uses all real/imaginary entry covariances; the
matrix primitive and its bounds are derived from the Hermitian process.
Source: arXiv:2201.05142v3, §6.4 Lemma 6.11.
atlas: matrix-resolvent-gaussian-universality (partial) -/
theorem hasDerivAt_resamplingInterpolation_hermitianCoordinateResolvent
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : E → E) 2 (ν i))
    (γ : Measure E) (hγ : HasGaussianLaw (id : E → E) γ)
    (hmean : ∀ i, ∫ z, z i ∂γ = 0)
    (hcov : ∀ i j,
      cov[(fun z : E => z i), (fun z : E => z j); γ] =
        cov[(fun p : ι × ((ι × Fin 3) → E) => resamplingTripleOriginal p i),
          (fun p : ι × ((ι × Fin 3) → E) => resamplingTripleOriginal p j);
          resamplingTripleMeasure ν])
    (A : M) (hA : A.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    let μ := ∫ p, resamplingTripleOriginal p ∂resamplingTripleMeasure ν
    let a := Real.sqrt t
    let b := Real.sqrt (1 - t)
    let Y₀ := fun q : (ι × ((ι × Fin 3) → E)) × E =>
      resamplingAffinePoint μ a b (resamplingTripleOriginal q.1) q.2
    let Y₁ := fun q : (ι × ((ι × Fin 3) → E)) × E =>
      resamplingAffinePoint μ a b (resamplingTripleFirst q.1) q.2
    let Y₂ := fun q : (ι × ((ι × Fin 3) → E)) × E =>
      resamplingAffinePoint μ a b (resamplingTripleSecond q.1) q.2
    let d := fun q : (ι × ((ι × Fin 3) → E)) × E =>
      L (resamplingTripleOriginal q.1 - resamplingTripleFirst q.1)
    let R := fun y => hermitianCoordinateResolvent A ζ y
    HasDerivAt (resamplingInterpolation ν γ (hermitianCoordinateResolvent A ζ))
      (((Fintype.card ι : ℝ) / (4 * a)) •
          (∫ q, R (Y₀ q) * d q * R (Y₀ q) - R (Y₁ q) * d q * R (Y₁ q)
            ∂(resamplingTripleMeasure ν).prod γ) -
        ((Fintype.card ι : ℝ) / 4) •
          ∫ q, (2 : ℝ) • (R (Y₂ q) * d q * R (Y₂ q) * d q * R (Y₂ q))
            ∂(resamplingTripleMeasure ν).prod γ) t := by
  let B : E →L[ℝ] (J → M) →L[ℝ] M := hermitianCoordinateCoefficientPairing
  have hΦ (y : E) : HasFDerivAt (hermitianCoordinateResolvent A ζ)
      (B.flip (hermitianCoordinateResolventCoefficients A ζ y)) y := by
    have he : B.flip (hermitianCoordinateResolventCoefficients A ζ y) =
        hermitianCoordinateResolventDeriv A ζ y := by
      ext u i j
      exact congrArg (fun C : M => C i j)
        (hermitianCoordinateCoefficientPairing_coefficients A ζ y u)
    rw [he]
    exact hasFDerivAt_hermitianCoordinateResolvent A hA ζ hζ y
  have h := hasDerivAt_resamplingInterpolation_matrix ν hν γ hγ hmean hcov
    (hermitianCoordinateResolvent A ζ) (hermitianCoordinateResolventCoefficients A ζ)
    (hermitianCoordinateResolventCoefficientsDeriv A ζ) B hΦ
    (hasFDerivAt_hermitianCoordinateResolventCoefficients A hA ζ hζ)
    (continuous_hermitianCoordinateResolventCoefficientsDeriv A hA ζ hζ)
    |ζ.im|⁻¹ (|ζ.im|⁻¹ ^ 2 * ‖L‖) (2 * |ζ.im|⁻¹ ^ 3 * ‖L‖ ^ 2)
    (specNorm_hermitianCoordinateResolvent_le A hA ζ hζ)
    (norm_hermitianCoordinateResolventCoefficients_le A hA ζ hζ)
    (norm_hermitianCoordinateResolventCoefficientsDeriv_le A hA ζ hζ) ht ht1
  dsimp only at h ⊢
  simpa only [B, hermitianCoordinateCoefficientPairing_sub_coefficients,
    hermitianCoordinateCoefficientPairing_coefficientsDeriv,
    hermitianCoordinateResolventDeriv_apply, hermitianCoordinateResolventSecondDeriv_apply,
    two_smul] using h


open scoped Matrix.Norms.L2Operator in
/-- The genuine six-word operator remainder is integrable, and it is the
actual derivative after discrete and Gaussian quadratic cancellation. Only
second moments and the full real-coordinate covariance match are assumed.
Source: arXiv:2201.05142v3, §6.4 Lemma 6.11.
atlas: matrix-resolvent-gaussian-universality (partial) -/
theorem integrable_and_hasDerivAt_resamplingInterpolation_resolventCubicRemainder
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : E → E) 2 (ν i))
    (γ : Measure E) (hγ : HasGaussianLaw (id : E → E) γ)
    (hmean : ∀ i, ∫ z, z i ∂γ = 0)
    (hcov : ∀ i j,
      cov[(fun z : E => z i), (fun z : E => z j); γ] =
        cov[(fun p : ι × ((ι × Fin 3) → E) => resamplingTripleOriginal p i),
          (fun p : ι × ((ι × Fin 3) → E) => resamplingTripleOriginal p j);
          resamplingTripleMeasure ν])
    (A : M) (hA : A.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    let P := resamplingTripleMeasure ν
    let Q := P.prod γ
    let μ := ∫ p, resamplingTripleOriginal p ∂P
    let a := Real.sqrt t
    let b := Real.sqrt (1-t)
    let Y₀ := fun q : (ι × ((ι × Fin 3) → E)) × E =>
      resamplingAffinePoint μ a b (resamplingTripleOriginal q.1) q.2
    let d := fun q : (ι × ((ι × Fin 3) → E)) × E =>
      L (resamplingTripleOriginal q.1-resamplingTripleFirst q.1)
    let f := fun q : (ι × ((ι × Fin 3) → E)) × E =>
      L (resamplingTripleOriginal q.1-resamplingTripleSecond q.1)
    let H := fun q => resolventCubicRemainder (A+L (Y₀ q)) (d q) (f q) a ζ
    Integrable H Q ∧
      HasDerivAt (resamplingInterpolation ν γ (hermitianCoordinateResolvent A ζ))
        (((Fintype.card ι : ℝ)*a/4) • ∫ q, H q ∂Q) t := by
  have := hγ.isProbabilityMeasure
  dsimp only
  let P := resamplingTripleMeasure ν
  let Q := P.prod γ
  let μ := ∫ p, resamplingTripleOriginal p ∂P
  let a := Real.sqrt t
  let b := Real.sqrt (1-t)
  let Y₀ := fun q : (ι × ((ι × Fin 3) → E)) × E =>
    resamplingAffinePoint μ a b (resamplingTripleOriginal q.1) q.2
  let Y₁ := fun q : (ι × ((ι × Fin 3) → E)) × E =>
    resamplingAffinePoint μ a b (resamplingTripleFirst q.1) q.2
  let Y₂ := fun q : (ι × ((ι × Fin 3) → E)) × E =>
    resamplingAffinePoint μ a b (resamplingTripleSecond q.1) q.2
  let d := fun q : (ι × ((ι × Fin 3) → E)) × E =>
    L (resamplingTripleOriginal q.1-resamplingTripleFirst q.1)
  let f := fun q : (ι × ((ι × Fin 3) → E)) × E =>
    L (resamplingTripleOriginal q.1-resamplingTripleSecond q.1)
  let R := hermitianCoordinateResolvent A ζ
  let H := fun q => resolventCubicRemainder (A+L (Y₀ q)) (d q) (f q) a ζ
  let V := fun q => R (Y₀ q)*d q*R (Y₀ q)-R (Y₁ q)*d q*R (Y₁ q)
  let K := fun q => (2 : ℝ) • (R (Y₂ q)*d q*R (Y₂ q)*d q*R (Y₂ q))
  let N : ℝ := Fintype.card ι
  let B : E →L[ℝ] (J → M) →L[ℝ] M := hermitianCoordinateCoefficientPairing
  let e (i j : n) : M →L[ℝ] ℂ :=
    ((Matrix.entryLinearMap ℂ ℂ i j).toContinuousLinearMap).restrictScalars ℝ
  let Be (i j : n) : E →L[ℝ] (J → M) →L[ℝ] ℂ :=
    (ContinuousLinearMap.compL ℝ (J → M) M ℂ (e i j)).comp B
  have ha : 0 < a := Real.sqrt_pos.mpr ht
  have hV : Integrable V Q := by
    apply Matrix.integrable_iff_entries.mpr
    intro i j
    have hi := (integrable_bilin_resamplingAffine (F := J → M) ν hν γ a b
      (hermitianCoordinateResolventCoefficients A ζ)
      (continuous_hermitianCoordinateResolventCoefficients A hA ζ hζ)
      (|ζ.im|⁻¹ ^ 2 * ‖L‖) (norm_hermitianCoordinateResolventCoefficients_le A hA ζ hζ)
      (Be i j)).2
    simpa only [V, R, d, Be, B, e, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.compL_apply, hermitianCoordinateCoefficientPairing_sub_coefficients,
      ContinuousLinearMap.coe_restrictScalars', LinearMap.coe_toContinuousLinearMap',
      Matrix.entryLinearMap_apply, hermitianCoordinateResolventDeriv_apply,
      Matrix.sub_apply] using hi
  have hK : Integrable K Q := by
    apply Matrix.integrable_iff_entries.mpr
    intro i j
    have hi := integrable_bilin_quadratic_resamplingTriple_affine (κ := J) (F := J → M) ν hν γ μ a b
      (hermitianCoordinateResolventCoefficientsDeriv A ζ)
      (continuous_hermitianCoordinateResolventCoefficientsDeriv A hA ζ hζ)
      (2 * |ζ.im|⁻¹ ^ 3 * ‖L‖ ^ 2)
      (norm_hermitianCoordinateResolventCoefficientsDeriv_le A hA ζ hζ) (Be i j)
    simpa only [K, R, d, Y₂, resamplingAffinePoint, Q, P, Be, B, e, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.compL_apply, hermitianCoordinateCoefficientPairing_coefficientsDeriv,
      ContinuousLinearMap.coe_restrictScalars', LinearMap.coe_toContinuousLinearMap',
      Matrix.entryLinearMap_apply, hermitianCoordinateResolventSecondDeriv_apply,
      two_smul, Matrix.add_apply, Matrix.smul_apply] using hi
  have hp (q : (ι × ((ι × Fin 3) → E)) × E) :
      V q = a • K q + a^2 • H q := by
    have h₀₁ : A+L (Y₀ q)-a • d q = A+L (Y₁ q) := by
      have hy : Y₀ q-Y₁ q =
          a • (resamplingTripleOriginal q.1-resamplingTripleFirst q.1) := by
        dsimp [Y₀, Y₁, resamplingAffinePoint]
        module
      have hl : L (Y₀ q)-L (Y₁ q) = a • d q := by
        rw [← map_sub, hy, map_smul]
      rw [← hl]
      abel
    have h₀₂ : A+L (Y₀ q)-a • f q = A+L (Y₂ q) := by
      have hy : Y₀ q-Y₂ q =
          a • (resamplingTripleOriginal q.1-resamplingTripleSecond q.1) := by
        dsimp [Y₀, Y₂, resamplingAffinePoint]
        module
      have hl : L (Y₀ q)-L (Y₂ q) = a • f q := by
        rw [← map_sub, hy, map_smul]
      rw [← hl]
      abel
    have hh := resolvent_mul_resolvent_sub_eq_smul_add_smul_sq
      (A+L (Y₀ q)) (d q) (f q) a ζ
      (hA.add (isHermitian_hermitianMatrixFromRealCoordinates _))
      (isHermitian_hermitianMatrixFromRealCoordinates _)
      (isHermitian_hermitianMatrixFromRealCoordinates _) hζ
    dsimp only at hh
    rw [h₀₁, h₀₂] at hh
    exact hh
  have hH : Integrable H Q := by
    have hi := (hV.sub (hK.smul a)).smul ((a^2)⁻¹)
    refine hi.congr (ae_of_all _ fun q => ?_)
    change (a^2)⁻¹ • (V q-a • K q) = H q
    rw [hp, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 ha.ne'), one_smul]
  refine ⟨hH, ?_⟩
  have hfirst : (∫ q, V q ∂Q) = a • (∫ q, K q ∂Q)+a^2 • ∫ q, H q ∂Q := by
    simp_rw [hp]
    have hKa : Integrable (fun q => a • K q) Q := by
      exact (hK.smul a).congr (ae_of_all _ fun q => rfl)
    have hHa : Integrable (fun q => a^2 • H q) Q := by
      exact (hH.smul (a^2)).congr (ae_of_all _ fun q => rfl)
    rw [integral_add hKa hHa]
    simp only [integral_smul]
  have hd := hasDerivAt_resamplingInterpolation_hermitianCoordinateResolvent ν hν γ hγ
    hmean hcov A hA ζ hζ ht ht1
  change HasDerivAt _ ((N/(4*a)) • (∫ q, V q ∂Q)-(N/4) • ∫ q, K q ∂Q) t at hd
  apply hd.congr_deriv
  rw [hfirst, smul_add, smul_smul, smul_smul]
  have hca : N/(4*a)*a = N/4 := by field_simp [ha.ne']
  have hcb : N/(4*a)*a^2 = N*a/4 := by field_simp [ha.ne']
  rw [hca, hcb]
  abel

end NLAlib
