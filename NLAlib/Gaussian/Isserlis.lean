import NLAlib.Gaussian.WickPairings
import NLAlib.Gaussian.CovarianceRepresentation

/-!
# General centered Gaussian Isserlis–Wick formula

All centered Gaussian vector laws, including correlated and singular covariance,
have the finite pairing formula for arbitrary moments and repeated indices.
Source: Isserlis 1918; operator re-derivation `pg:wick`.
Atlas: `isserlis`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder
namespace NLAlib

/-- For a centered Gaussian vector, covariance entries are exactly its
coordinate product expectations. Source: operator re-derivation
`pg:gaussian-linear-image`; supports `isserlis`. -/
theorem gaussianCovarianceMatrix_apply_eq_integral_mul_of_centered {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsGaussian μ]
    (hmean : ∫ x, x ∂μ = 0) (i j : Fin n) :
    gaussianCovarianceMatrix μ i j = ∫ x, x i * x j ∂μ := by
  have hmem : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 μ := by
    intro i
    exact IsGaussian.memLp_dual μ (EuclideanSpace.proj i) 2 (by simp)
  have hm : ∀ i : Fin n, ∫ x : EuclideanSpace ℝ (Fin n), x i ∂μ = 0 := by
    intro i
    have hh := (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).integral_comp_comm
      (show Integrable (fun x : EuclideanSpace ℝ (Fin n) => x) μ from IsGaussian.integrable_id)
    simpa only [EuclideanSpace.coe_proj, hmean, map_zero] using hh
  rw [gaussianCovarianceMatrix_apply μ IsGaussian.memLp_two_id,
    covariance_eq_sub (hmem i) (hmem j), hm, hm, zero_mul, sub_zero]
  rfl

/-- The full finite pairing formula for any centered Gaussian vector law.
The covariance can be correlated or singular, and index positions may repeat.
The canonical finite pairing type matches each first remaining position with
one partner and covers every position exactly once.
Source: Isserlis 1918; operator re-derivation `pg:wick`.
atlas: isserlis -/
theorem integral_prod_eval_gaussian_eq_sum_pairings {n m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsGaussian μ]
    (hmean : ∫ x, x ∂μ = 0) (idx : Fin m → Fin n) :
    ∫ x, ∏ r, x (idx r) ∂μ =
      ∑ π : GaussianPairings m,
        gaussianPairingWeight (fun a b => gaussianCovarianceMatrix μ (idx a) (idx b)) π := by
  let C := gaussianCovarianceMatrix μ
  let L := CFC.sqrt C
  have hC : C.PosSemidef := gaussianCovarianceMatrix_posSemidef μ
  have hL : L.IsSymm := Matrix.isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg C).isSelfAdjoint
  have hsq : L * L = C := CFC.sqrt_mul_sqrt_self C hC.nonneg
  have hdot : ∀ i j : Fin n, (fun a => L i a) ⬝ᵥ (fun a => L j a) = C i j := by
    intro i j
    change (L * Lᵀ) i j = C i j
    rw [hL.eq, hsq]
  have hrep := gaussian_eq_map_pi_sqrt_covariance_of_centered μ hmean
  have h := integral_prod_dotProduct_eq_sum_gaussianPairingWeight
    (fun r : Fin m => fun a => L (idx r) a)
  have hmap : (∫ x, ∏ r, x (idx r) ∂μ) =
      ∫ x : Fin n → ℝ, ∏ r, (fun a => L (idx r) a) ⬝ᵥ x
        ∂Measure.pi (fun _ => gaussianReal 0 1) := by
    rw [hrep, integral_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hmap]
  simpa only [hdot, C] using h

/-- The Isserlis formula with covariance spelled directly as coordinate product
expectations, including singular laws and repeated indices.
Source: Isserlis 1918; operator re-derivation `pg:wick`.
atlas: isserlis -/
theorem integral_prod_eval_gaussian_eq_sum_integral_mul_pairings {n m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsGaussian μ]
    (hmean : ∫ x, x ∂μ = 0) (idx : Fin m → Fin n) :
    ∫ x, ∏ r, x (idx r) ∂μ =
      ∑ π : GaussianPairings m,
        gaussianPairingWeight (fun a b => ∫ x, x (idx a) * x (idx b) ∂μ) π := by
  simpa only [gaussianCovarianceMatrix_apply_eq_integral_mul_of_centered μ hmean] using
    integral_prod_eval_gaussian_eq_sum_pairings μ hmean idx

/-- Every odd product of coordinates of any centered Gaussian vector has
expectation zero. Source: operator re-derivation `pg:wick`.
atlas: isserlis -/
theorem integral_prod_eval_gaussian_eq_zero_of_odd {n m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsGaussian μ]
    (hmean : ∫ x, x ∂μ = 0) (idx : Fin m → Fin n) (hm : Odd m) :
    ∫ x, ∏ r, x (idx r) ∂μ = 0 := by
  have hrep := gaussian_eq_map_pi_sqrt_covariance_of_centered μ hmean
  rw [hrep, integral_map (by fun_prop) (by fun_prop)]
  exact integral_prod_dotProduct_eq_zero_of_odd hm
    (fun r a => CFC.sqrt (gaussianCovarianceMatrix μ) (idx r) a)

/-- Every product in the general centered Gaussian Wick formula is absolutely
integrable, including correlated and singular covariance and repeated indices.
Source: operator re-derivation `pg:polynomial-stein`, `pg:gaussian-linear-image`. -/
theorem integrable_prod_eval_gaussian_of_centered {n m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsGaussian μ]
    (hmean : ∫ x, x ∂μ = 0) (idx : Fin m → Fin n) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => ∏ r, x (idx r)) μ := by
  rw [gaussian_eq_map_pi_sqrt_covariance_of_centered μ hmean]
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  exact integrable_prod_dotProduct_pi_gaussianReal Finset.univ
    (fun r a => CFC.sqrt (gaussianCovarianceMatrix μ) (idx r) a)

/-- The full Isserlis formula for a centered Gaussian vector on an arbitrary
probability space, with covariance written as its actual coordinate product
expectations. Correlated/singular laws and repeated coordinate positions are
included. Source: Isserlis 1918; operator re-derivation `pg:wick`.
atlas: isserlis -/
theorem integral_prod_gaussianVector_eq_sum_pairings
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m : ℕ} (G : Ω → EuclideanSpace ℝ (Fin n)) (hG : HasGaussianLaw G P)
    (hmean : ∫ ω, G ω ∂P = 0) (idx : Fin m → Fin n) :
    ∫ ω, ∏ r, G ω (idx r) ∂P =
      ∑ π : GaussianPairings m,
        gaussianPairingWeight (fun a b => ∫ ω, G ω (idx a) * G ω (idx b) ∂P) π := by
  have := hG.isGaussian_map
  have hm : ∫ x, x ∂P.map G = 0 := by
    calc
      _ = ∫ ω, G ω ∂P := integral_map hG.aemeasurable (by fun_prop)
      _ = 0 := hmean
  have hh := integral_prod_eval_gaussian_eq_sum_integral_mul_pairings (P.map G) hm idx
  have hout : (∫ x : EuclideanSpace ℝ (Fin n), ∏ r, x (idx r) ∂P.map G) =
      ∫ ω, ∏ r, G ω (idx r) ∂P := integral_map hG.aemeasurable (by fun_prop)
  have hcov : ∀ a b : Fin m,
      (∫ x : EuclideanSpace ℝ (Fin n), x (idx a) * x (idx b) ∂P.map G) =
      ∫ ω, G ω (idx a) * G ω (idx b) ∂P :=
    fun a b => integral_map hG.aemeasurable (by fun_prop)
  simpa only [hout, hcov] using hh

/-- Abstract centered Gaussian-vector product moments are absolutely integrable.
Source: operator re-derivation `pg:wick`, transport of the canonical Gaussian law. -/
theorem integrable_prod_gaussianVector_of_centered
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m : ℕ} (G : Ω → EuclideanSpace ℝ (Fin n)) (hG : HasGaussianLaw G P)
    (hmean : ∫ ω, G ω ∂P = 0) (idx : Fin m → Fin n) :
    Integrable (fun ω => ∏ r, G ω (idx r)) P := by
  have := hG.isGaussian_map
  have hm : ∫ x, x ∂P.map G = 0 := by
    calc
      _ = ∫ ω, G ω ∂P := integral_map hG.aemeasurable (by fun_prop)
      _ = 0 := hmean
  exact (integrable_map_measure (by fun_prop) hG.aemeasurable).mp
    (integrable_prod_eval_gaussian_of_centered (P.map G) hm idx)

end NLAlib
