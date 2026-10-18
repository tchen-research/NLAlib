import NLAlib.Probability.Concentration.Matrix.GaussianProxy
import NLAlib.Probability.Gaussian.Basic.IndependentProxy

/-!
# Gaussian-proxy eigenvalue bounds with a constructed proxy

An actual centered Hermitian Gaussian proxy is constructed from the summand
laws, then the expectation and sharp upper-tail comparison are applied. The
same proxy works for every deterministic Hermitian shift.
Source: Tropp (2026), Theorem 1.1.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix MatrixOrder
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ
local notation "J" => (n × n) ⊕ (n × n)

open scoped Matrix.Norms.L2Operator in
/-- Independent centered Hermitian random matrices with finite second moments
and a one-sided summand bound admit an actual Gaussian proxy satisfying both
the expectation comparison and the sharp upper tail. Its full covariance is
the covariance of the actual random sum. No proxy-existence hypothesis is
needed. Source: Tropp (2026), Theorem 1.1.
atlas: gaussian-proxy-eigenvalue-comparison -/
theorem exists_isGaussian_integral_lambdaMax_sum_le_and_measure_gt_le_of_hasLaw
    {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (W : Fin N → Ω → M) (ν : Fin N → Measure M)
    (hW : ∀ i, HasLaw (W i) (ν i) P) (hind : iIndepFun W P)
    (hν2 : ∀ i, MemLp (matrixRealCoordinates : M → J → ℝ) 2 (ν i))
    (hνmean : ∀ i, (∫ H, H ∂ν i) = 0)
    (hνHerm : ∀ i, ∀ᵐ H ∂ν i, H.IsHermitian)
    {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ i, ∀ᵐ H ∂ν i, H ≤ R • (1 : M)) :
    ∃ γ : Measure M, IsGaussian γ ∧ (∫ H, H ∂γ) = 0 ∧
      (∀ᵐ H ∂γ, H.IsHermitian) ∧
      (∀ a b, cov[fun ω => matrixRealCoordinates (∑ i, W i ω) a,
        fun ω => matrixRealCoordinates (∑ i, W i ω) b; P] =
          cov[fun H => matrixRealCoordinates H a, fun H => matrixRealCoordinates H b; γ]) ∧
      ∀ D : M, D.IsHermitian →
        (∫ ω, lambdaMax ((∑ i, W i ω) + D) ∂P) ≤
            (∫ Z, lambdaMax (D + Z) ∂γ) +
              Real.sqrt (2 * gaussianProxyVariance γ R * Real.log (Fintype.card n)) +
              (R / 3) * Real.log (Fintype.card n) ∧
        (∀ s : ℝ, 0 ≤ s → P.real {ω |
            (∫ Z, lambdaMax (D + Z) ∂γ) + Real.sqrt (2 * gaussianProxyVariance γ R * s) +
              (R / 3) * s < lambdaMax ((∑ i, W i ω) + D)} ≤
                (Fintype.card n : ℝ) * Real.exp (-s)) ∧
        (0 < R → ∀ s : ℝ, 0 ≤ s → P.real {ω |
            (∫ Z, lambdaMax (D + Z) ∂γ) + Real.sqrt (2 * gaussianProxyVariance γ R * s) +
              (R / 3) * s ≤ lambdaMax ((∑ i, W i ω) + D)} ≤
                (Fintype.card n : ℝ) * Real.exp (-s)) := by
  let (i : Fin N) : IsProbabilityMeasure (ν i) :=
    (hW i).isProbabilityMeasure_iff.mp inferInstance
  obtain ⟨γ, hγ, hγmean, hγHerm, hγcov⟩ :=
    exists_isGaussian_hermitian_integral_eq_zero_covariance_eq_sum ν hν2 hνmean hνHerm
  let : IsGaussian γ := hγ
  refine ⟨γ, hγ, hγmean, hγHerm, ?_, ?_⟩
  · intro a b
    exact (covariance_matrixRealCoordinates_sum_eq_sum_of_hasLaw W ν hW hind hν2 a b).trans
      (hγcov a b)
  · intro D hD
    exact integral_lambdaMax_sum_le_and_measure_gt_le_gaussian_proxy_of_hasLaw
      W ν hW hind hν2 hνmean hνHerm hR hbound γ hγHerm hγmean hγcov D hD

end NLAlib
