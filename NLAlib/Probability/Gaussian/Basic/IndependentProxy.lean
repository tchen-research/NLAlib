import NLAlib.Probability.Gaussian.Basic.CovarianceProxy
import NLAlib.Probability.Gaussian.Basic.MatrixSumCovariance

/-!
# Actual Gaussian covariance proxies for independent matrix sums

Centered Hermitian marginal laws with finite second moments have a centered
Hermitian Gaussian proxy for the covariance of their independent sum.
No nonsingularity or supplied Gaussian law is required.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
local notation "M" => Matrix n n ℂ
local notation "J" => (n × n) ⊕ (n × n)

open scoped Matrix.Norms.L2Operator in
/-- A finite family of centered Hermitian matrix laws has an actual centered
Hermitian Gaussian proxy whose full covariance is the sum of the marginal
covariances. Singular covariance and empty families are included.
Source: Gaussian covariance construction in Tropp's BMV replacement argument. -/
theorem exists_isGaussian_hermitian_integral_eq_zero_covariance_eq_sum
    (ν : ι → Measure M) [∀ i, IsProbabilityMeasure (ν i)]
    (hν2 : ∀ i, MemLp (matrixRealCoordinates : M → J → ℝ) 2 (ν i))
    (hνmean : ∀ i, (∫ H, H ∂ν i) = 0)
    (hνHerm : ∀ i, ∀ᵐ H ∂ν i, H.IsHermitian) :
    ∃ γ : Measure M, IsGaussian γ ∧ (∫ H, H ∂γ) = 0 ∧
      (∀ᵐ H ∂γ, H.IsHermitian) ∧ ∀ a b,
        (∑ i, cov[fun H => matrixRealCoordinates H a, fun H => matrixRealCoordinates H b; ν i]) =
          cov[fun H => matrixRealCoordinates H a, fun H => matrixRealCoordinates H b; γ] := by
  classical
  choose η hη hηmean hηHerm hηcov using fun i =>
    exists_isGaussian_hermitian_integral_eq_zero_covariance_eq
      (ν i) (hν2 i) (hνmean i) (hνHerm i)
  let (i : ι) : IsGaussian (η i) := hη i
  refine ⟨(Measure.pi η).map (fun x : ι → M => ∑ i, x i),
    isGaussian_map_sum_pi η, ?_, ae_isHermitian_map_sum_pi η hηHerm, ?_⟩
  · rw [integral_id_map_sum_pi_gaussian]
    simp only [hηmean, Finset.sum_const_zero]
  · intro a b
    rw [covariance_matrixRealCoordinates_map_sum_pi_eq_sum]
    simp only [hηcov]

/-- The full covariance of actual independent matrix-valued random variables
is the sum of the covariances of their marginal laws. -/
theorem covariance_matrixRealCoordinates_sum_eq_sum_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (W : ι → Ω → M) (ν : ι → Measure M)
    (hW : ∀ i, HasLaw (W i) (ν i) P) (hind : iIndepFun W P)
    (hν2 : ∀ i, MemLp (matrixRealCoordinates : M → J → ℝ) 2 (ν i)) (a b : J) :
    cov[fun ω => matrixRealCoordinates (∑ i, W i ω) a,
      fun ω => matrixRealCoordinates (∑ i, W i ω) b; P] =
        ∑ i, cov[fun H => matrixRealCoordinates H a, fun H => matrixRealCoordinates H b; ν i] := by
  have hW2 (i : ι) : MemLp (fun ω => matrixRealCoordinates (W i ω)) 2 P := by
    have hi := hν2 i
    rw [← (hW i).map_eq] at hi
    exact (memLp_map_measure_iff continuous_matrixRealCoordinates.aestronglyMeasurable
      (hW i).aemeasurable).mp hi
  rw [covariance_matrixRealCoordinates_sum_eq_sum W hW2 hind]
  apply Finset.sum_congr rfl
  intro i _
  exact (hW i).covariance_fun_comp
    (f := fun H => matrixRealCoordinates H a) (g := fun H => matrixRealCoordinates H b)
    (by fun_prop) (by fun_prop)

end NLAlib
