import NLAlib.Matrix.Functions.AggregateResolventMomentTaylor
import NLAlib.Probability.Transforms.ResolventMoments
import NLAlib.ForMathlib.MeasureTheory.FractionalHolder

/-!
# Actual expected aggregate cubic moment Taylor kernels

Continuity of the native kernel supplies measurability. Its actual aggregate
bound and Hölder derive integrability and the sharp expectation bound from
only the computed three-copy square-mass moment. The common base and copies
may have arbitrary dependence.
Source: Brailovskaya--van Handel, arXiv:2201.05142v3, Lemma 6.9.
Supports independent-sum-spectrum-universality (partial).
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped Matrix ENNReal
namespace NLAlib
variable {n ι Ω : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [MeasurableSpace Ω]
local notation "M" => Matrix n n ℂ
local notation "E" => ((n × n) ⊕ (n × n)) → ℝ
local notation "L" => (hermitianMatrixFromRealCoordinates : E →L[ℝ] M)

open scoped Matrix.Norms.L2Operator in
/-- The actual finite sum of first-copy moment Taylor kernels is measurable
and integrable, with the aggregate mass Hölder bound. Only the computed mass
needs an `L(2p)` moment; no independence or matrix-tail moment of the common
base is assumed. Zero radius and empty matrix or family shapes are included. -/
theorem integrable_and_norm_integral_sum_resolventMomentTaylorKernel_first_copy_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : M) (hA : A.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0)
    {p : ℕ} (hp : 0 < p) (x₀ : Ω → E) (hx₀m : AEMeasurable x₀ μ)
    (z : Ω → Fin 3 → ι → E) (hzm : AEMeasurable z μ)
    {R : ℝ} (hR : 0 ≤ R)
    (hZ : ∀ᵐ ω ∂μ, ∀ s i, specNorm (L (z ω s i)) ≤ R)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hsmall : 16 * (p : ℝ) * R ≤ |ζ.im|)
    (hMass : MemLp (fun ω => 2 * (specNorm (∑ i, L (z ω 0 i) ^ 2) +
      specNorm (∑ i, L (z ω 1 i) ^ 2) + specNorm (∑ i, L (z ω 2 i) ^ 2)))
      (2 * (p : ℝ≥0∞)) μ) :
    let mass := fun ω => 2 * (specNorm (∑ i, L (z ω 0 i) ^ 2) +
      specNorm (∑ i, L (z ω 1 i) ^ 2) + specNorm (∑ i, L (z ω 2 i) ^ 2))
    Integrable (fun ω => ∑ i, resolventMomentTaylorKernel A ζ p a
      (x₀ ω - a • (z ω 0 i - z ω 1 i)) (z ω 0 i - z ω 1 i)
        (z ω 1 i - z ω 2 i)) μ ∧
      ‖∫ ω, ∑ i, resolventMomentTaylorKernel A ζ p a
        (x₀ ω - a • (z ω 0 i - z ω 1 i)) (z ω 0 i - z ω 1 i)
          (z ω 1 i - z ω 2 i) ∂μ‖ ≤
        ((2 * p : ℕ) : ℝ) * ((2 * p + 1 : ℕ) : ℝ) * ((2 * p + 2 : ℕ) : ℝ) *
          3 * (2 * R) * (|ζ.im|⁻¹) ^ 4 * lpNorm mass (2 * (p : ℝ≥0∞)) μ *
            (∫ ω, resolventEvenMoment (A + L (x₀ ω)) ζ p ∂μ) ^
              (((2 * p - 1 : ℕ) : ℝ) / (2 * p : ℕ)) := by
  classical
  let mass : Ω → ℝ := fun ω => 2 * (specNorm (∑ i, L (z ω 0 i) ^ 2) +
    specNorm (∑ i, L (z ω 1 i) ^ 2) + specNorm (∑ i, L (z ω 2 i) ^ 2))
  let U : Ω → ℝ := fun ω => resolventEvenMoment (A + L (x₀ ω)) ζ p
  let q : ℝ := ((2 * p - 1 : ℕ) : ℝ) / (2 * p : ℕ)
  let K : ℝ := ((2 * p : ℕ) : ℝ) * ((2 * p + 1 : ℕ) : ℝ) *
    ((2 * p + 2 : ℕ) : ℝ) * 3 * (2 * R) * (|ζ.im|⁻¹) ^ 4
  let F : Ω → ℂ := fun ω => ∑ i, resolventMomentTaylorKernel A ζ p a
    (x₀ ω - a • (z ω 0 i - z ω 1 i)) (z ω 0 i - z ω 1 i)
      (z ω 1 i - z ω 2 i)
  have hKm (i : ι) : AEMeasurable (fun ω => resolventMomentTaylorKernel A ζ p a
      (x₀ ω - a • (z ω 0 i - z ω 1 i)) (z ω 0 i - z ω 1 i)
        (z ω 1 i - z ω 2 i)) μ := by
    have hDm : AEMeasurable (fun ω => z ω 0 i - z ω 1 i) μ :=
      ((hzm.eval 0).eval i).sub ((hzm.eval 1).eval i)
    have hVm : AEMeasurable (fun ω => z ω 1 i - z ω 2 i) μ :=
      ((hzm.eval 1).eval i).sub ((hzm.eval 2).eval i)
    have hxm : AEMeasurable (fun ω => x₀ ω - a • (z ω 0 i - z ω 1 i)) μ :=
      hx₀m.sub (hDm.const_smul a)
    have ht : AEMeasurable (fun ω =>
        (x₀ ω - a • (z ω 0 i - z ω 1 i), z ω 0 i - z ω 1 i, z ω 1 i - z ω 2 i)) μ :=
      hxm.prodMk (hDm.prodMk hVm)
    have hc := (continuous_resolventMomentTaylorKernel A hA ζ hζ p a).measurable
    have hcomp := hc.comp_aemeasurable ht
    simpa only [Function.comp_def] using hcomp
  have hFm : AEStronglyMeasurable F μ :=
    (Finset.aemeasurable_fun_sum Finset.univ (fun i _ => hKm i)).aestronglyMeasurable
  have hX : AEMeasurable (fun ω => A + L (x₀ ω)) μ :=
    aemeasurable_const.add ((L).continuous.measurable.comp_aemeasurable hx₀m)
  have hXHerm : ∀ᵐ ω ∂μ, (A + L (x₀ ω)).IsHermitian :=
    Filter.Eventually.of_forall fun ω => hA.add (isHermitian_hermitianMatrixFromRealCoordinates (x₀ ω))
  have hUi : Integrable U μ :=
    (integrable_and_integral_resolventEvenMoment_le μ _ hX hXHerm hζ hp).1
  have hUnn : ∀ᵐ ω ∂μ, 0 ≤ U ω :=
    Filter.Eventually.of_forall fun ω => resolventEvenMoment_nonneg _ ζ hp
  have hMnn : ∀ᵐ ω ∂μ, 0 ≤ mass ω := by
    filter_upwards [] with ω
    exact mul_nonneg (by norm_num) (add_nonneg
      (add_nonneg (specNorm_nonneg _) (specNorm_nonneg _)) (specNorm_nonneg _))
  have hq : q = (2 * (p : ℝ) - 1) / (2 * p) := by
    dsimp only [q]
    simp only [Nat.cast_sub (by omega : 1 ≤ 2 * p), Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one]
  obtain ⟨hGi, hGb⟩ := integrable_and_integral_mul_rpow_le_lpNorm_two_mul
    p hp hMass hUi hMnn hUnn
  rw [← hq] at hGi hGb
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hBound : ∀ᵐ ω ∂μ, ‖F ω‖ ≤ K * (mass ω * U ω ^ q) := by
    filter_upwards [hZ] with ω hω
    have hb := norm_sum_resolventMomentTaylorKernel_first_copy_le
      A hA ζ hζ hp (x₀ ω) (z ω) hR hω ha0 ha1 hsmall
    change ‖F ω‖ ≤ ((2 * p : ℕ) : ℝ) * ((2 * p + 1 : ℕ) : ℝ) *
      ((2 * p + 2 : ℕ) : ℝ) * 3 * (2 * R) * mass ω * (|ζ.im|⁻¹) ^ 4 * U ω ^ q at hb
    convert hb using 1
    dsimp only [K]
    ring
  have hKi : Integrable (fun ω => K * (mass ω * U ω ^ q)) μ := hGi.const_mul K
  have hFi : Integrable F μ := hKi.mono' hFm hBound
  refine ⟨hFi, ?_⟩
  calc
    ‖∫ ω, F ω ∂μ‖ ≤ ∫ ω, K * (mass ω * U ω ^ q) ∂μ :=
      norm_integral_le_of_norm_le hKi hBound
    _ = K * ∫ ω, mass ω * U ω ^ q ∂μ := integral_const_mul K _
    _ ≤ K * (lpNorm mass (2 * (p : ℝ≥0∞)) μ * (∫ ω, U ω ∂μ) ^ q) :=
      mul_le_mul_of_nonneg_left hGb hK
    _ = _ := by dsimp only [K, U, q]; ring

end NLAlib
