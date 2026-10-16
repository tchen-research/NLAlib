import NLAlib.RandomMatrix.Chaos.Integrability
import NLAlib.RandomMatrix.Chaos.ModeReindex
import NLAlib.RandomMatrix.Chaos.ZeroDegree

/-!
# Expected spectral norm of a product-law matrix chaos

The named expectation is the ordinary Bochner integral of the actual finite
polynomial under its coordinate product law. This module records the two
representation-independent facts needed for induction on the degree.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Classical
namespace NLAlib

variable {σ τ ι m n : Type*} [Fintype σ] [Fintype τ] [Fintype ι]
  [DecidableEq σ] [DecidableEq τ] [DecidableEq ι]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The actual expected spectral norm of a fully decoupled coefficient array
under its finite coordinate product law. -/
def expectedDecoupledMatrixChaosNorm (ν : ι → Measure ℝ)
    (A : (τ → ι) → Matrix m n ℝ) : ℝ :=
  ∫ x : τ × ι → ℝ, specNorm (decoupledMatrixChaos A (fun t i => x (t, i)))
    ∂Measure.pi (fun ti : τ × ι => ν ti.2)

/-- Expected chaos spectral norms are nonnegative. -/
theorem expectedDecoupledMatrixChaosNorm_nonneg (ν : ι → Measure ℝ)
    (A : (τ → ι) → Matrix m n ℝ) : 0 ≤ expectedDecoupledMatrixChaosNorm ν A :=
  integral_nonneg (fun _ => specNorm_nonneg _)

variable (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]

open scoped Matrix.Norms.L2Operator in
/-- The actual chaos expectation transports to an arbitrary sample space
through its joint coordinate product law. No extra moment hypothesis is
needed for the change-of-law identity. -/
theorem integral_specNorm_decoupledMatrixChaos_eq_expected_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {ξ : Ω → τ × ι → ℝ}
    (hξ : HasLaw ξ (Measure.pi (fun ti : τ × ι => ν ti.2)) μ)
    (A : (τ → ι) → Matrix m n ℝ) :
    (∫ ω, specNorm (decoupledMatrixChaos A (fun t i => ξ ω (t, i))) ∂μ) =
      expectedDecoupledMatrixChaosNorm ν A := by
  have hf : Continuous (fun x : τ × ι → ℝ =>
      ‖decoupledMatrixChaos A (fun t i => x (t, i))‖) :=
    (continuous_decoupledMatrixChaos A).comp (by fun_prop) |>.norm
  simpa only [Function.comp_apply, specNorm_eq_norm, expectedDecoupledMatrixChaosNorm] using
    hξ.integral_comp hf.aestronglyMeasurable

/-- At degree zero the expected chaos norm is exactly the variance parameter of
the unique deterministic coefficient. -/
theorem expectedDecoupledMatrixChaosNorm_of_isEmpty [IsEmpty τ]
    (A : (τ → ι) → Matrix m n ℝ) :
    expectedDecoupledMatrixChaosNorm ν A = chaosSigma A := by
  simp [expectedDecoupledMatrixChaosNorm, decoupledMatrixChaos_of_isEmpty,
    chaosSigma_of_isEmpty]

open scoped Matrix.Norms.L2Operator in
/-- Relabeling the coefficient modes preserves the expected spectral norm under
the same independent coordinate laws. -/
theorem expectedDecoupledMatrixChaosNorm_reindexModes (e : σ ≃ τ)
    (A : (τ → ι) → Matrix m n ℝ) :
    expectedDecoupledMatrixChaosNorm ν (chaosReindexModes e A) =
      expectedDecoupledMatrixChaosNorm ν A := by
  have hi : Function.Injective (fun ti : σ × ι => (e ti.1, ti.2)) := by
    intro ti tj hij
    apply Prod.ext
    · exact e.injective (congrArg Prod.fst hij)
    · exact congrArg (fun p : τ × ι => p.2) hij
  have hlaw := hasLaw_pi_select (fun ti : τ × ι => ν ti.2)
    (fun ti : σ × ι => (e ti.1, ti.2)) hi
  have hf : Continuous (fun x : σ × ι → ℝ =>
      ‖decoupledMatrixChaos (chaosReindexModes e A) (fun t i => x (t, i))‖) := by
    apply Continuous.norm
    exact (continuous_decoupledMatrixChaos _).comp (by fun_prop)
  have he := hlaw.integral_comp hf.aestronglyMeasurable
  simp only [Function.comp_apply] at he
  unfold expectedDecoupledMatrixChaosNorm
  simp only [specNorm_eq_norm]
  rw [← he]
  apply integral_congr_ae
  filter_upwards [] with x
  exact congrArg (fun M : Matrix m n ℝ => ‖M‖)
    (decoupledMatrixChaos_reindexModes e A (fun t i => x (t, i)))

end NLAlib
