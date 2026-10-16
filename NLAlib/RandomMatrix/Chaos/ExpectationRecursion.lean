import NLAlib.RandomMatrix.Chaos.ExpectedNorm
import NLAlib.RandomMatrix.Chaos.ProductRecursion

/-!
# Lifting a linear matrix-series estimate through one chaos group

This induction step applies a supplied linear-series inequality to the actual
conditional coefficient matrices, then identifies their three block matrices
with the lower-degree coefficient arrays. Final chaos theorems instantiate it
with proved Gaussian and subgaussian linear estimates.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Classical
namespace NLAlib

variable {τ ι m n : Type*} [Fintype τ] [Fintype ι] [DecidableEq τ] [DecidableEq ι]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]

/-- A genuine linear-series bound propagates through one independent chaos
group. This is the reusable recursion lemma, before choosing or proving the
linear constants; the row, column, and covariance branches are actual lower
chaos polynomials. -/
theorem expectedDecoupledMatrixChaosNorm_le_of_linear_bound
    (A : ((τ ⊕ Unit) → ι) → Matrix m n ℝ) (hν : ∀ i, Integrable id (ν i))
    (a b : ℝ)
    (hlinear : ∀ B : ι → Matrix m n ℝ,
      (∫ y : ι → ℝ, specNorm (∑ j, y j • B j) ∂Measure.pi ν) ≤
        a * (specNorm (coefficientRow B) + specNorm (coefficientColumn B)) +
          b * specNorm (coefficientEntryRows B)) :
    expectedDecoupledMatrixChaosNorm ν A ≤
      a * (expectedDecoupledMatrixChaosNorm ν (chaosRowCoefficients A) +
        expectedDecoupledMatrixChaosNorm ν (chaosColumnCoefficients A)) +
          b * expectedDecoupledMatrixChaosNorm ν (chaosEntryCoefficients A) := by
  let R := fun x : τ × ι → ℝ =>
    specNorm (decoupledMatrixChaos (chaosRowCoefficients A) (fun t i => x (t, i)))
  let C := fun x : τ × ι → ℝ =>
    specNorm (decoupledMatrixChaos (chaosColumnCoefficients A) (fun t i => x (t, i)))
  let V := fun x : τ × ι → ℝ =>
    specNorm (decoupledMatrixChaos (chaosEntryCoefficients A) (fun t i => x (t, i)))
  have hR : Integrable R (Measure.pi (fun ti : τ × ι => ν ti.2)) :=
    integrable_specNorm_decoupledMatrixChaos ν _ hν
  have hC : Integrable C (Measure.pi (fun ti : τ × ι => ν ti.2)) :=
    integrable_specNorm_decoupledMatrixChaos ν _ hν
  have hV : Integrable V (Measure.pi (fun ti : τ × ι => ν ti.2)) :=
    integrable_specNorm_decoupledMatrixChaos ν _ hν
  have hp (x : τ × ι → ℝ) :
      (∫ y : ι → ℝ, specNorm (∑ j, y j • decoupledMatrixChaos
        (fun z => A (chaosAppendTuple z j)) (fun t i => x (t, i))) ∂Measure.pi ν) ≤
      a * (R x + C x) + b * V x := by
    have h := hlinear (fun j => decoupledMatrixChaos
      (fun z => A (chaosAppendTuple z j)) (fun t i => x (t, i)))
    rw [coefficientRow_decoupledMatrixChaos, coefficientColumn_decoupledMatrixChaos,
      coefficientEntryRows_decoupledMatrixChaos] at h
    exact h
  unfold expectedDecoupledMatrixChaosNorm
  rw [integral_specNorm_decoupledMatrixChaos_sum_recursion ν A hν]
  have hstep := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun x => integral_nonneg (fun y => specNorm_nonneg _)))
    (((hR.add hC).const_mul a).add (hV.const_mul b))
    (Filter.Eventually.of_forall hp)
  simp only [Pi.add_apply] at hstep
  refine hstep.trans_eq ?_
  calc
    (∫ x, a * (R x + C x) + b * V x ∂Measure.pi (fun ti : τ × ι => ν ti.2)) =
        (∫ x, a * (R x + C x) ∂Measure.pi (fun ti : τ × ι => ν ti.2)) +
          ∫ x, b * V x ∂Measure.pi (fun ti : τ × ι => ν ti.2) := by
      simpa only [Pi.add_apply] using
        integral_add ((hR.add hC).const_mul a) (hV.const_mul b)
    _ = _ := by
      rw [integral_const_mul, integral_const_mul, integral_add hR hC]

end NLAlib
