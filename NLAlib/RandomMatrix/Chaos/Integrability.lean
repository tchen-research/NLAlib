import NLAlib.RandomMatrix.Chaos.Coloring
import NLAlib.ForMathlib.MeasureTheory.ProductSelection
import NLAlib.ForMathlib.MeasureTheory.Matrix

/-!
# Integrability of finite multilinear matrix chaos

First moments of the coordinates suffice: decoupled terms use distinct
coordinate groups, and the nonzero coupled terms use distinct coordinate
indices. Thus higher moments are unnecessary for the decoupling theorem.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical
namespace NLAlib

variable {τ ι m n : Type*} [Fintype τ] [Fintype ι]
  [Fintype m] [Fintype n] [DecidableEq τ] [DecidableEq ι]
  [DecidableEq m] [DecidableEq n]
  (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]

/-- A finite decoupled matrix chaos is a continuous polynomial of its coordinate
groups. -/
theorem continuous_decoupledMatrixChaos (A : (τ → ι) → Matrix m n ℝ) :
    Continuous (decoupledMatrixChaos A) := by
  unfold decoupledMatrixChaos
  fun_prop

open scoped Matrix.Norms.L2Operator in
/-- Distinct coordinate groups make every decoupled-chaos term integrable under
the product law as soon as every coordinate has a finite first moment. -/
theorem integrable_decoupledMatrixChaos (A : (τ → ι) → Matrix m n ℝ)
    (hν : ∀ i, Integrable id (ν i)) :
    Integrable (fun x : τ × ι → ℝ => decoupledMatrixChaos A (fun t i => x (t, i)))
      (Measure.pi (fun ti : τ × ι => ν ti.2)) := by
  unfold decoupledMatrixChaos
  apply integrable_finset_sum
  intro z _
  have hz : Function.Injective (fun t : τ => (t, z t)) := by
    intro t u htu
    exact congrArg Prod.fst htu
  exact (integrable_prod_pi_select (fun ti : τ × ι => ν ti.2)
    (fun t => (t, z t)) hz (fun _ => id) (fun t => hν (z t))).smul_const (A z)

open scoped Matrix.Norms.L2Operator in
/-- Diagonal-free coupled chaos is integrable with only finite first moments.
Source: distinct-coordinate factorization of each nonzero term.
atlas: matrix-chaos-decoupling-upper (partial) -/
theorem integrable_coupledMatrixChaos (A : (τ → ι) → Matrix m n ℝ)
    (hA : HasDistinctIndexSupport A) (hν : ∀ i, Integrable id (ν i)) :
    Integrable (coupledMatrixChaos A) (Measure.pi ν) := by
  unfold coupledMatrixChaos decoupledMatrixChaos
  apply integrable_finset_sum
  intro z _
  by_cases hz : Function.Injective z
  · exact (integrable_prod_pi_select ν z hz (fun _ => id) (fun t => hν (z t))).smul_const
      (A z)
  · simp only [hA z hz, smul_zero]
    exact integrable_const _

open scoped Matrix.Norms.L2Operator in
/-- Every retained-color chaos is integrable because matching colors force its
selected coordinate indices to be distinct. -/
theorem integrable_coloredMatrixChaos (A : (τ → ι) → Matrix m n ℝ)
    (c : ι → τ) (hν : ∀ i, Integrable id (ν i)) :
    Integrable (coloredMatrixChaos A c) (Measure.pi ν) := by
  unfold coloredMatrixChaos
  apply integrable_finset_sum
  intro z _
  by_cases hz : ∀ t, c (z t) = t
  · simp only [if_pos hz]
    have hi : Function.Injective z := by
      intro t u htu
      simpa [hz] using congrArg c htu
    exact (integrable_prod_pi_select ν z hi (fun _ => id) (fun t => hν (z t))).smul_const
      (A z)
  · simp only [if_neg hz]
    exact integrable_const _

open scoped Matrix.Norms.L2Operator in
/-- The expected spectral norm of the decoupled chaos is finite. -/
theorem integrable_specNorm_decoupledMatrixChaos (A : (τ → ι) → Matrix m n ℝ)
    (hν : ∀ i, Integrable id (ν i)) :
    Integrable (fun x : τ × ι → ℝ =>
      specNorm (decoupledMatrixChaos A (fun t i => x (t, i))))
      (Measure.pi (fun ti : τ × ι => ν ti.2)) := by
  simpa only [specNorm_eq_norm] using (integrable_decoupledMatrixChaos ν A hν).norm

open scoped Matrix.Norms.L2Operator in
/-- The expected spectral norm of the coupled chaos is finite. -/
theorem integrable_specNorm_coupledMatrixChaos (A : (τ → ι) → Matrix m n ℝ)
    (hA : HasDistinctIndexSupport A) (hν : ∀ i, Integrable id (ν i)) :
    Integrable (fun x => specNorm (coupledMatrixChaos A x)) (Measure.pi ν) := by
  simpa only [specNorm_eq_norm] using (integrable_coupledMatrixChaos ν A hA hν).norm

end NLAlib
