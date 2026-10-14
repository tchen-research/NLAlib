import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Smooth polynomial coefficients and coefficient derivatives

Finite convolution gives smooth coefficientwise multiplication and the product
rule. Degree bounds can be supplied separately for pairing with linear functionals;
no norm on the infinite-dimensional polynomial space is chosen.
-/

noncomputable section
namespace Polynomial

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {r : WithTop ℕ∞} {x : E}

/-- Coefficientwise multiplication preserves smoothness of polynomial families. -/
theorem contDiffAt_coeff_mul {p q : E → 𝕜[X]}
    (hp : ∀ k, ContDiffAt 𝕜 r (fun y => (p y).coeff k) x)
    (hq : ∀ k, ContDiffAt 𝕜 r (fun y => (q y).coeff k) x) (k : ℕ) :
    ContDiffAt 𝕜 r (fun y => (p y * q y).coeff k) x := by
  simp only [coeff_mul]
  exact ContDiffAt.sum (fun i _ => (hp i.1).mul (hq i.2))

/-- Coefficientwise derivative of a real polynomial family. -/
def HasCoeffDerivAt (p : ℝ → ℝ[X]) (p' : ℝ[X]) (x : ℝ) : Prop :=
  ∀ k, HasDerivAt (fun y => (p y).coeff k) (p'.coeff k) x

/-- A fixed polynomial has zero coefficient derivative. -/
theorem hasCoeffDerivAt_const (p : ℝ[X]) (x : ℝ) :
    HasCoeffDerivAt (fun _ => p) 0 x := by
  intro k
  simpa using hasDerivAt_const x (p.coeff k)

/-- Coefficientwise polynomial differentiation obeys the product rule. -/
theorem HasCoeffDerivAt.mul {p q : ℝ → ℝ[X]} {p' q' : ℝ[X]} {x : ℝ}
    (hp : HasCoeffDerivAt p p' x) (hq : HasCoeffDerivAt q q' x) :
    HasCoeffDerivAt (fun y => p y * q y) (p' * q x + p x * q') x := by
  intro k
  simp only [coeff_mul, coeff_add]
  convert HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.antidiagonal k) =>
    (hp i.1).mul (hq i.2)) using 1
  all_goals first | rfl | simp [Finset.sum_add_distrib]

end Polynomial

namespace Polynomial

variable {R T : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [TopologicalSpace T] {a : T}

/-- Coefficientwise multiplication preserves continuity of polynomial families. -/
theorem continuousAt_coeff_mul {p q : T → R[X]}
    (hp : ∀ k, ContinuousAt (fun y => (p y).coeff k) a)
    (hq : ∀ k, ContinuousAt (fun y => (q y).coeff k) a) (k : ℕ) :
    ContinuousAt (fun y => (p y * q y).coeff k) a := by
  simp only [coeff_mul]
  exact tendsto_finsetSum _ (fun i _ => (hp i.1).mul (hq i.2))

/-- Every coefficient of a finite product is continuous when every factor's
coefficients are continuous. -/
theorem continuousAt_coeff_prod {ι : Type*} (s : Finset ι) {p : ι → T → R[X]}
    (hp : ∀ i ∈ s, ∀ k, ContinuousAt (fun y => (p i y).coeff k) a) (k : ℕ) :
    ContinuousAt (fun y => (∏ i ∈ s, p i y).coeff k) a := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : T => (1 : R[X]).coeff k) a)
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact continuousAt_coeff_mul (hp i (Finset.mem_insert_self _ _))
      (fun j => ih (fun l hl => hp l (Finset.mem_insert_of_mem hl)) j) k

end Polynomial
