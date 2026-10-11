import NLAlib.Concentration.Matrix.Laplace.TraceIntegrability
import Mathlib.Probability.Martingale.Basic

/-!
# Actual matrix increment sums, conditional second moments, and trace potentials

Increment index `j` represents the step from time `j` to time `j+1`. Every conditional
second-moment theorem supplies integrability so that the Bochner definition is meaningful.
The local-variance interface uses a separately specified genuine local conditional moment.
-/

noncomputable section

open MeasureTheory Matrix Finset
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

variable {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]

/-- The cumulative actual matrix increments through time `k`, with step `j` occurring
between times `j` and `j+1`.
Source: operator rederivations Section 3, `Y_k`; atlas `matrix-freedman` (partial). -/
def matrixIncrementSum (X : ℕ → Ω → Matrix n n ℂ) (k : ℕ) (ω : Ω) : Matrix n n ℂ :=
  ∑ j ∈ range k, X j ω

/-- The actual Bochner conditional second moment of increment `j`, conditioned at time
`j`. Integrability of the squared increment is supplied in the global-variance theorems.
Source: operator rederivations Section 3.1, `V_k`; atlas `matrix-freedman` (partial). -/
def conditionalMatrixSecondMoment (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (μ : Measure Ω)
    (X : ℕ → Ω → Matrix n n ℂ) (j : ℕ) (ω : Ω) : Matrix n n ℂ :=
  μ[(fun ω => X j ω ^ 2) | ℱ j] ω

/-- The actual compensated matrix trace potential, with cumulative variance increments
specified explicitly. The matrix Freedman theorem supplies their genuine conditional
second-moment relation and the exact Bernstein coefficient.
Source: operator rederivations Section 3.3, `S_k`; atlas `matrix-freedman` (partial). -/
def matrixCompensatedTracePotential (θ c : ℝ) (X V : ℕ → Ω → Matrix n n ℂ)
    (k : ℕ) (ω : Ω) : ℝ :=
  traceExp (θ • matrixIncrementSum X k ω - c • matrixIncrementSum V k ω)

omit [MeasurableSpace Ω] [Fintype n] [DecidableEq n] in
/-- A cumulative matrix increment sum starts at zero.
Source: the finite-sum convention in Section 3; helper for `matrix-freedman` (partial). -/
@[simp] theorem matrixIncrementSum_zero (X : ℕ → Ω → Matrix n n ℂ) (ω : Ω) :
    matrixIncrementSum X 0 ω = 0 := by simp [matrixIncrementSum]

omit [MeasurableSpace Ω] [Fintype n] [DecidableEq n] in
/-- Adding one actual increment updates the cumulative matrix sum.
Source: the finite-sum convention in Section 3; helper for `matrix-freedman` (partial). -/
theorem matrixIncrementSum_succ (X : ℕ → Ω → Matrix n n ℂ) (k : ℕ) (ω : Ω) :
    matrixIncrementSum X (k + 1) ω = matrixIncrementSum X k ω + X k ω := by
  exact Finset.sum_range_succ _ _

omit [MeasurableSpace Ω] in
/-- The actual compensated trace potential starts at the ambient dimension.
Source: operator rederivations Section 3.3, `S_0=d`; helper for `matrix-freedman` (partial). -/
@[simp] theorem matrixCompensatedTracePotential_zero (θ c : ℝ)
    (X V : ℕ → Ω → Matrix n n ℂ) (ω : Ω) :
    matrixCompensatedTracePotential θ c X V 0 ω = Fintype.card n := by
  simp only [matrixCompensatedTracePotential, matrixIncrementSum_zero, smul_zero, sub_self]
  have h := traceExp_smul_one_eq_card_mul_exp (n := n) 0
  simpa only [zero_smul, Real.exp_zero, mul_one] using h

end NLAlib
