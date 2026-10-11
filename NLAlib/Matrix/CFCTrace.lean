import NLAlib.Matrix.InversePowerConcavity
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order

/-!
# Trace and positivity of Hermitian matrix functional calculus

Finite spectral calculus supplies exact trace sums and transfers scalar lower bounds.
These facts give the computable positive-lower-bound SLQ budgets.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace of real Hermitian functional calculus is the sum of the scalar function
at the actual eigenvalues, including the empty-index case.
Source: finite spectral theorem; helper for operator rederivations `rt:slq-relative`
and atlas `slq-error`. -/
theorem trace_cfc_eq_sum_eigenvalues {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, f (hA.eigenvalues i) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, trace_conjStarAlgAut]
  simp only [Matrix.trace_diagonal, Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq]

/-- A scalar lower bound at every eigenvalue gives the corresponding trace lower bound.
Source: finite spectral theorem; helper for operator rederivations `rt:slq-relative`
and atlas `slq-error`. -/
theorem mul_card_le_trace_cfc_of_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {f : ℝ → ℝ} {b : ℝ} (hb : ∀ i, b ≤ f (hA.eigenvalues i)) :
    b * Fintype.card n ≤ (cfc f A).trace := by
  rw [trace_cfc_eq_sum_eigenvalues hA f]
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using
    Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hb i)

/-- A function nonnegative at every eigenvalue has positive semidefinite real Hermitian
functional calculus, without a global positivity premise on the function.
Source: finite spectral theorem; helper for operator rederivations `rt:slq-relative`
and atlas `slq-error`. -/
theorem posSemidef_cfc_of_nonneg_eigenvalues {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {f : ℝ → ℝ} (hf : ∀ i, 0 ≤ f (hA.eigenvalues i)) : (cfc f A).PosSemidef := by
  apply LE.le.posSemidef
  apply cfc_nonneg
  intro x hx
  rw [hA.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact hf i

end NLAlib
