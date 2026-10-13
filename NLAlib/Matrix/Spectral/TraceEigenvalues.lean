import Mathlib.Analysis.Matrix.Spectrum

/-!
# Traces in Hermitian eigenbases

Trace is invariant under unitary conjugation (over any commutative star ring), so the trace of a
power of a real symmetric matrix is the power sum of its eigenvalues, and a quadratic trace in a
diagonal basis is a weighted sum of squared entries.

* `trace_conjStarAlgAut`: `tr (U A U⋆) = tr A`;
* `trace_pow_eq_sum_eigenvalues`: `tr (Rⁿ) = ∑ᵢ λᵢⁿ` for real symmetric `R`;
* `trace_mul_diagonal_pow_mul_mul_diagonal_pow`: `tr (B Λᵃ B Λᶜ) = ∑ᵢⱼ Bᵢⱼ² λⱼᵃ λᵢᶜ` for
 symmetric `B`.

The complex real-part form `re tr (Aʳ) = ∑ᵢ λᵢʳ` is `re_trace_pow_eq_sum_eigenvalues_pow`
(`NLAlib.Matrix.Inequalities.TracePowers`).
Source: finite spectral theorem and trace cyclicity; helpers for atlas
`wishart-lambda-min-tail`, `noncommutative-khintchine`, `sparse-ose`.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Trace is invariant under unitary conjugation, over any commutative star ring (in particular
`ℝ` and `ℂ`), including empty matrices.TracePowerConvexity.trace_conjStarAlgAut`). -/
theorem trace_conjStarAlgAut {R : Type*} [CommRing R] [StarRing R]
    (U : Matrix.unitaryGroup ι R) (A : Matrix ι ι R) :
    Matrix.trace (Unitary.conjStarAlgAut R _ U A) = Matrix.trace A := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]

/-- Natural trace powers of a Hermitian real matrix are the power sums of
its eigenvalues.MatrixTail.trace_pow_eq_sum_eigenvalues` (`sparse-ose`). -/
theorem trace_pow_eq_sum_eigenvalues {R : Matrix ι ι ℝ} (hR : R.IsHermitian) (n : ℕ) :
    Matrix.trace (R ^ n) = ∑ i, hR.eigenvalues i ^ n := by
  conv_lhs => rw [hR.spectral_theorem, ← map_pow]
  rw [trace_conjStarAlgAut,
    Matrix.diagonal_pow, Matrix.trace_diagonal]
  rfl

/-- A symmetric matrix quadratic trace in a diagonal basis is a weighted
sum of squares.trace_mul_diagonal_pow_mul_mul_diagonal_pow`;
atlas `wishart-lambda-min-tail` (operator calculus helper). -/
theorem trace_mul_diagonal_pow_mul_mul_diagonal_pow (B : Matrix ι ι ℝ)
    (hB : Bᵀ = B) (ev : ι → ℝ) (a c : ℕ) :
    Matrix.trace (B * (Matrix.diagonal ev) ^ a * B * (Matrix.diagonal ev) ^ c) =
      ∑ i, ∑ j, B i j ^ 2 * ev j ^ a * ev i ^ c := by
  rw [Matrix.diagonal_pow, Matrix.diagonal_pow,
    Matrix.mul_assoc B (Matrix.diagonal (ev ^ a)) B]
  have hentry (i : ι) : (B * (Matrix.diagonal (ev ^ a) * B)) i i =
      ∑ j, B i j * (ev j ^ a * B j i) := by
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.diagonal_mul]
    rfl
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
  simp_rw [hentry]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  have hs := congrFun (congrFun hB j) i
  simp only [Matrix.transpose_apply] at hs
  rw [hs]
  simp only [Pi.pow_apply]
  ring

end NLAlib
