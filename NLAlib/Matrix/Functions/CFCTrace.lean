import NLAlib.Matrix.Spectral.TraceEigenvalues
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order

/-!
# Trace and positivity of the Hermitian functional calculus

For Hermitian `A : Matrix n n 𝕜` (`[RCLike 𝕜]`): `cfc f A = U diag(f(λᵢ)) Uᴴ`
(`cfc_eq_eigenvectorUnitary_mul_diagonal_mul_conjTranspose`), `tr (cfc f A) = ∑ f(λᵢ)`
(`trace_cfc_eq_sum_eigenvalues`), the trace lower bound from a scalar lower bound at the
eigenvalues (`mul_card_le_re_trace_cfc_of_le`), and positivity of `cfc f A` when `f ≥ 0` on the
eigenvalues (`posSemidef_cfc_of_nonneg_eigenvalues`). Horn–Johnson 2013, Thm 2.5.6 and §4.1;
Higham 2008, *Functions of Matrices*, Def. 1.2. Used by the SLQ error bounds (`slq-error`).
-/

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The Hermitian functional calculus in eigenbasis coordinates: `f(A) = U diag(f(λᵢ)) Uᴴ`
(Mathlib's `IsHermitian.cfc`, unfolded). Horn–Johnson 2013, Thm 2.5.6. -/
theorem cfc_eq_eigenvectorUnitary_mul_diagonal_mul_conjTranspose {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    hA.cfc f = (hA.eigenvectorUnitary : Matrix n n 𝕜) *
      Matrix.diagonal (fun i => (f (hA.eigenvalues i) : 𝕜)) *
        (hA.eigenvectorUnitary : Matrix n n 𝕜)ᴴ := by
  simp [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    Function.comp_def]

/-- `tr f(A) = ∑ᵢ f(λᵢ(A))` for Hermitian `A` (empty index type included).
Horn–Johnson 2013, Thm 2.5.6; supports `slq-error`. -/
theorem trace_cfc_eq_sum_eigenvalues {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, (f (hA.eigenvalues i) : 𝕜) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, trace_conjStarAlgAut]
  simp only [Matrix.trace_diagonal, Function.comp_apply]

/-- The real part of `tr f(A)` is `∑ᵢ f(λᵢ(A))`. Horn–Johnson 2013, Thm 2.5.6. -/
theorem re_trace_cfc_eq_sum_eigenvalues {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    RCLike.re (cfc f A).trace = ∑ i, f (hA.eigenvalues i) := by
  rw [trace_cfc_eq_sum_eigenvalues hA f, map_sum]
  simp only [RCLike.ofReal_re]

/-- A scalar lower bound at every eigenvalue gives `b · card n ≤ Re tr f(A)`.
Horn–Johnson 2013, Thm 2.5.6; supports `slq-error`. -/
theorem mul_card_le_re_trace_cfc_of_le {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {f : ℝ → ℝ} {b : ℝ} (hb : ∀ i, b ≤ f (hA.eigenvalues i)) :
    b * Fintype.card n ≤ RCLike.re (cfc f A).trace := by
  rw [re_trace_cfc_eq_sum_eigenvalues hA f]
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using
    Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hb i)

/-- `f(A) ⪰ 0` when `f ≥ 0` at every eigenvalue of the Hermitian `A` (no global positivity of
`f` needed). Horn–Johnson 2013, Thm 2.5.6; supports `slq-error`. -/
theorem posSemidef_cfc_of_nonneg_eigenvalues {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {f : ℝ → ℝ} (hf : ∀ i, 0 ≤ f (hA.eigenvalues i)) : (cfc f A).PosSemidef := by
  apply LE.le.posSemidef
  apply cfc_nonneg
  intro x hx
  rw [hA.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact hf i

end NLAlib
