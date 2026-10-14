import NLAlib.Matrix.Functions.HermitianCalculus
import NLAlib.Matrix.Functions.PolynomialCalculus
import Mathlib.LinearAlgebra.Lagrange

/-! # Functional calculus of real diagonal matrices

Every scalar function on a finite real diagonal spectrum acts entrywise.
The polynomial and power corollaries support finite discrete spectral measures.
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator
open Matrix Polynomial

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Real continuous functional calculus of a real diagonal matrix is entrywise.
No global continuity assumption is needed on its finite spectrum. -/
theorem cfc_diagonal (f : ℝ → ℝ) (x : n → ℝ) :
    cfc f (Matrix.diagonal x) = Matrix.diagonal (fun i => f (x i)) := by
  classical
  let s := (Set.finite_range x).toFinset
  let p : ℝ[X] := Lagrange.interpolate s id f
  have hp : ∀ y ∈ Set.range x, p.eval y = f y := by
    intro y hy
    exact Lagrange.eval_interpolate_at_node (s := s) (v := id) (i := y) f
      Function.injective_id.injOn (by simpa [s] using hy)
  have heq : cfc f (Matrix.diagonal x) = cfc p.eval (Matrix.diagonal x) := by
    apply cfc_congr
    intro y hy
    rw [spectrum_diagonal] at hy
    exact (hp y hy).symm
  rw [heq, cfc_polynomial p _ (Matrix.isHermitian_diagonal x).isSelfAdjoint,
    aeval_diagonal]
  congr 1
  funext i
  exact hp (x i) ⟨i, rfl⟩

/-- Powers of a diagonal matrix are the diagonal of scalar powers. -/
theorem diagonal_pow (x : n → ℝ) (k : ℕ) :
    (Matrix.diagonal x) ^ k = Matrix.diagonal (fun i => x i ^ k) := by
  simpa using aeval_diagonal x (X ^ k)

end NLAlib
