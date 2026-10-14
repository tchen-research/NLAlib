import NLAlib.Krylov.Quadrature.JacobiFraction
import NLAlib.Matrix.Structured.JacobiFractionComplex

/-! # Complex finite Jacobi fractions with proved denominators

A nonreal shift makes every real symmetric Jacobi block invertible. The same
field-generic matrix and fraction as in the real interface therefore give the
ordinary nested complex fraction, with no extra nonvanishing assumption.
Cramer's quotient continues to describe every pole-free final resolvent even
when a real intermediate nested denominator vanishes.
-/

noncomputable section
open Matrix Polynomial
open scoped Matrix

namespace NLAlib

namespace LanczosDecomp

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ}

/-- Every actual signed Lanczos compression has the literal complex continued
fraction at every nonreal argument. Source: operator derivations (OF25).
atlas: jacobi-matrix-identities (partial) -/
theorem inv_smul_one_sub_map_T_apply_zero_zero (D : LanczosDecomp A b q)
    (hA : A.IsHermitian) (hq : 0 < q) {z : ℂ} (hz : z.im ≠ 0) :
    (z • (1 : Matrix (Fin q) (Fin q) ℂ) - D.T.map Complex.ofRealHom)⁻¹
      ⟨0, hq⟩ ⟨0, hq⟩ =
      jacobiFraction (Complex.ofRealHom ∘ D.alpha) (Complex.ofRealHom ∘ D.beta) z q 0 := by
  rw [D.T_eq_jacobiMatrix hA]
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  exact inv_smul_one_sub_map_jacobiMatrix_apply_zero_zero D.alpha D.beta m hz

end LanczosDecomp
end NLAlib
