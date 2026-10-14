import NLAlib.Matrix.Structured.JacobiAlgebra
import NLAlib.Matrix.Structured.BidiagonalLDL
import NLAlib.Matrix.Basic.SchurComplement

/-! # Positive pivots of symmetric Jacobi LDL factorization

The actual finite symmetric Jacobi matrix has unit lower bidiagonal factors.
Positive definiteness derives strict positivity of each recursively defined
pivot by the first-pivot Schur complement, including empty matrices.
Source: Gautschi (2004), Theorem 1.33; AQ15 in the operator re-derivations.
-/

noncomputable section
open Matrix
open scoped Matrix
namespace NLAlib

/-- The scalar LDL pivots of a symmetric Jacobi matrix; total at breakdown. -/
def jacobiLDLPivot (a b : ℕ → ℝ) : ℕ → ℝ
  | 0 => a 0
  | k + 1 => a (k + 1) - b (k + 1) ^ 2 / jacobiLDLPivot a b k

private def jacobiSchurDiagonal (a b : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then a 1 - b 1 ^ 2 / a 0 else a (k + 1)

private theorem pivotSchur_jacobiMatrix (a b : ℕ → ℝ) (n : ℕ) :
    pivotSchur (jacobiMatrix a b (n + 1)) =
      jacobiMatrix (jacobiSchurDiagonal a b) (fun k => b (k + 1)) n := by
  ext i j
  simp only [pivotSchur_apply, jacobiMatrix, Matrix.of_apply, Fin.val_zero,
    Fin.val_succ, jacobiSchurDiagonal]
  split_ifs <;> simp_all <;> try omega
  all_goals simp only [div_eq_mul_inv]
  all_goals ring

private theorem jacobiLDLPivot_succ (a b : ℕ → ℝ) (k : ℕ) :
    jacobiLDLPivot a b (k + 1) =
      jacobiLDLPivot (jacobiSchurDiagonal a b) (fun i => b (i + 1)) k := by
  induction k with
  | zero => simp [jacobiLDLPivot, jacobiSchurDiagonal]
  | succ k ih =>
    simp only [jacobiLDLPivot, jacobiSchurDiagonal,
      show k + 1 ≠ 0 by omega, if_false, ← ih]

/-- Every pivot of an actual positive definite finite symmetric Jacobi matrix
is strictly positive. The scalar recurrence therefore has no zero denominator
before termination; no pivot positivity is assumed separately.
atlas: kernel-polynomials-christoffel (partial) -/
theorem jacobiLDLPivot_pos_of_posDef {a b : ℕ → ℝ} {n : ℕ}
    (hJ : (jacobiMatrix a b n).PosDef) {k : ℕ} (hk : k < n) :
    0 < jacobiLDLPivot a b k := by
  induction n generalizing a b k with
  | zero => omega
  | succ n ih =>
    have ha : 0 < a 0 := by simpa [jacobiMatrix] using hJ.diag_pos (i := 0)
    have hS := ((posDef_iff_pivotSchur hJ.isHermitian).mp hJ).2
    rw [pivotSchur_jacobiMatrix] at hS
    cases k with
    | zero => exact ha
    | succ k => rw [jacobiLDLPivot_succ]; exact ih hS (by omega)

/-- The actual unit lower bidiagonal LDL factor, with the ratio of the signed
Jacobi off-diagonal to its strictly preceding scalar pivot. -/
def jacobiLDLLower (a b : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  darbouxLowerMatrix n (fun k => b (k + 1) / jacobiLDLPivot a b k)

/-- Positive definiteness makes the recursively defined bidiagonal LDL product
equal the actual finite symmetric Jacobi matrix, including dimension zero.
atlas: kernel-polynomials-christoffel (partial) -/
theorem jacobiMatrix_eq_ldl_of_posDef {a b : ℕ → ℝ} {n : ℕ}
    (hJ : (jacobiMatrix a b n).PosDef) :
    jacobiMatrix a b n = jacobiLDLLower a b n *
      diagonal (fun i : Fin n => jacobiLDLPivot a b i.val) *
      (jacobiLDLLower a b n)ᵀ := by
  ext i j
  rw [jacobiLDLLower, darbouxLowerMatrix_mul_diagonal_mul_transpose_apply]
  simp only [jacobiMatrix, Matrix.of_apply]
  split_ifs with hij hi0 hijs hjis
  · simp [hi0, jacobiLDLPivot]
  · have hp := (jacobiLDLPivot_pos_of_posDef hJ (show i.val - 1 < n by omega)).ne'
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    have hkp : jacobiLDLPivot a b k ≠ 0 := by
      simpa only [hk, Nat.succ_eq_add_one, Nat.add_sub_cancel] using hp
    simp only [hk, Nat.succ_eq_add_one, Nat.add_sub_cancel, jacobiLDLPivot]
    field_simp
    ring
  · have hp := (jacobiLDLPivot_pos_of_posDef hJ i.isLt).ne'
    rw [div_mul_cancel₀ _ hp, hijs]
  · have hp := (jacobiLDLPivot_pos_of_posDef hJ j.isLt).ne'
    rw [div_mul_cancel₀ _ hp, hjis]
  · rfl

end NLAlib
