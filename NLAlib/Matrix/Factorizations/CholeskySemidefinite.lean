import NLAlib.Matrix.Factorizations.CholeskyTrailingResidual
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Fintype.Sort
import Mathlib.Tactic.FieldSimp

/-!
# Triangular Cholesky factors for positive-semidefinite matrices

Induct on the trailing coordinate Schur residual. A vanishing pivot forces
the first row and column to vanish; the total square-root formula therefore
also works at zero pivots. Source: Higham, Theorem 10.1; Golub--Van Loan,
Theorem 4.2.7. Atlas target: `cholesky-decomposition`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- Extend a trailing factor by the nonnegative first scalar pivot.
Higham, Theorem 10.1; supports `cholesky-decomposition`. -/
def choleskyExtend {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (L : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => Fin.cases (Fin.cases (Real.sqrt (A 0 0)) (fun _ => 0) j)
    (fun i => Fin.cases (A i.succ 0 / Real.sqrt (A 0 0)) (fun j => L i j) j) i

/-- Extending a lower-triangular factor preserves lower triangularity.
Higham, Theorem 10.1; supports `cholesky-decomposition`. -/
theorem isLowerTriangular_choleskyExtend {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) {L : Matrix (Fin n) (Fin n) ℝ}
    (hL : L.IsLowerTriangular) : (choleskyExtend A L).IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact False.elim (lt_irrefl _ hij)
    | succ j => simp [choleskyExtend]
  | succ i =>
    cases j using Fin.cases with
    | zero => exact False.elim (Fin.not_lt_zero _ hij)
    | succ j =>
      simp only [choleskyExtend, Fin.cases_succ]
      exact hL (Fin.succ_lt_succ_iff.mp hij)

/-- The extension retains nonnegative diagonal entries, including a zero pivot.
Higham, Theorem 10.1; supports `cholesky-decomposition`. -/
theorem choleskyExtend_diag_nonneg {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) {L : Matrix (Fin n) (Fin n) ℝ}
    (hL : ∀ i, 0 ≤ L i i) : ∀ i, 0 ≤ choleskyExtend A L i i := by
  intro i
  cases i using Fin.cases with
  | zero => simp [choleskyExtend]
  | succ i => simpa [choleskyExtend] using hL i

/-- The first pivot cancels its square-root division, including at a zero
pivot by positive-semidefinite Gram vanishing. Higham, Theorem 10.1;
supports `cholesky-decomposition`. -/
theorem sqrt_pivot_mul_div_eq {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : A.PosSemidef) (i : Fin (n + 1)) :
    Real.sqrt (A 0 0) * (A i 0 / Real.sqrt (A 0 0)) = A i 0 := by
  by_cases hZero : A 0 0 = 0
  · have hi := apply_eq_zero_of_posSemidef_of_diag_eq_zero hA hZero i
    simp [hZero, hi]
  · have hSqrt : Real.sqrt (A 0 0) ≠ 0 := by
      intro h
      have hs : Real.sqrt (A 0 0) * Real.sqrt (A 0 0) = A 0 0 :=
        Real.mul_self_sqrt hA.diag_nonneg
      rw [h, zero_mul] at hs
      exact hZero hs.symm
    field_simp

/-- A trailing Schur factor reconstructs the entire matrix through the explicit
first-pivot extension. Higham, Theorem 10.1; supports `cholesky-decomposition`. -/
theorem choleskyExtend_mul_transpose {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : A.PosSemidef)
    (L : Matrix (Fin n) (Fin n) ℝ) (hL : L * Lᵀ = choleskyTrailingResidual A) :
    choleskyExtend A L * (choleskyExtend A L)ᵀ = A := by
  have hSqrt : Real.sqrt (A 0 0) * Real.sqrt (A 0 0) = A 0 0 :=
    Real.mul_self_sqrt hA.diag_nonneg
  have hSymm : ∀ i j, A i j = A j i := by
    intro i j
    simpa only [star_trivial] using (hA.isHermitian.apply i j).symm
  have hTail (i j : Fin n) : ∑ k, L i k * L j k = choleskyTrailingResidual A i j := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply] using congrFun (congrFun hL i) j
  ext i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => simpa [Matrix.mul_apply, Fin.sum_univ_succ, choleskyExtend] using hSqrt
    | succ j =>
      simpa [Matrix.mul_apply, Fin.sum_univ_succ, choleskyExtend, hSymm 0 j.succ] using
        sqrt_pivot_mul_div_eq hA j.succ
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      simpa [Matrix.mul_apply, Fin.sum_univ_succ, choleskyExtend, mul_comm] using
        sqrt_pivot_mul_div_eq hA i.succ
    | succ j =>
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
        choleskyExtend, Fin.cases_zero, Fin.cases_succ, hTail]
      rw [div_mul_div_comm, hSqrt]
      simp only [choleskyTrailingResidual, hSymm 0 j.succ]
      ring

/-- Every PSD real matrix has a lower-triangular Cholesky factor with nonnegative
diagonal, including singular matrices and the empty matrix. Higham,
Theorem 10.1; Golub--Van Loan, Theorem 4.2.7.
atlas: cholesky-decomposition (partial) -/
theorem exists_cholesky_of_posSemidef {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) :
    ∃ L : Matrix (Fin n) (Fin n) ℝ,
      L.IsLowerTriangular ∧ (∀ i, 0 ≤ L i i) ∧ L * Lᵀ = A := by
  induction n with
  | zero =>
    refine ⟨0, ?_, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · exact Subsingleton.elim _ _
  | succ n ih =>
    obtain ⟨L, hLower, hDiag, hFactor⟩ := ih (choleskyTrailingResidual A)
      (posSemidef_choleskyTrailingResidual hA)
    exact ⟨choleskyExtend A L, isLowerTriangular_choleskyExtend A hLower,
      choleskyExtend_diag_nonneg A hDiag, choleskyExtend_mul_transpose hA L hFactor⟩

/-- The semidefinite Cholesky factor exists over every linearly ordered finite
index type; finite normalization preserves the order and all zero pivots.
Higham, Theorem 10.1; Golub--Van Loan, Theorem 4.2.7.
atlas: cholesky-decomposition (partial) -/
theorem exists_cholesky_of_posSemidef_fintype {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) :
    ∃ L : Matrix ι ι ℝ, L.IsLowerTriangular ∧ (∀ i, 0 ≤ L i i) ∧ L * Lᵀ = A := by
  let e : Fin (Fintype.card ι) ≃o ι := monoEquivOfFin ι rfl
  let A' := A.reindex e.symm.toEquiv e.symm.toEquiv
  have hA' : A'.PosSemidef := hA.submatrix e
  obtain ⟨L', hLower, hDiag, hFactor⟩ := exists_cholesky_of_posSemidef A' hA'
  let L := L'.reindex e.toEquiv e.toEquiv
  refine ⟨L, ?_, ?_, ?_⟩
  · intro i j hij
    exact hLower (e.symm.strictMono hij)
  · intro i
    exact hDiag (e.symm i)
  · calc
      L * Lᵀ = (L' * L'ᵀ).reindex e.toEquiv e.toEquiv := by
        simp only [L, Matrix.reindex_apply, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]
      _ = A'.reindex e.toEquiv e.toEquiv := congrArg
        (fun M => M.reindex e.toEquiv e.toEquiv) hFactor
      _ = A := by ext i j; simp [A', Matrix.reindex_apply]

end NLAlib
