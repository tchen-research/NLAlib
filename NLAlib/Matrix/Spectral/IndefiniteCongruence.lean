import NLAlib.Matrix.Spectral.SimultaneousOrthogonal
/-!
# Simultaneous congruence for an invertible indefinite form

Two real symmetric forms, the first nonsingular, are simultaneously diagonal
under congruence exactly when their relative operator is diagonalizable over
the real field. Source: Horn--Johnson (2013), Theorem 4.5.17; atlas
`simultaneous-diagonalization-congruence`.
-/

noncomputable section
open Matrix
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Real simultaneous diagonal congruence implies real diagonalizability
of the relative operator when the first matrix is nonsingular.
Horn--Johnson (2013), Theorem 4.5.17; helper for simultaneous congruence. -/
theorem isDiagonalizable_inverse_mul_of_diagonal_congruence
    {A B X : Matrix n n ℝ} {a b : n → ℝ}
    (hA : IsUnit A) (hX : IsUnit X)
    (hXA : Xᵀ * A * X = diagonal a) (hXB : Xᵀ * B * X = diagonal b) :
    IsDiagonalizable (A⁻¹ * B) := by
  have hXt : IsUnit Xᵀ := (Matrix.isUnit_transpose X).mpr hX
  have hDa : IsUnit (diagonal a) := hXA ▸ (hXt.mul hA).mul hX
  have hDiag : diagonal a * diagonal (fun i => (a i)⁻¹ * b i) = diagonal b := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    have hai : a i ≠ 0 := ((Matrix.isUnit_diagonal.mp hDa).apply i).ne_zero
    simp [hai]
  refine ⟨X, fun i => (a i)⁻¹ * b i, hX, ?_⟩
  apply (hXt.mul hA).mul_left_cancel
  calc
    (Xᵀ * A) * ((A⁻¹ * B) * X) = Xᵀ * B * X := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc A A⁻¹, Matrix.mul_nonsing_inv A
        ((Matrix.isUnit_iff_isUnit_det _).mp hA), Matrix.one_mul]
    _ = diagonal b := hXB
    _ = (Xᵀ * A) * (X * diagonal (fun i => (a i)⁻¹ * b i)) := by
      rw [← Matrix.mul_assoc, hXA, hDiag]

/-- Real diagonalizability of the relative operator supplies an invertible
simultaneous diagonal congruence for a symmetric pair with nonsingular first
matrix. No definiteness assumption is used.
Horn--Johnson (2013), Theorem 4.5.17.
atlas: simultaneous-diagonalization-congruence (partial) -/
theorem exists_diagonal_congruence_of_isDiagonalizable_inverse_mul
    {A B : Matrix n n ℝ} (hA : A.IsHermitian) (hAu : IsUnit A)
    (hB : B.IsHermitian) (hT : IsDiagonalizable (A⁻¹ * B)) :
    ∃ (X : Matrix n n ℝ) (a b : n → ℝ), IsUnit X ∧
      Xᵀ * A * X = diagonal a ∧ Xᵀ * B * X = diagonal b := by
  obtain ⟨V, d, hV, hTV⟩ := hT
  let C := Vᵀ * A * V
  let D := diagonal d
  have hC : C.IsHermitian := by
    simpa only [C, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_mul V hA
  have hD : D.IsHermitian := isHermitian_diagonal_iff.mpr (fun _ => star_trivial _)
  have hCD : C * D = Vᵀ * B * V := by
    calc
      C * D = Vᵀ * A * (V * D) := Matrix.mul_assoc _ _ _
      _ = Vᵀ * (A * A⁻¹) * B * V := by rw [← hTV]; simp only [Matrix.mul_assoc]
      _ = Vᵀ * B * V := by
        rw [Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det _).mp hAu), Matrix.mul_one]
  have hCDsym : (C * D).IsHermitian := by
    rw [hCD]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_mul V hB
  have hComm : Commute C D := (hC.commute_iff hD).mpr hCDsym
  obtain ⟨U, a, e, hU, hCU, hDU⟩ :=
    exists_orthogonal_congruence_diagonal_of_commute hC hD hComm
  have hUu : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).mpr
    (Matrix.isUnit_det_of_left_inverse hU)
  have hUU : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  refine ⟨V * U, a, fun i => a i * e i, hV.mul hUu, ?_, ?_⟩
  · simpa only [Matrix.transpose_mul, Matrix.mul_assoc, C] using hCU
  · calc
      (V * U)ᵀ * B * (V * U) = Uᵀ * (C * D) * U := by
        rw [hCD, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = (Uᵀ * C * U) * (Uᵀ * D * U) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc U Uᵀ, hUU, Matrix.one_mul]
      _ = diagonal (fun i => a i * e i) := by
        rw [hCU, hDU, Matrix.diagonal_mul_diagonal]

/-- Two real symmetric matrices with nonsingular first matrix are
simultaneously diagonal under real congruence exactly when their relative
operator is diagonalizable over the real field. This formulation includes
the real-spectrum requirement in real diagonalizability itself.
Horn--Johnson (2013), Theorem 4.5.17.
atlas: simultaneous-diagonalization-congruence (partial) -/
theorem exists_diagonal_congruence_iff_isDiagonalizable_inverse_mul
    {A B : Matrix n n ℝ} (hA : A.IsHermitian) (hAu : IsUnit A) (hB : B.IsHermitian) :
    (∃ (X : Matrix n n ℝ) (a b : n → ℝ), IsUnit X ∧
      Xᵀ * A * X = diagonal a ∧ Xᵀ * B * X = diagonal b) ↔
      IsDiagonalizable (A⁻¹ * B) := by
  constructor
  · rintro ⟨X, a, b, hX, hXA, hXB⟩
    exact isDiagonalizable_inverse_mul_of_diagonal_congruence hAu hX hXA hXB
  · exact exists_diagonal_congruence_of_isDiagonalizable_inverse_mul hA hAu hB

end NLAlib
