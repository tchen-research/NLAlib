import NLAlib.Matrix.Spectral.Inertia
import NLAlib.Matrix.Spectral.Diagonalizable
import Mathlib.Analysis.Matrix.Order

/-!
# Definite pairs under simultaneous congruence

Whitening a positive definite matrix and orthogonally diagonalizing the
whitened symmetric second matrix gives one invertible congruence factor.
The diagonal entries are the actual eigenvalues of the relative operator,
and inherit the second matrix's inertia and positivity.
Source: Horn--Johnson (2013), Theorem 7.6.1 and Corollary 7.6.2.
This is the definite part of `simultaneous-diagonalization-congruence`.
-/

noncomputable section
open Matrix Polynomial
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A positive definite and symmetric pair is simultaneously congruent to
the identity and a real diagonal, in factor form. The diagonal entries are
nonnegative whenever the second matrix is PSD.
Horn--Johnson (2013), Theorem 7.6.1.
atlas: simultaneous-diagonalization-congruence (partial) -/
theorem exists_definite_pair_congruence_diagonal {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.IsHermitian) :
    ∃ (S : Matrix n n ℝ) (d : n → ℝ), IsUnit S ∧ A = S * Sᵀ ∧
      B = S * diagonal d * Sᵀ ∧ (B.PosSemidef → ∀ i, 0 ≤ d i) := by
  let R := CFC.sqrt A
  have hR : IsUnit R := (CFC.isUnit_sqrt_iff A hA.posSemidef.nonneg).mpr hA.isUnit
  have hRd := (Matrix.isUnit_iff_isUnit_det R).mp hR
  have hRt : Rᵀ = R := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq
  have hRit : R⁻¹ᵀ = R⁻¹ := by rw [Matrix.transpose_nonsing_inv, hRt]
  have hSq : R * R = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hRRi : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hRd
  have hRiR : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hRd
  let H := R⁻¹ * B * R⁻¹
  have hH : H.IsHermitian := by
    simpa only [H, Matrix.conjTranspose_eq_transpose_of_trivial, hRit] using
      Matrix.isHermitian_mul_mul_conjTranspose R⁻¹ hB
  let U : Matrix n n ℝ := hH.eigenvectorUnitary
  have hUU : U * Uᵀ = 1 := eigenvectorUnitary_mul_transpose_self hH
  have hU : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).mpr
    (Matrix.isUnit_det_of_right_inverse hUU)
  refine ⟨R * U, hH.eigenvalues, hR.mul hU, ?_, ?_, ?_⟩
  · symm
    calc
      (R * U) * (R * U)ᵀ = R * (U * Uᵀ) * R := by
        rw [Matrix.transpose_mul, hRt]
        simp only [Matrix.mul_assoc]
      _ = A := by rw [hUU, Matrix.mul_one, hSq]
  · have hRHR : R * H * R = B := by
      calc
        R * H * R = (R * R⁻¹) * B * (R⁻¹ * R) := by
          simp only [H, Matrix.mul_assoc]
        _ = B := by rw [hRRi, hRiR, Matrix.one_mul, Matrix.mul_one]
    calc
      B = R * H * R := hRHR.symm
      _ = R * (U * diagonal hH.eigenvalues * Uᵀ) * R := by
        rw [← eq_eigenvectorUnitary_mul_diagonal_mul_transpose hH]
      _ = (R * U) * diagonal hH.eigenvalues * (R * U)ᵀ := by
        rw [Matrix.transpose_mul, hRt]
        simp only [Matrix.mul_assoc]
  · intro hBPSD
    have hHPSD : H.PosSemidef := by
      simpa only [H, Matrix.conjTranspose_eq_transpose_of_trivial, hRit] using
        hBPSD.mul_mul_conjTranspose_same R⁻¹
    exact hHPSD.eigenvalues_nonneg

/-- Simultaneous congruence to identity and a diagonal makes the relative
operator similar to that exact diagonal. Horn--Johnson (2013), Theorem 7.6.1;
helper for `simultaneous-diagonalization-congruence`. -/
theorem inverse_mul_eq_inv_transpose_mul_diagonal_mul_transpose
    {A B S : Matrix n n ℝ} {d : n → ℝ} (hS : IsUnit S)
    (hA : A = S * Sᵀ) (hB : B = S * diagonal d * Sᵀ) :
    A⁻¹ * B = Sᵀ⁻¹ * diagonal d * Sᵀ := by
  have hSd := (Matrix.isUnit_iff_isUnit_det S).mp hS
  rw [hA, hB, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc S⁻¹ S, Matrix.nonsing_inv_mul S hSd, Matrix.one_mul]

/-- The diagonal of a definite-pair congruence enumerates the relative
operator's eigenvalues with full characteristic multiplicity.
Horn--Johnson (2013), Theorem 7.6.1;
helper for `simultaneous-diagonalization-congruence`. -/
theorem charpoly_inverse_mul_eq_prod_of_congruence
    {A B S : Matrix n n ℝ} {d : n → ℝ} (hS : IsUnit S)
    (hA : A = S * Sᵀ) (hB : B = S * diagonal d * Sᵀ) :
    (A⁻¹ * B).charpoly = ∏ i, (X - C (d i)) := by
  have hSt : IsUnit Sᵀ := (Matrix.isUnit_transpose S).mpr hS
  rw [inverse_mul_eq_inv_transpose_mul_diagonal_mul_transpose hS hA hB]
  have h := Matrix.charpoly_units_conj' hSt.unit (diagonal d)
  simpa only [Matrix.coe_units_inv, hSt.unit_spec, Matrix.charpoly_diagonal] using h

/-- The real relative spectrum of a definite-pair congruence is exactly
the diagonal range. Horn--Johnson (2013), Theorem 7.6.1;
helper for `simultaneous-diagonalization-congruence`. -/
theorem spectrum_inverse_mul_eq_range_of_congruence
    {A B S : Matrix n n ℝ} {d : n → ℝ} (hS : IsUnit S)
    (hA : A = S * Sᵀ) (hB : B = S * diagonal d * Sᵀ) :
    spectrum ℝ (A⁻¹ * B) = Set.range d := by
  have hSt : IsUnit Sᵀ := (Matrix.isUnit_transpose S).mpr hS
  rw [inverse_mul_eq_inv_transpose_mul_diagonal_mul_transpose hS hA hB]
  have h := spectrum.units_conjugate' (R := ℝ) (a := diagonal d) (u := hSt.unit)
  simpa only [Matrix.coe_units_inv, hSt.unit_spec, spectrum_diagonal] using h

/-- The relative operator of a definite-pair congruence is diagonalizable
over the real field. Horn--Johnson (2013), Corollary 7.6.2;
helper for `simultaneous-diagonalization-congruence`. -/
theorem isDiagonalizable_inverse_mul_of_congruence
    {A B S : Matrix n n ℝ} {d : n → ℝ} (hS : IsUnit S)
    (hA : A = S * Sᵀ) (hB : B = S * diagonal d * Sᵀ) :
    IsDiagonalizable (A⁻¹ * B) := by
  have hSt : IsUnit Sᵀ := (Matrix.isUnit_transpose S).mpr hS
  refine ⟨Sᵀ⁻¹, d, Matrix.isUnit_nonsing_inv_iff.mpr hSt, ?_⟩
  rw [inverse_mul_eq_inv_transpose_mul_diagonal_mul_transpose hS hA hB]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv Sᵀ ((Matrix.isUnit_iff_isUnit_det _).mp hSt), Matrix.mul_one]

/-- Positive and negative inertia of the definite-pair diagonal are those
of the second matrix. Horn--Johnson (2013), Theorem 7.6.1;
helper for `simultaneous-diagonalization-congruence`. -/
theorem inertia_diagonal_eq_of_congruence {B S : Matrix n n ℝ} {d : n → ℝ}
    (hS : IsUnit S) (hB : B = S * diagonal d * Sᵀ) :
    inertiaPos (diagonal d) = inertiaPos B ∧ inertiaNeg (diagonal d) = inertiaNeg B := by
  have hSt : IsUnit Sᵀ := (Matrix.isUnit_transpose S).mpr hS
  have hp := inertiaPos_transpose_mul_mul (diagonal d) hSt
  have hn := inertiaNeg_transpose_mul_mul (diagonal d) hSt
  rw [Matrix.transpose_transpose, ← hB] at hp hn
  exact ⟨hp.symm, hn.symm⟩

/-- A positive definite and symmetric pair has a real diagonalizable
relative operator. Horn--Johnson (2013), Corollary 7.6.2.
atlas: simultaneous-diagonalization-congruence (partial) -/
theorem isDiagonalizable_inverse_mul_of_posDef {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.IsHermitian) : IsDiagonalizable (A⁻¹ * B) := by
  obtain ⟨S, d, hS, hAA, hBB, -⟩ := exists_definite_pair_congruence_diagonal hA hB
  exact isDiagonalizable_inverse_mul_of_congruence hS hAA hBB

/-- The product of a positive definite real matrix and a symmetric real
matrix is diagonalizable over the real field.
Horn--Johnson (2013), Corollary 7.6.2.
atlas: simultaneous-diagonalization-congruence (partial) -/
theorem isDiagonalizable_mul_of_posDef {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.IsHermitian) : IsDiagonalizable (A * B) := by
  let : Invertible A := hA.isUnit.invertible
  simpa only [Matrix.inv_inv_of_invertible] using
    isDiagonalizable_inverse_mul_of_posDef hA.inv hB

/-- The relative operator of a positive definite and PSD pair has
nonnegative real spectrum. Horn--Johnson (2013), Corollary 7.6.2.
atlas: simultaneous-diagonalization-congruence (partial) -/
theorem spectrum_inverse_mul_subset_nonneg_of_posDef {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.PosSemidef) : spectrum ℝ (A⁻¹ * B) ⊆ Set.Ici 0 := by
  obtain ⟨S, d, hS, hAA, hBB, hd⟩ := exists_definite_pair_congruence_diagonal hA hB.isHermitian
  rw [spectrum_inverse_mul_eq_range_of_congruence hS hAA hBB]
  rintro _ ⟨i, rfl⟩
  exact hd hB i

/-- The product of a positive definite and PSD real pair has nonnegative
real spectrum. Horn--Johnson (2013), Corollary 7.6.2.
atlas: simultaneous-diagonalization-congruence (partial) -/
theorem spectrum_mul_subset_nonneg_of_posDef {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.PosSemidef) : spectrum ℝ (A * B) ⊆ Set.Ici 0 := by
  let : Invertible A := hA.isUnit.invertible
  simpa only [Matrix.inv_inv_of_invertible] using
    spectrum_inverse_mul_subset_nonneg_of_posDef hA.inv hB

/-- The full definite-pair congruence clause gives the exact relative
eigenvalue list, its inertia and PSD signs, and real diagonalizability of
both relative and ordinary products. The general indefinite and PSD-pair
variants are separate parts of the atlas bundle.
Horn--Johnson (2013), Theorem 7.6.1 and Corollary 7.6.2.
atlas: simultaneous-diagonalization-congruence (partial) -/
theorem definite_pair_congruence_characterizations {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.IsHermitian) :
    (∃ (S : Matrix n n ℝ) (d : n → ℝ), IsUnit S ∧ A = S * Sᵀ ∧
      B = S * diagonal d * Sᵀ ∧
      (A⁻¹ * B).charpoly = ∏ i, (X - C (d i)) ∧
      spectrum ℝ (A⁻¹ * B) = Set.range d ∧ IsDiagonalizable (A⁻¹ * B) ∧
      inertiaPos (diagonal d) = inertiaPos B ∧ inertiaNeg (diagonal d) = inertiaNeg B ∧
      (B.PosSemidef → ∀ i, 0 ≤ d i)) ∧
    IsDiagonalizable (A * B) ∧ (B.PosSemidef → spectrum ℝ (A * B) ⊆ Set.Ici 0) := by
  obtain ⟨S, d, hS, hAA, hBB, hd⟩ := exists_definite_pair_congruence_diagonal hA hB
  have hi := inertia_diagonal_eq_of_congruence hS hBB
  exact ⟨⟨S, d, hS, hAA, hBB, charpoly_inverse_mul_eq_prod_of_congruence hS hAA hBB,
    spectrum_inverse_mul_eq_range_of_congruence hS hAA hBB,
    isDiagonalizable_inverse_mul_of_congruence hS hAA hBB, hi.1, hi.2, hd⟩,
    isDiagonalizable_mul_of_posDef hA hB, spectrum_mul_subset_nonneg_of_posDef hA⟩

end NLAlib
