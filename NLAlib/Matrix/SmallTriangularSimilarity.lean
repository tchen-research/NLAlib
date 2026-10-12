import NLAlib.Matrix.SchurTriangularization
import Mathlib.Analysis.RCLike.Basic

/-!
# Arbitrarily small strictly upper entries by diagonal similarity

Scaling coordinate `i` by a positive scalar raised to its ordered position
shrinks every strict upper entry while preserving diagonal entries and zeros.
Source: Horn–Johnson (2013), §2.3.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

/-- Positive diagonal scaling makes all entries above a prescribed coordinate
ranking smaller than any positive epsilon, preserving diagonal entries and
all existing zeros. Source: Horn–Johnson (2013), §2.3; the chosen parameter
is `ε / (1 + ∑ i j, ‖T i j‖ + ε)`, and both real and complex fields are allowed. -/
theorem exists_diagonal_similarity_small_upper_entries
    {n K : Type*} [Fintype n] [DecidableEq n] [RCLike K]
    (T : Matrix n n K) (r : n → ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : Matrix n n K, IsUnit D ∧
      (∀ i, (D⁻¹ * T * D) i i = T i i) ∧
      (∀ i j, T i j = 0 → (D⁻¹ * T * D) i j = 0) ∧
      (∀ i j, r i < r j → ‖(D⁻¹ * T * D) i j‖ < ε) := by
  classical
  let M : ℝ := ∑ i, ∑ j, ‖T i j‖
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  have hentryM (i j : n) : ‖T i j‖ ≤ M :=
    (Finset.single_le_sum (fun k _ => norm_nonneg (T i k)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => norm_nonneg (T k l))
        (Finset.mem_univ i))
  let δ : ℝ := ε / (1 + M + ε)
  have hden : 0 < 1 + M + ε := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hδ1 : δ ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hMδ : M * δ < ε := by
    dsimp [δ]
    rw [← mul_div_assoc, div_lt_iff₀ hden]
    nlinarith
  have hδK : (δ : K) ≠ 0 := by exact_mod_cast hδ.ne'
  let D : Matrix n n K := Matrix.diagonal (fun i => (δ : K) ^ r i)
  let H : Matrix n n K := Matrix.diagonal (fun i => ((δ : K) ^ r i)⁻¹)
  have hHD : H * D = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [inv_mul_cancel₀ (pow_ne_zero _ hδK), Matrix.diagonal_one]
  have hD : IsUnit D := (Matrix.isUnit_iff_isUnit_det D).mpr (Matrix.isUnit_det_of_left_inverse hHD)
  have hInv : D⁻¹ = H := Matrix.inv_eq_left_inv hHD
  have hentry (i j : n) : (D⁻¹ * T * D) i j = ((δ : K) ^ r i)⁻¹ * T i j * (δ : K) ^ r j := by
    rw [hInv]
    dsimp only [H, D]
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine ⟨D, hD, ?_, ?_, ?_⟩
  · intro i
    rw [hentry]
    field_simp
  · intro i j hij
    rw [hentry, hij, mul_zero, zero_mul]
  · intro i j hij
    have hnorm : ‖(D⁻¹ * T * D) i j‖ = ‖T i j‖ * δ ^ (r j - r i) := by
      rw [hentry, norm_mul, norm_mul, norm_inv, norm_pow, norm_pow]
      simp only [RCLike.norm_ofReal, abs_of_pos hδ]
      rw [pow_sub₀ δ hδ.ne' (Nat.le_of_lt hij)]
      ring
    rw [hnorm]
    calc
      ‖T i j‖ * δ ^ (r j - r i) ≤ ‖T i j‖ * δ :=
        mul_le_mul_of_nonneg_left (pow_le_of_le_one hδ.le hδ1 (by omega)) (norm_nonneg _)
      _ ≤ M * δ := mul_le_mul_of_nonneg_right (hentryM i j) hδ.le
      _ < ε := hMδ

/-- Any real or complex triangularizing similarity can be refined to make
its strict upper entries arbitrarily small over the same field. Source:
Horn–Johnson (2013), §2.3; this supplies the real small-entry clause whenever
a real triangular form exists. -/
theorem exists_similarity_small_entries_of_triangular_similarity
    {n K : Type*} [Fintype n] [DecidableEq n] [RCLike K]
    (A S : Matrix n n K) (hS : IsUnit S) (e : Fin (Fintype.card n) ≃ n)
    (htri : ∀ i j, e.symm j < e.symm i → (S⁻¹ * A * S) i j = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : Matrix n n K, IsUnit R ∧
      (∀ i j, e.symm j < e.symm i → (R⁻¹ * A * R) i j = 0) ∧
      (∀ i j, e.symm i < e.symm j → ‖(R⁻¹ * A * R) i j‖ < ε) := by
  obtain ⟨D, hD, _, hzero, hsmall⟩ := exists_diagonal_similarity_small_upper_entries
    (S⁻¹ * A * S) (fun i => (e.symm i).val) hε
  have hsim : (S * D)⁻¹ * A * (S * D) = D⁻¹ * (S⁻¹ * A * S) * D := by
    rw [Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
  refine ⟨S * D, hS.mul hD, ?_, ?_⟩
  · intro i j hij
    rw [hsim]
    exact hzero i j (htri i j hij)
  · intro i j hij
    rw [hsim]
    exact hsmall i j hij

/-- Every complex matrix has an upper triangular similar matrix whose
strictly upper entries are smaller than any prescribed positive epsilon.
Source: Horn–Johnson (2013), §2.3; arbitrary finite labels are ordered by
the supplied enumeration, and zero-dimensional matrices are included.
atlas: schur-triangularization (partial) -/
theorem exists_similarity_upper_triangular_small_entries
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (e : Fin (Fintype.card n) ≃ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Matrix n n ℂ, IsUnit S ∧
      (∀ i j, e.symm j < e.symm i → (S⁻¹ * A * S) i j = 0) ∧
      (∀ i j, e.symm i < e.symm j → ‖(S⁻¹ * A * S) i j‖ < ε) := by
  obtain ⟨U, T, hA, htri, _⟩ := exists_unitary_schur_triangularization A e
  obtain ⟨D, hD, _, hzero, hsmall⟩ :=
    exists_diagonal_similarity_small_upper_entries T (fun i => (e.symm i).val) hε
  have hUt : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self U
  have hU : IsUnit (U : Matrix n n ℂ) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hUt)
  have hUinv : (U : Matrix n n ℂ)⁻¹ = (U : Matrix n n ℂ)ᴴ := Matrix.inv_eq_left_inv hUt
  let S := (U : Matrix n n ℂ) * D
  have hsim : S⁻¹ * A * S = D⁻¹ * T * D := by
    dsimp [S]
    rw [Matrix.mul_inv_rev, hUinv, hA]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (U : Matrix n n ℂ)ᴴ (U : Matrix n n ℂ),
      hUt, Matrix.one_mul]
  refine ⟨S, hU.mul hD, ?_, ?_⟩
  · intro i j hij
    rw [hsim]
    exact hzero i j (htri i j hij)
  · intro i j hij
    rw [hsim]
    exact hsmall i j hij

end NLAlib
