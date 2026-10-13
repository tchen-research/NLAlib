import NLAlib.Matrix.Inequalities.Schur
import NLAlib.Matrix.Inequalities.MajorizationProperties
import NLAlib.Matrix.Spectral.SchurTriangularization
import NLAlib.Matrix.Spectral.NormalSimilarity
/-!
# Hermitian parts and unitary triangularization

Mathlib's self-adjoint-part map is the Hermitian part `(A+A*)/2`.
It commutes with unitary conjugation and has the real parts on its diagonal.
Source: Horn--Johnson (2013), Section 4.3;
supports `real-part-eigenvalue-majorization`.
-/

noncomputable section
open Matrix Polynomial
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- The real diagonal of the Hermitian part is the real diagonal of the
original matrix. Horn--Johnson (2013), Section 4.3;
helper for real-part eigenvalue majorization. -/
theorem real_diagonal_selfAdjointPart (A : Matrix n n ℂ) (i : n) :
    ((selfAdjointPart ℝ A : Matrix n n ℂ) i i).re = (A i i).re := by
  simp [selfAdjointPart_apply_coe, Matrix.star_eq_conjTranspose, Complex.real_smul]
  ring

omit [DecidableEq n] in
/-- Taking the Hermitian part commutes with matrix conjugation by a unitary.
The identity itself holds for an arbitrary conjugating matrix.
Horn--Johnson (2013), Section 4.3; helper for real-part majorization. -/
theorem selfAdjointPart_mul_mul_conjTranspose (U A : Matrix n n ℂ) :
    (selfAdjointPart ℝ (U * A * Uᴴ) : Matrix n n ℂ) =
      U * (selfAdjointPart ℝ A : Matrix n n ℂ) * Uᴴ := by
  simp only [selfAdjointPart_apply_coe, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

/-- The complete real-part eigenvalue list of a complex matrix is majorized
by the Hermitian-part eigenvalues. Eigenvalue multiplicities are
specified by the characteristic factorization; the list may be in any order.
Horn--Johnson (2013), Theorem 4.3.50.
atlas: real-part-eigenvalue-majorization (partial) -/
theorem majorized_real_parts_eigenvalues_selfAdjointPart
    (A : Matrix n n ℂ) (z : n → ℂ)
    (hz : A.charpoly = ∏ i, (X - C (z i))) :
    Majorized (fun i => (z i).re)
      (Matrix.IsHermitian.eigenvalues (selfAdjointPart ℝ A).property) := by
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  obtain ⟨U, T, hA, -, hTchar⟩ := exists_unitary_schur_triangularization A e
  let hH : (selfAdjointPart ℝ A : Matrix n n ℂ).IsHermitian := (selfAdjointPart ℝ A).property
  let hK : (selfAdjointPart ℝ T : Matrix n n ℂ).IsHermitian := (selfAdjointPart ℝ T).property
  have hHK : hH.eigenvalues = hK.eigenvalues := by
    apply (hH.eigenvalues_eq_eigenvalues_iff hK).mpr
    have hconj : (selfAdjointPart ℝ A : Matrix n n ℂ) =
        (U : Matrix n n ℂ) * (selfAdjointPart ℝ T : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ := by
      rw [hA, selfAdjointPart_mul_mul_conjTranspose]
    rw [hconj, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      ← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self, Matrix.one_mul]
  have hmajor : Majorized (fun i => (T i i).re) hH.eigenvalues := by
    rw [hHK]
    simpa only [RCLike.re_to_complex, real_diagonal_selfAdjointPart] using
      majorized_diagonal_eigenvalues hK
  obtain ⟨σ, hσ⟩ := exists_perm_eq_of_prod_X_sub_C_eq z (fun i => T i i)
    (hz.symm.trans hTchar)
  have hperm := majorized_comp_perm (fun i => (T i i).re) σ
  have hre : (fun i => (z i).re) = (fun i => (T i i).re) ∘ σ := by
    funext i
    exact congrArg Complex.re (hσ i).symm
  rw [hre]
  exact hperm.trans hmajor

/-- Bendixson's bounds place the real part of every characteristic eigenvalue
between the smallest and largest Hermitian-part eigenvalues. The presence of
the selected eigenvalue provides positive dimension.
Horn--Johnson (2013), Corollary 4.3.51.
atlas: real-part-eigenvalue-majorization (partial) -/
theorem real_part_eigenvalue_mem_Icc_selfAdjointPart
    (A : Matrix n n ℂ) (z : n → ℂ)
    (hz : A.charpoly = ∏ j, (X - C (z j))) (i : n) :
    let hdim : 0 < Fintype.card n := Fintype.card_pos_iff.mpr ⟨i⟩
    let hH : (selfAdjointPart ℝ A : Matrix n n ℂ).IsHermitian := (selfAdjointPart ℝ A).property
    (z i).re ∈ Set.Icc
      (hH.eigenvalues₀ ⟨Fintype.card n - 1, Nat.sub_lt hdim (by decide)⟩)
      (hH.eigenvalues₀ ⟨0, hdim⟩) := by
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  obtain ⟨U, T, hA, -, hTchar⟩ := exists_unitary_schur_triangularization A e
  let hH : (selfAdjointPart ℝ A : Matrix n n ℂ).IsHermitian := (selfAdjointPart ℝ A).property
  let hK : (selfAdjointPart ℝ T : Matrix n n ℂ).IsHermitian := (selfAdjointPart ℝ T).property
  have hHK : hH.eigenvalues = hK.eigenvalues := by
    apply (hH.eigenvalues_eq_eigenvalues_iff hK).mpr
    have hconj : (selfAdjointPart ℝ A : Matrix n n ℂ) =
        (U : Matrix n n ℂ) * (selfAdjointPart ℝ T : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ := by
      rw [hA, selfAdjointPart_mul_mul_conjTranspose]
    rw [hconj, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      ← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self, Matrix.one_mul]
  have hsorted : hH.eigenvalues₀ = hK.eigenvalues₀ := by
    funext k
    have hh := congrFun hHK (e k)
    simpa only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply] using hh
  obtain ⟨σ, hσ⟩ := exists_perm_eq_of_prod_X_sub_C_eq z (fun j => T j j)
    (hz.symm.trans hTchar)
  have hb := re_diagonal_mem_Icc_eigenvalues₀ hK (σ i) (Fintype.card_pos_iff.mpr ⟨i⟩)
  simpa only [RCLike.re_to_complex, real_diagonal_selfAdjointPart, hσ, ← hsorted] using hb

end NLAlib
