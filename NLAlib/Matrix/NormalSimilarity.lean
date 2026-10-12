import NLAlib.Matrix.NormalSpectral
import NLAlib.ForMathlib.Data.MultisetPermutation
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Unitary similarity classification of normal matrices

Characteristic eigenvalue lists can be reordered by column permutations
of a unitary eigenbasis. Matching lists classify complex normal matrices
up to unitary similarity. Source: Horn–Johnson (2013), Theorem 2.5.8;
atlas `normal-matrices`.
-/

noncomputable section
open Polynomial
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Equal complete characteristic factorizations differ by an index
permutation. Source: Horn–Johnson (2013), §2.5; root multiplicities are
retained, so repeated eigenvalues require no special case. -/
theorem exists_perm_eq_of_prod_X_sub_C_eq (a b : n → ℂ)
    (hab : (∏ i, (X - C (a i))) = ∏ i, (X - C (b i))) :
    ∃ σ : Equiv.Perm n, ∀ i, b (σ i) = a i := by
  have hprod : ((Finset.univ.val.map a).map fun z => X - C z).prod =
      ((Finset.univ.val.map b).map fun z => X - C z).prod := by
    simpa only [Multiset.map_map, Function.comp_def, Finset.prod_map_val] using hab
  have hroots := congrArg Polynomial.roots hprod
  simp only [Polynomial.roots_multiset_prod_X_sub_C] at hroots
  exact exists_perm_eq_of_map_univ_val_eq a b hroots

/-- A normal matrix can be unitarily diagonalized in any prescribed complete
characteristic eigenvalue order. Source: Horn–Johnson (2013), Theorem 2.5.3;
the order may contain repeated eigenvalues and an empty index type.
atlas: normal-matrices (partial) -/
theorem exists_unitary_diagonalization_of_normal_with_charpoly {A : Matrix n n ℂ}
    (hA : A * Aᴴ = Aᴴ * A) (d : n → ℂ)
    (hd : A.charpoly = ∏ i, (X - C (d i))) :
    ∃ U : Matrix.unitaryGroup n ℂ,
      A = (U : Matrix n n ℂ) * Matrix.diagonal d * (U : Matrix n n ℂ)ᴴ := by
  classical
  obtain ⟨U, a, hUa⟩ := exists_unitary_diagonalization_of_normal hA
  have hUt : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self U
  have hAU : A * (U : Matrix n n ℂ) = (U : Matrix n n ℂ) * Matrix.diagonal a := by
    rw [hUa, Matrix.mul_assoc, hUt, Matrix.mul_one]
  have ha : A.charpoly = ∏ i, (X - C (a i)) := by
    rw [hUa, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hUt, Matrix.one_mul,
      Matrix.charpoly_diagonal]
  obtain ⟨σ, hσ⟩ := exists_perm_eq_of_prod_X_sub_C_eq d a (hd.symm.trans ha)
  let V : Matrix n n ℂ := (U : Matrix n n ℂ).submatrix id σ
  have hVt : Vᴴ * V = 1 := by
    rw [show Vᴴ = (U : Matrix n n ℂ)ᴴ.submatrix σ id from rfl]
    have hmul := Matrix.submatrix_mul_equiv (U : Matrix n n ℂ)ᴴ (U : Matrix n n ℂ)
      σ (Equiv.refl n) σ
    simp only [Equiv.coe_refl] at hmul
    change (U : Matrix n n ℂ)ᴴ.submatrix σ id * (U : Matrix n n ℂ).submatrix id σ = 1
    rw [hmul, hUt, Matrix.submatrix_one_equiv]
  let W : Matrix.unitaryGroup n ℂ := ⟨V, Matrix.mem_unitaryGroup_iff'.mpr hVt⟩
  have hAV : A * V = V * Matrix.diagonal d := by
    ext i j
    have h := congrArg (fun M : Matrix n n ℂ => M i (σ j)) hAU
    rw [Matrix.mul_diagonal] at h
    rw [Matrix.mul_diagonal]
    simpa only [V, Matrix.mul_apply, Matrix.submatrix_apply, id_eq, hσ] using h
  have hVV : V * Vᴴ = 1 := Unitary.coe_mul_star_self W
  refine ⟨W, ?_⟩
  change A = V * Matrix.diagonal d * Vᴴ
  calc
    A = A * (V * Vᴴ) := by rw [hVV, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, hAV]

/-- Two complex normal matrices are unitarily similar exactly when they
have the same characteristic eigenvalues with multiplicity. Source:
Horn–Johnson (2013), Theorem 2.5.8; equality of characteristic polynomials
is the precise multiplicity-sensitive equality of eigenvalue lists.
atlas: normal-matrices (partial) -/
theorem exists_unitary_similarity_iff_charpoly_eq_of_normal {A B : Matrix n n ℂ}
    (hA : A * Aᴴ = Aᴴ * A) (hB : B * Bᴴ = Bᴴ * B) :
    (∃ U : Matrix.unitaryGroup n ℂ,
      A = (U : Matrix n n ℂ) * B * (U : Matrix n n ℂ)ᴴ) ↔ A.charpoly = B.charpoly := by
  constructor
  · rintro ⟨U, hAB⟩
    have hUt : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self U
    rw [hAB, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hUt, Matrix.one_mul]
  · intro hchar
    obtain ⟨V, d, hVd⟩ := exists_unitary_diagonalization_of_normal hB
    have hVt : (V : Matrix n n ℂ)ᴴ * (V : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self V
    have hd : B.charpoly = ∏ i, (X - C (d i)) := by
      rw [hVd, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hVt, Matrix.one_mul,
        Matrix.charpoly_diagonal]
    obtain ⟨W, hWd⟩ := exists_unitary_diagonalization_of_normal_with_charpoly hA d (hchar.trans hd)
    let U : Matrix.unitaryGroup n ℂ := W * star V
    refine ⟨U, ?_⟩
    rw [hVd]
    change A = ((W : Matrix n n ℂ) * (V : Matrix n n ℂ)ᴴ) *
      ((V : Matrix n n ℂ) * Matrix.diagonal d * (V : Matrix n n ℂ)ᴴ) *
        ((W : Matrix n n ℂ) * (V : Matrix n n ℂ)ᴴ)ᴴ
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc (V : Matrix n n ℂ)ᴴ (V : Matrix n n ℂ),
      hVt, Matrix.one_mul]
    simpa only [Matrix.mul_assoc] using hWd

end NLAlib
