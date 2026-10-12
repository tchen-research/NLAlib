import NLAlib.Matrix.Spectral.SimultaneousTriangularization
import NLAlib.Matrix.Spectral.SimultaneousDiagonalization
import NLAlib.Matrix.Spectral.SchurFrobenius
import NLAlib.Matrix.Spectral.NormalSimilarity
/-!
# Simultaneous normal diagonalization and prescribed eigenvalue order

A common Schur basis diagonalizes every normal member. One column
permutation then prescribes the complete eigenvalue order of any chosen
member, for both general diagonalizable and normal families.
Source: Horn–Johnson (2013), Theorems 1.3.21 and 2.4.8.1.
-/

noncomputable section
open Polynomial
open scoped Matrix Matrix.Norms.Frobenius

namespace NLAlib

variable {n ι : Type*} [Fintype n] [DecidableEq n]

/-- Every commuting family of complex normal matrices has one common
unitary diagonalization. Source: Horn–Johnson (2013), Theorem 2.4.8.1;
the family may be infinite or empty, and zero-dimensional shapes are included.
atlas: simultaneous-diagonalization (partial) -/
theorem exists_simultaneous_unitary_diagonalization_of_normal_of_commute
    (A : ι → Matrix n n ℂ) (hA : ∀ a, A a * (A a)ᴴ = (A a)ᴴ * A a)
    (hcomm : Pairwise fun a b => Commute (A a) (A b)) :
    ∃ (U : Matrix.unitaryGroup n ℂ) (d : ι → n → ℂ),
      ∀ a, A a = (U : Matrix n n ℂ) * Matrix.diagonal (d a) * (U : Matrix n n ℂ)ᴴ := by
  classical
  obtain ⟨U, T, hT⟩ := exists_simultaneous_unitary_schur_triangularization A hcomm
    (Fintype.equivFin n).symm
  refine ⟨U, fun a => (T a).diag, fun a => ?_⟩
  obtain ⟨hrep, _, hchar⟩ := hT a
  have hnorm := frobenius_norm_sq_eq_sum_norm_sq_of_normal (hA a) (T a).diag hchar
  rw [hrep, frobenius_norm_sq_unitary_similarity] at hnorm
  simp only [Matrix.diag_apply] at hnorm
  have hmass := frobenius_norm_sq_eq_diagonal_add_off_diagonal (T a)
  have hzero : ‖T a - Matrix.diagonal (T a).diag‖ ^ 2 = 0 := by linarith
  have hdiag : T a = Matrix.diagonal (T a).diag :=
    sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))
  rw [hdiag] at hrep
  exact hrep

/-- A family of normal matrices commutes exactly when it shares a unitary
diagonalization. Source: Horn–Johnson (2013), Theorem 2.4.8.1; arbitrary
families and finite matrix shapes are allowed.
atlas: simultaneous-diagonalization (partial) -/
theorem pairwise_commute_iff_exists_simultaneous_unitary_diagonalization
    (A : ι → Matrix n n ℂ) (hA : ∀ a, A a * (A a)ᴴ = (A a)ᴴ * A a) :
    (Pairwise fun a b => Commute (A a) (A b)) ↔
      ∃ (U : Matrix.unitaryGroup n ℂ) (d : ι → n → ℂ),
        ∀ a, A a = (U : Matrix n n ℂ) * Matrix.diagonal (d a) * (U : Matrix n n ℂ)ᴴ := by
  constructor
  · exact exists_simultaneous_unitary_diagonalization_of_normal_of_commute A hA
  · rintro ⟨U, d, hrep⟩ a b _
    have hUt : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self U
    have hU : IsUnit (U : Matrix n n ℂ) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hUt)
    apply commute_of_simultaneous_diagonalization hU
    · rw [hrep, Matrix.mul_assoc, hUt, Matrix.mul_one]
    · rw [hrep, Matrix.mul_assoc, hUt, Matrix.mul_one]

/-- A common invertible eigenvector basis can put one selected member's
eigenvalues in any prescribed complete characteristic order. Source:
Horn–Johnson (2013), Theorem 1.3.21; repeated eigenvalues are retained.
atlas: simultaneous-diagonalization (partial) -/
theorem exists_simultaneous_diagonalization_with_charpoly
    (A : ι → Matrix n n ℂ) (hdiag : ∀ a, IsDiagonalizable (A a))
    (hcomm : Pairwise fun a b => Commute (A a) (A b)) (a₀ : ι) (d₀ : n → ℂ)
    (hd₀ : (A a₀).charpoly = ∏ j, (X - C (d₀ j))) :
    ∃ (V : Matrix n n ℂ) (d : ι → n → ℂ), IsUnit V ∧ d a₀ = d₀ ∧
      ∀ a, A a * V = V * Matrix.diagonal (d a) := by
  classical
  obtain ⟨V, d, hV, hAV⟩ := exists_simultaneous_diagonalization_of_commute A hdiag hcomm
  have hchar : (A a₀).charpoly = ∏ j, (X - C (d a₀ j)) := by
    have hsim : A a₀ = V * Matrix.diagonal (d a₀) * V⁻¹ := by
      rw [← hAV, Matrix.mul_assoc, Matrix.mul_nonsing_inv V
        ((Matrix.isUnit_iff_isUnit_det V).mp hV), Matrix.mul_one]
    rw [hsim, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul V ((Matrix.isUnit_iff_isUnit_det V).mp hV),
      Matrix.one_mul, Matrix.charpoly_diagonal]
  obtain ⟨σ, hσ⟩ := exists_perm_eq_of_prod_X_sub_C_eq d₀ (d a₀) (hd₀.symm.trans hchar)
  let W := V.submatrix id σ
  refine ⟨W, fun a j => d a (σ j), ?_, funext hσ, ?_⟩
  · exact (Matrix.isUnit_submatrix_equiv (Equiv.refl n) σ).mpr hV
  · intro a
    ext i j
    have h := congrArg (fun M : Matrix n n ℂ => M i (σ j)) (hAV a)
    rw [Matrix.mul_diagonal] at h ⊢
    exact h

/-- A commuting normal family's common unitary eigenbasis can put one
selected member's eigenvalues in any prescribed characteristic order.
Source: Horn–Johnson (2013), Theorem 2.4.8.1; repeated values, arbitrary
families, and empty matrix shapes are included.
atlas: simultaneous-diagonalization (partial) -/
theorem exists_simultaneous_unitary_diagonalization_with_charpoly
    (A : ι → Matrix n n ℂ) (hA : ∀ a, A a * (A a)ᴴ = (A a)ᴴ * A a)
    (hcomm : Pairwise fun a b => Commute (A a) (A b)) (a₀ : ι) (d₀ : n → ℂ)
    (hd₀ : (A a₀).charpoly = ∏ j, (X - C (d₀ j))) :
    ∃ (U : Matrix.unitaryGroup n ℂ) (d : ι → n → ℂ), d a₀ = d₀ ∧
      ∀ a, A a = (U : Matrix n n ℂ) * Matrix.diagonal (d a) * (U : Matrix n n ℂ)ᴴ := by
  classical
  obtain ⟨U, d, hrep⟩ := exists_simultaneous_unitary_diagonalization_of_normal_of_commute A hA hcomm
  have hUt : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self U
  have hchar : (A a₀).charpoly = ∏ j, (X - C (d a₀ j)) := by
    rw [hrep, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hUt,
      Matrix.one_mul, Matrix.charpoly_diagonal]
  obtain ⟨σ, hσ⟩ := exists_perm_eq_of_prod_X_sub_C_eq d₀ (d a₀) (hd₀.symm.trans hchar)
  let V : Matrix n n ℂ := (U : Matrix n n ℂ).submatrix id σ
  have hVt : Vᴴ * V = 1 := by
    rw [show Vᴴ = (U : Matrix n n ℂ)ᴴ.submatrix σ id from rfl]
    have hmul := Matrix.submatrix_mul_equiv (U : Matrix n n ℂ)ᴴ (U : Matrix n n ℂ)
      σ (Equiv.refl n) σ
    simp only [Equiv.coe_refl] at hmul
    change (U : Matrix n n ℂ)ᴴ.submatrix σ id * (U : Matrix n n ℂ).submatrix id σ = 1
    rw [hmul, hUt, Matrix.submatrix_one_equiv]
  let W : Matrix.unitaryGroup n ℂ := ⟨V, Matrix.mem_unitaryGroup_iff'.mpr hVt⟩
  refine ⟨W, fun a j => d a (σ j), funext hσ, fun a => ?_⟩
  have hAU : A a * (U : Matrix n n ℂ) = (U : Matrix n n ℂ) * Matrix.diagonal (d a) := by
    rw [hrep, Matrix.mul_assoc, hUt, Matrix.mul_one]
  have hAV : A a * V = V * Matrix.diagonal (fun j => d a (σ j)) := by
    ext i j
    have h := congrArg (fun M : Matrix n n ℂ => M i (σ j)) hAU
    rw [Matrix.mul_diagonal] at h ⊢
    exact h
  have hVV : V * Vᴴ = 1 := Unitary.coe_mul_star_self W
  change A a = V * Matrix.diagonal (fun j => d a (σ j)) * Vᴴ
  rw [← hAV, Matrix.mul_assoc, hVV, Matrix.mul_one]

end NLAlib
