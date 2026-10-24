/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Functions.PolynomialIntertwining
import NLAlib.Matrix.Norms.SpectralNormBounds
import NLAlib.Matrix.Norms.Complexification
import NLAlib.Matrix.Spectral.NormalSpectral

/-! # Polynomial spectral bounds through a diagonalization

The source polynomial-similarity argument works over either RCLike field
and for polynomials over any compatible coefficient ring. In particular
real residual polynomials may be evaluated on a complex diagonalization.

Ported from NLA-lib/NLAlib, commit
6a845a2ec27f37c1a98118c107a06a13ce45273d,
`Matrix/Functions/Polynomial.lean`,
`specNorm_aeval_le_pseudoConditionNumber_mul` (Apache-2.0,
NLAlib contributors), using the backend's existing intertwining API.
-/

noncomputable section
open Polynomial
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem aeval_diagonal_eval₂ {R 𝕜 : Type*} [CommSemiring R]
    [CommSemiring 𝕜] [Algebra R 𝕜] (d : n → 𝕜) (p : R[X]) :
    aeval (Matrix.diagonal d) p = Matrix.diagonal (fun i => p.eval₂ (algebraMap R 𝕜) (d i)) := by
  have h := Polynomial.aeval_algHom_apply (Matrix.diagonalAlgHom R (n := n) (α := 𝕜)) d p
  simp only [Matrix.diagonalAlgHom_apply] at h
  rw [h]
  congr 1
  funext i
  rw [aeval_pi_apply₂, aeval_def]

/-- Polynomial evaluation through an actual diagonalization has the
source eigenvector condition-factor bound, including empty matrices.
Polynomials may have real coefficients while the diagonalization is
complex. Source: Saad (2003), Proposition 6.32. Proof adapted from
NLA-lib/NLAlib commit 6a845a2, `specNorm_aeval_le_pseudoConditionNumber_mul`.
atlas: gmres-diagonalizable (partial) -/
theorem specNorm_aeval_le_of_eq_mul_diagonal_mul {R 𝕜 : Type*}
    [CommSemiring R] [RCLike 𝕜] [Algebra R 𝕜]
    {A V W : Matrix n n 𝕜} {d : n → 𝕜}
    (hVW : V * W = 1) (hA : A = V * Matrix.diagonal d * W)
    (p : R[X]) {M : ℝ} (hM : ∀ i, ‖p.eval₂ (algebraMap R 𝕜) (d i)‖ ≤ M) :
    specNorm (aeval A p) ≤ specNorm V * specNorm W * M := by
  classical
  rcases isEmpty_or_nonempty n with hn | hn
  · simp only [Subsingleton.elim (aeval A p) 0, Subsingleton.elim V 0,
      specNorm_zero, zero_mul, le_refl]
  · let i : n := Classical.choice hn
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM i)
    have hWV : W * V = 1 := mul_eq_one_comm.mp hVW
    have hAV : A * V = V * Matrix.diagonal d := by
      rw [hA, Matrix.mul_assoc, Matrix.mul_assoc, hWV, Matrix.mul_one]
    have hpoly := aeval_mul_eq_mul_aeval_of_mul_eq hAV p
    have hpA : aeval A p = V * Matrix.diagonal
        (fun j => p.eval₂ (algebraMap R 𝕜) (d j)) * W := by
      rw [← aeval_diagonal_eval₂, ← hpoly, Matrix.mul_assoc, hVW, Matrix.mul_one]
    have hD : specNorm (Matrix.diagonal (fun j => p.eval₂ (algebraMap R 𝕜) (d j))) ≤ M := by
      rw [specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
      exact (pi_norm_le_iff_of_nonneg hM0).mpr hM
    rw [hpA]
    calc
      _ ≤ (specNorm V * specNorm (Matrix.diagonal
          (fun j => p.eval₂ (algebraMap R 𝕜) (d j)))) * specNorm W :=
        (specNorm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _))
      _ ≤ (specNorm V * M) * specNorm W :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hD (specNorm_nonneg _)) (specNorm_nonneg _)
      _ = _ := by ring

/-- A real polynomial on a normal complex matrix is bounded by its
values on the actual complex spectrum. Unitary diagonalization removes
the eigenvector condition factor. Source: Saad (2003), Proposition 6.32;
the normal specialization of the source polynomial-similarity bound.
atlas: gmres-diagonalizable (partial) -/
theorem specNorm_aeval_le_of_normal {A : Matrix n n ℂ}
    (hA : A * Aᴴ = Aᴴ * A) (p : ℝ[X]) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ spectrum ℂ A, ‖p.eval₂ (algebraMap ℝ ℂ) z‖ ≤ M) :
    specNorm (aeval A p) ≤ M := by
  obtain ⟨U, d, hAd⟩ := exists_unitary_diagonalization_of_normal hA
  have hU : HasOrthonormalCols (U : Matrix n n ℂ) := Unitary.coe_star_mul_self U
  have hUU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 := Unitary.coe_mul_star_self U
  have hUd : A * (U : Matrix n n ℂ) = (U : Matrix n n ℂ) * Matrix.diagonal d := by
    rw [hAd, Matrix.mul_assoc, Matrix.mul_assoc, hU.conjTranspose_mul_self, Matrix.mul_one]
  have hpoly := aeval_mul_eq_mul_aeval_of_mul_eq hUd p
  have hpA : aeval A p = (U : Matrix n n ℂ) * Matrix.diagonal
      (fun i => p.eval₂ (algebraMap ℝ ℂ) (d i)) * (U : Matrix n n ℂ)ᴴ := by
    rw [← aeval_diagonal_eval₂, ← hpoly, Matrix.mul_assoc, hUU, Matrix.mul_one]
  have hs : spectrum ℂ A = Set.range d := by
    rw [hAd]
    simpa only [← Matrix.star_eq_conjTranspose, Unitary.coe_star, spectrum_diagonal]
      using Unitary.spectrum_star_right_conjugate (R := ℂ) (a := Matrix.diagonal d) (U := U)
  rw [hpA, specNorm_mul_conjTranspose_right_of_hasOrthonormalCols hU,
    specNorm_mul_left_of_hasOrthonormalCols hU, specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hM0).mpr (fun i => hM (d i) (by rw [hs]; exact ⟨i, rfl⟩))

/-- Real matrix polynomial evaluation commutes with entrywise complexification. -/
theorem map_ofReal_aeval (A : Matrix n n ℝ) (p : ℝ[X]) :
    (aeval A p).map (algebraMap ℝ ℂ) = aeval (A.map (algebraMap ℝ ℂ)) p := by
  let φ : Matrix n n ℝ →ₐ[ℝ] Matrix n n ℂ :=
    { toRingHom := (algebraMap ℝ ℂ).mapMatrix
      commutes' := by
        intro c
        ext i j
        by_cases hij : i = j <;>
          simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal, Matrix.map_apply, hij] }
  exact (Polynomial.aeval_algHom_apply φ A p).symm

end NLAlib
