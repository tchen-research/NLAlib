import NLAlib.ForMathlib.RepresentationTheory.SchurAveraging
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.UnitaryGroup

/-! # Schur orthogonality for finite matrix coefficients

The coefficient identities follow from actual averaging of matrix units and
native irreducibility, without taking orthogonality as an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Finset
open scoped Matrix
namespace Representation

variable {G m n : Type*} [Group G] [Fintype G]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The matrix of the actual Schur average is the finite average of conjugates. -/
theorem toMatrix_averagedIntertwiningMap
    (ρ : Representation ℂ G (n → ℂ)) (σ : Representation ℂ G (m → ℂ))
    (M : Matrix m n ℂ) :
    LinearMap.toMatrix' (averagedIntertwiningMap ρ σ M.toLin').toLinearMap =
      (Fintype.card G : ℂ)⁻¹ • ∑ g : G,
        LinearMap.toMatrix' (σ g) * (M * LinearMap.toMatrix' (ρ g⁻¹)) := by
  rw [averagedIntertwiningMap_toLinearMap]
  simp only [map_smul, map_sum, LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_toLin']

/-- On one irreducible, the matrix average is ordinary trace divided by dimension. -/
theorem sum_matrix_conjugates_eq_trace_smul
    [Nonempty n] (ρ : Representation ℂ G (n → ℂ)) [IsIrreducible ρ]
    (M : Matrix n n ℂ) :
    (Fintype.card G : ℂ)⁻¹ • ∑ g : G,
        LinearMap.toMatrix' (ρ g) * (M * LinearMap.toMatrix' (ρ g⁻¹)) =
      (M.trace / Fintype.card n) • (1 : Matrix n n ℂ) := by
  rw [← toMatrix_averagedIntertwiningMap]
  rw [averagedIntertwiningMap_self_toLinearMap ρ
    (by simpa using (Nat.cast_ne_zero.mpr Fintype.card_ne_zero :
      (Fintype.card n : ℂ) ≠ 0))]
  simp

/-- Averaging conjugates between inequivalent irreducibles gives the zero matrix. -/
theorem sum_matrix_conjugates_eq_zero
    (ρ : Representation ℂ G (n → ℂ)) (σ : Representation ℂ G (m → ℂ))
    [IsIrreducible ρ] [IsIrreducible σ] (hne : IsEmpty (Equiv ρ σ))
    (M : Matrix m n ℂ) :
    (Fintype.card G : ℂ)⁻¹ • ∑ g : G,
      LinearMap.toMatrix' (σ g) * (M * LinearMap.toMatrix' (ρ g⁻¹)) = 0 := by
  rw [← toMatrix_averagedIntertwiningMap, averagedIntertwiningMap_eq_zero ρ σ hne]
  simp

/-- In a unitary matrix realization, inversion is conjugate transpose. -/
theorem toMatrix_inv_eq_conjTranspose
    (ρ : Representation ℂ G (n → ℂ))
    (hu : ∀ g, LinearMap.toMatrix' (ρ g) ∈ Matrix.unitaryGroup n ℂ) (g : G) :
    LinearMap.toMatrix' (ρ g⁻¹) = (LinearMap.toMatrix' (ρ g))ᴴ := by
  have hleft : (LinearMap.toMatrix' (ρ g))ᴴ * LinearMap.toMatrix' (ρ g) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (hu g)
  have hright : LinearMap.toMatrix' (ρ g) * LinearMap.toMatrix' (ρ g⁻¹) = 1 := by
    rw [← LinearMap.toMatrix'_mul, ← map_mul, mul_inv_cancel, map_one,
      LinearMap.toMatrix'_one]
  calc
    _ = 1 * LinearMap.toMatrix' (ρ g⁻¹) := (Matrix.one_mul _).symm
    _ = _ := by rw [← hleft, Matrix.mul_assoc, hright, Matrix.mul_one]

/-- Matrix coefficients of a single irreducible unitary representation satisfy
Schur orthogonality with the exact reciprocal dimension normalization. -/
theorem matrix_coefficients_orthogonality_self
    [Nonempty n] (ρ : Representation ℂ G (n → ℂ)) [IsIrreducible ρ]
    (hu : ∀ g, LinearMap.toMatrix' (ρ g) ∈ Matrix.unitaryGroup n ℂ)
    (i j a b : n) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g : G,
        LinearMap.toMatrix' (ρ g) i a * star (LinearMap.toMatrix' (ρ g) j b) =
      if a = b then (Fintype.card n : ℂ)⁻¹ * (if i = j then 1 else 0) else 0 := by
  have hh := congrArg (fun M : Matrix n n ℂ => M i j)
    (sum_matrix_conjugates_eq_trace_smul ρ (Matrix.single a b 1))
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.single_apply] at hh
  simp only [toMatrix_inv_eq_conjTranspose ρ hu, Matrix.conjTranspose_apply] at hh
  have ht : (Matrix.single a b (1 : ℂ)).trace = if a = b then 1 else 0 := by
    split_ifs with hab
    · subst b; exact Matrix.trace_single_eq_same _ _
    · exact Matrix.trace_single_eq_of_ne _ _ _ hab
  by_cases hab : a = b <;> by_cases hij : i = j <;>
    simpa [ht, hab, hij, Matrix.one_apply, div_eq_mul_inv, ite_and, mul_ite, ite_mul] using hh

/-- Matrix coefficients of inequivalent irreducible unitary representations are
orthogonal; no Fourier orthogonality certificate is assumed. -/
theorem matrix_coefficients_orthogonality_of_inequivalent
    (ρ : Representation ℂ G (n → ℂ)) (σ : Representation ℂ G (m → ℂ))
    [IsIrreducible ρ] [IsIrreducible σ] (hne : IsEmpty (Equiv ρ σ))
    (hρ : ∀ g, LinearMap.toMatrix' (ρ g) ∈ Matrix.unitaryGroup n ℂ)
    (i a : m) (j b : n) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g : G,
      LinearMap.toMatrix' (σ g) i a * star (LinearMap.toMatrix' (ρ g) j b) = 0 := by
  have hh := congrArg (fun M : Matrix m n ℂ => M i j)
    (sum_matrix_conjugates_eq_zero ρ σ hne (Matrix.single a b 1))
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply] at hh
  simp only [toMatrix_inv_eq_conjTranspose ρ hρ, Matrix.conjTranspose_apply] at hh
  simpa [ite_and, mul_ite, ite_mul] using hh

end Representation
