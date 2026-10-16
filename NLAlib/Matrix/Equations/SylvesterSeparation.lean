import NLAlib.Matrix.Spectral.SylvesterQualitative
import NLAlib.Matrix.Perturbation.Pseudospectrum
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # The actual Frobenius separation of a rectangular Sylvester operator -/
noncomputable section
open scoped Matrix Kronecker
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {K m n : Type*} [RCLike K] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Column-major vectorization, with no chosen coordinate enumeration. -/
def matrixVectorization (X : Matrix m n K) : n × m → K := fun ji => X ji.2 ji.1

open scoped Matrix.Norms.L2Operator in
/-- The genuine column-major Kronecker matrix of `X ↦ AX-XB`. -/
def sylvesterKronecker (A : Matrix m m K) (B : Matrix n n K) : Matrix (n × m) (n × m) K :=
  (1 : Matrix n n K) ⊗ₖ A - Bᵀ ⊗ₖ (1 : Matrix m m K)

open scoped Matrix.Norms.L2Operator in
/-- Vectorization exactly identifies the actual Sylvester equation with its
Kronecker linear system. -/
theorem sylvesterKronecker_mulVec (A : Matrix m m K) (B : Matrix n n K) (X : Matrix m n K) :
    sylvesterKronecker A B *ᵥ matrixVectorization X = matrixVectorization (A * X - X * B) := by
  ext ⟨j,i⟩
  simp only [sylvesterKronecker, Matrix.mulVec, dotProduct, matrixVectorization, Fintype.sum_prod_type]
  simp [Matrix.one_apply, Matrix.mul_apply, Matrix.transpose_apply, mul_sub,
    Finset.sum_sub_distrib, mul_ite, Finset.sum_ite_irrel, mul_comm]

omit [DecidableEq m] [DecidableEq n] in
open scoped Matrix.Norms.L2Operator in
/-- Vectorization is an isometry for the actual Frobenius and Euclidean norms. -/
theorem norm_matrixVectorization (X : Matrix m n K) :
    ‖WithLp.toLp 2 (matrixVectorization X)‖ = frobNorm X := by
  have hs : ‖WithLp.toLp 2 (matrixVectorization X)‖ ^ 2 = frobNorm X ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, frobNorm_sq, frobSq_eq_sum_norm_sq]
    simp only [matrixVectorization, Fintype.sum_prod_type]
    exact Finset.sum_comm
  nlinarith [norm_nonneg (WithLp.toLp 2 (matrixVectorization X)), frobNorm_nonneg X]

open scoped Matrix.Norms.L2Operator in
/-- Frobenius separation, equal by construction to the smallest singular
value of the genuine Kronecker operator. -/
def sylvesterSep (A : Matrix m m K) (B : Matrix n n K) : ℝ :=
  singularValues (sylvesterKronecker A B) (Fintype.card (n × m) - 1)

open scoped Matrix.Norms.L2Operator in
/-- Separation is nonnegative even when the operator is singular. -/
theorem sylvesterSep_nonneg (A : Matrix m m K) (B : Matrix n n K) : 0 ≤ sylvesterSep A B :=
  singularValues_nonneg _ _

open scoped Matrix.Norms.L2Operator in
/-- Separation is a lower expansion bound on every actual matrix argument. -/
theorem sylvesterSep_mul_frobNorm_le (A : Matrix m m K) (B : Matrix n n K) (X : Matrix m n K) :
    sylvesterSep A B * frobNorm X ≤ frobNorm (A * X - X * B) := by
  have h := singularValues_last_mul_norm_le (sylvesterKronecker A B) (matrixVectorization X)
  simpa only [sylvesterSep, sylvesterKronecker_mulVec, norm_matrixVectorization] using h

open scoped Matrix.Norms.L2Operator in
/-- The separation minimum is attained by an actual unit-Frobenius matrix. -/
theorem exists_frobNorm_one_sylvester_eq_sep [Nonempty m] [Nonempty n]
    (A : Matrix m m K) (B : Matrix n n K) :
    ∃ X : Matrix m n K, frobNorm X = 1 ∧ frobNorm (A * X - X * B) = sylvesterSep A B := by
  obtain ⟨v, hv, hKv⟩ := exists_unit_norm_mulVec_eq_singularValues_last (sylvesterKronecker A B)
  let X : Matrix m n K := fun i j => v (j,i)
  have hvX : matrixVectorization X = v := by ext ⟨j,i⟩; rfl
  refine ⟨X, ?_, ?_⟩
  · rw [← norm_matrixVectorization, hvX]; exact hv
  · rw [← norm_matrixVectorization, ← sylvesterKronecker_mulVec, hvX]
    exact hKv

open scoped Matrix.Norms.L2Operator in
/-- Frobenius separation is exactly the attained unit-sphere minimum.
Source: user derivations, equations (G1) and the Kronecker vectorization route.
atlas: sylvester-separation-residual-conditioning (partial) -/
theorem isLeast_sylvesterSep [Nonempty m] [Nonempty n]
    (A : Matrix m m K) (B : Matrix n n K) :
    IsLeast {c : ℝ | ∃ X : Matrix m n K, frobNorm X = 1 ∧ frobNorm (A * X - X * B) = c}
      (sylvesterSep A B) := by
  refine ⟨exists_frobNorm_one_sylvester_eq_sep A B, ?_⟩
  rintro c ⟨X, hX, rfl⟩
  simpa only [hX, mul_one] using sylvesterSep_mul_frobNorm_le A B X

open scoped Matrix.Norms.L2Operator in
/-- Positive separation is exactly injectivity of the actual operator. -/
theorem sylvesterSep_pos_iff_injective [Nonempty m] [Nonempty n]
    (A : Matrix m m K) (B : Matrix n n K) :
    0 < sylvesterSep A B ↔ Function.Injective (sylvesterLinearMap A B) := by
  constructor
  · intro hsep
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro X hX
    have h := sylvesterSep_mul_frobNorm_le A B X
    change A * X - X * B = 0 at hX
    rw [hX, frobNorm_zero] at h
    have hz : frobNorm X = 0 := by nlinarith [frobNorm_nonneg X]
    exact (frobNorm_eq_zero_iff X).mp hz
  · intro hinj
    by_contra h
    have hz : sylvesterSep A B = 0 := le_antisymm (le_of_not_gt h) (sylvesterSep_nonneg A B)
    obtain ⟨X, hX, hS⟩ := exists_frobNorm_one_sylvester_eq_sep A B
    rw [hz] at hS
    have hL : sylvesterLinearMap A B X = sylvesterLinearMap A B 0 := by
      change A * X - X * B = _
      rw [(frobNorm_eq_zero_iff (A * X - X * B)).mp hS]
      simp [sylvesterLinearMap]
    have hzero := hinj hL
    rw [hzero, frobNorm_zero] at hX
    norm_num at hX

open scoped Matrix.Norms.L2Operator in
/-- For complex matrices the sharp separation is positive exactly when the
two actual spectra are disjoint; normality is unnecessary. -/
theorem sylvesterSep_pos_iff_disjoint_spectrum [Nonempty m] [Nonempty n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    0 < sylvesterSep A B ↔ Disjoint (spectrum ℂ A) (spectrum ℂ B) := by
  rw [sylvesterSep_pos_iff_injective, ← sylvesterLinearMap_bijective_iff_disjoint_spectrum]
  exact ⟨fun h => ⟨h, LinearMap.injective_iff_surjective.mp h⟩, fun h => h.1⟩

open scoped Matrix.Norms.L2Operator in
/-- The residual gives the sharp constant-one Frobenius a posteriori bound. -/
theorem frobNorm_sub_le_residual_div_sylvesterSep (A : Matrix m m K) (B : Matrix n n K)
    (C X Xhat : Matrix m n K) (hsep : 0 < sylvesterSep A B)
    (hX : A * X - X * B = C) :
    frobNorm (X - Xhat) ≤ frobNorm (C - (A * Xhat - Xhat * B)) / sylvesterSep A B := by
  apply (le_div_iff₀ hsep).mpr
  rw [mul_comm]
  have he : A * (X - Xhat) - (X - Xhat) * B = C - (A * Xhat - Xhat * B) := by
    rw [← hX, Matrix.mul_sub, Matrix.sub_mul]; abel
  exact (sylvesterSep_mul_frobNorm_le A B (X - Xhat)).trans_eq (congrArg frobNorm he)

end NLAlib
