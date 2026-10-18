import NLAlib.Matrix.Functions.LogarithmicNorm
import Mathlib.Analysis.CStarAlgebra.Exponential

/-!
# Ordered complex-time exponential products

The list order is retained in every product. Hermitian generators give
unitary imaginary-time factors and uniform norm bounds on vertical strips.
Source: Sutter--Berta--Tomamichel, arXiv:1604.03023v3, Theorem 3.2 proof.
-/

noncomputable section

open Matrix Complex Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A finite product of complex-time exponentials in its specified list order. -/
def orderedMatrixExp (H : List (Matrix n n ℂ)) (z : ℂ) : Matrix n n ℂ :=
  (H.map (fun A => matrixExp (z • A))).prod

@[simp] theorem orderedMatrixExp_nil (z : ℂ) :
    orderedMatrixExp ([] : List (Matrix n n ℂ)) z = 1 := rfl

@[simp] theorem orderedMatrixExp_cons (A : Matrix n n ℂ) (H : List (Matrix n n ℂ)) (z : ℂ) :
    orderedMatrixExp (A :: H) z = matrixExp (z • A) * orderedMatrixExp H z := rfl

@[simp] theorem orderedMatrixExp_zero (H : List (Matrix n n ℂ)) : orderedMatrixExp H 0 = 1 := by
  induction H with
  | nil => rfl
  | cons A H ih => simp [orderedMatrixExp_cons, matrixExp, ih]

/-- Ordered exponential products are entire, without commutativity of the
generators or a choice of logarithmic branches. -/
theorem analyticAt_orderedMatrixExp (H : List (Matrix n n ℂ)) (z : ℂ) :
    AnalyticAt ℂ (orderedMatrixExp H) z := by
  induction H with
  | nil => exact analyticAt_const
  | cons A H ih =>
    change AnalyticAt ℂ (fun w : ℂ => matrixExp (w • A) * orderedMatrixExp H w) z
    have he : AnalyticAt ℂ (fun w : ℂ => matrixExp (w • A)) z := by
      have hs : AnalyticAt ℂ (fun w : ℂ => w • A) z := analyticAt_id.smul analyticAt_const
      have hx : AnalyticAt ℂ (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) (z • A) :=
        NormedSpace.exp_analytic _
      exact hx.comp (f := fun w : ℂ => w • A) hs
    exact he.mul ih

set_option backward.isDefEq.respectTransparency false in
/-- The first derivative of the ordered product at zero is the actual sum
of its generators, without any commutation assumption. -/
theorem hasDerivAt_orderedMatrixExp_zero (H : List (Matrix n n ℂ)) :
    HasDerivAt (orderedMatrixExp H) H.sum (0 : ℂ) := by
  induction H with
  | nil =>
    convert! hasDerivAt_const (0 : ℂ) (1 : Matrix n n ℂ) using 1
  | cons A H ih =>
    have he := hasDerivAt_exp_smul_const A (0 : ℂ)
    have hp := he.mul ih
    convert! hp using 1
    simp only [List.sum_cons, zero_smul, NormedSpace.exp_zero,
      orderedMatrixExp_zero, one_mul, mul_one]

/-- Every ordered exponential product is an actual invertible matrix. -/
theorem isUnit_orderedMatrixExp (H : List (Matrix n n ℂ)) (z : ℂ) :
    IsUnit (orderedMatrixExp H z) := by
  let : NormedAlgebra ℚ (Matrix n n ℂ) := .restrictScalars ℚ ℂ _
  induction H with
  | nil => exact isUnit_one
  | cons A H ih => exact (NormedSpace.isUnit_exp (z • A)).mul ih

/-- The imaginary-time exponential of a Hermitian generator is unitary. -/
theorem matrixExp_imaginary_smul_mem_unitary {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (t : ℝ) :
    matrixExp (((t : ℂ) * I) • A) ∈ unitary (Matrix n n ℂ) := by
  let : NormedAlgebra ℚ (Matrix n n ℂ) := .restrictScalars ℚ ℂ _
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  rw [skewAdjoint.mem_iff]
  simp [star_smul, hA.isSelfAdjoint.star_eq, mul_smul]

/-- Products of imaginary-time factors are unitary in their original order. -/
theorem orderedMatrixExp_imaginary_mem_unitary (H : List (Matrix n n ℂ))
    (hH : ∀ A ∈ H, A.IsHermitian) (t : ℝ) :
    orderedMatrixExp H ((t : ℂ) * I) ∈ unitary (Matrix n n ℂ) := by
  induction H with
  | nil => exact (unitary _).one_mem
  | cons A H ih =>
    exact (unitary _).mul_mem (matrixExp_imaginary_smul_mem_unitary (hH A (by simp)) t)
      (ih (fun B hB => hH B (by simp [hB])))

/-- The Hermitian part of a complex scalar multiple of a Hermitian matrix is
the real scalar multiple by the real part. -/
theorem selfAdjointPart_complex_smul_of_isHermitian {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (z : ℂ) :
    (selfAdjointPart ℝ (z • A) : Matrix n n ℂ) = z.re • A := by
  simp only [selfAdjointPart_apply_coe, star_smul, hA.isSelfAdjoint.star_eq]
  rw [← add_smul, Complex.star_def, Complex.add_conj]
  simp [← Complex.coe_smul, smul_smul]

/-- The spectral norm of a complex-time Hermitian exponential is bounded
only by the real part of time. The imaginary part has no growth cost. -/
theorem norm_matrixExp_complex_smul_le {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (z : ℂ) :
    ‖matrixExp (z • A)‖ ≤ Real.exp (|z.re| * ‖A‖) := by
  have hs : IsSelfAdjoint (z.re • A) := (IsSelfAdjoint.all z.re).smul hA.isSelfAdjoint
  have hup : (selfAdjointPart ℝ (z • A) : Matrix n n ℂ) ≤ (|z.re| * ‖A‖) • 1 := by
    rw [selfAdjointPart_complex_smul_of_isHermitian hA]
    simpa only [Algebra.algebraMap_eq_smul_one, norm_smul, Real.norm_eq_abs] using
      hs.le_algebraMap_norm_self
  have h := specNorm_matrixExp_smul_le_of_selfAdjointPart_le hup (t := 1) (by norm_num)
  simpa only [one_smul, one_mul, specNorm_eq_norm] using h

/-- Actual ordered products satisfy an explicit uniform vertical-strip
bound. No commutation of distinct factors is used. -/
theorem norm_orderedMatrixExp_le (H : List (Matrix n n ℂ))
    (hH : ∀ A ∈ H, A.IsHermitian) (z : ℂ) :
    ‖orderedMatrixExp H z‖ ≤ Real.exp (|z.re| * (H.map (fun A => ‖A‖)).sum) := by
  induction H with
  | nil =>
    by_cases hn : Nonempty n
    · let := hn
      simp
    · let : IsEmpty n := not_nonempty_iff.mp hn
      have hzero : (1 : Matrix n n ℂ) = 0 := Subsingleton.elim _ _
      simp [hzero]
  | cons A H ih =>
    simp only [orderedMatrixExp_cons, List.map_cons, List.sum_cons]
    calc
      _ ≤ ‖matrixExp (z • A)‖ * ‖orderedMatrixExp H z‖ := norm_mul_le _ _
      _ ≤ Real.exp (|z.re| * ‖A‖) * Real.exp (|z.re| * (H.map (fun B => ‖B‖)).sum) :=
        mul_le_mul (norm_matrixExp_complex_smul_le (hH A (by simp)) z)
          (ih (fun B hB => hH B (by simp [hB]))) (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Concatenation preserves the displayed order of the two finite products. -/
@[simp] theorem orderedMatrixExp_append (H K : List (Matrix n n ℂ)) (z : ℂ) :
    orderedMatrixExp (H ++ K) z = orderedMatrixExp H z * orderedMatrixExp K z := by
  simp [orderedMatrixExp, List.map_append, List.prod_append]

/-- Reversing the factors and negating time constructs an actual left
inverse; every cancellation retains its adjacent order. -/
theorem orderedMatrixExp_reverse_neg_mul (H : List (Matrix n n ℂ)) (z : ℂ) :
    orderedMatrixExp H.reverse (-z) * orderedMatrixExp H z = 1 := by
  let : NormedAlgebra ℚ (Matrix n n ℂ) := .restrictScalars ℚ ℂ _
  induction H with
  | nil => simp
  | cons A H ih =>
    have hcancel : matrixExp ((-z) • A) * matrixExp (z • A) = 1 := by
      simp only [matrixExp, neg_smul]
      rw [← NormedSpace.exp_add_of_commute (Commute.refl (z • A)).neg_left,
        neg_add_cancel, NormedSpace.exp_zero]
    rw [List.reverse_cons, orderedMatrixExp_append]
    simp only [orderedMatrixExp_cons, orderedMatrixExp_nil, mul_one]
    calc
      _ = orderedMatrixExp H.reverse (-z) *
          ((matrixExp ((-z) • A) * matrixExp (z • A)) * orderedMatrixExp H z) := by
        simp only [mul_assoc]
      _ = 1 := by rw [hcancel, one_mul, ih]

/-- Imaginary time has no norm growth, including the empty matrix shape. -/
theorem norm_orderedMatrixExp_imaginary_le_one (H : List (Matrix n n ℂ))
    (hH : ∀ A ∈ H, A.IsHermitian) (t : ℝ) :
    ‖orderedMatrixExp H ((t : ℂ) * I)‖ ≤ 1 := by
  simpa using norm_orderedMatrixExp_le H hH ((t : ℂ) * I)

/-- The same explicit constant bounds the whole closed vertical strip. -/
theorem norm_orderedMatrixExp_le_exp_sum_norm (H : List (Matrix n n ℂ))
    (hH : ∀ A ∈ H, A.IsHermitian) {z : ℂ} (hz : |z.re| ≤ 1) :
    ‖orderedMatrixExp H z‖ ≤ Real.exp ((H.map (fun A => ‖A‖)).sum) := by
  have hs : 0 ≤ (H.map (fun A => ‖A‖)).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨A, _, rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg _
  apply (norm_orderedMatrixExp_le H hH z).trans
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The explicit reverse product gives a uniform lower norm bound on the
right boundary; consequently its logarithm cannot develop a negative tail. -/
theorem exp_neg_sum_norm_le_norm_orderedMatrixExp_right [Nonempty n]
    (H : List (Matrix n n ℂ)) (hH : ∀ A ∈ H, A.IsHermitian) (t : ℝ) :
    Real.exp (-(H.map (fun A => ‖A‖)).sum) ≤
      ‖orderedMatrixExp H (1 + (t : ℂ) * I)‖ := by
  have hrev : ∀ A ∈ H.reverse, A.IsHermitian := by simpa using hH
  have hInv := norm_orderedMatrixExp_le_exp_sum_norm H.reverse hrev
    (z := -(1 + (t : ℂ) * I)) (by simp)
  rw [List.map_reverse, List.sum_reverse] at hInv
  have hprod := norm_mul_le (orderedMatrixExp H.reverse (-(1 + (t : ℂ) * I)))
    (orderedMatrixExp H (1 + (t : ℂ) * I))
  rw [orderedMatrixExp_reverse_neg_mul, norm_one] at hprod
  have he : 1 ≤ Real.exp ((H.map (fun A => ‖A‖)).sum) *
      ‖orderedMatrixExp H (1 + (t : ℂ) * I)‖ :=
    hprod.trans (mul_le_mul_of_nonneg_right hInv (norm_nonneg _))
  rw [Real.exp_neg, ← one_div]
  exact (div_le_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using he)

end NLAlib
