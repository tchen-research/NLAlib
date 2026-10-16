import NLAlib.Matrix.Norms.Core
import NLAlib.Matrix.Basic.RankInequalities
import NLAlib.Matrix.Basic.RankBounds
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.NoncommRing

/-!
# The two-solve Sylvester ADI iteration

The iteration is defined by its actual two linear solves. Only the two solved
shifted matrices must be invertible; numerator factors may be singular.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {K m n : Type*} [RCLike K] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- The first Sylvester ADI solve. -/
def sylvesterADIHalf (A : Matrix m m K) (B : Matrix n n K)
    (C Y : Matrix m n K) (β : K) : Matrix m n K :=
  (A - β • 1)⁻¹ * (Y * (B - β • 1) + C)

/-- One Sylvester ADI step, performing the left solve followed by the right solve. -/
def sylvesterADIStep (A : Matrix m m K) (B : Matrix n n K)
    (C Y : Matrix m n K) (α β : K) : Matrix m n K :=
  ((A - α • 1) * sylvesterADIHalf A B C Y β - C) * (B - α • 1)⁻¹

/-- The residual convention for `A X - X B = C`. -/
def sylvesterResidual (A : Matrix m m K) (B : Matrix n n K)
    (C Y : Matrix m n K) : Matrix m n K := C - A * Y + Y * B

/-- The first computed intermediate matrix solves its stated shifted system. -/
theorem shifted_mul_sylvesterADIHalf (A : Matrix m m K) (B : Matrix n n K)
    (C Y : Matrix m n K) (β : K) (hβ : IsUnit (A - β • 1).det) :
    (A - β • 1) * sylvesterADIHalf A B C Y β = Y * (B - β • 1) + C := by
  simp [sylvesterADIHalf, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hβ]

/-- The completed ADI step solves its stated right shifted system. -/
theorem sylvesterADIStep_mul_shifted (A : Matrix m m K) (B : Matrix n n K)
    (C Y : Matrix m n K) (α β : K) (hα : IsUnit (B - α • 1).det) :
    sylvesterADIStep A B C Y α β * (B - α • 1) =
      (A - α • 1) * sylvesterADIHalf A B C Y β - C := by
  simp [sylvesterADIStep, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hα]

private theorem shifted_inv_mul_decomposition (A : Matrix m m K) (α β : K)
    (hβ : IsUnit (A - β • 1).det) :
    (A - α • 1) * (A - β • 1)⁻¹ = 1 + (β - α) • (A - β • 1)⁻¹ := by
  have h : A - α • (1 : Matrix m m K) = (A - β • 1) + (β - α) • 1 := by module
  rw [h, Matrix.add_mul, Matrix.mul_nonsing_inv _ hβ]
  simp

private theorem inv_mul_shifted_decomposition (A : Matrix m m K) (α β : K)
    (hβ : IsUnit (A - β • 1).det) :
    (A - β • 1)⁻¹ * (A - α • 1) = 1 + (β - α) • (A - β • 1)⁻¹ := by
  have h : A - α • (1 : Matrix m m K) = (A - β • 1) + (β - α) • 1 := by module
  rw [h, Matrix.mul_add, Matrix.nonsing_inv_mul _ hβ]
  simp

/-- The exact ADI correction is the old residual multiplied by the two solved
inverses. Equal shifts therefore give an unchanged iterate.
Source: user derivations, equation (G3).
atlas: adi-sylvester-rational-error (partial) -/
theorem sylvesterADIStep_sub (A : Matrix m m K) (B : Matrix n n K)
    (C Y : Matrix m n K) (α β : K)
    (hβ : IsUnit (A - β • 1).det) (hα : IsUnit (B - α • 1).det) :
    sylvesterADIStep A B C Y α β - Y =
      (β - α) • ((A - β • 1)⁻¹ * sylvesterResidual A B C Y * (B - α • 1)⁻¹) := by
  have hcancel : Function.Injective (fun Z : Matrix m n K => Z * (B - α • 1)) := by
    intro Z W h
    have := congrArg (fun T => T * (B - α • 1)⁻¹) h
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hα] using this
  apply hcancel
  dsimp only
  rw [Matrix.sub_mul, sylvesterADIStep_mul_shifted _ _ _ _ _ _ hα]
  rw [Matrix.smul_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hα, Matrix.mul_one]
  simp only [sylvesterADIHalf, ← Matrix.mul_assoc,
    shifted_inv_mul_decomposition _ _ _ hβ]
  have hinv : (A - β • 1)⁻¹ * A = 1 + β • (A - β • 1)⁻¹ := by
    simpa using inv_mul_shifted_decomposition A 0 β hβ
  simp only [sylvesterResidual, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    smul_add, smul_sub]
  simp only [← Matrix.mul_assoc, hinv, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
  module

omit [Fintype n] [DecidableEq n] in
private theorem mul_left_cancel_shifted (A : Matrix m m K) (β : K)
    (hβ : IsUnit (A - β • 1).det) {Z W : Matrix m n K}
    (h : (A - β • 1) * Z = (A - β • 1) * W) : Z = W := by
  have := congrArg (fun T => (A - β • 1)⁻¹ * T) h
  simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hβ] using this

omit [Fintype m] [DecidableEq m] in
private theorem mul_right_cancel_shifted (B : Matrix n n K) (α : K)
    (hα : IsUnit (B - α • 1).det) {Z W : Matrix m n K}
    (h : Z * (B - α • 1) = W * (B - α • 1)) : Z = W := by
  have := congrArg (fun T => T * (B - α • 1)⁻¹) h
  simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hα] using this

/-- Exact error after the first solve. -/
theorem sub_sylvesterADIHalf (A : Matrix m m K) (B : Matrix n n K)
    (C X Y : Matrix m n K) (β : K) (hX : A * X - X * B = C)
    (hβ : IsUnit (A - β • 1).det) :
    X - sylvesterADIHalf A B C Y β = (A - β • 1)⁻¹ * (X - Y) * (B - β • 1) := by
  apply mul_left_cancel_shifted A β hβ
  simp only [Matrix.mul_sub, shifted_mul_sylvesterADIHalf _ _ _ _ _ hβ,
    ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hβ, Matrix.one_mul]
  rw [← hX]
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]
  module

/-- One actual two-solve ADI step transports the exact error by the two
rational factors. No numerator invertibility is assumed.
Source: user derivations, Sylvester ADI error identity.
atlas: adi-sylvester-rational-error (partial) -/
theorem sub_sylvesterADIStep (A : Matrix m m K) (B : Matrix n n K)
    (C X Y : Matrix m n K) (α β : K) (hX : A * X - X * B = C)
    (hβ : IsUnit (A - β • 1).det) (hα : IsUnit (B - α • 1).det) :
    X - sylvesterADIStep A B C Y α β =
      ((A - α • 1) * (A - β • 1)⁻¹) * (X - Y) *
        ((B - β • 1) * (B - α • 1)⁻¹) := by
  apply mul_right_cancel_shifted B α hα
  rw [Matrix.sub_mul, sylvesterADIStep_mul_shifted _ _ _ _ _ _ hα]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hα, Matrix.mul_one]
  rw [← Matrix.mul_assoc (A - β • 1)⁻¹,
    ← sub_sylvesterADIHalf A B C X Y β hX hβ]
  rw [← hX]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]
  module

/-- The recursive sequence of actual Sylvester ADI iterates. -/
def sylvesterADI (A : Matrix m m K) (B : Matrix n n K) (C X₀ : Matrix m n K)
    (α β : ℕ → K) : ℕ → Matrix m n K
  | 0 => X₀
  | j + 1 => sylvesterADIStep A B C (sylvesterADI A B C X₀ α β j) (α j) (β j)

/-- Accumulated left error multiplier, in the order generated by the solves. -/
def sylvesterADILeft (A : Matrix m m K) (α β : ℕ → K) : ℕ → Matrix m m K
  | 0 => 1
  | j + 1 => ((A - α j • 1) * (A - β j • 1)⁻¹) * sylvesterADILeft A α β j

/-- Accumulated right error multiplier. -/
def sylvesterADIRight (B : Matrix n n K) (α β : ℕ → K) : ℕ → Matrix n n K
  | 0 => 1
  | j + 1 => sylvesterADIRight B α β j * ((B - β j • 1) * (B - α j • 1)⁻¹)

/-- The finite-step rational error identity for the actual ADI process.
Source: user derivations, Sylvester ADI.
atlas: adi-sylvester-rational-error (partial) -/
theorem sub_sylvesterADI (A : Matrix m m K) (B : Matrix n n K)
    (C X X₀ : Matrix m n K) (α β : ℕ → K) (hX : A * X - X * B = C)
    (hβ : ∀ j, IsUnit (A - β j • 1).det) (hα : ∀ j, IsUnit (B - α j • 1).det)
    (j : ℕ) : X - sylvesterADI A B C X₀ α β j =
      sylvesterADILeft A α β j * (X - X₀) * sylvesterADIRight B α β j := by
  induction j with
  | zero => simp [sylvesterADI, sylvesterADILeft, sylvesterADIRight]
  | succ j hj =>
    rw [sylvesterADI, sub_sylvesterADIStep _ _ _ _ _ _ _ hX (hβ j) (hα j), hj]
    simp [sylvesterADILeft, sylvesterADIRight, Matrix.mul_assoc]

/-- Spectral-norm ADI error bound, with no claim of arbitrary-shift convergence.
atlas: adi-sylvester-rational-error (partial) -/
theorem specNorm_sub_sylvesterADI_le (A : Matrix m m K) (B : Matrix n n K)
    (C X X₀ : Matrix m n K) (α β : ℕ → K) (hX : A * X - X * B = C)
    (hβ : ∀ j, IsUnit (A - β j • 1).det) (hα : ∀ j, IsUnit (B - α j • 1).det)
    (j : ℕ) : specNorm (X - sylvesterADI A B C X₀ α β j) ≤
      specNorm (sylvesterADILeft A α β j) * specNorm (sylvesterADIRight B α β j) *
        specNorm (X - X₀) := by
  rw [sub_sylvesterADI _ _ _ _ _ _ _ hX hβ hα]
  calc
    _ ≤ specNorm (sylvesterADILeft A α β j * (X - X₀)) *
        specNorm (sylvesterADIRight B α β j) := specNorm_mul_le _ _
    _ ≤ (specNorm (sylvesterADILeft A α β j) * specNorm (X - X₀)) *
        specNorm (sylvesterADIRight B α β j) :=
      mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _)
    _ = _ := by ring

/-- Frobenius-norm ADI error bound under the same solved-factor hypotheses.
atlas: adi-sylvester-rational-error (partial) -/
theorem frobNorm_sub_sylvesterADI_le (A : Matrix m m K) (B : Matrix n n K)
    (C X X₀ : Matrix m n K) (α β : ℕ → K) (hX : A * X - X * B = C)
    (hβ : ∀ j, IsUnit (A - β j • 1).det) (hα : ∀ j, IsUnit (B - α j • 1).det)
    (j : ℕ) : frobNorm (X - sylvesterADI A B C X₀ α β j) ≤
      specNorm (sylvesterADILeft A α β j) * specNorm (sylvesterADIRight B α β j) *
        frobNorm (X - X₀) := by
  rw [sub_sylvesterADI _ _ _ _ _ _ _ hX hβ hα]
  calc
    _ ≤ frobNorm (sylvesterADILeft A α β j * (X - X₀)) *
        specNorm (sylvesterADIRight B α β j) := frobNorm_mul_le_frobNorm_mul_specNorm _ _
    _ ≤ (specNorm (sylvesterADILeft A α β j) * frobNorm (X - X₀)) *
        specNorm (sylvesterADIRight B α β j) :=
      mul_le_mul_of_nonneg_right (frobNorm_mul_le_specNorm_mul_frobNorm _ _) (specNorm_nonneg _)
    _ = _ := by ring

/-- The residual of an actual ADI step has the same rational transport as
the error, even when the Sylvester equation has no solution. -/
theorem sylvesterResidual_sylvesterADIStep (A : Matrix m m K) (B : Matrix n n K)
    (C Y : Matrix m n K) (α β : K)
    (hβ : IsUnit (A - β • 1).det) (hα : IsUnit (B - α • 1).det) :
    sylvesterResidual A B C (sylvesterADIStep A B C Y α β) =
      ((A - α • 1) * (A - β • 1)⁻¹) * sylvesterResidual A B C Y *
        ((B - β • 1) * (B - α • 1)⁻¹) := by
  have hstep := eq_add_of_sub_eq (sylvesterADIStep_sub A B C Y α β hβ hα)
  have hAi : A * (A - β • 1)⁻¹ = 1 + β • (A - β • 1)⁻¹ := by
    simpa using shifted_inv_mul_decomposition A 0 β hβ
  have hiB : (B - α • 1)⁻¹ * B = 1 + α • (B - α • 1)⁻¹ := by
    simpa using inv_mul_shifted_decomposition B 0 α hα
  let R := sylvesterResidual A B C Y
  have hres : sylvesterResidual A B C (sylvesterADIStep A B C Y α β) =
      R - (β - α) • (A * ((A - β • 1)⁻¹ * R * (B - α • 1)⁻¹)) +
        (β - α) • ((A - β • 1)⁻¹ * R * (B - α • 1)⁻¹ * B) := by
    rw [hstep]
    dsimp only [sylvesterResidual, R]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub]
    module
  have h₁ : A * ((A - β • 1)⁻¹ * R * (B - α • 1)⁻¹) =
      R * (B - α • 1)⁻¹ + β • ((A - β • 1)⁻¹ * R * (B - α • 1)⁻¹) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hAi]
    simp only [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
  have h₂ : (A - β • 1)⁻¹ * R * (B - α • 1)⁻¹ * B =
      (A - β • 1)⁻¹ * R + α • ((A - β • 1)⁻¹ * R * (B - α • 1)⁻¹) := by
    rw [Matrix.mul_assoc _ (B - α • 1)⁻¹ B, hiB]
    simp only [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  rw [hres, h₁, h₂, shifted_inv_mul_decomposition A α β hβ,
    shifted_inv_mul_decomposition B β α hα]
  change _ = (1 + (β - α) • (A - β • 1)⁻¹) * R *
    (1 + (α - β) • (B - α • 1)⁻¹)
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, smul_add, smul_smul]
  module

/-- All finite residuals are rational images of the initial residual. -/
theorem sylvesterResidual_sylvesterADI (A : Matrix m m K) (B : Matrix n n K)
    (C X₀ : Matrix m n K) (α β : ℕ → K)
    (hβ : ∀ j, IsUnit (A - β j • 1).det) (hα : ∀ j, IsUnit (B - α j • 1).det) (j : ℕ) :
    sylvesterResidual A B C (sylvesterADI A B C X₀ α β j) =
      sylvesterADILeft A α β j * sylvesterResidual A B C X₀ * sylvesterADIRight B α β j := by
  induction j with
  | zero => simp [sylvesterADI, sylvesterADILeft, sylvesterADIRight]
  | succ j hj =>
    rw [sylvesterADI, sylvesterResidual_sylvesterADIStep _ _ _ _ _ _ (hβ j) (hα j), hj]
    simp [sylvesterADILeft, sylvesterADIRight, Matrix.mul_assoc]

/-- ADI never increases the rank of the initial residual. -/
theorem rank_sylvesterResidual_sylvesterADI_le (A : Matrix m m K) (B : Matrix n n K)
    (C X₀ : Matrix m n K) (α β : ℕ → K)
    (hβ : ∀ j, IsUnit (A - β j • 1).det) (hα : ∀ j, IsUnit (B - α j • 1).det) (j : ℕ) :
    (sylvesterResidual A B C (sylvesterADI A B C X₀ α β j)).rank ≤
      (sylvesterResidual A B C X₀).rank := by
  rw [sylvesterResidual_sylvesterADI _ _ _ _ _ _ hβ hα]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- Starting from zero, `j` ADI steps have rank at most `j*r` when the
right-hand side has rank at most `r`. Equal shifts and singular numerator
factors are included. Source: user derivations, ADI rank bound.
atlas: adi-sylvester-rational-error (partial) -/
theorem rank_sylvesterADI_zero_le (A : Matrix m m K) (B : Matrix n n K)
    (C : Matrix m n K) (α β : ℕ → K)
    (hβ : ∀ j, IsUnit (A - β j • 1).det) (hα : ∀ j, IsUnit (B - α j • 1).det)
    (r : ℕ) (hC : C.rank ≤ r) (j : ℕ) : (sylvesterADI A B C 0 α β j).rank ≤ j * r := by
  induction j with
  | zero => simp [sylvesterADI]
  | succ j hj =>
    have hstep := sylvesterADIStep_sub A B C (sylvesterADI A B C 0 α β j)
      (α j) (β j) (hβ j) (hα j)
    have hR : (sylvesterResidual A B C (sylvesterADI A B C 0 α β j)).rank ≤ r := by
      apply (rank_sylvesterResidual_sylvesterADI_le A B C 0 α β hβ hα j).trans
      simpa [sylvesterResidual] using hC
    have hcor : (((β j - α j) • ((A - β j • 1)⁻¹ *
        sylvesterResidual A B C (sylvesterADI A B C 0 α β j) * (B - α j • 1)⁻¹))).rank ≤ r := by
      rw [← Matrix.smul_mul, ← Matrix.smul_mul]
      exact ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans hR
    rw [sylvesterADI, eq_add_of_sub_eq hstep]
    exact (rank_add_le _ _).trans (by simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add hcor hj)

end NLAlib
