import NLAlib.Matrix.Basic.MoorePenroseTransformations
import NLAlib.Matrix.Spectral.FiniteIndexTransport
import NLAlib.Matrix.Functions.FunctionalCalculusEigenvalues
/-!
# Spectral condition numbers

The total condition number is `specNorm A * specNorm A†`, including at
deficient and zero rank, for matrices over `ℝ` or `ℂ` (`[RCLike 𝕜]`). Source: Golub--Van Loan,
Section 2.6.2; Higham, Theorem 6.5. Atlas target: `condition-number-def`.

The singular-value and eigenvalue characterisations at the end stay real: they rest on the real
singular-value stack (`Norms/RankNorm`, `Spectral/FiniteIndexTransport`, `Spectral/SpectralBounds`).
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

/-- The spectral condition number with the total Moore--Penrose inverse.
Golub--Van Loan, Section 2.6.2.
atlas: condition-number-def (partial) -/
def conditionNumber (A : Matrix m n 𝕜) : ℝ :=
  specNorm A * specNorm (moorePenroseInverse A)

/-- The zero matrix has condition number zero, including empty shapes.
Golub--Van Loan, Section 2.6.2; supports `condition-number-def`. -/
@[simp] theorem conditionNumber_zero : conditionNumber (0 : Matrix m n 𝕜) = 0 := by
  simp [conditionNumber, specNorm]

/-- Spectral condition numbers are nonnegative.
Golub--Van Loan, Section 2.6.2; supports `condition-number-def`. -/
theorem conditionNumber_nonneg (A : Matrix m n 𝕜) : 0 ≤ conditionNumber A :=
  mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)

/-- The condition number is at least one exactly on the nonzero branch.
Golub--Van Loan, Section 2.6.2.
atlas: condition-number-def (partial) -/
theorem one_le_conditionNumber {A : Matrix m n 𝕜} (hA : A ≠ 0) :
    1 ≤ conditionNumber A := by
  have hPos : 0 < specNorm A := norm_pos_iff.mpr hA
  have hBound : specNorm A ≤ conditionNumber A * specNorm A := by
    calc
      specNorm A = specNorm (A * moorePenroseInverse A * A) :=
        congrArg specNorm (mul_moorePenroseInverse_mul A).symm
      _ ≤ specNorm (A * moorePenroseInverse A) * specNorm A := specNorm_mul_le _ _
      _ ≤ specNorm A * specNorm (moorePenroseInverse A) * specNorm A :=
        mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _)
      _ = conditionNumber A * specNorm A := rfl
  nlinarith

/-- Conjugate transposition preserves the condition number at every rank.
Golub--Van Loan, Section 2.6.2.
atlas: condition-number-def (partial) -/
theorem conditionNumber_conjTranspose (A : Matrix m n 𝕜) :
    conditionNumber Aᴴ = conditionNumber A := by
  rw [conditionNumber, moorePenroseInverse_conjTranspose, specNorm_conjTranspose,
    specNorm_conjTranspose, conditionNumber]

/-- Transposition preserves the condition number at every rank.
Golub--Van Loan, Section 2.6.2.
atlas: condition-number-def (partial) -/
theorem conditionNumber_transpose (A : Matrix m n 𝕜) : conditionNumber Aᵀ = conditionNumber A := by
  rw [conditionNumber, moorePenroseInverse_transpose, specNorm_transpose,
    specNorm_transpose, conditionNumber]

/-- Nonzero scalar multiplication preserves the condition number.
Golub--Van Loan, Section 2.6.2.
atlas: condition-number-def (partial) -/
theorem conditionNumber_smul {c : 𝕜} (hc : c ≠ 0) (A : Matrix m n 𝕜) :
    conditionNumber (c • A) = conditionNumber A := by
  simp only [conditionNumber, moorePenroseInverse_smul, specNorm, norm_smul, norm_inv]
  have hAbs : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  field_simp

/-- Taking a column Gram matrix `AᴴA` squares the condition number, including at
deficient rank. Golub--Van Loan, Section 2.6.2.
atlas: condition-number-def (partial) -/
theorem conditionNumber_conjTranspose_mul_self (A : Matrix m n 𝕜) :
    conditionNumber (Aᴴ * A) = conditionNumber A ^ 2 := by
  have hGram (B : Matrix m n 𝕜) : specNorm (Bᴴ * B) = specNorm B ^ 2 := by
    rw [specNorm_eq_norm, Matrix.l2_opNorm_conjTranspose_mul_self, sq, specNorm_eq_norm]
  rw [conditionNumber, moorePenroseInverse_conjTranspose_mul_self, hGram,
    specNorm_mul_conjTranspose_self, conditionNumber]
  ring

/-- Taking a column Gram matrix squares the condition number, including at
deficient rank (real form of `conditionNumber_conjTranspose_mul_self`).
Golub--Van Loan, Section 2.6.2.
atlas: condition-number-def (partial) -/
theorem conditionNumber_transpose_mul_self (A : Matrix m n ℝ) :
    conditionNumber (Aᵀ * A) = conditionNumber A ^ 2 :=
  conditionNumber_conjTranspose_mul_self A

/-- Left multiplication by a rectangular orthonormal frame (`QᴴQ = 1`) preserves condition
numbers. Golub--Van Loan, Section 2.6.2 and §5.3.2 (`κ(R) = κ(A)` for `A = QR`).
atlas: condition-number-def (partial) -/
theorem conditionNumber_mul_left_of_hasOrthonormalCols (Q : Matrix p m 𝕜)
    (A : Matrix m n 𝕜) (hQ : HasOrthonormalCols Q) : conditionNumber (Q * A) = conditionNumber A := by
  rw [conditionNumber, moorePenroseInverse_mul_left_eq_mul_conjTranspose Q A hQ,
    specNorm_mul_left_of_conjTranspose_mul_self hQ.conjTranspose_mul_self,
    specNorm_mul_conjTranspose_right_of_conjTranspose_mul_self hQ.conjTranspose_mul_self,
    conditionNumber]

/-- At positive rank the condition number is the ratio of the largest and
last positive singular values, `κ(A) = σ₁/σ_r` (zero-indexed: `σ 0 / σ (r-1)`), on arbitrary
finite index types and over `ℝ` or `ℂ`. Golub--Van Loan 2013, Sections 2.6.2 and 5.5.2.
atlas: condition-number-def (partial) -/
theorem conditionNumber_eq_singularValues_ratio (A : Matrix m n 𝕜) (hr : 0 < A.rank) :
    conditionNumber A = singularValues A 0 / singularValues A (A.rank - 1) := by
  rw [conditionNumber, specNorm_moorePenroseInverse_eq_fintype, if_neg (Nat.ne_of_gt hr),
    singularValues_reindex, ← singularValues_zero_eq_specNorm]
  ring

/-- On the nonsingular branch the condition number uses the ordinary inverse:
`κ(A) = ‖A‖₂ ‖A⁻¹‖₂`. Golub--Van Loan 2013, Section 2.6.2, eq. (2.6.4); Trefethen–Bau 1997,
eq. (12.13); supports `linear-system-perturbation`.
atlas: condition-number-def (partial) -/
theorem conditionNumber_eq_mul_specNorm_inv {A : Matrix n n 𝕜} (hA : IsUnit A) :
    conditionNumber A = specNorm A * specNorm A⁻¹ := by
  rw [conditionNumber, moorePenroseInverse_eq_inv_of_isUnit A hA]

/-- For a positive-definite real matrix of positive dimension, the condition
number is the ratio of its largest and smallest positive eigenvalues.
Golub--Van Loan, Section 2.6.2.
atlas: condition-number-def (partial) -/
theorem conditionNumber_eq_eigenvalues₀_ratio [Nonempty n]
    (A : Matrix n n ℝ) (hA : A.PosDef) :
    conditionNumber A = hA.isHermitian.eigenvalues₀ ⟨0, Fintype.card_pos⟩ /
      hA.isHermitian.eigenvalues₀
        ⟨Fintype.card n - 1, Nat.sub_lt Fintype.card_pos (by decide : 0 < 1)⟩ := by
  have hRank := Matrix.rank_of_isUnit A hA.isUnit
  have hPos : 0 < A.rank := by rw [hRank]; exact Fintype.card_pos
  rw [conditionNumber_eq_singularValues_ratio A hPos, hRank]
  exact congrArg₂ (fun a b : ℝ => a / b)
    (singularValues_eq_eigenvalues₀_of_posSemidef hA.posSemidef
      ⟨0, Fintype.card_pos⟩)
    (singularValues_eq_eigenvalues₀_of_posSemidef hA.posSemidef
      ⟨Fintype.card n - 1, Nat.sub_lt Fintype.card_pos (by decide : 0 < 1)⟩)

end NLAlib
