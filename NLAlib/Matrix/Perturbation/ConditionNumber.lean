import NLAlib.Matrix.Basic.MoorePenroseTransformations
import NLAlib.Matrix.Spectral.EckartYoung
import NLAlib.Matrix.Norms.RankNorm
import NLAlib.Matrix.Norms.Reindex
import NLAlib.Matrix.Subspaces.OrthogonalProducts
import NLAlib.Matrix.Functions.FunctionalCalculusEigenvalues
/-!
# Spectral condition numbers

Two quantities, over `ℝ` or `ℂ` (`[RCLike 𝕜]`):

* `conditionNumber A : ℝ≥0∞`, the textbook condition number `κ₂(A) = ‖A‖₂ ‖A⁻¹‖₂` of a square
 matrix, `⊤` when `A` is singular (Golub–Van Loan 2013, §2.6.2; Higham 2002, Thm 6.5;
 Trefethen–Bau 1997, Lecture 12). API: `conditionNumber_of_isUnit`, `conditionNumber_eq_top_iff`,
 `one_le_conditionNumber`, `conditionNumber_eq_singularValues_ratio`,
 `conditionNumber_eq_eigenvalues₀_ratio`, `conditionNumber_conjTranspose`, `conditionNumber_inv`.
 Perturbation bounds take `(hA : IsUnit A)` and are stated with `(conditionNumber A).toReal`.
* `moorePenroseConditionNumber A : ℝ`, the pseudoinverse quantity `‖A‖₂ ‖A⁺‖₂ = σ₁/σ_r` for a
 matrix of any shape (`r = rank A`), which is `0` at `A = 0` and finite at every rank. It is not
 "the" condition number; the two agree for invertible square `A`
 (`conditionNumber_eq_ofReal_moorePenroseConditionNumber`).

Atlas: `condition-number-def`.
-/

noncomputable section
open scoped Matrix ENNReal
namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

/-! ### The condition number of a square matrix -/

open Classical in
/-- The spectral condition number `κ₂(A) = ‖A‖₂ ‖A⁻¹‖₂` of a square matrix, `⊤` when `A` is
singular. Golub–Van Loan 2013, §2.6.2; Trefethen–Bau 1997, eq. (12.13).
atlas: condition-number-def -/
def conditionNumber (A : Matrix n n 𝕜) : ℝ≥0∞ :=
  if IsUnit A then ENNReal.ofReal (specNorm A * specNorm A⁻¹) else ⊤

/-- On an invertible matrix the condition number is `‖A‖₂ ‖A⁻¹‖₂`. Golub–Van Loan 2013, §2.6.2.
atlas: condition-number-def -/
theorem conditionNumber_of_isUnit {A : Matrix n n 𝕜} (hA : IsUnit A) :
    conditionNumber A = ENNReal.ofReal (specNorm A * specNorm A⁻¹) := by
  rw [conditionNumber, if_pos hA]

/-- A singular matrix has condition number `⊤`. Golub–Van Loan 2013, §2.6.2. -/
theorem conditionNumber_of_not_isUnit {A : Matrix n n 𝕜} (hA : ¬ IsUnit A) :
    conditionNumber A = ⊤ := by
  rw [conditionNumber, if_neg hA]

/-- The condition number is `⊤` exactly on singular matrices. Golub–Van Loan 2013, §2.6.2.
atlas: condition-number-def -/
theorem conditionNumber_eq_top_iff (A : Matrix n n 𝕜) : conditionNumber A = ⊤ ↔ ¬ IsUnit A := by
  by_cases hA : IsUnit A
  · simp [conditionNumber_of_isUnit hA, hA]
  · simp [conditionNumber_of_not_isUnit hA, hA]

/-- The condition number is finite exactly on invertible matrices. -/
theorem conditionNumber_ne_top_iff (A : Matrix n n 𝕜) : conditionNumber A ≠ ⊤ ↔ IsUnit A := by
  rw [Ne, conditionNumber_eq_top_iff, not_not]

/-- The real value of the condition number of an invertible matrix is `‖A‖₂ ‖A⁻¹‖₂`; this is the
form the perturbation bounds are stated in. Golub–Van Loan 2013, §2.6.2. -/
theorem conditionNumber_toReal_of_isUnit {A : Matrix n n 𝕜} (hA : IsUnit A) :
    (conditionNumber A).toReal = specNorm A * specNorm A⁻¹ := by
  rw [conditionNumber_of_isUnit hA,
    ENNReal.toReal_ofReal (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _))]

open scoped Matrix.Norms.L2Operator in
/-- A nonzero idempotent has `‖P‖₂ ≥ 1` (`‖P‖₂ = ‖P²‖₂ ≤ ‖P‖₂²`). Golub–Van Loan 2013, §2.5.1. -/
theorem one_le_specNorm_of_isIdempotentElem {P : Matrix n n 𝕜} (hP : IsIdempotentElem P)
    (h0 : P ≠ 0) : 1 ≤ specNorm P := by
  have hpos : 0 < specNorm P := by rw [specNorm_eq_norm]; exact norm_pos_iff.mpr h0
  have h := specNorm_mul_le P P
  rw [show P * P = P from hP] at h
  nlinarith

/-- On a nonempty index type the identity has spectral norm `1`. -/
theorem specNorm_one [Nonempty n] : specNorm (1 : Matrix n n 𝕜) = 1 :=
  le_antisymm specNorm_one_le (one_le_specNorm_of_isIdempotentElem (IsIdempotentElem.one)
    one_ne_zero)

/-- `κ₂(A) ≥ 1` on a nonempty index type (`1 = ‖A A⁻¹‖₂ ≤ ‖A‖₂ ‖A⁻¹‖₂`, and `⊤ ≥ 1` on singular
matrices). Golub–Van Loan 2013, §2.6.2.
atlas: condition-number-def -/
theorem one_le_conditionNumber [Nonempty n] (A : Matrix n n 𝕜) : 1 ≤ conditionNumber A := by
  by_cases hA : IsUnit A
  · rw [conditionNumber_of_isUnit hA, ENNReal.one_le_ofReal]
    calc (1 : ℝ) = specNorm (1 : Matrix n n 𝕜) := specNorm_one.symm
      _ = specNorm (A * A⁻¹) := by
        rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA)]
      _ ≤ specNorm A * specNorm A⁻¹ := specNorm_mul_le _ _
  · rw [conditionNumber_of_not_isUnit hA]; exact le_top

/-- `κ₂(A) = σ₁/σ_n` for an invertible `A` (zero-indexed: `σ 0 / σ (card n - 1)`).
Golub–Van Loan 2013, §2.6.2 and §5.5.2; Trefethen–Bau 1997, eq. (12.14).
atlas: condition-number-def -/
theorem conditionNumber_eq_singularValues_ratio {A : Matrix n n 𝕜} (hA : IsUnit A) :
    conditionNumber A =
      ENNReal.ofReal (singularValues A 0 / singularValues A (Fintype.card n - 1)) := by
  have hrank := Matrix.rank_of_isUnit A hA
  rcases isEmpty_or_nonempty n with hn | hn
  · have h0 : A = 0 := Subsingleton.elim _ _
    subst h0
    rw [conditionNumber_of_isUnit hA, singularValues_eq_zero_of_width_le (0 : Matrix n n 𝕜)
      (by simp), zero_div, specNorm_zero, zero_mul]
  · have hpos : 0 < A.rank := by rw [hrank]; exact Fintype.card_pos
    rw [conditionNumber_of_isUnit hA, ← moorePenroseInverse_eq_inv_of_isUnit A hA,
      specNorm_moorePenroseInverse_eq_inv_singularValues_last_positive A hpos, hrank,
      ← singularValues_zero_eq_specNorm, mul_one_div]

/-- For a positive-definite `A` on a nonempty index type, `κ₂(A) = λ_max/λ_min`, the ratio of the
first and last sorted eigenvalues. Golub–Van Loan 2013, §2.6.2.
atlas: condition-number-def -/
theorem conditionNumber_eq_eigenvalues₀_ratio [Nonempty n] {A : Matrix n n ℝ} (hA : A.PosDef) :
    conditionNumber A = ENNReal.ofReal (hA.isHermitian.eigenvalues₀ ⟨0, Fintype.card_pos⟩ /
      hA.isHermitian.eigenvalues₀
        ⟨Fintype.card n - 1, Nat.sub_lt Fintype.card_pos (by decide : 0 < 1)⟩) := by
  rw [conditionNumber_eq_singularValues_ratio hA.isUnit,
    singularValues_eq_eigenvalues₀_of_posSemidef hA.posSemidef ⟨0, Fintype.card_pos⟩,
    singularValues_eq_eigenvalues₀_of_posSemidef hA.posSemidef
      ⟨Fintype.card n - 1, Nat.sub_lt Fintype.card_pos (by decide : 0 < 1)⟩]

/-- `IsUnit Aᴴ ↔ IsUnit A`. -/
theorem _root_.Matrix.isUnit_conjTranspose_iff (A : Matrix n n 𝕜) : IsUnit Aᴴ ↔ IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_conjTranspose, isUnit_star,
    ← Matrix.isUnit_iff_isUnit_det]

/-- Conjugate transposition preserves the condition number. Golub–Van Loan 2013, §2.6.2.
atlas: condition-number-def -/
theorem conditionNumber_conjTranspose (A : Matrix n n 𝕜) :
    conditionNumber Aᴴ = conditionNumber A := by
  by_cases hA : IsUnit A
  · rw [conditionNumber_of_isUnit hA, conditionNumber_of_isUnit
      ((Matrix.isUnit_conjTranspose_iff A).2 hA), ← Matrix.conjTranspose_nonsing_inv,
      specNorm_conjTranspose, specNorm_conjTranspose]
  · rw [conditionNumber_of_not_isUnit hA,
      conditionNumber_of_not_isUnit ((Matrix.isUnit_conjTranspose_iff A).not.2 hA)]

/-- Inversion preserves the condition number: `κ₂(A⁻¹) = κ₂(A)` (both `⊤` when `A` is singular,
where `A⁻¹ = 0`). Golub–Van Loan 2013, §2.6.2.
atlas: condition-number-def -/
theorem conditionNumber_inv (A : Matrix n n 𝕜) : conditionNumber A⁻¹ = conditionNumber A := by
  by_cases hA : IsUnit A
  · rw [conditionNumber_of_isUnit hA, conditionNumber_of_isUnit (Matrix.isUnit_nonsing_inv_iff.2 hA),
      Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA), mul_comm]
  · rw [conditionNumber_of_not_isUnit hA,
      conditionNumber_of_not_isUnit (Matrix.isUnit_nonsing_inv_iff.not.2 hA)]

/-! ### The pseudoinverse condition number -/

/-- The pseudoinverse condition number `‖A‖₂ ‖A⁺‖₂` of a matrix of any shape, with the
Moore–Penrose inverse: it equals `σ₁/σ_r` with `r = rank A`
(`moorePenroseConditionNumber_eq_singularValues_ratio`) and is `0` at `A = 0` (every shape). For
an invertible square matrix it is the real value of `conditionNumber A`
(`conditionNumber_toReal_eq_moorePenroseConditionNumber`). Golub–Van Loan 2013, §2.6.2 and
§5.5.2 (the condition number of a full-rank rectangular matrix).
atlas: condition-number-def -/
def moorePenroseConditionNumber (A : Matrix m n 𝕜) : ℝ :=
  specNorm A * specNorm (moorePenroseInverse A)

/-- The condition number of an invertible matrix is the pseudoinverse quantity
`moorePenroseConditionNumber A` (cast to `ℝ≥0∞`). Golub–Van Loan 2013, §2.6.2. -/
theorem conditionNumber_eq_ofReal_moorePenroseConditionNumber {A : Matrix n n 𝕜}
    (hA : IsUnit A) :
    conditionNumber A = ENNReal.ofReal (moorePenroseConditionNumber A) := by
  rw [conditionNumber_of_isUnit hA, moorePenroseConditionNumber,
    moorePenroseInverse_eq_inv_of_isUnit A hA]

/-- The real value of the condition number of an invertible matrix is
`moorePenroseConditionNumber A`. -/
theorem conditionNumber_toReal_eq_moorePenroseConditionNumber {A : Matrix n n 𝕜}
    (hA : IsUnit A) : (conditionNumber A).toReal = moorePenroseConditionNumber A := by
  rw [conditionNumber_toReal_of_isUnit hA, moorePenroseConditionNumber,
    moorePenroseInverse_eq_inv_of_isUnit A hA]

/-- The zero matrix has pseudoinverse condition number zero, including empty shapes.
Golub–Van Loan 2013, §2.6.2; supports `condition-number-def`. -/
@[simp] theorem moorePenroseConditionNumber_zero :
    moorePenroseConditionNumber (0 : Matrix m n 𝕜) = 0 := by
  simp [moorePenroseConditionNumber, specNorm_zero]

/-- Pseudoinverse condition numbers are nonnegative.
Golub–Van Loan 2013, §2.6.2; supports `condition-number-def`. -/
theorem moorePenroseConditionNumber_nonneg (A : Matrix m n 𝕜) :
    0 ≤ moorePenroseConditionNumber A :=
  mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)

open scoped Matrix.Norms.L2Operator in
/-- The pseudoinverse condition number is at least one on every nonzero matrix.
Golub–Van Loan 2013, §2.6.2.
atlas: condition-number-def -/
theorem one_le_moorePenroseConditionNumber {A : Matrix m n 𝕜} (hA : A ≠ 0) :
    1 ≤ moorePenroseConditionNumber A := by
  have hPos : 0 < specNorm A := by rw [specNorm_eq_norm]; exact norm_pos_iff.mpr hA
  have hBound : specNorm A ≤ moorePenroseConditionNumber A * specNorm A := by
    calc
      specNorm A = specNorm (A * moorePenroseInverse A * A) :=
        congrArg specNorm (mul_moorePenroseInverse_mul A).symm
      _ ≤ specNorm (A * moorePenroseInverse A) * specNorm A := specNorm_mul_le _ _
      _ ≤ specNorm A * specNorm (moorePenroseInverse A) * specNorm A :=
        mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _)
      _ = moorePenroseConditionNumber A * specNorm A := rfl
  nlinarith

/-- Conjugate transposition preserves the pseudoinverse condition number at every rank.
Golub–Van Loan 2013, §2.6.2.
atlas: condition-number-def (partial) -/
theorem moorePenroseConditionNumber_conjTranspose (A : Matrix m n 𝕜) :
    moorePenroseConditionNumber Aᴴ = moorePenroseConditionNumber A := by
  rw [moorePenroseConditionNumber, moorePenroseInverse_conjTranspose, specNorm_conjTranspose,
    specNorm_conjTranspose, moorePenroseConditionNumber]

/-- Transposition preserves the pseudoinverse condition number at every rank.
Golub–Van Loan 2013, §2.6.2.
atlas: condition-number-def -/
theorem moorePenroseConditionNumber_transpose (A : Matrix m n 𝕜) :
    moorePenroseConditionNumber Aᵀ = moorePenroseConditionNumber A := by
  rw [moorePenroseConditionNumber, moorePenroseInverse_transpose, specNorm_transpose,
    specNorm_transpose, moorePenroseConditionNumber]

open scoped Matrix.Norms.L2Operator in
/-- Nonzero scalar multiplication preserves the pseudoinverse condition number.
Golub–Van Loan 2013, §2.6.2.
atlas: condition-number-def -/
theorem moorePenroseConditionNumber_smul {c : 𝕜} (hc : c ≠ 0) (A : Matrix m n 𝕜) :
    moorePenroseConditionNumber (c • A) = moorePenroseConditionNumber A := by
  simp only [moorePenroseConditionNumber, moorePenroseInverse_smul, specNorm, norm_smul, norm_inv]
  have hAbs : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  field_simp

/-- Taking a column Gram matrix `AᴴA` squares the pseudoinverse condition number, including at
deficient rank. Golub–Van Loan 2013, §2.6.2.
atlas: condition-number-def (partial) -/
theorem moorePenroseConditionNumber_conjTranspose_mul_self (A : Matrix m n 𝕜) :
    moorePenroseConditionNumber (Aᴴ * A) = moorePenroseConditionNumber A ^ 2 := by
  rw [moorePenroseConditionNumber, moorePenroseInverse_conjTranspose_mul_self,
    ← specNorm_sq_eq_specNorm_conjTranspose_mul_self, specNorm_mul_conjTranspose_self,
    moorePenroseConditionNumber]
  ring

/-- Left multiplication by a rectangular orthonormal frame (`QᴴQ = 1`) preserves the
pseudoinverse condition number. Golub–Van Loan 2013, §2.6.2 and §5.3.2 (`κ(R) = κ(A)` for
`A = QR`).
atlas: condition-number-def -/
theorem moorePenroseConditionNumber_mul_left_of_hasOrthonormalCols (Q : Matrix p m 𝕜)
    (A : Matrix m n 𝕜) (hQ : HasOrthonormalCols Q) :
    moorePenroseConditionNumber (Q * A) = moorePenroseConditionNumber A := by
  rw [moorePenroseConditionNumber, moorePenroseInverse_mul_left_of_hasOrthonormalCols Q A hQ,
    specNorm_mul_left_of_hasOrthonormalCols hQ.conjTranspose_mul_self,
    specNorm_mul_conjTranspose_right_of_hasOrthonormalCols hQ.conjTranspose_mul_self,
    moorePenroseConditionNumber]

/-- At positive rank the pseudoinverse condition number is the ratio of the largest and
last positive singular values, `σ₁/σ_r` (zero-indexed: `σ 0 / σ (r-1)`), on arbitrary
finite index types. Golub–Van Loan 2013, §2.6.2 and §5.5.2.
atlas: condition-number-def -/
theorem moorePenroseConditionNumber_eq_singularValues_ratio (A : Matrix m n 𝕜)
    (hr : 0 < A.rank) :
    moorePenroseConditionNumber A = singularValues A 0 / singularValues A (A.rank - 1) := by
  rw [moorePenroseConditionNumber, specNorm_moorePenroseInverse_eq_inv_singularValues_last_positive
    A hr, ← singularValues_zero_eq_specNorm, mul_one_div]

/-- On an invertible square matrix the pseudoinverse condition number uses the ordinary inverse:
`‖A‖₂ ‖A⁻¹‖₂`. Golub–Van Loan 2013, eq. (2.6.4); Trefethen–Bau 1997, eq. (12.13).
atlas: condition-number-def (partial) -/
theorem moorePenroseConditionNumber_eq_mul_specNorm_inv {A : Matrix n n 𝕜} (hA : IsUnit A) :
    moorePenroseConditionNumber A = specNorm A * specNorm A⁻¹ := by
  rw [moorePenroseConditionNumber, moorePenroseInverse_eq_inv_of_isUnit A hA]

/-- For a positive-definite real matrix on a nonempty index type, the pseudoinverse condition
number is the ratio of its largest and smallest eigenvalues. Golub–Van Loan 2013, §2.6.2.
atlas: condition-number-def -/
theorem moorePenroseConditionNumber_eq_eigenvalues₀_ratio [Nonempty n]
    {A : Matrix n n ℝ} (hA : A.PosDef) :
    moorePenroseConditionNumber A = hA.isHermitian.eigenvalues₀ ⟨0, Fintype.card_pos⟩ /
      hA.isHermitian.eigenvalues₀
        ⟨Fintype.card n - 1, Nat.sub_lt Fintype.card_pos (by decide : 0 < 1)⟩ := by
  have hRank := Matrix.rank_of_isUnit A hA.isUnit
  have hPos : 0 < A.rank := by rw [hRank]; exact Fintype.card_pos
  rw [moorePenroseConditionNumber_eq_singularValues_ratio A hPos, hRank]
  exact congrArg₂ (fun a b : ℝ => a / b)
    (singularValues_eq_eigenvalues₀_of_posSemidef hA.posSemidef
      ⟨0, Fintype.card_pos⟩)
    (singularValues_eq_eigenvalues₀_of_posSemidef hA.posSemidef
      ⟨Fintype.card n - 1, Nat.sub_lt Fintype.card_pos (by decide : 0 < 1)⟩)

end NLAlib
