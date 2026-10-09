import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Rank
import NLAlib.Matrix.Norms

/-!
# Orthonormal frames, projectors and residuals

* `NLAlib.HasOrthonormalCols Q`: `Qᵀ Q = I`.
* `NLAlib.residual Q A = A − Q (Qᵀ A) = (I − QQᵀ) A`, the part of `A` outside `range Q`.
* `NLAlib.IsBestRankApprox k C Y`: `Y` has rank `≤ k` and minimises the Frobenius distance to
  `C` among rank-`≤ k` matrices. Until Eckart–Young is proved (atlas `eckart-young`) this
  optimality property is how `⟦C⟧ₖ` enters statements.

## Contents

* The orthogonal projector `P = QQᵀ`: symmetry, idempotence, `Qᵀ(I − P) = 0`.
* The residual: `residual Q A = (I − QQᵀ) A`, orthogonality to `range Q`, Pythagoras
  `‖A‖_F² = ‖QQᵀA‖_F² + ‖(I − QQᵀ)A‖_F²`, `‖(I − QQᵀ)A‖_F ≤ ‖A‖_F`, `‖QᵀA‖_F ≤ ‖A‖_F`.
* Best approximation in a range: `‖A − QB‖_F² = ‖(I − QQᵀ)A‖_F² + ‖QᵀA − B‖_F²`, and the
  monotonicity of the residual under range inclusion (HMT 2011, Prop. 8.5, Frobenius case).
* Range-finder fact: `range(AΩ) ⊆ range(Q)` (written `Q (Qᵀ (A Ω)) = A Ω`) gives
  `(I − QQᵀ) A Ω = 0`.

Proofs ported from the LRA project (`LRA/Basic.lean`, `LRA/Deterministic/RangeFinder.lean`,
Chen–Persson formalization), namespace renamed and statements generalised from `Fin` to
arbitrary `Fintype` index types.

Atlas: `projection-facts`, `eckart-young`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {m n q : Type*} [Fintype m] [Fintype n] [Fintype q]

/-! ### Definitions -/

/-- `Q` has orthonormal columns: `Qᵀ Q = I`. -/
def HasOrthonormalCols [DecidableEq q] (Q : Matrix m q ℝ) : Prop := Qᵀ * Q = 1

/-- Residual of `A` after projecting onto the column space of `Q`: `(I − QQᵀ) A`. -/
def residual (Q : Matrix m q ℝ) (A : Matrix m n ℝ) : Matrix m n ℝ := A - Q * (Qᵀ * A)

/-- `Y` is a best rank-`k` Frobenius approximation of `C`. -/
def IsBestRankApprox (k : ℕ) (C Y : Matrix m n ℝ) : Prop :=
  Y.rank ≤ k ∧ ∀ Z : Matrix m n ℝ, Z.rank ≤ k → frobSq (C - Y) ≤ frobSq (C - Z)

/-! ### The orthogonal projector `QQᵀ` -/

omit [Fintype m] in
/-- `QQᵀ` is symmetric. Atlas `projection-facts`. -/
theorem mul_transpose_symm (Q : Matrix m q ℝ) : (Q * Qᵀ)ᵀ = Q * Qᵀ := by
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

/-- Idempotence of `P = QQᵀ` for `Q` with orthonormal columns: `P² = P`.
Atlas `projection-facts`. -/
theorem mul_transpose_mul_mul_transpose [DecidableEq q] {Q : Matrix m q ℝ}
    (hQ : HasOrthonormalCols Q) : Q * Qᵀ * (Q * Qᵀ) = Q * Qᵀ := by
  have h : Qᵀ * Q = 1 := hQ
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Qᵀ, h, Matrix.one_mul]

/-- Idempotence of the complementary projector `I − QQᵀ`. Atlas `projection-facts`. -/
theorem one_sub_mul_transpose_idem [DecidableEq m] [DecidableEq q] {Q : Matrix m q ℝ}
    (hQ : HasOrthonormalCols Q) : (1 - Q * Qᵀ) * (1 - Q * Qᵀ) = 1 - Q * Qᵀ := by
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, mul_transpose_mul_mul_transpose hQ]
  abel

/-- `Qᵀ (I − QQᵀ) = 0` for `Q` with orthonormal columns. Atlas `projection-facts`. -/
theorem transpose_mul_one_sub_mul_transpose [DecidableEq m] [DecidableEq q] {Q : Matrix m q ℝ}
    (hQ : HasOrthonormalCols Q) : Qᵀ * (1 - Q * Qᵀ) = 0 := by
  have h : Qᵀ * Q = 1 := hQ
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h, Matrix.one_mul, sub_self]

/-- `(I − QQᵀ)ᵀ Q = 0` for `Q` with orthonormal columns. Atlas `projection-facts`. -/
theorem one_sub_mul_transpose_transpose_mul [DecidableEq m] [DecidableEq q] {Q : Matrix m q ℝ}
    (hQ : HasOrthonormalCols Q) : (1 - Q * Qᵀ)ᵀ * Q = 0 := by
  have h : Qᵀ * Q = 1 := hQ
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, h,
    Matrix.mul_one, sub_self]

/-! ### The residual `(I − QQᵀ) A` -/

omit [Fintype n] in
/-- `residual Q A = (I − QQᵀ) A`. Atlas `projection-facts`. -/
theorem residual_eq_one_sub_mul [DecidableEq m] (Q : Matrix m q ℝ) (A : Matrix m n ℝ) :
    residual Q A = (1 - Q * Qᵀ) * A := by
  rw [residual, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]

omit [Fintype n] in
/-- Orthogonal decomposition `A = Q(QᵀA) + residual Q A`. Atlas `projection-facts`. -/
theorem mul_transpose_mul_add_residual (Q : Matrix m q ℝ) (A : Matrix m n ℝ) :
    Q * (Qᵀ * A) + residual Q A = A := by
  rw [residual]; abel

omit [Fintype n] in
/-- The residual is orthogonal to `range Q`: `Qᵀ (I − QQᵀ) A = 0`. Atlas `projection-facts`. -/
theorem transpose_mul_residual [DecidableEq q] {Q : Matrix m q ℝ} (hQ : HasOrthonormalCols Q)
    (A : Matrix m n ℝ) : Qᵀ * residual Q A = 0 := by
  unfold residual HasOrthonormalCols at *
  rw [Matrix.mul_sub, ← Matrix.mul_assoc, hQ, Matrix.one_mul, sub_self]

/-- The residual is Frobenius-orthogonal to every matrix `QX` with columns in `range Q`.
Atlas `projection-facts`. -/
theorem frobInner_mul_residual [DecidableEq q] {Q : Matrix m q ℝ} (hQ : HasOrthonormalCols Q)
    (X : Matrix q n ℝ) (A : Matrix m n ℝ) : frobInner (Q * X) (residual Q A) = 0 := by
  rw [frobInner_eq_trace, Matrix.transpose_mul, Matrix.mul_assoc, transpose_mul_residual hQ,
    Matrix.mul_zero, Matrix.trace_zero]

omit [Fintype n] in
/-- Projecting the residual again changes nothing: `(I − QQᵀ)² A = (I − QQᵀ) A`.
Atlas `projection-facts`. -/
theorem residual_residual [DecidableEq q] {Q : Matrix m q ℝ} (hQ : HasOrthonormalCols Q)
    (A : Matrix m n ℝ) : residual Q (residual Q A) = residual Q A := by
  show residual Q A - Q * (Qᵀ * residual Q A) = residual Q A
  rw [transpose_mul_residual hQ, Matrix.mul_zero, sub_zero]

/-- The residual of `QX` vanishes. Atlas `projection-facts`. -/
theorem residual_mul_self [DecidableEq q] {Q : Matrix m q ℝ} (hQ : HasOrthonormalCols Q)
    {p : Type*} [Fintype p] (X : Matrix q p ℝ) : residual Q (Q * X) = 0 := by
  have h : Qᵀ * Q = 1 := hQ
  rw [residual, ← Matrix.mul_assoc Qᵀ, h, Matrix.one_mul, sub_self]

/-- The residual commutes with right multiplication: `((I − QQᵀ)A) Ω = (I − QQᵀ)(AΩ)`.
Atlas `projection-facts`. -/
theorem residual_mul (Q : Matrix m q ℝ) (A : Matrix m n ℝ) {p : Type*} [Fintype p]
    (Ω : Matrix n p ℝ) : residual Q A * Ω = residual Q (A * Ω) := by
  simp only [residual, Matrix.sub_mul, Matrix.mul_assoc]

/-- If `range(AΩ) ⊆ range(Q)`, written `Q (Qᵀ (AΩ)) = AΩ`, then `(I − QQᵀ) A Ω = 0`.
This is how `Q = orth(AΩ)` enters the range-finder analysis (HMT 2011, proof of Thm 9.1).
No orthonormality is needed. Atlas `projection-facts`. -/
theorem residual_mul_eq_zero_of_range {Q : Matrix m q ℝ} {A : Matrix m n ℝ} {p : Type*}
    [Fintype p] {Ω : Matrix n p ℝ} (h : Q * (Qᵀ * (A * Ω)) = A * Ω) :
    residual Q A * Ω = 0 := by
  rw [residual_mul, residual, h, sub_self]

/-! ### Pythagoras and contraction -/

/-- Pythagoras for the projector: `‖A‖_F² = ‖Q(QᵀA)‖_F² + ‖(I − QQᵀ)A‖_F²`.
Atlas `projection-facts`. -/
theorem frobSq_eq_frobSq_proj_add_residual [DecidableEq q] {Q : Matrix m q ℝ}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n ℝ) :
    frobSq A = frobSq (Q * (Qᵀ * A)) + frobSq (residual Q A) := by
  conv_lhs => rw [← mul_transpose_mul_add_residual Q A]
  exact frobSq_add_of_frobInner_eq_zero _ _ (frobInner_mul_residual hQ _ A)

/-- Pythagoras with the projection measured in `range Q` coordinates:
`‖A‖_F² = ‖QᵀA‖_F² + ‖(I − QQᵀ)A‖_F²`. Atlas `projection-facts`. -/
theorem frobSq_eq_frobSq_transpose_mul_add_residual [DecidableEq q] {Q : Matrix m q ℝ}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n ℝ) :
    frobSq A = frobSq (Qᵀ * A) + frobSq (residual Q A) := by
  rw [frobSq_eq_frobSq_proj_add_residual hQ A, frobSq_mul_left_of_orthonormal hQ]

/-- `‖(I − QQᵀ)A‖_F² = ‖A‖_F² − ‖QᵀA‖_F²`. Atlas `projection-facts`. -/
theorem frobSq_residual_eq_sub [DecidableEq q] {Q : Matrix m q ℝ}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n ℝ) :
    frobSq (residual Q A) = frobSq A - frobSq (Qᵀ * A) := by
  rw [frobSq_eq_frobSq_transpose_mul_add_residual hQ A]; ring

/-- The residual contracts: `‖(I − QQᵀ)A‖_F² ≤ ‖A‖_F²`. Atlas `projection-facts`. -/
theorem frobSq_residual_le [DecidableEq q] {Q : Matrix m q ℝ} (hQ : HasOrthonormalCols Q)
    (A : Matrix m n ℝ) : frobSq (residual Q A) ≤ frobSq A := by
  rw [frobSq_eq_frobSq_proj_add_residual hQ A]
  exact le_add_of_nonneg_left (frobSq_nonneg _)

/-- `‖QᵀA‖_F² ≤ ‖A‖_F²` for `Q` with orthonormal columns. Atlas `projection-facts`. -/
theorem frobSq_transpose_mul_le [DecidableEq q] {Q : Matrix m q ℝ} (hQ : HasOrthonormalCols Q)
    (A : Matrix m n ℝ) : frobSq (Qᵀ * A) ≤ frobSq A := by
  rw [frobSq_eq_frobSq_transpose_mul_add_residual hQ A]
  exact le_add_of_nonneg_right (frobSq_nonneg _)

/-- The projection contracts: `‖QQᵀA‖_F² ≤ ‖A‖_F²`. Atlas `projection-facts`. -/
theorem frobSq_proj_le [DecidableEq q] {Q : Matrix m q ℝ} (hQ : HasOrthonormalCols Q)
    (A : Matrix m n ℝ) : frobSq (Q * (Qᵀ * A)) ≤ frobSq A := by
  rw [frobSq_mul_left_of_orthonormal hQ]; exact frobSq_transpose_mul_le hQ A

/-! ### Best approximation in a range and monotonicity -/

/-- Pythagoras in `range Q`: for every `B`,
`‖A − QB‖_F² = ‖(I − QQᵀ)A‖_F² + ‖QᵀA − B‖_F²` (proof of HMT 2011, Thm 9.1; LRA
`pythagoras_range`). Atlas `projection-facts`. -/
theorem frobSq_sub_mul_eq [DecidableEq q] {Q : Matrix m q ℝ} (hQ : HasOrthonormalCols Q)
    (A : Matrix m n ℝ) (B : Matrix q n ℝ) :
    frobSq (A - Q * B) = frobSq (residual Q A) + frobSq (Qᵀ * A - B) := by
  have hdecomp : A - Q * B = residual Q A + Q * (Qᵀ * A - B) := by
    rw [residual, Matrix.mul_sub]; abel
  rw [hdecomp, frobSq_add_of_frobInner_eq_zero _ _ (by
      rw [frobInner_comm]; exact frobInner_mul_residual hQ _ A),
    frobSq_mul_left_of_orthonormal hQ]

/-- `Q(QᵀA)` is the best Frobenius approximation of `A` with columns in `range Q`:
`‖(I − QQᵀ)A‖_F² ≤ ‖A − QB‖_F²` for every `B`. Atlas `projection-facts`. -/
theorem frobSq_residual_le_frobSq_sub_mul [DecidableEq q] {Q : Matrix m q ℝ}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n ℝ) (B : Matrix q n ℝ) :
    frobSq (residual Q A) ≤ frobSq (A - Q * B) := by
  rw [frobSq_sub_mul_eq hQ A B]
  exact le_add_of_nonneg_right (frobSq_nonneg _)

/-- Monotonicity of the residual under range inclusion (HMT 2011, Prop. 8.5, Frobenius case):
if `range Q₁ ⊆ range Q₂`, written `Q₁ = Q₂ C`, then `‖(I − Q₂Q₂ᵀ)A‖_F² ≤ ‖(I − Q₁Q₁ᵀ)A‖_F²`.
Deviation: only `Q₂` needs orthonormal columns; `Q₁` is arbitrary (with `residual` defined
by the formula `A − Q₁Q₁ᵀA`). Atlas `projection-facts`. -/
theorem frobSq_residual_le_of_eq_mul [DecidableEq q] {q₁ : Type*} [Fintype q₁]
    {Q₁ : Matrix m q₁ ℝ} {Q₂ : Matrix m q ℝ} (hQ₂ : HasOrthonormalCols Q₂)
    {C : Matrix q q₁ ℝ} (hC : Q₁ = Q₂ * C) (A : Matrix m n ℝ) :
    frobSq (residual Q₂ A) ≤ frobSq (residual Q₁ A) := by
  have h : residual Q₁ A = A - Q₂ * (C * (Q₁ᵀ * A)) := by
    rw [residual, hC, Matrix.mul_assoc, ← hC]
  rw [h]
  exact frobSq_residual_le_frobSq_sub_mul hQ₂ A _

/-- `Q ⟦QᵀA⟧ₖ` is a best rank-`k` Frobenius approximation of `A` among matrices `QB` with
`rank B ≤ k` (HMT 2011, proof of Thm 9.1; LRA `best_in_range`). Atlas `projection-facts`. -/
theorem frobSq_sub_mul_le_of_isBestRankApprox [DecidableEq q] {k : ℕ} {Q : Matrix m q ℝ}
    (hQ : HasOrthonormalCols Q) {A : Matrix m n ℝ} {Y : Matrix q n ℝ}
    (hY : IsBestRankApprox k (Qᵀ * A) Y) (B : Matrix q n ℝ) (hB : B.rank ≤ k) :
    frobSq (A - Q * Y) ≤ frobSq (A - Q * B) := by
  rw [frobSq_sub_mul_eq hQ A Y, frobSq_sub_mul_eq hQ A B]
  exact add_le_add le_rfl (hY.2 B hB)

end NLAlib
