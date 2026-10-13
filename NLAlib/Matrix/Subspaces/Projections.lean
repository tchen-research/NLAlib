import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Hermitian
import NLAlib.Matrix.Norms.Core
/-!
# Orthonormal frames, projectors and residuals

Stated over `{𝕜 : Type*} [RCLike 𝕜]` with `conjTranspose` (RCLike round, decision D4); at
`𝕜 := ℝ` every definition is definitionally the old real one.

* `NLAlib.HasOrthonormalCols Q`: `Qᴴ Q = I` (at `ℝ`: `Qᵀ Q = I`).
* `NLAlib.residual Q A = A − Q (Qᴴ A) = (I − QQᴴ) A`, the part of `A` outside `range Q`.
* `NLAlib.IsBestRankApprox k C Y`: `Y` has rank `≤ k` and minimises the Frobenius distance to
  `C` among rank-`≤ k` matrices. Until Eckart–Young is proved (atlas `eckart-young`) this
  optimality property is how `⟦C⟧ₖ` enters statements.

## Contents

* Isometry: `‖Qx‖² = ‖x‖²` for `Q` with orthonormal columns.
* The orthogonal projector `P = QQᴴ`: idempotence, `Qᴴ(I − P) = 0`.
* The residual: `residual Q A = (I − QQᴴ) A`, orthogonality to `range Q`, Pythagoras
  `‖A‖_F² = ‖QQᴴA‖_F² + ‖(I − QQᴴ)A‖_F²`, `‖(I − QQᴴ)A‖_F ≤ ‖A‖_F`, `‖QᴴA‖_F ≤ ‖A‖_F`.
* Best approximation in a range: `‖A − QB‖_F² = ‖(I − QQᴴ)A‖_F² + ‖QᴴA − B‖_F²`, and the
  monotonicity of the residual under range inclusion (HMT 2011, Prop. 8.5, Frobenius case).
* Range-finder fact: `range(AΩ) ⊆ range(Q)` (written `Q (Qᴴ (A Ω)) = A Ω`) gives
  `(I − QQᴴ) A Ω = 0`.
* Orthogonal completions: a matrix with orthonormal columns has at most as many columns as
  rows (`card_le_card_of_hasOrthonormalCols`) and extends to a unitary matrix
  (`exists_unitary_completion`) or, with the complementary block, to `QQᴴ + Q⊥Q⊥ᴴ = I`
  (`exists_unitary_complement`); for such a completion `QᴴQ⊥ = 0` and
  `(I − QQᴴ)A = Q⊥Q⊥ᴴ(I − QQᴴ)A`.
* Vectors and compressions: `QQᴴx = x` on `range Q`, `‖Qᴴx‖² ≤ ‖x‖²` (equality on `range Q`),
  `Q'Q'ᴴQ = Q` under range inclusion, `QQᴴ = Q'Q'ᴴ` for equal ranges, and symmetry of the
  compression `QᵀAQ` of a symmetric `A` (`isSymm_transpose_mul_mul`,
  `isHermitian_transpose_mul_mul`; the general Hermitian form is Mathlib's
  `Matrix.IsHermitian.conjTranspose_mul_mul`).

## Real statements

Every lemma whose statement contains `ᵀ` or a real dot product keeps its name and real
statement as a one-line corollary of the general `conjTranspose` lemma (RCLike round, decision
D1). Bridges at `ℝ`: `hasOrthonormalCols_iff_transpose_mul_self`,
`HasOrthonormalCols.transpose_mul_self` (use `rw [hQ.transpose_mul_self]` where `rw [hQ]` was
used on a `Qᵀ` goal) and `residual_eq_sub_mul_transpose_mul` (for `rw [residual]` on a real
goal).

The canonical orthonormal basis matrix `orthonormalBasisMatrix S` of a subspace is in
`Matrix/Subspaces/OrthonormalBasisMatrix.lean`.

Proofs ported from the LRA project (`LRA/Basic.lean`, `LRA/Deterministic/RangeFinder.lean`,
Chen–Persson formalization), namespace renamed and statements generalised from `Fin` to
arbitrary `Fintype` index types.

Atlas: `projection-facts`, `eckart-young`, `orthonormal-completion`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n q : Type*} [Fintype m] [Fintype n] [Fintype q]

/-! ### Definitions -/

/-- `Q` has orthonormal columns: `Qᴴ Q = I` (at `𝕜 = ℝ` this is `Qᵀ Q = I` by definition).
atlas: orthonormal-columns-def -/
def HasOrthonormalCols [DecidableEq q] (Q : Matrix m q 𝕜) : Prop := Qᴴ * Q = 1

/-- Residual of `A` after projecting onto the column space of `Q`: `(I − QQᴴ) A`.
atlas: residual-def -/
def residual (Q : Matrix m q 𝕜) (A : Matrix m n 𝕜) : Matrix m n 𝕜 := A - Q * (Qᴴ * A)

/-- `Y` is a best rank-`k` Frobenius approximation of `C`.
atlas: best-rank-approx-def -/
def IsBestRankApprox (k : ℕ) (C Y : Matrix m n 𝕜) : Prop :=
  Y.rank ≤ k ∧ ∀ Z : Matrix m n 𝕜, Z.rank ≤ k → frobSq (C - Y) ≤ frobSq (C - Z)

/-! ### Bridges -/

omit [Fintype q] in
/-- Eliminator for `HasOrthonormalCols`: `Qᴴ Q = I`. -/
theorem HasOrthonormalCols.conjTranspose_mul_self [DecidableEq q] {Q : Matrix m q 𝕜}
    (hQ : HasOrthonormalCols Q) : Qᴴ * Q = 1 := hQ

omit [Fintype q] in
/-- `HasOrthonormalCols Q` unfolded: `Qᴴ Q = I`. -/
theorem hasOrthonormalCols_iff_conjTranspose_mul_self [DecidableEq q] {Q : Matrix m q 𝕜} :
    HasOrthonormalCols Q ↔ Qᴴ * Q = 1 := Iff.rfl

omit [Fintype q] in
/-- Real eliminator for `HasOrthonormalCols`: `Qᵀ Q = I`. Use `rw [hQ.transpose_mul_self]` on
goals that contain `Qᵀ * Q`. -/
theorem HasOrthonormalCols.transpose_mul_self [DecidableEq q] {Q : Matrix m q ℝ}
    (hQ : HasOrthonormalCols Q) : Qᵀ * Q = 1 := hQ

omit [Fintype q] in
/-- Over `ℝ`, `HasOrthonormalCols Q` unfolds to `Qᵀ Q = I`. -/
theorem hasOrthonormalCols_iff_transpose_mul_self [DecidableEq q] {Q : Matrix m q ℝ} :
    HasOrthonormalCols Q ↔ Qᵀ * Q = 1 := Iff.rfl

omit [Fintype n] in
/-- The defining formula of the residual over `ℝ`: `residual Q A = A − Q (Qᵀ A)`. -/
theorem residual_eq_sub_mul_transpose_mul (Q : Matrix m q ℝ) (A : Matrix m n ℝ) :
    residual Q A = A - Q * (Qᵀ * A) := rfl

/-! ### Isometry -/

/-- If `U` has orthonormal columns (`Uᴴ U = 1`) then `‖Ux‖² = ‖x‖²`, written with dot products.
Helper for `ose-def`; atlas `projection-facts`. -/
theorem star_mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols [DecidableEq q]
    {U : Matrix m q 𝕜} (hU : HasOrthonormalCols U) (x : q → 𝕜) :
    star (U *ᵥ x) ⬝ᵥ (U *ᵥ x) = star x ⬝ᵥ x := by
  rw [star_mulVec_dotProduct_mulVec_self, hU.conjTranspose_mul_self, Matrix.one_mulVec]

/-- If a real `U` has orthonormal columns (`Uᵀ U = 1`) then `‖Ux‖² = ‖x‖²`. Helper for
`ose-def`; atlas `projection-facts`. -/
theorem mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols [DecidableEq q] {U : Matrix m q ℝ}
    (hU : HasOrthonormalCols U) (x : q → ℝ) : (U *ᵥ x) ⬝ᵥ (U *ᵥ x) = x ⬝ᵥ x := by
  rw [mulVec_dotProduct_mulVec_self, show Uᵀ * U = 1 from hU, Matrix.one_mulVec]

/-! ### The orthogonal projector `QQᴴ` -/

omit [Fintype m] in
/-- `QQᵀ` is symmetric (real form; the general statement is Mathlib's
`Matrix.isHermitian_mul_conjTranspose_self`). Atlas `projection-facts`. -/
theorem mul_transpose_symm (Q : Matrix m q ℝ) : (Q * Qᵀ)ᵀ = Q * Qᵀ := by
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

/-- Idempotence of `P = QQᴴ` for `Q` with orthonormal columns: `P² = P`.
Atlas `projection-facts`. -/
theorem mul_conjTranspose_mul_mul_conjTranspose [DecidableEq q] {Q : Matrix m q 𝕜}
    (hQ : HasOrthonormalCols Q) : Q * Qᴴ * (Q * Qᴴ) = Q * Qᴴ := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ, hQ.conjTranspose_mul_self, Matrix.one_mul]

/-- Idempotence of `P = QQᵀ` for a real `Q` with orthonormal columns: `P² = P`.
Atlas `projection-facts`. -/
theorem mul_transpose_mul_mul_transpose [DecidableEq q] {Q : Matrix m q ℝ}
    (hQ : HasOrthonormalCols Q) : Q * Qᵀ * (Q * Qᵀ) = Q * Qᵀ :=
  mul_conjTranspose_mul_mul_conjTranspose hQ

/-- Idempotence of the complementary projector `I − QQᴴ`. Atlas `projection-facts`. -/
theorem one_sub_mul_conjTranspose_idem [DecidableEq m] [DecidableEq q] {Q : Matrix m q 𝕜}
    (hQ : HasOrthonormalCols Q) : (1 - Q * Qᴴ) * (1 - Q * Qᴴ) = 1 - Q * Qᴴ := by
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, mul_conjTranspose_mul_mul_conjTranspose hQ]
  abel

/-- Idempotence of the complementary projector `I − QQᵀ` over `ℝ`. Atlas `projection-facts`. -/
theorem one_sub_mul_transpose_idem [DecidableEq m] [DecidableEq q] {Q : Matrix m q ℝ}
    (hQ : HasOrthonormalCols Q) : (1 - Q * Qᵀ) * (1 - Q * Qᵀ) = 1 - Q * Qᵀ :=
  one_sub_mul_conjTranspose_idem hQ

/-- `Qᴴ (I − QQᴴ) = 0` for `Q` with orthonormal columns. Atlas `projection-facts`. -/
theorem conjTranspose_mul_one_sub_mul_conjTranspose [DecidableEq m] [DecidableEq q]
    {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q) : Qᴴ * (1 - Q * Qᴴ) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hQ.conjTranspose_mul_self,
    Matrix.one_mul, sub_self]

/-- `Qᵀ (I − QQᵀ) = 0` for a real `Q` with orthonormal columns. Atlas `projection-facts`. -/
theorem transpose_mul_one_sub_mul_transpose [DecidableEq m] [DecidableEq q] {Q : Matrix m q ℝ}
    (hQ : HasOrthonormalCols Q) : Qᵀ * (1 - Q * Qᵀ) = 0 :=
  conjTranspose_mul_one_sub_mul_conjTranspose hQ

/-- `(I − QQᴴ)ᴴ Q = 0` for `Q` with orthonormal columns. Atlas `projection-facts`. -/
theorem one_sub_mul_conjTranspose_conjTranspose_mul [DecidableEq m] [DecidableEq q]
    {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q) : (1 - Q * Qᴴ)ᴴ * Q = 0 := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc,
    hQ.conjTranspose_mul_self, Matrix.mul_one, sub_self]

/-- `(I − QQᵀ)ᵀ Q = 0` for a real `Q` with orthonormal columns. Atlas `projection-facts`. -/
theorem one_sub_mul_transpose_transpose_mul [DecidableEq m] [DecidableEq q] {Q : Matrix m q ℝ}
    (hQ : HasOrthonormalCols Q) : (1 - Q * Qᵀ)ᵀ * Q = 0 :=
  one_sub_mul_conjTranspose_conjTranspose_mul hQ

/-! ### The residual `(I − QQᴴ) A` -/

omit [Fintype n] in
/-- `residual Q A = (I − QQᴴ) A`. Atlas `projection-facts`. -/
theorem residual_eq_one_sub_mul_conjTranspose_mul [DecidableEq m] (Q : Matrix m q 𝕜)
    (A : Matrix m n 𝕜) : residual Q A = (1 - Q * Qᴴ) * A := by
  rw [residual, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]

omit [Fintype n] in
/-- `residual Q A = (I − QQᵀ) A` over `ℝ`. Atlas `projection-facts`. -/
theorem residual_eq_one_sub_mul [DecidableEq m] (Q : Matrix m q ℝ) (A : Matrix m n ℝ) :
    residual Q A = (1 - Q * Qᵀ) * A :=
  residual_eq_one_sub_mul_conjTranspose_mul Q A

omit [Fintype n] in
/-- Orthogonal decomposition `A = Q(QᴴA) + residual Q A`. Atlas `projection-facts`. -/
theorem mul_conjTranspose_mul_add_residual (Q : Matrix m q 𝕜) (A : Matrix m n 𝕜) :
    Q * (Qᴴ * A) + residual Q A = A := by
  rw [residual]; abel

omit [Fintype n] in
/-- Orthogonal decomposition `A = Q(QᵀA) + residual Q A` over `ℝ`. Atlas `projection-facts`. -/
theorem mul_transpose_mul_add_residual (Q : Matrix m q ℝ) (A : Matrix m n ℝ) :
    Q * (Qᵀ * A) + residual Q A = A :=
  mul_conjTranspose_mul_add_residual Q A

omit [Fintype n] in
/-- The residual is orthogonal to `range Q`: `Qᴴ (I − QQᴴ) A = 0`. Atlas `projection-facts`.
atlas: projection-facts -/
theorem conjTranspose_mul_residual [DecidableEq q] {Q : Matrix m q 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) : Qᴴ * residual Q A = 0 := by
  rw [residual, Matrix.mul_sub, ← Matrix.mul_assoc, hQ.conjTranspose_mul_self, Matrix.one_mul,
    sub_self]

omit [Fintype n] in
/-- The residual is orthogonal to `range Q` over `ℝ`: `Qᵀ (I − QQᵀ) A = 0`.
Atlas `projection-facts`.
atlas: projection-facts -/
theorem transpose_mul_residual [DecidableEq q] {Q : Matrix m q ℝ} (hQ : HasOrthonormalCols Q)
    (A : Matrix m n ℝ) : Qᵀ * residual Q A = 0 :=
  conjTranspose_mul_residual hQ A

/-- The residual is Frobenius-orthogonal to every matrix `QX` with columns in `range Q`.
Atlas `projection-facts`. -/
theorem frobInner_mul_residual [DecidableEq q] {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q)
    (X : Matrix q n 𝕜) (A : Matrix m n 𝕜) : frobInner (Q * X) (residual Q A) = 0 := by
  rw [frobInner_eq_re_trace, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    conjTranspose_mul_residual hQ, Matrix.mul_zero, Matrix.trace_zero, map_zero]

omit [Fintype n] in
/-- Projecting the residual again changes nothing: `(I − QQᴴ)² A = (I − QQᴴ) A`.
Atlas `projection-facts`. -/
theorem residual_residual [DecidableEq q] {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix m n 𝕜) : residual Q (residual Q A) = residual Q A := by
  show residual Q A - Q * (Qᴴ * residual Q A) = residual Q A
  rw [conjTranspose_mul_residual hQ, Matrix.mul_zero, sub_zero]

/-- The residual of `QX` vanishes. Atlas `projection-facts`. -/
theorem residual_mul_self [DecidableEq q] {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q)
    {p : Type*} [Fintype p] (X : Matrix q p 𝕜) : residual Q (Q * X) = 0 := by
  rw [residual, ← Matrix.mul_assoc Qᴴ, hQ.conjTranspose_mul_self, Matrix.one_mul, sub_self]

/-- The residual commutes with right multiplication: `((I − QQᴴ)A) Ω = (I − QQᴴ)(AΩ)`.
Atlas `projection-facts`. -/
theorem residual_mul (Q : Matrix m q 𝕜) (A : Matrix m n 𝕜) {p : Type*} [Fintype p]
    (Ω : Matrix n p 𝕜) : residual Q A * Ω = residual Q (A * Ω) := by
  simp only [residual, Matrix.sub_mul, Matrix.mul_assoc]

/-- If `range(AΩ) ⊆ range(Q)`, written `Q (Qᴴ (AΩ)) = AΩ`, then `(I − QQᴴ) A Ω = 0`.
This is how `Q = orth(AΩ)` enters the range-finder analysis (HMT 2011, proof of Thm 9.1).
No orthonormality is needed. Over `ℝ` the hypothesis may be given as `Q (Qᵀ (AΩ)) = AΩ`.
Atlas `projection-facts`.
atlas: projection-facts -/
theorem residual_mul_eq_zero_of_range {Q : Matrix m q 𝕜} {A : Matrix m n 𝕜} {p : Type*}
    [Fintype p] {Ω : Matrix n p 𝕜} (h : Q * (Qᴴ * (A * Ω)) = A * Ω) :
    residual Q A * Ω = 0 := by
  rw [residual_mul, residual, h, sub_self]

/-! ### Pythagoras and contraction -/

/-- The squared Frobenius size of an orthonormal frame is its width.
Stewart–Sun §I.5; valid at width zero. -/
theorem frobSq_frame_eq_card [DecidableEq n] {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) :
    frobSq Q = Fintype.card n := by
  rw [frobSq, frobInner_eq_re_trace, hQ.conjTranspose_mul_self, Matrix.trace_one,
    RCLike.natCast_re]

/-- Pythagoras for the projector: `‖A‖_F² = ‖Q(QᴴA)‖_F² + ‖(I − QQᴴ)A‖_F²`.
Atlas `projection-facts`.
atlas: projection-facts -/
theorem frobSq_eq_frobSq_proj_add_residual [DecidableEq q] {Q : Matrix m q 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) :
    frobSq A = frobSq (Q * (Qᴴ * A)) + frobSq (residual Q A) := by
  conv_lhs => rw [← mul_conjTranspose_mul_add_residual Q A]
  exact frobSq_add_of_frobInner_eq_zero _ _ (frobInner_mul_residual hQ _ A)

/-- Pythagoras with the projection measured in `range Q` coordinates:
`‖A‖_F² = ‖QᴴA‖_F² + ‖(I − QQᴴ)A‖_F²`. Atlas `projection-facts`. -/
theorem frobSq_eq_frobSq_conjTranspose_mul_add_residual [DecidableEq q] {Q : Matrix m q 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) :
    frobSq A = frobSq (Qᴴ * A) + frobSq (residual Q A) := by
  rw [frobSq_eq_frobSq_proj_add_residual hQ A,
    frobSq_mul_left_of_conjTranspose_mul_self hQ.conjTranspose_mul_self]

/-- Pythagoras with the projection measured in `range Q` coordinates, over `ℝ`:
`‖A‖_F² = ‖QᵀA‖_F² + ‖(I − QQᵀ)A‖_F²`. Atlas `projection-facts`. -/
theorem frobSq_eq_frobSq_transpose_mul_add_residual [DecidableEq q] {Q : Matrix m q ℝ}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n ℝ) :
    frobSq A = frobSq (Qᵀ * A) + frobSq (residual Q A) :=
  frobSq_eq_frobSq_conjTranspose_mul_add_residual hQ A

/-- `‖(I − QQᴴ)A‖_F² = ‖A‖_F² − ‖QᴴA‖_F²`. Atlas `projection-facts`. -/
theorem frobSq_residual_eq_frobSq_sub_frobSq_conjTranspose_mul [DecidableEq q]
    {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) :
    frobSq (residual Q A) = frobSq A - frobSq (Qᴴ * A) := by
  rw [frobSq_eq_frobSq_conjTranspose_mul_add_residual hQ A]; ring

/-- `‖(I − QQᵀ)A‖_F² = ‖A‖_F² − ‖QᵀA‖_F²` over `ℝ`. Atlas `projection-facts`. -/
theorem frobSq_residual_eq_sub [DecidableEq q] {Q : Matrix m q ℝ}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n ℝ) :
    frobSq (residual Q A) = frobSq A - frobSq (Qᵀ * A) :=
  frobSq_residual_eq_frobSq_sub_frobSq_conjTranspose_mul hQ A

/-- The residual contracts: `‖(I − QQᴴ)A‖_F² ≤ ‖A‖_F²`. Atlas `projection-facts`.
atlas: projection-facts -/
theorem frobSq_residual_le [DecidableEq q] {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix m n 𝕜) : frobSq (residual Q A) ≤ frobSq A := by
  rw [frobSq_eq_frobSq_proj_add_residual hQ A]
  exact le_add_of_nonneg_left (frobSq_nonneg _)

/-- `‖QᴴA‖_F² ≤ ‖A‖_F²` for `Q` with orthonormal columns. Atlas `projection-facts`. -/
theorem frobSq_conjTranspose_mul_le [DecidableEq q] {Q : Matrix m q 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) : frobSq (Qᴴ * A) ≤ frobSq A := by
  rw [frobSq_eq_frobSq_conjTranspose_mul_add_residual hQ A]
  exact le_add_of_nonneg_right (frobSq_nonneg _)

/-- `‖QᵀA‖_F² ≤ ‖A‖_F²` for a real `Q` with orthonormal columns. Atlas `projection-facts`. -/
theorem frobSq_transpose_mul_le [DecidableEq q] {Q : Matrix m q ℝ} (hQ : HasOrthonormalCols Q)
    (A : Matrix m n ℝ) : frobSq (Qᵀ * A) ≤ frobSq A :=
  frobSq_conjTranspose_mul_le hQ A

/-- The projection contracts: `‖QQᴴA‖_F² ≤ ‖A‖_F²`. Atlas `projection-facts`. -/
theorem frobSq_proj_le [DecidableEq q] {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix m n 𝕜) : frobSq (Q * (Qᴴ * A)) ≤ frobSq A := by
  rw [frobSq_mul_left_of_conjTranspose_mul_self hQ.conjTranspose_mul_self]
  exact frobSq_conjTranspose_mul_le hQ A

/-! ### Best approximation in a range and monotonicity -/

/-- Pythagoras in `range Q`: for every `B`,
`‖A − QB‖_F² = ‖(I − QQᴴ)A‖_F² + ‖QᴴA − B‖_F²` (proof of HMT 2011, Thm 9.1; LRA
`pythagoras_range`). Atlas `projection-facts`.
atlas: projection-facts -/
theorem frobSq_sub_mul_eq_frobSq_residual_add_frobSq_conjTranspose_mul_sub [DecidableEq q]
    {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) (B : Matrix q n 𝕜) :
    frobSq (A - Q * B) = frobSq (residual Q A) + frobSq (Qᴴ * A - B) := by
  have hdecomp : A - Q * B = residual Q A + Q * (Qᴴ * A - B) := by
    rw [residual, Matrix.mul_sub]; abel
  rw [hdecomp, frobSq_add_of_frobInner_eq_zero _ _ (by
      rw [frobInner_comm]; exact frobInner_mul_residual hQ _ A),
    frobSq_mul_left_of_conjTranspose_mul_self hQ.conjTranspose_mul_self]

/-- Pythagoras in `range Q` over `ℝ`: for every `B`,
`‖A − QB‖_F² = ‖(I − QQᵀ)A‖_F² + ‖QᵀA − B‖_F²` (proof of HMT 2011, Thm 9.1; LRA
`pythagoras_range`). Atlas `projection-facts`.
atlas: projection-facts -/
theorem frobSq_sub_mul_eq [DecidableEq q] {Q : Matrix m q ℝ} (hQ : HasOrthonormalCols Q)
    (A : Matrix m n ℝ) (B : Matrix q n ℝ) :
    frobSq (A - Q * B) = frobSq (residual Q A) + frobSq (Qᵀ * A - B) :=
  frobSq_sub_mul_eq_frobSq_residual_add_frobSq_conjTranspose_mul_sub hQ A B

/-- `Q(QᴴA)` is the best Frobenius approximation of `A` with columns in `range Q`:
`‖(I − QQᴴ)A‖_F² ≤ ‖A − QB‖_F²` for every `B`. Atlas `projection-facts`. -/
theorem frobSq_residual_le_frobSq_sub_mul [DecidableEq q] {Q : Matrix m q 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) (B : Matrix q n 𝕜) :
    frobSq (residual Q A) ≤ frobSq (A - Q * B) := by
  rw [frobSq_sub_mul_eq_frobSq_residual_add_frobSq_conjTranspose_mul_sub hQ A B]
  exact le_add_of_nonneg_right (frobSq_nonneg _)

/-- Monotonicity of the residual under range inclusion (HMT 2011, Prop. 8.5, Frobenius case):
if `range Q₁ ⊆ range Q₂`, written `Q₁ = Q₂ C`, then `‖(I − Q₂Q₂ᴴ)A‖_F² ≤ ‖(I − Q₁Q₁ᴴ)A‖_F²`.
Deviation: only `Q₂` needs orthonormal columns; `Q₁` is arbitrary (with `residual` defined
by the formula `A − Q₁Q₁ᴴA`). Atlas `projection-facts`.
atlas: projection-facts -/
theorem frobSq_residual_le_of_eq_mul [DecidableEq q] {q₁ : Type*} [Fintype q₁]
    {Q₁ : Matrix m q₁ 𝕜} {Q₂ : Matrix m q 𝕜} (hQ₂ : HasOrthonormalCols Q₂)
    {C : Matrix q q₁ 𝕜} (hC : Q₁ = Q₂ * C) (A : Matrix m n 𝕜) :
    frobSq (residual Q₂ A) ≤ frobSq (residual Q₁ A) := by
  have h : residual Q₁ A = A - Q₂ * (C * (Q₁ᴴ * A)) := by
    rw [residual, hC, Matrix.mul_assoc, ← hC]
  rw [h]
  exact frobSq_residual_le_frobSq_sub_mul hQ₂ A _

/-- `Q ⟦QᴴA⟧ₖ` is a best rank-`k` Frobenius approximation of `A` among matrices `QB` with
`rank B ≤ k` (HMT 2011, proof of Thm 9.1; LRA `best_in_range`). Over `ℝ` the hypothesis may be
given as `IsBestRankApprox k (Qᵀ * A) Y`. Atlas `projection-facts`.
atlas: projection-facts -/
theorem frobSq_sub_mul_le_of_isBestRankApprox [DecidableEq q] {k : ℕ} {Q : Matrix m q 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix m n 𝕜} {Y : Matrix q n 𝕜}
    (hY : IsBestRankApprox k (Qᴴ * A) Y) (B : Matrix q n 𝕜) (hB : B.rank ≤ k) :
    frobSq (A - Q * Y) ≤ frobSq (A - Q * B) := by
  rw [frobSq_sub_mul_eq_frobSq_residual_add_frobSq_conjTranspose_mul_sub hQ A Y,
    frobSq_sub_mul_eq_frobSq_residual_add_frobSq_conjTranspose_mul_sub hQ A B]
  exact add_le_add le_rfl (hY.2 B hB)

/-! ### Orthogonality of column blocks and orthogonal completions -/

omit [Fintype n] [Fintype q] in
/-- `AᴴB = 0 ↔ BᴴA = 0`: orthogonality of column spaces is symmetric.
Atlas `projection-facts`. -/
theorem conjTranspose_mul_eq_zero_comm {A : Matrix m n 𝕜} {B : Matrix m q 𝕜} :
    Aᴴ * B = 0 ↔ Bᴴ * A = 0 := by
  constructor <;> intro h <;> simpa using congrArg Matrix.conjTranspose h

omit [Fintype n] [Fintype q] in
/-- `AᵀB = 0 ↔ BᵀA = 0` over `ℝ`: orthogonality of column spaces is symmetric.
Atlas `projection-facts`. -/
theorem transpose_mul_eq_zero_comm {A : Matrix m n ℝ} {B : Matrix m q ℝ} :
    Aᵀ * B = 0 ↔ Bᵀ * A = 0 :=
  conjTranspose_mul_eq_zero_comm

omit [Fintype q] in
/-- `(PᴴQ)ᴴ(PᴴQ) = (QᴴP)(QᴴP)ᴴ`: the Gram matrix of `PᴴQ` is the outer Gram matrix of
`QᴴP`. Atlas `projection-facts`. -/
theorem gram_conjTranspose_mul_eq (P : Matrix m n 𝕜) (Q : Matrix m q 𝕜) :
    (Pᴴ * Q)ᴴ * (Pᴴ * Q) = (Qᴴ * P) * (Qᴴ * P)ᴴ := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

omit [Fintype q] in
/-- `(PᵀQ)ᵀ(PᵀQ) = (QᵀP)(QᵀP)ᵀ` over `ℝ`: the Gram matrix of `PᵀQ` is the outer Gram matrix
of `QᵀP`. Atlas `projection-facts`. -/
theorem gram_transpose_mul_eq (P : Matrix m n ℝ) (Q : Matrix m q ℝ) :
    (Pᵀ * Q)ᵀ * (Pᵀ * Q) = (Qᵀ * P) * (Qᵀ * P)ᵀ :=
  gram_conjTranspose_mul_eq P Q

/-- If `QᴴQ = I`, `QpᴴQp = I` and `QQᴴ + QpQpᴴ = I`, then `QᴴQp = 0`.
Atlas `orthonormal-completion`. -/
theorem conjTranspose_mul_eq_zero_of_completion [DecidableEq m] [DecidableEq n] [DecidableEq q]
    {Q : Matrix m q 𝕜} {Qp : Matrix m n 𝕜} (hQ : Qᴴ * Q = 1) (hQp : Qpᴴ * Qp = 1)
    (hcomp : Q * Qᴴ + Qp * Qpᴴ = 1) : Qᴴ * Qp = 0 := by
  have h := congrArg (fun M => Qᴴ * M * Qp) hcomp
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one] at h
  rw [← Matrix.mul_assoc, hQ, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hQp,
    Matrix.mul_one] at h
  simpa using h

/-- If `QᵀQ = I`, `QpᵀQp = I` and `QQᵀ + QpQpᵀ = I` over `ℝ`, then `QᵀQp = 0`.
Atlas `orthonormal-completion`. -/
theorem transpose_mul_eq_zero_of_completion [DecidableEq m] [DecidableEq n] [DecidableEq q]
    {Q : Matrix m q ℝ} {Qp : Matrix m n ℝ} (hQ : Qᵀ * Q = 1) (hQp : Qpᵀ * Qp = 1)
    (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1) : Qᵀ * Qp = 0 :=
  conjTranspose_mul_eq_zero_of_completion hQ hQp hcomp

omit [Fintype n] in
/-- For a completion `QQᴴ + QpQpᴴ = I` of `Q`, the residual lies in `range Qp`:
`(I − QQᴴ)A = Qp (Qpᴴ (I − QQᴴ)A)` (Chen–Persson, proof of `lem:completion`, item 1).
Atlas `projection-facts`. -/
theorem residual_eq_mul_conjTranspose_mul_residual [DecidableEq m] [DecidableEq q] {r : Type*}
    [Fintype r] {Q : Matrix m q 𝕜} {Qp : Matrix m r 𝕜} (hQ : HasOrthonormalCols Q)
    (hcomp : Q * Qᴴ + Qp * Qpᴴ = 1) (A : Matrix m n 𝕜) :
    residual Q A = Qp * (Qpᴴ * residual Q A) := by
  have h : (Q * Qᴴ + Qp * Qpᴴ) * residual Q A = residual Q A := by
    rw [hcomp, Matrix.one_mul]
  rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, conjTranspose_mul_residual hQ A,
    Matrix.mul_zero, zero_add] at h
  exact h.symm

omit [Fintype n] in
/-- For an orthogonal completion `QQᵀ + QpQpᵀ = I` of a real `Q`, the residual lies in
`range Qp`: `(I − QQᵀ)A = Qp (Qpᵀ (I − QQᵀ)A)` (Chen–Persson, proof of `lem:completion`,
item 1). Atlas `projection-facts`. -/
theorem residual_eq_mul_transpose_mul_residual [DecidableEq m] [DecidableEq q] {r : Type*}
    [Fintype r] {Q : Matrix m q ℝ} {Qp : Matrix m r ℝ} (hQ : HasOrthonormalCols Q)
    (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1) (A : Matrix m n ℝ) :
    residual Q A = Qp * (Qpᵀ * residual Q A) :=
  residual_eq_mul_conjTranspose_mul_residual hQ hcomp A

/-- Columns of a matrix as vectors of Euclidean space. -/
private def col {k : ℕ} {ι : Type*} (V : Matrix (Fin k) ι 𝕜) (j : ι) :
    EuclideanSpace 𝕜 (Fin k) :=
  WithLp.toLp 2 (fun i => V i j)

private lemma col_orthonormal {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix (Fin k) ι 𝕜) (hV : Vᴴ * V = 1) : Orthonormal 𝕜 (col V) := by
  rw [orthonormal_iff_ite]
  intro a b
  have := congrFun (congrFun hV a) b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at this
  simp only [col, PiLp.inner_apply, RCLike.inner_apply]
  rw [← this]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]; rfl

/-- A matrix with orthonormal columns has at most as many columns as rows (general finite
index types). Atlas `orthonormal-completion`.
atlas: orthonormal-completion -/
theorem card_le_card_of_hasOrthonormalCols {r : Type*} [Fintype r] [DecidableEq r]
    {Q : Matrix m r 𝕜} (hQ : HasOrthonormalCols Q) : Fintype.card r ≤ Fintype.card m := by
  have hinj : Function.Injective Q.mulVecLin := by
    intro x y hxy
    have h := congrArg (fun v => Qᴴ *ᵥ v) hxy
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] at h
    rwa [hQ.conjTranspose_mul_self, Matrix.one_mulVec, Matrix.one_mulVec] at h
  simpa [Module.finrank_fintype_fun_eq_card] using
    LinearMap.finrank_le_finrank_of_injective hinj

/-- **Unitary completion.** A matrix `V` with orthonormal columns indexed by `ι` (`VᴴV = I`),
placed in the columns `e '' ι` of `Fin k`, extends to a unitary `k × k` matrix `W`
(`WᴴW = I`). Helper for HMT 2011 §10.2. Ported from the Prove2me workspace (Gaussian Random
Matrices series). Atlas `orthonormal-completion`.
atlas: orthonormal-completion -/
theorem exists_unitary_completion {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix (Fin k) ι 𝕜) (hV : Vᴴ * V = 1) (e : ι ↪ Fin k) :
    ∃ W : Matrix (Fin k) (Fin k) 𝕜, Wᴴ * W = 1 ∧ ∀ i j, W i (e j) = V i j := by
  classical
  let v : Fin k → EuclideanSpace 𝕜 (Fin k) := Function.extend e (col V) 0
  have hv : Orthonormal 𝕜 ((Set.range e).domRestrict v) := by
    have h1 : (Set.range e).domRestrict v =
        col V ∘ (Equiv.ofInjective e e.injective).symm := by
      funext x
      obtain ⟨a, j, rfl⟩ := x
      have : (Equiv.ofInjective e e.injective).symm ⟨e j, j, rfl⟩ = j :=
        (Equiv.ofInjective e e.injective).symm_apply_eq.mpr rfl
      simp only [Set.domRestrict_apply, Function.comp_apply, this, v]
      exact e.injective.extend_apply _ _ _
    rw [h1]
    exact (col_orthonormal V hV).comp _ (Equiv.injective _)
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp [finrank_euclideanSpace])
  refine ⟨Matrix.of fun i a => b a i, ?_, ?_⟩
  · ext a c
    have := (orthonormal_iff_ite.mp b.orthonormal) a c
    simp only [PiLp.inner_apply, RCLike.inner_apply] at this
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]; rfl
  · intro i j
    simp only [Matrix.of_apply]
    rw [hb (e j) ⟨j, rfl⟩]
    simp only [v, e.injective.extend_apply, col]

/-- **Orthogonal completion.** A real matrix `V` with orthonormal columns indexed by `ι`, placed
in the columns `e '' ι` of `Fin k`, extends to an orthogonal `k × k` matrix `W`.
Real form of `exists_unitary_completion`. Helper for HMT 2011 §10.2. Ported from the Prove2me
workspace (Gaussian Random Matrices series). Atlas `orthonormal-completion`.
atlas: orthonormal-completion -/
theorem exists_orthogonal_completion {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix (Fin k) ι ℝ) (hV : Vᵀ * V = 1) (e : ι ↪ Fin k) :
    ∃ W : Matrix (Fin k) (Fin k) ℝ, Wᵀ * W = 1 ∧ ∀ i j, W i (e j) = V i j :=
  exists_unitary_completion V hV e

/-- **Unitary complement.** A matrix `Q` with orthonormal columns has a complement `Qp` with
orthonormal columns and `QQᴴ + QpQpᴴ = I` (here `Qp` has `k − q` columns). From
`exists_unitary_completion`. Atlas `orthonormal-completion`.
atlas: orthonormal-completion -/
theorem exists_unitary_complement {k q : ℕ} (Q : Matrix (Fin k) (Fin q) 𝕜)
    (hQ : HasOrthonormalCols Q) :
    ∃ r : ℕ, ∃ Qp : Matrix (Fin k) (Fin r) 𝕜,
      HasOrthonormalCols Qp ∧ Q * Qᴴ + Qp * Qpᴴ = 1 := by
  have hqk : q ≤ k := by simpa using card_le_card_of_hasOrthonormalCols hQ
  obtain ⟨r, rfl⟩ : ∃ r, k = q + r := ⟨k - q, by omega⟩
  obtain ⟨W, hW, hWQ⟩ := exists_unitary_completion Q hQ (Fin.castAddEmb r)
  have hWW : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
  refine ⟨r, Matrix.of fun i j => W i (Fin.natAdd q j), ?_, ?_⟩
  · ext a b
    have := congrFun (congrFun hW (Fin.natAdd q a)) (Fin.natAdd q b)
    simpa [HasOrthonormalCols, Matrix.mul_apply, Matrix.one_apply, Fin.natAdd_inj] using this
  · ext a b
    have := congrFun (congrFun hWW a) b
    rw [Matrix.mul_apply, Fin.sum_univ_add] at this
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
    rw [← this]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.conjTranspose_apply]
    rw [← hWQ a j, ← hWQ b j]
    rfl

/-- **Orthonormal complement.** A real matrix `Q` with orthonormal columns has a complement
`Qp` with orthonormal columns and `QQᵀ + QpQpᵀ = I` (here `Qp` has `k − q` columns). Real form
of `exists_unitary_complement`. Atlas `orthonormal-completion`.
atlas: orthonormal-completion -/
theorem exists_orthonormal_complement {k q : ℕ} (Q : Matrix (Fin k) (Fin q) ℝ)
    (hQ : HasOrthonormalCols Q) :
    ∃ r : ℕ, ∃ Qp : Matrix (Fin k) (Fin r) ℝ,
      HasOrthonormalCols Qp ∧ Q * Qᵀ + Qp * Qpᵀ = 1 :=
  exists_unitary_complement Q hQ

/-! ### Projected matrices and vectors in a range -/

omit [Fintype m] in
/-- If `Q` has orthonormal columns and `x ∈ range Q`, then `Q Qᴴ x = x`: the projector `QQᴴ`
fixes its range. Atlas `projection-facts`. -/
theorem mulVec_conjTranspose_mulVec_of_mem_range [Fintype m] [DecidableEq q]
    {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q) {x : m → 𝕜}
    (hx : x ∈ LinearMap.range Q.mulVecLin) : Q *ᵥ (Qᴴ *ᵥ x) = x := by
  obtain ⟨y, rfl⟩ := hx
  have h : Qᴴ *ᵥ (Q *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, hQ.conjTranspose_mul_self, Matrix.one_mulVec]
  simp only [Matrix.mulVecLin_apply, h]

omit [Fintype m] in
/-- If a real `Q` has orthonormal columns and `x ∈ range Q`, then `Q Qᵀ x = x`: the projector
`QQᵀ` fixes its range. Atlas `projection-facts` (moved from
`NLAlib.Krylov.Quadrature.GaussQuadrature`). -/
theorem mulVec_transpose_mulVec_of_mem_range [Fintype m] [DecidableEq q] {Q : Matrix m q ℝ}
    (hQ : HasOrthonormalCols Q) {x : m → ℝ} (hx : x ∈ LinearMap.range Q.mulVecLin) :
    Q *ᵥ (Qᵀ *ᵥ x) = x :=
  mulVec_conjTranspose_mulVec_of_mem_range hQ hx

omit [Fintype q] in
/-- The compression `Qᵀ A Q` of a symmetric `A` is symmetric (any `Q`).
Atlas `projection-facts` (moved from `NLAlib.Krylov.Quadrature.GaussQuadrature`). -/
theorem isSymm_transpose_mul_mul {A : Matrix m m 𝕜} (hA : A.IsSymm) (Q : Matrix m q 𝕜) :
    (Qᵀ * A * Q).IsSymm := by
  rw [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    hA.eq, Matrix.mul_assoc]

omit [Fintype q] in
/-- The compression `Qᵀ A Q` of a real symmetric (Hermitian) `A` is Hermitian (any `Q`); the
`IsHermitian` form of `isSymm_transpose_mul_mul`, which is what `hB.eigenvalues` and `cfc` need.
The general form is Mathlib's `Matrix.isHermitian_conjTranspose_mul_mul`.
Atlas `projection-facts`. -/
theorem isHermitian_transpose_mul_mul {A : Matrix m m ℝ} (hA : A.IsHermitian)
    (Q : Matrix m q ℝ) : (Qᵀ * A * Q).IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_mul Q hA

/-- `Qᴴ` is a contraction for `Q` with orthonormal columns: `‖Qᴴ x‖² ≤ ‖x‖²` (Bessel), written
with explicit sums. Atlas `projection-facts`. -/
theorem sum_norm_sq_conjTranspose_mulVec_le [DecidableEq q] {Q : Matrix m q 𝕜}
    (hQ : HasOrthonormalCols Q) (x : m → 𝕜) :
    ∑ i, ‖(Qᴴ *ᵥ x) i‖ ^ 2 ≤ ∑ i, ‖x i‖ ^ 2 := by
  classical
  have hn : specNorm Qᴴ ≤ 1 := by
    rw [specNorm_conjTranspose]
    exact specNorm_le_one_of_conjTranspose_mul_self hQ.conjTranspose_mul_self
  have h := sum_norm_sq_mulVec_le_specNorm_sq Qᴴ x
  have h1 : specNorm Qᴴ ^ 2 ≤ 1 := by
    have := specNorm_nonneg Qᴴ
    nlinarith
  have h2 : 0 ≤ ∑ i, ‖x i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  nlinarith

/-- A real `Qᵀ` is a contraction for `Q` with orthonormal columns: `‖Qᵀ x‖² ≤ ‖x‖²` (Bessel).
Atlas `projection-facts`. -/
theorem transpose_mulVec_dotProduct_self_le [DecidableEq q] {Q : Matrix m q ℝ}
    (hQ : HasOrthonormalCols Q) (x : m → ℝ) : (Qᵀ *ᵥ x) ⬝ᵥ (Qᵀ *ᵥ x) ≤ x ⬝ᵥ x := by
  simpa [dotProduct, sq] using sum_norm_sq_conjTranspose_mulVec_le hQ x

omit [Fintype m] in
/-- For `x ∈ range Q` and `Q` with orthonormal columns, `‖Qᴴ x‖² = ‖x‖²`, written with dot
products. Atlas `projection-facts`. -/
theorem star_conjTranspose_mulVec_dotProduct_self_of_mem_range [Fintype m] [DecidableEq q]
    {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q) {x : m → 𝕜}
    (hx : x ∈ LinearMap.range Q.mulVecLin) :
    star (Qᴴ *ᵥ x) ⬝ᵥ (Qᴴ *ᵥ x) = star x ⬝ᵥ x := by
  obtain ⟨y, rfl⟩ := hx
  have h : Qᴴ *ᵥ (Q *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, hQ.conjTranspose_mul_self, Matrix.one_mulVec]
  simp only [Matrix.mulVecLin_apply, h]
  exact (star_mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols hQ y).symm

omit [Fintype m] in
/-- For `x ∈ range Q` and a real `Q` with orthonormal columns, `‖Qᵀ x‖² = ‖x‖²`.
Atlas `projection-facts`. -/
theorem transpose_mulVec_dotProduct_self_of_mem_range [Fintype m] [DecidableEq q]
    {Q : Matrix m q ℝ} (hQ : HasOrthonormalCols Q) {x : m → ℝ}
    (hx : x ∈ LinearMap.range Q.mulVecLin) : (Qᵀ *ᵥ x) ⬝ᵥ (Qᵀ *ᵥ x) = x ⬝ᵥ x :=
  star_conjTranspose_mulVec_dotProduct_self_of_mem_range hQ hx

omit [Fintype m] in
/-- Range inclusion as a matrix identity: if `range Q ⊆ range Q'` and `Q'` has orthonormal
columns, then `Q' Q'ᴴ Q = Q`. Atlas `projection-facts`. -/
theorem mul_conjTranspose_mul_eq_of_range_le [Fintype m] [DecidableEq q] {q' : Type*}
    [Fintype q'] {Q : Matrix m q' 𝕜} {Q' : Matrix m q 𝕜} (hQ' : HasOrthonormalCols Q')
    (h : LinearMap.range Q.mulVecLin ≤ LinearMap.range Q'.mulVecLin) : Q' * (Q'ᴴ * Q) = Q := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact mulVec_conjTranspose_mulVec_of_mem_range hQ' (h ⟨v, rfl⟩)

omit [Fintype m] in
/-- Range inclusion as a matrix identity over `ℝ`: if `range Q ⊆ range Q'` and `Q'` has
orthonormal columns, then `Q' Q'ᵀ Q = Q`. Atlas `projection-facts`. -/
theorem mul_transpose_mul_eq_of_range_le [Fintype m] [DecidableEq q] {q' : Type*} [Fintype q']
    {Q : Matrix m q' ℝ} {Q' : Matrix m q ℝ} (hQ' : HasOrthonormalCols Q')
    (h : LinearMap.range Q.mulVecLin ≤ LinearMap.range Q'.mulVecLin) : Q' * (Q'ᵀ * Q) = Q :=
  mul_conjTranspose_mul_eq_of_range_le hQ' h

omit [Fintype m] in
/-- The orthogonal projector depends only on the range: if `Q`, `Q'` have orthonormal columns
and the same range, then `QQᴴ = Q'Q'ᴴ`. Atlas `projection-facts`. -/
theorem mul_conjTranspose_eq_of_range_eq [Fintype m] [DecidableEq q] {q' : Type*} [Fintype q']
    [DecidableEq q'] {Q : Matrix m q 𝕜} {Q' : Matrix m q' 𝕜} (hQ : HasOrthonormalCols Q)
    (hQ' : HasOrthonormalCols Q')
    (h : LinearMap.range Q.mulVecLin = LinearMap.range Q'.mulVecLin) : Q * Qᴴ = Q' * Q'ᴴ := by
  have h1 : Q' * (Q'ᴴ * Q) = Q := mul_conjTranspose_mul_eq_of_range_le hQ' h.le
  have h2 : Q * (Qᴴ * Q') = Q' := mul_conjTranspose_mul_eq_of_range_le hQ h.ge
  have e1 : Q * Qᴴ = Q' * Q'ᴴ * (Q * Qᴴ) := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc Q', h1]
  calc Q * Qᴴ = (Q * Qᴴ)ᴴ := (Matrix.isHermitian_mul_conjTranspose_self Q).symm
    _ = (Q' * Q'ᴴ * (Q * Qᴴ))ᴴ := by rw [← e1]
    _ = Q * (Qᴴ * Q') * Q'ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = Q' * Q'ᴴ := by rw [h2]

omit [Fintype m] in
/-- The orthogonal projector depends only on the range, over `ℝ`: if `Q`, `Q'` have orthonormal
columns and the same range, then `QQᵀ = Q'Q'ᵀ`. Atlas `projection-facts`. -/
theorem mul_transpose_eq_of_range_eq [Fintype m] [DecidableEq q] {q' : Type*} [Fintype q']
    [DecidableEq q'] {Q : Matrix m q ℝ} {Q' : Matrix m q' ℝ} (hQ : HasOrthonormalCols Q)
    (hQ' : HasOrthonormalCols Q')
    (h : LinearMap.range Q.mulVecLin = LinearMap.range Q'.mulVecLin) : Q * Qᵀ = Q' * Q'ᵀ :=
  mul_conjTranspose_eq_of_range_eq hQ hQ' h

end NLAlib
