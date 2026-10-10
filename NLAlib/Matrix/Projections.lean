import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.InnerProductSpace.PiL2
import NLAlib.Matrix.Norms

/-!
# Orthonormal frames, projectors and residuals

* `NLAlib.HasOrthonormalCols Q`: `Qᵀ Q = I`.
* `NLAlib.residual Q A = A − Q (Qᵀ A) = (I − QQᵀ) A`, the part of `A` outside `range Q`.
* `NLAlib.IsBestRankApprox k C Y`: `Y` has rank `≤ k` and minimises the Frobenius distance to
  `C` among rank-`≤ k` matrices. Until Eckart–Young is proved (atlas `eckart-young`) this
  optimality property is how `⟦C⟧ₖ` enters statements.

## Contents

* Isometry: `‖Qx‖² = ‖x‖²` for `Q` with orthonormal columns.
* The orthogonal projector `P = QQᵀ`: symmetry, idempotence, `Qᵀ(I − P) = 0`.
* The residual: `residual Q A = (I − QQᵀ) A`, orthogonality to `range Q`, Pythagoras
  `‖A‖_F² = ‖QQᵀA‖_F² + ‖(I − QQᵀ)A‖_F²`, `‖(I − QQᵀ)A‖_F ≤ ‖A‖_F`, `‖QᵀA‖_F ≤ ‖A‖_F`.
* Best approximation in a range: `‖A − QB‖_F² = ‖(I − QQᵀ)A‖_F² + ‖QᵀA − B‖_F²`, and the
  monotonicity of the residual under range inclusion (HMT 2011, Prop. 8.5, Frobenius case).
* Range-finder fact: `range(AΩ) ⊆ range(Q)` (written `Q (Qᵀ (A Ω)) = A Ω`) gives
  `(I − QQᵀ) A Ω = 0`.
* Orthogonal completions: a matrix with orthonormal columns has at most as many columns as
  rows and extends to an orthogonal matrix (`exists_orthogonal_completion`) or, with the
  complementary block, to `QQᵀ + Q⊥Q⊥ᵀ = I` (`exists_orthonormal_complement`); for such a
  completion `QᵀQ⊥ = 0` and `(I − QQᵀ)A = Q⊥Q⊥ᵀ(I − QQᵀ)A`.

Proofs ported from the LRA project (`LRA/Basic.lean`, `LRA/Deterministic/RangeFinder.lean`,
Chen–Persson formalization), namespace renamed and statements generalised from `Fin` to
arbitrary `Fintype` index types.

Atlas: `projection-facts`, `eckart-young`, `orthonormal-completion`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {m n q : Type*} [Fintype m] [Fintype n] [Fintype q]

/-! ### Definitions -/

/-- `Q` has orthonormal columns: `Qᵀ Q = I`.
atlas: orthonormal-columns-def -/
def HasOrthonormalCols [DecidableEq q] (Q : Matrix m q ℝ) : Prop := Qᵀ * Q = 1

/-- Residual of `A` after projecting onto the column space of `Q`: `(I − QQᵀ) A`.
atlas: residual-def -/
def residual (Q : Matrix m q ℝ) (A : Matrix m n ℝ) : Matrix m n ℝ := A - Q * (Qᵀ * A)

/-- `Y` is a best rank-`k` Frobenius approximation of `C`.
atlas: best-rank-approx-def -/
def IsBestRankApprox (k : ℕ) (C Y : Matrix m n ℝ) : Prop :=
  Y.rank ≤ k ∧ ∀ Z : Matrix m n ℝ, Z.rank ≤ k → frobSq (C - Y) ≤ frobSq (C - Z)

/-- If `U` has orthonormal columns (`Uᵀ U = 1`) then `‖Ux‖² = ‖x‖²`. Helper for `ose-def`;
atlas `projection-facts`. -/
theorem mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols [DecidableEq q] {U : Matrix m q ℝ}
    (hU : HasOrthonormalCols U) (x : q → ℝ) : (U *ᵥ x) ⬝ᵥ (U *ᵥ x) = x ⬝ᵥ x := by
  rw [mulVec_dotProduct_mulVec_self, show Uᵀ * U = 1 from hU, Matrix.one_mulVec]

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
/-- The residual is orthogonal to `range Q`: `Qᵀ (I − QQᵀ) A = 0`. Atlas `projection-facts`.
atlas: projection-facts -/
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
No orthonormality is needed. Atlas `projection-facts`.
atlas: projection-facts -/
theorem residual_mul_eq_zero_of_range {Q : Matrix m q ℝ} {A : Matrix m n ℝ} {p : Type*}
    [Fintype p] {Ω : Matrix n p ℝ} (h : Q * (Qᵀ * (A * Ω)) = A * Ω) :
    residual Q A * Ω = 0 := by
  rw [residual_mul, residual, h, sub_self]

/-! ### Pythagoras and contraction -/

/-- Pythagoras for the projector: `‖A‖_F² = ‖Q(QᵀA)‖_F² + ‖(I − QQᵀ)A‖_F²`.
Atlas `projection-facts`.
atlas: projection-facts -/
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

/-- The residual contracts: `‖(I − QQᵀ)A‖_F² ≤ ‖A‖_F²`. Atlas `projection-facts`.
atlas: projection-facts -/
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
`pythagoras_range`). Atlas `projection-facts`.
atlas: projection-facts -/
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
by the formula `A − Q₁Q₁ᵀA`). Atlas `projection-facts`.
atlas: projection-facts -/
theorem frobSq_residual_le_of_eq_mul [DecidableEq q] {q₁ : Type*} [Fintype q₁]
    {Q₁ : Matrix m q₁ ℝ} {Q₂ : Matrix m q ℝ} (hQ₂ : HasOrthonormalCols Q₂)
    {C : Matrix q q₁ ℝ} (hC : Q₁ = Q₂ * C) (A : Matrix m n ℝ) :
    frobSq (residual Q₂ A) ≤ frobSq (residual Q₁ A) := by
  have h : residual Q₁ A = A - Q₂ * (C * (Q₁ᵀ * A)) := by
    rw [residual, hC, Matrix.mul_assoc, ← hC]
  rw [h]
  exact frobSq_residual_le_frobSq_sub_mul hQ₂ A _

/-- `Q ⟦QᵀA⟧ₖ` is a best rank-`k` Frobenius approximation of `A` among matrices `QB` with
`rank B ≤ k` (HMT 2011, proof of Thm 9.1; LRA `best_in_range`). Atlas `projection-facts`.
atlas: projection-facts -/
theorem frobSq_sub_mul_le_of_isBestRankApprox [DecidableEq q] {k : ℕ} {Q : Matrix m q ℝ}
    (hQ : HasOrthonormalCols Q) {A : Matrix m n ℝ} {Y : Matrix q n ℝ}
    (hY : IsBestRankApprox k (Qᵀ * A) Y) (B : Matrix q n ℝ) (hB : B.rank ≤ k) :
    frobSq (A - Q * Y) ≤ frobSq (A - Q * B) := by
  rw [frobSq_sub_mul_eq hQ A Y, frobSq_sub_mul_eq hQ A B]
  exact add_le_add le_rfl (hY.2 B hB)

/-! ### Orthogonality of column blocks and orthogonal completions -/

omit [Fintype n] [Fintype q] in
/-- `AᵀB = 0 ↔ BᵀA = 0`: orthogonality of column spaces is symmetric.
Atlas `projection-facts`. -/
theorem transpose_mul_eq_zero_comm {A : Matrix m n ℝ} {B : Matrix m q ℝ} :
    Aᵀ * B = 0 ↔ Bᵀ * A = 0 := by
  constructor <;> intro h <;> simpa using congrArg Matrix.transpose h

omit [Fintype q] in
/-- `(PᵀQ)ᵀ(PᵀQ) = (QᵀP)(QᵀP)ᵀ`: the Gram matrix of `PᵀQ` is the outer Gram matrix of
`QᵀP`. Atlas `projection-facts`. -/
theorem gram_transpose_mul_eq (P : Matrix m n ℝ) (Q : Matrix m q ℝ) :
    (Pᵀ * Q)ᵀ * (Pᵀ * Q) = (Qᵀ * P) * (Qᵀ * P)ᵀ := by
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_mul,
    Matrix.transpose_transpose]

/-- If `QᵀQ = I`, `QpᵀQp = I` and `QQᵀ + QpQpᵀ = I`, then `QᵀQp = 0`.
Atlas `orthonormal-completion`. -/
theorem transpose_mul_eq_zero_of_completion [DecidableEq m] [DecidableEq n] [DecidableEq q]
    {Q : Matrix m q ℝ} {Qp : Matrix m n ℝ} (hQ : Qᵀ * Q = 1) (hQp : Qpᵀ * Qp = 1)
    (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1) : Qᵀ * Qp = 0 := by
  have h := congrArg (fun M => Qᵀ * M * Qp) hcomp
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one] at h
  rw [← Matrix.mul_assoc, hQ, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hQp,
    Matrix.mul_one] at h
  simpa using h

omit [Fintype n] in
/-- For an orthogonal completion `QQᵀ + QpQpᵀ = I` of `Q`, the residual lies in `range Qp`:
`(I − QQᵀ)A = Qp (Qpᵀ (I − QQᵀ)A)` (Chen–Persson, proof of `lem:completion`, item 1).
Atlas `projection-facts`. -/
theorem residual_eq_mul_transpose_mul_residual [DecidableEq m] [DecidableEq q] {r : Type*}
    [Fintype r] {Q : Matrix m q ℝ} {Qp : Matrix m r ℝ} (hQ : HasOrthonormalCols Q)
    (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1) (A : Matrix m n ℝ) :
    residual Q A = Qp * (Qpᵀ * residual Q A) := by
  have h : (Q * Qᵀ + Qp * Qpᵀ) * residual Q A = residual Q A := by
    rw [hcomp, Matrix.one_mul]
  rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, transpose_mul_residual hQ A,
    Matrix.mul_zero, zero_add] at h
  exact h.symm

/-- Columns of a matrix as vectors of Euclidean space. -/
private def col {k : ℕ} {ι : Type*} (V : Matrix (Fin k) ι ℝ) (j : ι) :
    EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i => V i j)

private lemma col_orthonormal {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix (Fin k) ι ℝ) (hV : Vᵀ * V = 1) : Orthonormal ℝ (col V) := by
  rw [orthonormal_iff_ite]
  intro a b
  have := congrFun (congrFun hV b) a
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at this
  simp only [col, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [this]
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]

/-- A real matrix with orthonormal columns has at most as many columns as rows.
Ported from the Prove2me workspace (Gaussian Random Matrices series). Atlas
`orthonormal-completion`. -/
theorem card_le_of_transpose_mul_self_eq_one {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix (Fin k) ι ℝ) (hV : Vᵀ * V = 1) : Fintype.card ι ≤ k := by
  have := (col_orthonormal V hV).linearIndependent.fintype_card_le_finrank
  simpa [finrank_euclideanSpace] using this

/-- **Orthogonal completion.** A real matrix `V` with orthonormal columns indexed by `ι`, placed
in the columns `e '' ι` of `Fin k`, extends to an orthogonal `k × k` matrix `W`.
Helper for HMT 2011 §10.2. Ported from the Prove2me workspace (Gaussian Random Matrices
series). Atlas `orthonormal-completion`.
atlas: orthonormal-completion -/
theorem exists_orthogonal_completion {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix (Fin k) ι ℝ) (hV : Vᵀ * V = 1) (e : ι ↪ Fin k) :
    ∃ W : Matrix (Fin k) (Fin k) ℝ, Wᵀ * W = 1 ∧ ∀ i j, W i (e j) = V i j := by
  classical
  let v : Fin k → EuclideanSpace ℝ (Fin k) := Function.extend e (col V) 0
  have hv : Orthonormal ℝ ((Set.range e).domRestrict v) := by
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
    have := (orthonormal_iff_ite.mp b.orthonormal) c a
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
    rw [show (if a = c then (1:ℝ) else 0) = if c = a then 1 else 0 by simp [eq_comm], ← this]
  · intro i j
    simp only [Matrix.of_apply]
    rw [hb (e j) ⟨j, rfl⟩]
    simp only [v, e.injective.extend_apply, col]

/-- **Orthonormal complement.** A matrix `Q` with orthonormal columns has a complement `Qp` with
orthonormal columns and `QQᵀ + QpQpᵀ = I` (here `Qp` has `k − q` columns). From
`exists_orthogonal_completion`. Atlas `orthonormal-completion`.
atlas: orthonormal-completion -/
theorem exists_orthonormal_complement {k q : ℕ} (Q : Matrix (Fin k) (Fin q) ℝ)
    (hQ : HasOrthonormalCols Q) :
    ∃ r : ℕ, ∃ Qp : Matrix (Fin k) (Fin r) ℝ,
      HasOrthonormalCols Qp ∧ Q * Qᵀ + Qp * Qpᵀ = 1 := by
  have hqk : q ≤ k := by simpa using card_le_of_transpose_mul_self_eq_one Q hQ
  obtain ⟨r, rfl⟩ : ∃ r, k = q + r := ⟨k - q, by omega⟩
  obtain ⟨W, hW, hWQ⟩ := exists_orthogonal_completion Q hQ (Fin.castAddEmb r)
  have hWW : W * Wᵀ = 1 := mul_eq_one_comm.mp hW
  refine ⟨r, Matrix.of fun i j => W i (Fin.natAdd q j), ?_, ?_⟩
  · ext a b
    have := congrFun (congrFun hW (Fin.natAdd q a)) (Fin.natAdd q b)
    simpa [Matrix.mul_apply, Matrix.one_apply, Fin.natAdd_inj] using this
  · ext a b
    have := congrFun (congrFun hWW a) b
    rw [Matrix.mul_apply, Fin.sum_univ_add] at this
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    rw [← this]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.transpose_apply]
    rw [← hWQ a j, ← hWQ b j]
    rfl

end NLAlib
