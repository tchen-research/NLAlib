import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Matrix norms

The two norms every NLAlib statement is written in.

* `NLAlib.frobInner`, `NLAlib.frobSq`, `NLAlib.frobNorm`: the Frobenius inner product, its
  squared norm and the norm, as explicit sums so that algebraic identities close by `simp`/`ring`.
* `NLAlib.specNorm`: the spectral (ℓ₂ operator) norm, which is Mathlib's `‖A‖` under
  `open scoped Matrix.Norms.L2Operator`. Defined as a name so statements read like the sources;
  `specNorm_eq_norm` is the bridge.

## Contents

* Algebra of `frobInner` (bilinearity, symmetry, trace form, transpose).
* `frobSq` / `frobNorm`: nonnegativity, definiteness, expansion of `frobSq (A ± B)`, Pythagoras,
  Cauchy–Schwarz, triangle inequality, transpose.
* Products: `⟨PX, QY⟩_F = ⟨X, PᵀQY⟩_F`, invariance under multiplication by matrices with
  orthonormal columns (stated with the raw hypothesis `Qᵀ * Q = 1`, which is
  `NLAlib.HasOrthonormalCols Q` by definition).
* Rows: `‖A‖_F² = ∑ᵢ ‖Aᵢ‖²`, `‖Av‖² = ∑ᵢ (Aᵢ ⬝ v)²`, `‖Av‖² = vᵀ(AᵀA)v`, `v ⬝ v ≥ 0`.
* Spectral norm: transpose, submultiplicativity, `‖I‖₂ ≤ 1`, `‖P‖₂ ≤ 1` and `‖PᵀX‖₂ = ‖X‖₂` on
  `range P` for orthonormal columns, the mixed inequalities `‖AB‖_F ≤ ‖A‖₂ ‖B‖_F`,
  `‖AB‖_F ≤ ‖A‖_F ‖B‖₂`, `‖A‖₂ ≤ ‖A‖_F`, and the quadratic-form bound `|xᵀMx| ≤ ‖M‖₂ ‖x‖²`.
* Spectral-norm helpers (audit G0 C1): the triangle inequality, `‖AAᵀ‖₂ = ‖A‖₂²`,
  `‖P‖₂ ≤ 1` for orthogonal projectors, `‖(I − QQᵀ)A‖₂ ≤ ‖A‖₂`, and the block bound
  `‖X + Y‖₂² ≤ ‖X‖₂² + ‖Y‖₂²` when `XYᵀ = 0` (or `XᵀY = 0`).

The Frobenius algebra is ported from the LRA project (`LRA/Basic.lean`,
`LRA/Deterministic/RangeFinder.lean`, Chen–Persson formalization), namespace renamed.

Atlas: `norms-frob-spec`.
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

/-! ### Definitions -/

/-- Frobenius inner product `⟨A, B⟩_F = ∑ᵢⱼ Aᵢⱼ Bᵢⱼ`.
atlas: matrix-norms-def -/
def frobInner (A B : Matrix m n ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

/-- Squared Frobenius norm `‖A‖_F²`.
atlas: matrix-norms-def -/
def frobSq (A : Matrix m n ℝ) : ℝ := frobInner A A

/-- Frobenius norm `‖A‖_F`.
atlas: matrix-norms-def -/
def frobNorm (A : Matrix m n ℝ) : ℝ := Real.sqrt (frobSq A)

/-- Spectral norm `‖A‖₂`, the largest singular value: Mathlib's ℓ₂ operator norm.
atlas: matrix-norms-def -/
def specNorm [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) : ℝ := ‖A‖

/-- Bridge to Mathlib's ℓ₂ operator norm (`Matrix.Norms.L2Operator`). Atlas `norms-frob-spec`.
atlas: norms-frob-spec -/
theorem specNorm_eq_norm [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) :
    specNorm A = ‖A‖ := rfl

/-- `‖A‖₂ ≥ 0`. Atlas `norms-frob-spec`. -/
theorem specNorm_nonneg [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) : 0 ≤ specNorm A :=
  norm_nonneg A

/-! ### Algebra of the Frobenius inner product -/

/-- Symmetry of `⟨·,·⟩_F`. Standard; atlas `norms-frob-spec`. -/
theorem frobInner_comm (A B : Matrix m n ℝ) : frobInner A B = frobInner B A := by
  unfold frobInner
  simp_rw [mul_comm]

/-- Trace form `⟨A, B⟩_F = tr(AᵀB)`. Standard; atlas `norms-frob-spec`. -/
theorem frobInner_eq_trace (A B : Matrix m n ℝ) : frobInner A B = (Aᵀ * B).trace := by
  unfold frobInner Matrix.trace
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

/-- Additivity in the first argument. Atlas `norms-frob-spec`. -/
theorem frobInner_add_left (A B C : Matrix m n ℝ) :
    frobInner (A + B) C = frobInner A C + frobInner B C := by
  unfold frobInner
  simp [add_mul, Finset.sum_add_distrib]

/-- Additivity in the second argument. Atlas `norms-frob-spec`. -/
theorem frobInner_add_right (A B C : Matrix m n ℝ) :
    frobInner A (B + C) = frobInner A B + frobInner A C := by
  rw [frobInner_comm, frobInner_add_left, frobInner_comm B, frobInner_comm C]

/-- Subtraction in the first argument. Atlas `norms-frob-spec`. -/
theorem frobInner_sub_left (A B C : Matrix m n ℝ) :
    frobInner (A - B) C = frobInner A C - frobInner B C := by
  unfold frobInner
  simp [sub_mul, Finset.sum_sub_distrib]

/-- Subtraction in the second argument. Atlas `norms-frob-spec`. -/
theorem frobInner_sub_right (A B C : Matrix m n ℝ) :
    frobInner A (B - C) = frobInner A B - frobInner A C := by
  rw [frobInner_comm, frobInner_sub_left, frobInner_comm B, frobInner_comm C]

/-- Homogeneity in the first argument. Atlas `norms-frob-spec`. -/
theorem frobInner_smul_left (c : ℝ) (A B : Matrix m n ℝ) :
    frobInner (c • A) B = c * frobInner A B := by
  unfold frobInner
  simp [Finset.mul_sum, mul_assoc]

/-- Homogeneity in the second argument. Atlas `norms-frob-spec`. -/
theorem frobInner_smul_right (c : ℝ) (A B : Matrix m n ℝ) :
    frobInner A (c • B) = c * frobInner A B := by
  rw [frobInner_comm, frobInner_smul_left, frobInner_comm]

/-- Negation in the first argument. Atlas `norms-frob-spec`. -/
theorem frobInner_neg_left (A B : Matrix m n ℝ) : frobInner (-A) B = -frobInner A B := by
  unfold frobInner; simp [Finset.sum_neg_distrib]

/-- Negation in the second argument. Atlas `norms-frob-spec`. -/
theorem frobInner_neg_right (A B : Matrix m n ℝ) : frobInner A (-B) = -frobInner A B := by
  rw [frobInner_comm, frobInner_neg_left, frobInner_comm]

/-- `⟨0, B⟩_F = 0`. Atlas `norms-frob-spec`. -/
@[simp] theorem frobInner_zero_left (B : Matrix m n ℝ) :
    frobInner (0 : Matrix m n ℝ) B = 0 := by
  unfold frobInner; simp

/-- `⟨A, 0⟩_F = 0`. Atlas `norms-frob-spec`. -/
@[simp] theorem frobInner_zero_right (A : Matrix m n ℝ) :
    frobInner A (0 : Matrix m n ℝ) = 0 := by
  unfold frobInner; simp

/-- `⟨Aᵀ, Bᵀ⟩_F = ⟨A, B⟩_F`. Atlas `norms-frob-spec`. -/
theorem frobInner_transpose (A B : Matrix m n ℝ) : frobInner Aᵀ Bᵀ = frobInner A B := by
  unfold frobInner
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_comm]

/-! ### Squared Frobenius norm and Frobenius norm -/

/-- `‖A‖_F² = ∑ᵢⱼ Aᵢⱼ²`. Atlas `norms-frob-spec`.
atlas: norms-frob-spec -/
theorem frobSq_eq_sum_sq (A : Matrix m n ℝ) : frobSq A = ∑ i, ∑ j, A i j ^ 2 := by
  unfold frobSq frobInner; simp_rw [sq]

/-- `‖A‖_F² ≥ 0`. Atlas `norms-frob-spec`. -/
theorem frobSq_nonneg (A : Matrix m n ℝ) : 0 ≤ frobSq A := by
  unfold frobSq frobInner
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _

/-- `‖0‖_F² = 0`. Atlas `norms-frob-spec`. -/
@[simp] theorem frobSq_zero : frobSq (0 : Matrix m n ℝ) = 0 := by
  unfold frobSq frobInner; simp

/-- Definiteness: `‖A‖_F² = 0 ↔ A = 0`. Atlas `norms-frob-spec`. -/
theorem frobSq_eq_zero_iff (A : Matrix m n ℝ) : frobSq A = 0 ↔ A = 0 := by
  unfold frobSq frobInner
  constructor
  · intro h
    have h1 : ∀ i ∈ (Finset.univ : Finset m), ∑ j, A i j * A i j = 0 := by
      intro i _
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg (A i j))).1 h i
        (Finset.mem_univ _)
    ext i j
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (A i j))).1
      (h1 i (Finset.mem_univ _)) j (Finset.mem_univ _)
    simpa using this
  · rintro rfl; simp

/-- `‖-A‖_F² = ‖A‖_F²`. Atlas `norms-frob-spec`. -/
theorem frobSq_neg (A : Matrix m n ℝ) : frobSq (-A) = frobSq A := by
  unfold frobSq; rw [frobInner_neg_left, frobInner_neg_right, neg_neg]

/-- `‖A - B‖_F² = ‖B - A‖_F²`. Atlas `norms-frob-spec`. -/
theorem frobSq_sub_comm (A B : Matrix m n ℝ) : frobSq (A - B) = frobSq (B - A) := by
  rw [← frobSq_neg, neg_sub]

/-- `‖cA‖_F² = c² ‖A‖_F²`. Atlas `norms-frob-spec`. -/
theorem frobSq_smul (c : ℝ) (A : Matrix m n ℝ) : frobSq (c • A) = c ^ 2 * frobSq A := by
  unfold frobSq; rw [frobInner_smul_left, frobInner_smul_right]; ring

/-- `‖A + B‖_F² = ‖A‖_F² + 2⟨A, B⟩_F + ‖B‖_F²`. Atlas `norms-frob-spec`. -/
theorem frobSq_add (A B : Matrix m n ℝ) :
    frobSq (A + B) = frobSq A + 2 * frobInner A B + frobSq B := by
  unfold frobSq
  rw [frobInner_add_left, frobInner_add_right, frobInner_add_right, frobInner_comm B A]
  ring

/-- `‖A - B‖_F² = ‖A‖_F² - 2⟨A, B⟩_F + ‖B‖_F²`. Atlas `norms-frob-spec`. -/
theorem frobSq_sub (A B : Matrix m n ℝ) :
    frobSq (A - B) = frobSq A - 2 * frobInner A B + frobSq B := by
  unfold frobSq
  rw [frobInner_sub_left, frobInner_sub_right, frobInner_sub_right, frobInner_comm B A]
  ring

/-- Pythagoras: orthogonal summands have additive squared norms. Atlas `norms-frob-spec`. -/
theorem frobSq_add_of_frobInner_eq_zero (A B : Matrix m n ℝ) (h : frobInner A B = 0) :
    frobSq (A + B) = frobSq A + frobSq B := by
  rw [frobSq_add, h]; ring

/-- Pythagoras for a difference of orthogonal matrices. Atlas `norms-frob-spec`. -/
theorem frobSq_sub_of_frobInner_eq_zero (A B : Matrix m n ℝ) (h : frobInner A B = 0) :
    frobSq (A - B) = frobSq A + frobSq B := by
  rw [frobSq_sub, h]; ring

/-- `‖Aᵀ‖_F² = ‖A‖_F²`. Atlas `norms-frob-spec`. -/
theorem frobSq_transpose (A : Matrix m n ℝ) : frobSq Aᵀ = frobSq A :=
  frobInner_transpose A A

/-- `‖A‖_F ≥ 0`. Atlas `norms-frob-spec`. -/
theorem frobNorm_nonneg (A : Matrix m n ℝ) : 0 ≤ frobNorm A := Real.sqrt_nonneg _

/-- `‖A‖_F² = frobSq A`. Atlas `norms-frob-spec`. -/
theorem frobNorm_sq (A : Matrix m n ℝ) : frobNorm A ^ 2 = frobSq A :=
  Real.sq_sqrt (frobSq_nonneg A)

/-- Definiteness of `‖·‖_F`. Atlas `norms-frob-spec`. -/
theorem frobNorm_eq_zero_iff (A : Matrix m n ℝ) : frobNorm A = 0 ↔ A = 0 := by
  rw [frobNorm, Real.sqrt_eq_zero (frobSq_nonneg A), frobSq_eq_zero_iff]

/-- `‖0‖_F = 0`. Atlas `norms-frob-spec`. -/
@[simp] theorem frobNorm_zero : frobNorm (0 : Matrix m n ℝ) = 0 := by
  simp [frobNorm]

/-- `‖Aᵀ‖_F = ‖A‖_F`. Atlas `norms-frob-spec`. -/
theorem frobNorm_transpose (A : Matrix m n ℝ) : frobNorm Aᵀ = frobNorm A := by
  rw [frobNorm, frobSq_transpose, frobNorm]

/-- `‖-A‖_F = ‖A‖_F`. Atlas `norms-frob-spec`. -/
theorem frobNorm_neg (A : Matrix m n ℝ) : frobNorm (-A) = frobNorm A := by
  rw [frobNorm, frobSq_neg, frobNorm]

/-- `‖cA‖_F = |c| ‖A‖_F`. Atlas `norms-frob-spec`. -/
theorem frobNorm_smul (c : ℝ) (A : Matrix m n ℝ) : frobNorm (c • A) = |c| * frobNorm A := by
  rw [frobNorm, frobSq_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, frobNorm]

/-! ### Rows and dot products -/

/-- `v ⬝ᵥ v ≥ 0` for real vectors (Mathlib has only the `star` forms
`dotProduct_star_self_nonneg`). Atlas `norms-frob-spec`. -/
theorem dotProduct_self_nonneg (v : n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

/-- `‖A‖_F² = ∑ᵢ ‖Aᵢ‖²`, the sum of the squared norms of the rows. Atlas `norms-frob-spec`. -/
theorem frobSq_eq_sum_dotProduct_self (A : Matrix m n ℝ) : frobSq A = ∑ i, A i ⬝ᵥ A i := by
  simp [frobSq, frobInner, dotProduct]

omit [Fintype m] in
/-- `‖Av‖² = ∑ᵢ (Aᵢ ⬝ v)²`, written with dot products. Atlas `norms-frob-spec`. -/
theorem mulVec_dotProduct_mulVec_eq_sum_sq [Fintype m] (A : Matrix m n ℝ) (v : n → ℝ) :
    (A *ᵥ v) ⬝ᵥ (A *ᵥ v) = ∑ i, (A i ⬝ᵥ v) ^ 2 := by
  simp only [dotProduct, sq]
  rfl

/-- `‖Ax‖² = xᵀ (AᵀA) x`. Helper for the Gram forms of `ose-def`; atlas `norms-frob-spec`. -/
theorem mulVec_dotProduct_mulVec_self (A : Matrix m n ℝ) (x : n → ℝ) :
    (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ ((Aᵀ * A) *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x Aᵀ, Matrix.vecMul_transpose]

/-! ### Cauchy–Schwarz and the triangle inequality -/

/-- Cauchy–Schwarz for the Frobenius inner product: `⟨A, B⟩_F ≤ ‖A‖_F ‖B‖_F`.
Standard; atlas `norms-frob-spec`.
atlas: norms-frob-spec -/
theorem frobInner_le_frobNorm_mul_frobNorm (A B : Matrix m n ℝ) :
    frobInner A B ≤ frobNorm A * frobNorm B := by
  -- Discriminant argument: `0 ≤ ‖tA - B‖_F²` for `t = ⟨A, B⟩_F / ‖A‖_F²`.
  by_cases hA : frobSq A = 0
  · have : A = 0 := (frobSq_eq_zero_iff A).1 hA
    subst this; simp
  · have hApos : 0 < frobSq A := lt_of_le_of_ne (frobSq_nonneg A) (Ne.symm hA)
    set t := frobInner A B / frobSq A with ht
    have h0 : 0 ≤ frobSq (t • A - B) := frobSq_nonneg _
    rw [frobSq_sub, frobInner_smul_left, frobSq_smul] at h0
    have key : frobInner A B ^ 2 ≤ frobSq A * frobSq B := by
      have : t ^ 2 * frobSq A - 2 * (t * frobInner A B) + frobSq B =
          frobSq B - frobInner A B ^ 2 / frobSq A := by
        rw [ht]; field_simp; ring
      rw [this] at h0
      have := (sub_nonneg.1 h0)
      rwa [div_le_iff₀ hApos, mul_comm] at this
    have hprod : frobNorm A * frobNorm B = Real.sqrt (frobSq A * frobSq B) := by
      unfold frobNorm; rw [Real.sqrt_mul (frobSq_nonneg A)]
    rw [hprod]
    calc frobInner A B ≤ |frobInner A B| := le_abs_self _
      _ = Real.sqrt (frobInner A B ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (frobSq A * frobSq B) := Real.sqrt_le_sqrt key

/-- Cauchy–Schwarz, absolute-value form: `|⟨A, B⟩_F| ≤ ‖A‖_F ‖B‖_F`. Atlas `norms-frob-spec`. -/
theorem abs_frobInner_le_frobNorm_mul_frobNorm (A B : Matrix m n ℝ) :
    |frobInner A B| ≤ frobNorm A * frobNorm B := by
  rw [abs_le]
  constructor
  · have := frobInner_le_frobNorm_mul_frobNorm (-A) B
    rw [frobInner_neg_left, frobNorm_neg] at this
    linarith
  · exact frobInner_le_frobNorm_mul_frobNorm A B

/-- Triangle inequality `‖A + B‖_F ≤ ‖A‖_F + ‖B‖_F`. Atlas `norms-frob-spec`. -/
theorem frobNorm_add_le (A B : Matrix m n ℝ) : frobNorm (A + B) ≤ frobNorm A + frobNorm B := by
  have hs : 0 ≤ frobNorm A + frobNorm B := add_nonneg (frobNorm_nonneg A) (frobNorm_nonneg B)
  rw [frobNorm, Real.sqrt_le_left hs, frobSq_add, add_sq, frobNorm_sq, frobNorm_sq]
  have := frobInner_le_frobNorm_mul_frobNorm A B
  nlinarith

/-- Triangle inequality for a difference. Atlas `norms-frob-spec`. -/
theorem frobNorm_sub_le (A B : Matrix m n ℝ) : frobNorm (A - B) ≤ frobNorm A + frobNorm B := by
  rw [sub_eq_add_neg, ← frobNorm_neg B]; exact frobNorm_add_le A (-B)

/-! ### Interaction with matrix products -/

/-- `⟨P X, Q Y⟩_F = ⟨X, (Pᵀ Q) Y⟩_F`. Atlas `norms-frob-spec`. -/
theorem frobInner_mul_mul (P : Matrix m p ℝ) (X : Matrix p n ℝ) (Q : Matrix m p ℝ)
    (Y : Matrix p n ℝ) : frobInner (P * X) (Q * Y) = frobInner X (Pᵀ * Q * Y) := by
  rw [frobInner_eq_trace, frobInner_eq_trace, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- Matrices with orthogonal column spaces (`Pᵀ Q = 0`) are Frobenius-orthogonal.
Atlas `norms-frob-spec`. -/
theorem frobInner_mul_mul_eq_zero {p' : Type*} [Fintype p'] (P : Matrix m p ℝ)
    (X : Matrix p n ℝ) (Q : Matrix m p' ℝ) (Y : Matrix p' n ℝ) (h : Pᵀ * Q = 0) :
    frobInner (P * X) (Q * Y) = 0 := by
  rw [frobInner_eq_trace, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Pᵀ, h]
  simp

/-- Left multiplication by `Q` with `QᵀQ = I` preserves `⟨·,·⟩_F`. The hypothesis is
`NLAlib.HasOrthonormalCols Q` unfolded. Atlas `norms-frob-spec`. -/
theorem frobInner_mul_left_of_orthonormal [DecidableEq p] {Q : Matrix m p ℝ}
    (hQ : Qᵀ * Q = 1) (X Y : Matrix p n ℝ) :
    frobInner (Q * X) (Q * Y) = frobInner X Y := by
  rw [frobInner_mul_mul, hQ, Matrix.one_mul]

/-- Unitary invariance, left: `‖Q X‖_F² = ‖X‖_F²` when `QᵀQ = I`. Atlas `norms-frob-spec`.
atlas: norms-frob-spec -/
theorem frobSq_mul_left_of_orthonormal [DecidableEq p] {Q : Matrix m p ℝ}
    (hQ : Qᵀ * Q = 1) (X : Matrix p n ℝ) : frobSq (Q * X) = frobSq X :=
  frobInner_mul_left_of_orthonormal hQ X X

/-- Unitary invariance, right: `‖X Vᵀ‖_F² = ‖X‖_F²` when `VᵀV = I`. Atlas `norms-frob-spec`. -/
theorem frobSq_mul_right_of_orthonormal [DecidableEq p] {V : Matrix n p ℝ}
    (hV : Vᵀ * V = 1) (X : Matrix m p ℝ) : frobSq (X * Vᵀ) = frobSq X := by
  rw [← frobSq_transpose, Matrix.transpose_mul, Matrix.transpose_transpose,
    frobSq_mul_left_of_orthonormal hV, frobSq_transpose]

/-! ### Spectral norm -/

section Spectral

variable [DecidableEq m] [DecidableEq n]

/-- `‖Aᵀ‖₂ = ‖A‖₂`. Standard; atlas `norms-frob-spec`. -/
theorem specNorm_transpose (A : Matrix m n ℝ) : specNorm Aᵀ = specNorm A := by
  unfold specNorm
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.l2_opNorm_conjTranspose]

/-- Submultiplicativity `‖AB‖₂ ≤ ‖A‖₂ ‖B‖₂`. Standard; atlas `norms-frob-spec`.
atlas: norms-frob-spec -/
theorem specNorm_mul_le [DecidableEq p] (A : Matrix m n ℝ) (B : Matrix n p ℝ) :
    specNorm (A * B) ≤ specNorm A * specNorm B :=
  Matrix.l2_opNorm_mul A B

/-- Operator-norm bound in coordinates: `‖Ax‖₂² ≤ ‖A‖₂² ‖x‖₂²`, written with explicit sums.
Atlas `norms-frob-spec`. -/
theorem sum_sq_mulVec_le_specNorm_sq (A : Matrix m n ℝ) (x : n → ℝ) :
    ∑ i, (A *ᵥ x) i ^ 2 ≤ specNorm A ^ 2 * ∑ j, x j ^ 2 := by
  have h := A.l2_opNorm_mulVec (WithLp.toLp 2 x)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at h2
  simpa [specNorm] using h2

/-- Mixed inequality `‖AB‖_F² ≤ ‖A‖₂² ‖B‖_F²` (apply the operator bound to each column of `B`).
Standard (e.g. Golub–Van Loan, 4th ed., §2.3); atlas `norms-frob-spec`.
atlas: norms-frob-spec -/
theorem frobSq_mul_le_specNorm_sq_mul_frobSq (A : Matrix m n ℝ) (B : Matrix n p ℝ) :
    frobSq (A * B) ≤ specNorm A ^ 2 * frobSq B := by
  rw [frobSq_eq_sum_sq, frobSq_eq_sum_sq, Finset.sum_comm,
    Finset.sum_comm (f := fun i j => B i j ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have := sum_sq_mulVec_le_specNorm_sq A (fun k => B k j)
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

omit [DecidableEq m] in
/-- Mixed inequality `‖AB‖_F² ≤ ‖A‖_F² ‖B‖₂²` (transpose of the previous one).
Standard (e.g. Golub–Van Loan, 4th ed., §2.3); atlas `norms-frob-spec`.
atlas: norms-frob-spec -/
theorem frobSq_mul_le_frobSq_mul_specNorm_sq [DecidableEq p] (A : Matrix m n ℝ)
    (B : Matrix n p ℝ) :
    frobSq (A * B) ≤ frobSq A * specNorm B ^ 2 := by
  rw [← frobSq_transpose, Matrix.transpose_mul, ← frobSq_transpose A, ← specNorm_transpose B,
    mul_comm]
  exact frobSq_mul_le_specNorm_sq_mul_frobSq Bᵀ Aᵀ

/-- Mixed inequality `‖AB‖_F ≤ ‖A‖₂ ‖B‖_F`. Atlas `norms-frob-spec`. -/
theorem frobNorm_mul_le_specNorm_mul_frobNorm (A : Matrix m n ℝ) (B : Matrix n p ℝ) :
    frobNorm (A * B) ≤ specNorm A * frobNorm B := by
  refine le_of_pow_le_pow_left₀ two_ne_zero
    (mul_nonneg (specNorm_nonneg A) (frobNorm_nonneg B)) ?_
  rw [mul_pow, frobNorm_sq, frobNorm_sq]
  exact frobSq_mul_le_specNorm_sq_mul_frobSq A B

omit [DecidableEq m] in
/-- Mixed inequality `‖AB‖_F ≤ ‖A‖_F ‖B‖₂`. Atlas `norms-frob-spec`. -/
theorem frobNorm_mul_le_frobNorm_mul_specNorm [DecidableEq p] (A : Matrix m n ℝ)
    (B : Matrix n p ℝ) :
    frobNorm (A * B) ≤ frobNorm A * specNorm B := by
  refine le_of_pow_le_pow_left₀ two_ne_zero
    (mul_nonneg (frobNorm_nonneg A) (specNorm_nonneg B)) ?_
  rw [mul_pow, frobNorm_sq, frobNorm_sq]
  exact frobSq_mul_le_frobSq_mul_specNorm_sq A B

/-- The spectral norm of the identity is at most `1` (it is `1` when the index type is
nonempty and `0` when it is empty). Standard; atlas `norms-frob-spec`. -/
theorem specNorm_one_le : specNorm (1 : Matrix n n ℝ) ≤ 1 := by
  rw [specNorm_eq_norm, ← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simp

/-- A matrix with orthonormal columns has spectral norm at most `1`. The hypothesis is
`NLAlib.HasOrthonormalCols P` unfolded. Standard; atlas `norms-frob-spec`. -/
theorem specNorm_le_one_of_orthonormal {P : Matrix m n ℝ} (hP : Pᵀ * P = 1) :
    specNorm P ≤ 1 := by
  rw [specNorm_eq_norm]
  have h : ‖P‖ * ‖P‖ ≤ 1 := by
    have h1 := Matrix.l2_opNorm_conjTranspose_mul_self P
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hP] at h1
    rw [← h1]
    exact specNorm_one_le
  nlinarith [norm_nonneg P]

/-- Spectral isometry on the range of a matrix with orthonormal columns: if `PᵀP = I` and
`X = P (Pᵀ X)` (i.e. `range X ⊆ range P`), then `‖PᵀX‖₂ = ‖X‖₂`. Standard (used in
Chen–Persson, proof of `lem:tGN-core`, as `‖Q⊥ᵀA⊥‖ = ‖A⊥‖`); atlas `norms-frob-spec`. -/
theorem specNorm_transpose_mul_of_eq_mul [DecidableEq p] {P : Matrix m n ℝ} (hP : Pᵀ * P = 1)
    {X : Matrix m p ℝ} (hX : X = P * (Pᵀ * X)) : specNorm (Pᵀ * X) = specNorm X := by
  have hP1 : specNorm P ≤ 1 := specNorm_le_one_of_orthonormal hP
  have hPt : specNorm Pᵀ ≤ 1 := by rw [specNorm_transpose]; exact hP1
  apply le_antisymm
  · calc specNorm (Pᵀ * X) ≤ specNorm Pᵀ * specNorm X := specNorm_mul_le _ _
      _ ≤ 1 * specNorm X := by gcongr; exact specNorm_nonneg _
      _ = specNorm X := one_mul _
  · calc specNorm X = specNorm (P * (Pᵀ * X)) := by rw [← hX]
      _ ≤ specNorm P * specNorm (Pᵀ * X) := specNorm_mul_le _ _
      _ ≤ 1 * specNorm (Pᵀ * X) := by gcongr; exact specNorm_nonneg _
      _ = specNorm (Pᵀ * X) := one_mul _

omit [DecidableEq m] [DecidableEq n] in
/-- Row-wise Cauchy–Schwarz: `‖Ax‖₂² ≤ ‖A‖_F² ‖x‖₂²`, written with explicit sums.
Atlas `norms-frob-spec`. -/
theorem sum_sq_mulVec_le_frobSq (A : Matrix m n ℝ) (x : n → ℝ) :
    ∑ i, (A *ᵥ x) i ^ 2 ≤ frobSq A * ∑ j, x j ^ 2 := by
  rw [frobSq_eq_sum_sq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  simpa [Matrix.mulVec, dotProduct] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) x

/-- `‖A‖₂ ≤ ‖A‖_F`. Standard (Golub–Van Loan, 4th ed., eq. (2.3.7)); atlas `norms-frob-spec`.
atlas: norms-frob-spec -/
theorem specNorm_le_frobNorm (A : Matrix m n ℝ) : specNorm A ≤ frobNorm A := by
  unfold specNorm
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (frobNorm_nonneg A) fun x => ?_
  have h := sum_sq_mulVec_le_frobSq A x
  have hx : ∑ j, x.ofLp j ^ 2 = ‖x‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq x).symm
  have hy : ‖(Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A x‖ ^ 2 =
      ∑ i, (A *ᵥ x.ofLp) i ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]; rfl
  rw [hx, ← frobNorm_sq, ← mul_pow, ← hy] at h
  exact le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg (frobNorm_nonneg A) (norm_nonneg x)) h

/-- `‖A‖₂² ≤ ‖A‖_F²`. Atlas `norms-frob-spec`. -/
theorem specNorm_sq_le_frobSq (A : Matrix m n ℝ) : specNorm A ^ 2 ≤ frobSq A := by
  rw [← frobNorm_sq]
  exact pow_le_pow_left₀ (specNorm_nonneg A) (specNorm_le_frobNorm A) 2

/-- Submultiplicativity of the Frobenius norm, squared: `‖AB‖_F² ≤ ‖A‖_F² ‖B‖_F²`.
Atlas `norms-frob-spec`. -/
theorem frobSq_mul_le (A : Matrix m n ℝ) (B : Matrix n p ℝ) :
    frobSq (A * B) ≤ frobSq A * frobSq B :=
  (frobSq_mul_le_specNorm_sq_mul_frobSq A B).trans
    (mul_le_mul_of_nonneg_right (specNorm_sq_le_frobSq A) (frobSq_nonneg B))

/-- Submultiplicativity of the Frobenius norm: `‖AB‖_F ≤ ‖A‖_F ‖B‖_F`. Atlas `norms-frob-spec`. -/
theorem frobNorm_mul_le (A : Matrix m n ℝ) (B : Matrix n p ℝ) :
    frobNorm (A * B) ≤ frobNorm A * frobNorm B :=
  (frobNorm_mul_le_specNorm_mul_frobNorm A B).trans
    (mul_le_mul_of_nonneg_right (specNorm_le_frobNorm A) (frobNorm_nonneg B))

/-- Quadratic-form bound by the spectral norm: `|xᵀ M x| ≤ ‖M‖₂ ‖x‖²`. Helper for the Gram form
of `ose-def`; atlas `norms-frob-spec`. -/
theorem abs_dotProduct_mulVec_le_specNorm (M : Matrix n n ℝ) (x : n → ℝ) :
    |x ⬝ᵥ (M *ᵥ x)| ≤ specNorm M * (x ⬝ᵥ x) := by
  rw [specNorm_eq_norm]
  have h := M.l2_opNorm_mulVec (WithLp.toLp 2 x)
  have hx : ‖WithLp.toLp 2 x‖ ^ 2 = x ⬝ᵥ x := by
    rw [EuclideanSpace.real_norm_sq_eq]; simp [dotProduct, sq]
  have hcs :=
    abs_real_inner_le_norm (WithLp.toLp 2 x) ((EuclideanSpace.equiv n ℝ).symm (M *ᵥ x))
  have hi : inner ℝ (WithLp.toLp 2 x) ((EuclideanSpace.equiv n ℝ).symm (M *ᵥ x)) =
      x ⬝ᵥ (M *ᵥ x) := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rw [hi] at hcs
  calc |x ⬝ᵥ (M *ᵥ x)| ≤ _ := hcs
    _ ≤ ‖WithLp.toLp 2 x‖ * (‖M‖ * ‖WithLp.toLp 2 x‖) := by gcongr
    _ = ‖M‖ * (x ⬝ᵥ x) := by rw [← hx]; ring

/-- Triangle inequality for the spectral norm: `‖A + B‖₂ ≤ ‖A‖₂ + ‖B‖₂`. Standard
(Golub–Van Loan, 4th ed., §2.3); audit G0 C1; atlas `norms-frob-spec`.
atlas: norms-frob-spec -/
theorem specNorm_add_le (A B : Matrix m n ℝ) : specNorm (A + B) ≤ specNorm A + specNorm B :=
  norm_add_le A B

/-- `‖-A‖₂ = ‖A‖₂`. Atlas `norms-frob-spec`. -/
theorem specNorm_neg (A : Matrix m n ℝ) : specNorm (-A) = specNorm A := norm_neg A

/-- `‖A - B‖₂ = ‖B - A‖₂`. Atlas `norms-frob-spec`. -/
theorem specNorm_sub_comm (A B : Matrix m n ℝ) : specNorm (A - B) = specNorm (B - A) :=
  norm_sub_rev A B

/-- Triangle inequality for a difference: `‖A - B‖₂ ≤ ‖A‖₂ + ‖B‖₂`. Atlas `norms-frob-spec`. -/
theorem specNorm_sub_le (A B : Matrix m n ℝ) : specNorm (A - B) ≤ specNorm A + specNorm B :=
  norm_sub_le A B

/-- `‖AAᵀ‖₂ = ‖A‖₂²`, written for the row Gram matrix (the column form `‖AᵀA‖₂ = ‖A‖₂²` is
`specNorm_sq_eq_specNorm_transpose_mul_self` in `NLAlib.Matrix.SpectralBounds`). Standard
(the C*-identity); atlas `norms-frob-spec`.
atlas: norms-frob-spec -/
theorem specNorm_mul_transpose_self (A : Matrix m n ℝ) :
    specNorm (A * Aᵀ) = specNorm A ^ 2 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self Aᵀ
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] at h
  rw [specNorm_eq_norm, h, sq, ← specNorm_eq_norm, specNorm_transpose]

/-- An orthogonal projector (symmetric idempotent `P`) has spectral norm at most `1`
(it is `0` or `1`). Proof: `‖P‖₂ = ‖PᵀP‖₂ = ‖P‖₂²`. Standard (Golub–Van Loan, 4th ed., §2.5.1);
audit G0 C1; atlas `norms-frob-spec`, `projection-facts`.
atlas: projection-facts -/
theorem specNorm_le_one_of_isSymm_of_isIdempotentElem {P : Matrix n n ℝ} (hs : P.IsSymm)
    (hp : IsIdempotentElem P) : specNorm P ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self P
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, hs.eq, show P * P = P from hp] at h
  rw [specNorm_eq_norm]
  have h0 := norm_nonneg P
  by_contra hlt
  rw [not_le] at hlt
  nlinarith

/-- The residual `A − Q(QᵀA) = (I − QQᵀ)A` (`NLAlib.residual Q A`, which unfolds to this
expression) has spectral norm at most `‖A‖₂` when `QᵀQ = I` (`NLAlib.HasOrthonormalCols Q`
unfolded). Stated without `residual` because `NLAlib.Matrix.Projections` imports this file.
Standard (HMT 2011, §8.4); audit G0 C1 (`specNorm_residual_le`); atlas `projection-facts`.
atlas: norms-frob-spec -/
theorem specNorm_sub_mul_transpose_mul_le [DecidableEq p] {Q : Matrix m p ℝ} (hQ : Qᵀ * Q = 1)
    (A : Matrix m n ℝ) : specNorm (A - Q * (Qᵀ * A)) ≤ specNorm A := by
  set P : Matrix m m ℝ := 1 - Q * Qᵀ with hP
  have hs : P.IsSymm := by
    simp [hP, Matrix.IsSymm, Matrix.transpose_sub, Matrix.transpose_mul]
  have hp : IsIdempotentElem P := by
    change P * P = P
    have hQQ : Q * Qᵀ * (Q * Qᵀ) = Q * Qᵀ := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Qᵀ, hQ, Matrix.one_mul]
    rw [hP, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hQQ]
    abel
  have hPA : A - Q * (Qᵀ * A) = P * A := by
    rw [hP, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  rw [hPA]
  calc specNorm (P * A) ≤ specNorm P * specNorm A := specNorm_mul_le P A
    _ ≤ 1 * specNorm A :=
      mul_le_mul_of_nonneg_right (specNorm_le_one_of_isSymm_of_isIdempotentElem hs hp)
        (specNorm_nonneg A)
    _ = specNorm A := one_mul _

/-- Block bound for row-orthogonal summands: if `XYᵀ = 0` then
`‖X + Y‖₂² ≤ ‖X‖₂² + ‖Y‖₂²`, because `(X + Y)(X + Y)ᵀ = XXᵀ + YYᵀ`. Standard (used in HMT 2011,
proof of Thm 9.1); audit G0 C1; atlas `norms-frob-spec`.
atlas: norms-frob-spec -/
theorem specNorm_add_sq_le_of_mul_transpose_eq_zero {X Y : Matrix m n ℝ} (h : X * Yᵀ = 0) :
    specNorm (X + Y) ^ 2 ≤ specNorm X ^ 2 + specNorm Y ^ 2 := by
  have h' : Y * Xᵀ = 0 := by
    rw [← Matrix.transpose_transpose (Y * Xᵀ), Matrix.transpose_mul, Matrix.transpose_transpose,
      h, Matrix.transpose_zero]
  have hG : (X + Y) * (X + Y)ᵀ = X * Xᵀ + Y * Yᵀ := by
    rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h, h']
    abel
  rw [← specNorm_mul_transpose_self, ← specNorm_mul_transpose_self,
    ← specNorm_mul_transpose_self, hG]
  exact specNorm_add_le _ _

/-- Block bound for column-orthogonal summands: if `XᵀY = 0` then
`‖X + Y‖₂² ≤ ‖X‖₂² + ‖Y‖₂²` (transpose of `specNorm_add_sq_le_of_mul_transpose_eq_zero`).
Standard; audit G0 C1; atlas `norms-frob-spec`. -/
theorem specNorm_add_sq_le_of_transpose_mul_eq_zero {X Y : Matrix m n ℝ} (h : Xᵀ * Y = 0) :
    specNorm (X + Y) ^ 2 ≤ specNorm X ^ 2 + specNorm Y ^ 2 := by
  have h' : Xᵀ * Yᵀᵀ = 0 := by rw [Matrix.transpose_transpose]; exact h
  have := specNorm_add_sq_le_of_mul_transpose_eq_zero h'
  rwa [← Matrix.transpose_add, specNorm_transpose, specNorm_transpose, specNorm_transpose] at this

end Spectral

end NLAlib
