import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# The Frobenius inner product and norm

* `NLAlib.frobInner`, `NLAlib.frobSq`, `NLAlib.frobNorm`: the Frobenius inner product, its
  squared norm and the norm, over any `RCLike` field `𝕜`. The inner product is the real part
  `⟨A, B⟩_F = Re ∑ᵢⱼ conj(Aᵢⱼ) Bᵢⱼ = Re tr(AᴴB)`, the inner product of the underlying real
  Hilbert space (Mathlib's `real_inner`); the `𝕜`-valued pairing is `(Aᴴ * B).trace`. Over `ℝ`
  every definition is the old explicit sum by `rfl` (`frobInner_eq_sum_mul`).

## Contents

* Algebra of `frobInner` (bilinearity over real scalars, symmetry, trace forms
  `Re tr(AᴴB) = Re tr(ABᴴ)`, transpose and conjugate transpose).
* `frobSq` / `frobNorm`: `‖A‖_F² = ∑ᵢⱼ |Aᵢⱼ|²`, nonnegativity, definiteness, expansion of
  `frobSq (A ± B)`, Pythagoras, Cauchy–Schwarz, triangle inequality, transpose, `‖I‖_F² = n`.
* Rows: `‖A‖_F² = ∑ᵢ ‖Aᵢ‖²`, `‖Av‖² = ∑ᵢ (Aᵢ ⬝ v)²`, `‖Av‖² = v*(AᴴA)v`, `v ⬝ v ≥ 0`,
  `‖Bx‖² ≤ ‖B‖_F² ‖x‖²`.
* Products: `⟨PX, QY⟩_F = ⟨X, PᴴQY⟩_F` and invariance under multiplication by matrices with
  orthonormal columns (stated with the raw hypothesis `Qᴴ * Q = 1`, which is
  `NLAlib.HasOrthonormalCols Q` by definition).

Real statements written with `ᵀ` or real dot products keep their names as corollaries of the
general `conjTranspose` lemmas (RCLike round, decision D1). The spectral norm and the mixed
inequalities are in `NLAlib.Matrix.Norms.Core`, which imports this file.

The Frobenius algebra is ported from the LRA project (`LRA/Basic.lean`,
`LRA/Deterministic/RangeFinder.lean`, Chen–Persson formalization), namespace renamed.

Atlas: `matrix-norms-def`, `norms-frob-spec`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

/-! ### Definitions -/

/-- Frobenius inner product `⟨A, B⟩_F = Re ∑ᵢⱼ conj(Aᵢⱼ) Bᵢⱼ = Re tr(AᴴB)`; over `ℝ` it is
`∑ᵢⱼ Aᵢⱼ Bᵢⱼ` (`frobInner_eq_sum_mul`).
atlas: matrix-norms-def -/
def frobInner (A B : Matrix m n 𝕜) : ℝ := RCLike.re (∑ i, ∑ j, star (A i j) * B i j)

/-- Squared Frobenius norm `‖A‖_F²`.
atlas: matrix-norms-def -/
def frobSq (A : Matrix m n 𝕜) : ℝ := frobInner A A

/-- Frobenius norm `‖A‖_F`.
atlas: matrix-norms-def -/
def frobNorm (A : Matrix m n 𝕜) : ℝ := Real.sqrt (frobSq A)

/-- Over `ℝ` the Frobenius inner product is the plain entrywise sum (definitional). -/
theorem frobInner_eq_sum_mul (A B : Matrix m n ℝ) : frobInner A B = ∑ i, ∑ j, A i j * B i j :=
  rfl

/-- `⟨A, B⟩_F = ∑ᵢⱼ Re(conj(Aᵢⱼ) Bᵢⱼ)`. -/
theorem frobInner_eq_sum_re (A B : Matrix m n 𝕜) :
    frobInner A B = ∑ i, ∑ j, RCLike.re (star (A i j) * B i j) := by
  simp only [frobInner, map_sum]

/-! ### Algebra of the Frobenius inner product -/

/-- Symmetry of `⟨·,·⟩_F`. Standard; atlas `norms-frob-spec`. -/
theorem frobInner_comm (A B : Matrix m n 𝕜) : frobInner A B = frobInner B A := by
  unfold frobInner
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← RCLike.conj_re (star (B i j) * A i j), ← RCLike.star_def, star_mul, star_star]

/-- Trace form `⟨A, B⟩_F = Re tr(AᴴB)`. Standard; atlas `norms-frob-spec`. -/
theorem frobInner_eq_re_trace (A B : Matrix m n 𝕜) :
    frobInner A B = RCLike.re (Aᴴ * B).trace := by
  unfold frobInner Matrix.trace
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]

/-- Trace form `⟨A, B⟩_F = tr(AᵀB)` over `ℝ`. Standard; atlas `norms-frob-spec`. -/
theorem frobInner_eq_trace (A B : Matrix m n ℝ) : frobInner A B = (Aᵀ * B).trace := by
  simpa using frobInner_eq_re_trace A B

/-- The Frobenius pairing is also the real part of the trace of the row cross-product,
`⟨A, B⟩_F = Re tr(ABᴴ)`. Horn–Johnson §7.4. -/
theorem frobInner_eq_re_trace_mul_conjTranspose (A B : Matrix m n 𝕜) :
    frobInner A B = RCLike.re (A * Bᴴ).trace := by
  rw [frobInner_comm, frobInner_eq_re_trace, Matrix.trace_mul_comm]

/-- The Frobenius pairing is also the trace of the row cross-product, `⟨A, B⟩_F = tr(ABᵀ)`
over `ℝ`. Horn–Johnson §7.4; Procrustes equality helper. -/
theorem frobInner_eq_trace_mul_transpose (A B : Matrix m n ℝ) :
    frobInner A B = (A * Bᵀ).trace := by
  simpa using frobInner_eq_re_trace_mul_conjTranspose A B

/-- Additivity in the first argument. Atlas `norms-frob-spec`. -/
theorem frobInner_add_left (A B C : Matrix m n 𝕜) :
    frobInner (A + B) C = frobInner A C + frobInner B C := by
  unfold frobInner
  simp [add_mul, Finset.sum_add_distrib]

/-- Additivity in the second argument. Atlas `norms-frob-spec`. -/
theorem frobInner_add_right (A B C : Matrix m n 𝕜) :
    frobInner A (B + C) = frobInner A B + frobInner A C := by
  rw [frobInner_comm, frobInner_add_left, frobInner_comm B, frobInner_comm C]

/-- Subtraction in the first argument. Atlas `norms-frob-spec`. -/
theorem frobInner_sub_left (A B C : Matrix m n 𝕜) :
    frobInner (A - B) C = frobInner A C - frobInner B C := by
  unfold frobInner
  simp [sub_mul, Finset.sum_sub_distrib]

/-- Subtraction in the second argument. Atlas `norms-frob-spec`. -/
theorem frobInner_sub_right (A B C : Matrix m n 𝕜) :
    frobInner A (B - C) = frobInner A B - frobInner A C := by
  rw [frobInner_comm, frobInner_sub_left, frobInner_comm B, frobInner_comm C]

/-- Homogeneity in the first argument for a real scalar. Atlas `norms-frob-spec`. -/
theorem frobInner_smul_left (c : ℝ) (A B : Matrix m n 𝕜) :
    frobInner (c • A) B = c * frobInner A B := by
  unfold frobInner
  rw [← RCLike.re_ofReal_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, RCLike.real_smul_eq_coe_mul, star_mul', RCLike.star_def,
    RCLike.conj_ofReal, mul_assoc]

/-- Homogeneity in the second argument for a real scalar. Atlas `norms-frob-spec`. -/
theorem frobInner_smul_right (c : ℝ) (A B : Matrix m n 𝕜) :
    frobInner A (c • B) = c * frobInner A B := by
  rw [frobInner_comm, frobInner_smul_left, frobInner_comm]

/-- Negation in the first argument. Atlas `norms-frob-spec`. -/
theorem frobInner_neg_left (A B : Matrix m n 𝕜) : frobInner (-A) B = -frobInner A B := by
  unfold frobInner; simp [Finset.sum_neg_distrib]

/-- Negation in the second argument. Atlas `norms-frob-spec`. -/
theorem frobInner_neg_right (A B : Matrix m n 𝕜) : frobInner A (-B) = -frobInner A B := by
  rw [frobInner_comm, frobInner_neg_left, frobInner_comm]

/-- `⟨0, B⟩_F = 0`. Atlas `norms-frob-spec`. -/
@[simp] theorem frobInner_zero_left (B : Matrix m n 𝕜) :
    frobInner (0 : Matrix m n 𝕜) B = 0 := by
  unfold frobInner; simp

/-- `⟨A, 0⟩_F = 0`. Atlas `norms-frob-spec`. -/
@[simp] theorem frobInner_zero_right (A : Matrix m n 𝕜) :
    frobInner A (0 : Matrix m n 𝕜) = 0 := by
  unfold frobInner; simp

/-- `⟨Aᵀ, Bᵀ⟩_F = ⟨A, B⟩_F`. Atlas `norms-frob-spec`. -/
theorem frobInner_transpose (A B : Matrix m n 𝕜) : frobInner Aᵀ Bᵀ = frobInner A B := by
  unfold frobInner
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_comm]

/-- `⟨Aᴴ, Bᴴ⟩_F = ⟨A, B⟩_F`. Atlas `norms-frob-spec`. -/
theorem frobInner_conjTranspose (A B : Matrix m n 𝕜) : frobInner Aᴴ Bᴴ = frobInner A B := by
  rw [frobInner_eq_re_trace, Matrix.conjTranspose_conjTranspose,
    frobInner_eq_re_trace_mul_conjTranspose]

/-! ### Squared Frobenius norm and Frobenius norm -/

/-- `‖A‖_F² = ∑ᵢⱼ |Aᵢⱼ|²`. Atlas `norms-frob-spec`.
atlas: norms-frob-spec -/
theorem frobSq_eq_sum_norm_sq (A : Matrix m n 𝕜) : frobSq A = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  unfold frobSq frobInner
  simp only [map_sum, RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- `‖A‖_F² = ∑ᵢⱼ Aᵢⱼ²` over `ℝ`. Atlas `norms-frob-spec`.
atlas: norms-frob-spec -/
theorem frobSq_eq_sum_sq (A : Matrix m n ℝ) : frobSq A = ∑ i, ∑ j, A i j ^ 2 := by
  simp [frobSq_eq_sum_norm_sq]

/-- `‖A‖_F² ≥ 0`. Atlas `norms-frob-spec`. -/
theorem frobSq_nonneg (A : Matrix m n 𝕜) : 0 ≤ frobSq A := by
  rw [frobSq_eq_sum_norm_sq]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

/-- `‖0‖_F² = 0`. Atlas `norms-frob-spec`. -/
@[simp] theorem frobSq_zero : frobSq (0 : Matrix m n 𝕜) = 0 := by
  unfold frobSq; simp

/-- Definiteness: `‖A‖_F² = 0 ↔ A = 0`. Atlas `norms-frob-spec`. -/
theorem frobSq_eq_zero_iff (A : Matrix m n 𝕜) : frobSq A = 0 ↔ A = 0 := by
  rw [frobSq_eq_sum_norm_sq, Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg ‖A i j‖)]
  simp only [Finset.mem_univ, true_implies]
  constructor
  · intro h; ext i j
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖A i j‖)).1 (h i) j
      (Finset.mem_univ _)
    simpa using this
  · rintro rfl; simp

/-- `‖-A‖_F² = ‖A‖_F²`. Atlas `norms-frob-spec`. -/
theorem frobSq_neg (A : Matrix m n 𝕜) : frobSq (-A) = frobSq A := by
  unfold frobSq; rw [frobInner_neg_left, frobInner_neg_right, neg_neg]

/-- `‖A - B‖_F² = ‖B - A‖_F²`. Atlas `norms-frob-spec`. -/
theorem frobSq_sub_comm (A B : Matrix m n 𝕜) : frobSq (A - B) = frobSq (B - A) := by
  rw [← frobSq_neg, neg_sub]

/-- `‖cA‖_F² = c² ‖A‖_F²` for a real scalar `c`. Atlas `norms-frob-spec`. -/
theorem frobSq_smul (c : ℝ) (A : Matrix m n 𝕜) : frobSq (c • A) = c ^ 2 * frobSq A := by
  unfold frobSq; rw [frobInner_smul_left, frobInner_smul_right]; ring

/-- `‖cA‖_F² = |c|² ‖A‖_F²` for a scalar `c : 𝕜`. Atlas `norms-frob-spec`. -/
theorem frobSq_smul_eq_norm_sq_mul (c : 𝕜) (A : Matrix m n 𝕜) :
    frobSq (c • A) = ‖c‖ ^ 2 * frobSq A := by
  simp only [frobSq_eq_sum_norm_sq, Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow,
    Finset.mul_sum]

/-- `‖A + B‖_F² = ‖A‖_F² + 2⟨A, B⟩_F + ‖B‖_F²`. Atlas `norms-frob-spec`. -/
theorem frobSq_add (A B : Matrix m n 𝕜) :
    frobSq (A + B) = frobSq A + 2 * frobInner A B + frobSq B := by
  unfold frobSq
  rw [frobInner_add_left, frobInner_add_right, frobInner_add_right, frobInner_comm B A]
  ring

/-- `‖A - B‖_F² = ‖A‖_F² - 2⟨A, B⟩_F + ‖B‖_F²`. Atlas `norms-frob-spec`. -/
theorem frobSq_sub (A B : Matrix m n 𝕜) :
    frobSq (A - B) = frobSq A - 2 * frobInner A B + frobSq B := by
  unfold frobSq
  rw [frobInner_sub_left, frobInner_sub_right, frobInner_sub_right, frobInner_comm B A]
  ring

/-- Pythagoras: orthogonal summands have additive squared norms. Atlas `norms-frob-spec`. -/
theorem frobSq_add_of_frobInner_eq_zero (A B : Matrix m n 𝕜) (h : frobInner A B = 0) :
    frobSq (A + B) = frobSq A + frobSq B := by
  rw [frobSq_add, h]; ring

/-- Pythagoras for a difference of orthogonal matrices. Atlas `norms-frob-spec`. -/
theorem frobSq_sub_of_frobInner_eq_zero (A B : Matrix m n 𝕜) (h : frobInner A B = 0) :
    frobSq (A - B) = frobSq A + frobSq B := by
  rw [frobSq_sub, h]; ring

/-- `‖Aᵀ‖_F² = ‖A‖_F²`. Atlas `norms-frob-spec`. -/
theorem frobSq_transpose (A : Matrix m n 𝕜) : frobSq Aᵀ = frobSq A :=
  frobInner_transpose A A

/-- `‖Aᴴ‖_F² = ‖A‖_F²`. Atlas `norms-frob-spec`. -/
theorem frobSq_conjTranspose (A : Matrix m n 𝕜) : frobSq Aᴴ = frobSq A :=
  frobInner_conjTranspose A A

/-- `‖A‖_F ≥ 0`. Atlas `norms-frob-spec`. -/
theorem frobNorm_nonneg (A : Matrix m n 𝕜) : 0 ≤ frobNorm A := Real.sqrt_nonneg _

/-- `‖A‖_F² = frobSq A`. Atlas `norms-frob-spec`. -/
theorem frobNorm_sq (A : Matrix m n 𝕜) : frobNorm A ^ 2 = frobSq A :=
  Real.sq_sqrt (frobSq_nonneg A)

/-- Definiteness of `‖·‖_F`. Atlas `norms-frob-spec`. -/
theorem frobNorm_eq_zero_iff (A : Matrix m n 𝕜) : frobNorm A = 0 ↔ A = 0 := by
  rw [frobNorm, Real.sqrt_eq_zero (frobSq_nonneg A), frobSq_eq_zero_iff]

/-- `‖0‖_F = 0`. Atlas `norms-frob-spec`. -/
@[simp] theorem frobNorm_zero : frobNorm (0 : Matrix m n 𝕜) = 0 := by
  simp [frobNorm]

/-- `‖Aᵀ‖_F = ‖A‖_F`. Atlas `norms-frob-spec`. -/
theorem frobNorm_transpose (A : Matrix m n 𝕜) : frobNorm Aᵀ = frobNorm A := by
  rw [frobNorm, frobSq_transpose, frobNorm]

/-- `‖Aᴴ‖_F = ‖A‖_F`. Atlas `norms-frob-spec`. -/
theorem frobNorm_conjTranspose (A : Matrix m n 𝕜) : frobNorm Aᴴ = frobNorm A := by
  rw [frobNorm, frobSq_conjTranspose, frobNorm]

/-- `‖-A‖_F = ‖A‖_F`. Atlas `norms-frob-spec`. -/
theorem frobNorm_neg (A : Matrix m n 𝕜) : frobNorm (-A) = frobNorm A := by
  rw [frobNorm, frobSq_neg, frobNorm]

/-- `‖cA‖_F = |c| ‖A‖_F` for a real scalar `c`. Atlas `norms-frob-spec`. -/
theorem frobNorm_smul (c : ℝ) (A : Matrix m n 𝕜) : frobNorm (c • A) = |c| * frobNorm A := by
  rw [frobNorm, frobSq_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, frobNorm]

/-- `‖cA‖_F = |c| ‖A‖_F` for a scalar `c : 𝕜`. Atlas `norms-frob-spec`. -/
theorem frobNorm_smul_eq_norm_mul (c : 𝕜) (A : Matrix m n 𝕜) :
    frobNorm (c • A) = ‖c‖ * frobNorm A := by
  rw [frobNorm, frobSq_smul_eq_norm_sq_mul, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg c), frobNorm]

/-- `‖I‖_F² = n`. Atlas: `slq-error` (helper). -/
theorem frobNorm_one_sq [DecidableEq n] : frobNorm (1 : Matrix n n 𝕜) ^ 2 = Fintype.card n := by
  rw [frobNorm_sq, frobSq_eq_sum_norm_sq]
  simp [Matrix.one_apply, apply_ite (fun x : 𝕜 => ‖x‖ ^ 2)]

/-- The diagonal carries at most the whole Frobenius mass: `∑ᵢ |Aᵢᵢ|² ≤ ‖A‖_F²`. -/
theorem sum_norm_diag_sq_le_frobSq (A : Matrix n n 𝕜) :
    (∑ i, ‖A i i‖ ^ 2) ≤ frobSq A := by
  rw [frobSq_eq_sum_norm_sq]
  exact Finset.sum_le_sum fun i _ =>
    Finset.single_le_sum (f := fun j => ‖A i j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

/-- The diagonal carries at most the whole Frobenius mass: `∑ᵢ Aᵢᵢ² ≤ ‖A‖_F²` over `ℝ`.
Moved from the Hanson–Wright chain (HighDimProb commit c0cb8d9); atlas `hanson-wright` (helper). -/
theorem sum_diag_sq_le_frobSq (A : Matrix n n ℝ) :
    (∑ i, A i i ^ 2) ≤ frobSq A := by
  simpa using sum_norm_diag_sq_le_frobSq A

/-- `∑ᵢ Aᵢᵢ² ≤ ‖A‖_F²`, stated with `frobNorm A ^ 2`.
Moved from the Hanson–Wright chain (HighDimProb commit c0cb8d9); atlas `hanson-wright` (helper). -/
theorem sum_diag_sq_le_frobNorm_sq (A : Matrix n n ℝ) :
    (∑ i, A i i ^ 2) ≤ frobNorm A ^ 2 := by
  rw [frobNorm_sq]
  exact sum_diag_sq_le_frobSq A

/-! ### Rows and dot products -/

/-- `v ⬝ᵥ v ≥ 0` for real vectors (Mathlib has only the `star` forms
`dotProduct_star_self_nonneg`). Atlas `norms-frob-spec`. -/
theorem dotProduct_self_nonneg (v : n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

/-- `‖A‖_F² = ∑ᵢ Re(Aᵢ* Aᵢ)`, the sum of the squared norms of the rows. -/
theorem frobSq_eq_sum_re_star_dotProduct_self (A : Matrix m n 𝕜) :
    frobSq A = ∑ i, RCLike.re (star (A i) ⬝ᵥ A i) := by
  simp [frobSq, frobInner, dotProduct]

/-- `‖A‖_F² = ∑ᵢ ‖Aᵢ‖²`, the sum of the squared norms of the rows, over `ℝ`.
Atlas `norms-frob-spec`. -/
theorem frobSq_eq_sum_dotProduct_self (A : Matrix m n ℝ) : frobSq A = ∑ i, A i ⬝ᵥ A i := by
  simpa using frobSq_eq_sum_re_star_dotProduct_self A

omit [Fintype m] in
/-- `‖Av‖² = ∑ᵢ (Aᵢ ⬝ v)²`, written with dot products. Atlas `norms-frob-spec`. -/
theorem mulVec_dotProduct_mulVec_eq_sum_sq [Fintype m] (A : Matrix m n ℝ) (v : n → ℝ) :
    (A *ᵥ v) ⬝ᵥ (A *ᵥ v) = ∑ i, (A i ⬝ᵥ v) ^ 2 := by
  simp only [dotProduct, sq]
  rfl

/-- `‖Ax‖² = x* (AᴴA) x`, written with dot products. Atlas `norms-frob-spec`. -/
theorem star_mulVec_dotProduct_mulVec_self (A : Matrix m n 𝕜) (x : n → 𝕜) :
    star (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = star x ⬝ᵥ ((Aᴴ * A) *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (star x) Aᴴ, Matrix.star_mulVec]

/-- `‖Ax‖² = xᵀ (AᵀA) x` over `ℝ`. Helper for the Gram forms of `ose-def`; atlas
`norms-frob-spec`. -/
theorem mulVec_dotProduct_mulVec_self (A : Matrix m n ℝ) (x : n → ℝ) :
    (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ ((Aᵀ * A) *ᵥ x) := by
  simpa using star_mulVec_dotProduct_mulVec_self A x

/-- Row-wise Cauchy–Schwarz: `‖Ax‖₂² ≤ ‖A‖_F² ‖x‖₂²`, written with explicit sums.
Atlas `norms-frob-spec`. -/
theorem sum_norm_sq_mulVec_le_frobSq (A : Matrix m n 𝕜) (x : n → 𝕜) :
    ∑ i, ‖(A *ᵥ x) i‖ ^ 2 ≤ frobSq A * ∑ j, ‖x j‖ ^ 2 := by
  rw [frobSq_eq_sum_norm_sq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖(A *ᵥ x) i‖ ≤ ∑ j, ‖A i j‖ * ‖x j‖ := by
    simp only [Matrix.mulVec, dotProduct]
    exact (norm_sum_le _ _).trans (le_of_eq (by simp only [norm_mul]))
  calc ‖(A *ᵥ x) i‖ ^ 2 ≤ (∑ j, ‖A i j‖ * ‖x j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- Row-wise Cauchy–Schwarz over `ℝ`: `‖Ax‖₂² ≤ ‖A‖_F² ‖x‖₂²`, written with explicit sums.
Atlas `norms-frob-spec`. -/
theorem sum_sq_mulVec_le_frobSq (A : Matrix m n ℝ) (x : n → ℝ) :
    ∑ i, (A *ᵥ x) i ^ 2 ≤ frobSq A * ∑ j, x j ^ 2 := by
  simpa using sum_norm_sq_mulVec_le_frobSq A x

/-- Row-wise Cauchy–Schwarz, dot-product form: `‖Bx‖₂² ≤ ‖B‖_F² ‖x‖₂²`.
Atlas `norm-lipschitz`. -/
theorem mulVec_dotProduct_mulVec_le_frobSq_mul (B : Matrix m n ℝ) (x : n → ℝ) :
    (B *ᵥ x) ⬝ᵥ (B *ᵥ x) ≤ frobSq B * (x ⬝ᵥ x) := by
  have h := sum_sq_mulVec_le_frobSq B x
  simpa [dotProduct, sq] using h

/-! ### Cauchy–Schwarz and the triangle inequality -/

/-- Cauchy–Schwarz for the Frobenius inner product: `⟨A, B⟩_F ≤ ‖A‖_F ‖B‖_F`.
Standard; atlas `norms-frob-spec`.
atlas: norms-frob-spec -/
theorem frobInner_le_frobNorm_mul_frobNorm (A B : Matrix m n 𝕜) :
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
theorem abs_frobInner_le_frobNorm_mul_frobNorm (A B : Matrix m n 𝕜) :
    |frobInner A B| ≤ frobNorm A * frobNorm B := by
  rw [abs_le]
  constructor
  · have := frobInner_le_frobNorm_mul_frobNorm (-A) B
    rw [frobInner_neg_left, frobNorm_neg] at this
    linarith
  · exact frobInner_le_frobNorm_mul_frobNorm A B

/-- Triangle inequality `‖A + B‖_F ≤ ‖A‖_F + ‖B‖_F`. Atlas `norms-frob-spec`. -/
theorem frobNorm_add_le (A B : Matrix m n 𝕜) : frobNorm (A + B) ≤ frobNorm A + frobNorm B := by
  have hs : 0 ≤ frobNorm A + frobNorm B := add_nonneg (frobNorm_nonneg A) (frobNorm_nonneg B)
  rw [frobNorm, Real.sqrt_le_left hs, frobSq_add, add_sq, frobNorm_sq, frobNorm_sq]
  have := frobInner_le_frobNorm_mul_frobNorm A B
  nlinarith

/-- Triangle inequality for a difference. Atlas `norms-frob-spec`. -/
theorem frobNorm_sub_le (A B : Matrix m n 𝕜) : frobNorm (A - B) ≤ frobNorm A + frobNorm B := by
  rw [sub_eq_add_neg, ← frobNorm_neg B]; exact frobNorm_add_le A (-B)

/-! ### Interaction with matrix products -/

/-- `⟨P X, Q Y⟩_F = ⟨X, (Pᴴ Q) Y⟩_F`. Atlas `norms-frob-spec`. -/
theorem frobInner_mul_mul_conjTranspose (P : Matrix m p 𝕜) (X : Matrix p n 𝕜)
    (Q : Matrix m p 𝕜) (Y : Matrix p n 𝕜) :
    frobInner (P * X) (Q * Y) = frobInner X (Pᴴ * Q * Y) := by
  rw [frobInner_eq_re_trace, frobInner_eq_re_trace, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- `⟨P X, Q Y⟩_F = ⟨X, (Pᵀ Q) Y⟩_F` over `ℝ`. Atlas `norms-frob-spec`. -/
theorem frobInner_mul_mul (P : Matrix m p ℝ) (X : Matrix p n ℝ) (Q : Matrix m p ℝ)
    (Y : Matrix p n ℝ) : frobInner (P * X) (Q * Y) = frobInner X (Pᵀ * Q * Y) := by
  simpa using frobInner_mul_mul_conjTranspose P X Q Y

/-- Matrices with orthogonal column spaces (`Pᴴ Q = 0`) are Frobenius-orthogonal.
Atlas `norms-frob-spec`. -/
theorem frobInner_mul_mul_eq_zero_of_conjTranspose_mul_eq_zero {p' : Type*} [Fintype p']
    (P : Matrix m p 𝕜) (X : Matrix p n 𝕜) (Q : Matrix m p' 𝕜) (Y : Matrix p' n 𝕜)
    (h : Pᴴ * Q = 0) : frobInner (P * X) (Q * Y) = 0 := by
  rw [frobInner_eq_re_trace, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Pᴴ, h]
  simp

/-- Real matrices with orthogonal column spaces (`Pᵀ Q = 0`) are Frobenius-orthogonal.
Atlas `norms-frob-spec`. -/
theorem frobInner_mul_mul_eq_zero {p' : Type*} [Fintype p'] (P : Matrix m p ℝ)
    (X : Matrix p n ℝ) (Q : Matrix m p' ℝ) (Y : Matrix p' n ℝ) (h : Pᵀ * Q = 0) :
    frobInner (P * X) (Q * Y) = 0 :=
  frobInner_mul_mul_eq_zero_of_conjTranspose_mul_eq_zero P X Q Y (by simpa using h)

/-- Left multiplication by `Q` with `QᴴQ = I` preserves `⟨·,·⟩_F`. The hypothesis is
`NLAlib.HasOrthonormalCols Q` unfolded. Atlas `norms-frob-spec`. -/
theorem frobInner_mul_left_of_conjTranspose_mul_self [DecidableEq p] {Q : Matrix m p 𝕜}
    (hQ : Qᴴ * Q = 1) (X Y : Matrix p n 𝕜) :
    frobInner (Q * X) (Q * Y) = frobInner X Y := by
  rw [frobInner_mul_mul_conjTranspose, hQ, Matrix.one_mul]

/-- Left multiplication by a real `Q` with `QᵀQ = I` preserves `⟨·,·⟩_F`.
Atlas `norms-frob-spec`. -/
theorem frobInner_mul_left_of_orthonormal [DecidableEq p] {Q : Matrix m p ℝ}
    (hQ : Qᵀ * Q = 1) (X Y : Matrix p n ℝ) :
    frobInner (Q * X) (Q * Y) = frobInner X Y :=
  frobInner_mul_left_of_conjTranspose_mul_self (by simpa using hQ) X Y

/-- Unitary invariance, left: `‖Q X‖_F² = ‖X‖_F²` when `QᴴQ = I`. Atlas `norms-frob-spec`.
atlas: norms-frob-spec -/
theorem frobSq_mul_left_of_conjTranspose_mul_self [DecidableEq p] {Q : Matrix m p 𝕜}
    (hQ : Qᴴ * Q = 1) (X : Matrix p n 𝕜) : frobSq (Q * X) = frobSq X :=
  frobInner_mul_left_of_conjTranspose_mul_self hQ X X

/-- Orthogonal invariance, left: `‖Q X‖_F² = ‖X‖_F²` when `QᵀQ = I` over `ℝ`.
Atlas `norms-frob-spec`.
atlas: norms-frob-spec -/
theorem frobSq_mul_left_of_orthonormal [DecidableEq p] {Q : Matrix m p ℝ}
    (hQ : Qᵀ * Q = 1) (X : Matrix p n ℝ) : frobSq (Q * X) = frobSq X :=
  frobSq_mul_left_of_conjTranspose_mul_self (by simpa using hQ) X

/-- Unitary invariance, right: `‖X Vᴴ‖_F² = ‖X‖_F²` when `VᴴV = I`. Atlas `norms-frob-spec`. -/
theorem frobSq_mul_right_of_conjTranspose_mul_self [DecidableEq p] {V : Matrix n p 𝕜}
    (hV : Vᴴ * V = 1) (X : Matrix m p 𝕜) : frobSq (X * Vᴴ) = frobSq X := by
  rw [← frobSq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    frobSq_mul_left_of_conjTranspose_mul_self hV, frobSq_conjTranspose]

/-- Orthogonal invariance, right: `‖X Vᵀ‖_F² = ‖X‖_F²` when `VᵀV = I` over `ℝ`.
Atlas `norms-frob-spec`. -/
theorem frobSq_mul_right_of_orthonormal [DecidableEq p] {V : Matrix n p ℝ}
    (hV : Vᵀ * V = 1) (X : Matrix m p ℝ) : frobSq (X * Vᵀ) = frobSq X := by
  simpa using frobSq_mul_right_of_conjTranspose_mul_self (V := V) (by simpa using hV) X

end NLAlib
