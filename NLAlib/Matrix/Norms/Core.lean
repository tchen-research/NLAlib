import Mathlib.LinearAlgebra.Matrix.Hermitian
import NLAlib.Matrix.Norms.Frobenius
import NLAlib.Matrix.Basic.Orthonormal

/-!
# Matrix norms

The two norms every NLAlib statement is written in, over any `RCLike` field `𝕜`.

* `NLAlib.frobInner`, `NLAlib.frobSq`, `NLAlib.frobNorm` (in `NLAlib.Matrix.Norms.Frobenius`,
 imported here): the Frobenius inner product `Re tr(AᴴB)`, its squared norm and the norm.
* `NLAlib.specNorm`: the spectral (ℓ₂ operator) norm, which is Mathlib's `‖A‖` under
 `open scoped Matrix.Norms.L2Operator`. Defined as a name so statements read like the sources;
 `specNorm_eq_norm` is the bridge.

## Contents

* Euclidean length: `‖v‖ = √(v ⬝ v) = √(∑ vⱼ²)` for real `EuclideanSpace`, positivity and the
 triangle inequalities for `√(v ⬝ v)`.
* Spectral norm: `‖0‖₂ = 0`, conjugate transpose, transpose and entrywise conjugation,
 submultiplicativity, `‖I‖₂ ≤ 1`, `‖P‖₂ ≤ 1` and `‖PᴴX‖₂ = ‖X‖₂` on `range P` for orthonormal
 columns, the mixed inequalities `‖AB‖_F ≤ ‖A‖₂ ‖B‖_F`, `‖AB‖_F ≤ ‖A‖_F ‖B‖₂`, `‖A‖₂ ≤ ‖A‖_F`,
 and the real quadratic-form bound `|xᵀMx| ≤ ‖M‖₂ ‖x‖²`.
* Spectral-norm helpers: the triangle inequality, `‖AAᴴ‖₂ = ‖A‖₂²`,
 `‖P‖₂ ≤ 1` for orthogonal projectors, `‖(I − QQᴴ)A‖₂ ≤ ‖A‖₂`, and the block bound
 `‖X + Y‖₂² ≤ ‖X‖₂² + ‖Y‖₂²` when `XYᴴ = 0` (or `XᴴY = 0`).

Statements are written with `ᴴ`; real users get `ᵀ` from the simp lemma
`Matrix.conjTranspose_eq_transpose_of_trivial` (foundation change F1; the real `ᵀ` corollaries of
the RCLike round are removed, see `docs/renames/2026-10-F1.json`). `specNorm` needs `DecidableEq`
only on the column index: Mathlib's ℓ₂ operator norm is built from `Matrix.toLin'`, whose inverse
uses `Pi.single`.

Further spectral-norm bounds (orthonormal-frame invariance, Lipschitz bounds, diagonal and
block-diagonal bounds) are in `NLAlib.Matrix.Norms.SpectralNormBounds`; invariance under
`Matrix.reindex` is in `NLAlib.Matrix.Norms.Reindex`.

Atlas: `norms-frob-spec`.
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

/-! ### Definition -/

/-- Spectral norm `‖A‖₂`, the largest singular value: Mathlib's ℓ₂ operator norm.
atlas: matrix-norms-def -/
def specNorm [DecidableEq n] (A : Matrix m n 𝕜) : ℝ := ‖A‖

/-- Bridge to Mathlib's ℓ₂ operator norm (`Matrix.Norms.L2Operator`). Atlas `norms-frob-spec`.
atlas: norms-frob-spec -/
theorem specNorm_eq_norm [DecidableEq n] (A : Matrix m n 𝕜) :
    specNorm A = ‖A‖ := rfl

/-- `‖A‖₂ ≥ 0`. Atlas `norms-frob-spec`. -/
theorem specNorm_nonneg [DecidableEq n] (A : Matrix m n 𝕜) : 0 ≤ specNorm A :=
  norm_nonneg A

/-! ### Euclidean length `√(v ⬝ v)` -/

/-- `‖v‖ = √(v ⬝ v)` for a real Euclidean vector. Atlas `norm-lipschitz` (helper). -/
theorem norm_eq_sqrt_dotProduct (v : EuclideanSpace ℝ n) : ‖v‖ = Real.sqrt (v.ofLp ⬝ᵥ v.ofLp) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [dotProduct, sq]

/-- `‖v‖₂ = √(v ⬝ v)` for the Euclidean norm of `WithLp.toLp 2 v`; `norm_eq_sqrt_dotProduct`
read from right to left. Atlas `norm-lipschitz`. -/
theorem sqrt_dotProduct_self_eq_norm (v : m → ℝ) :
    Real.sqrt (v ⬝ᵥ v) = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ m)‖ :=
  (norm_eq_sqrt_dotProduct _).symm

/-- `‖u‖ = √(∑ⱼ uⱼ²)` for a real Euclidean vector. Atlas `norm-lipschitz` (helper). -/
theorem norm_eq_sqrt_sum_sq {κ : Type*} [Fintype κ] (u : EuclideanSpace ℝ κ) :
    ‖u‖ = Real.sqrt (∑ j, u j ^ 2) := by
  rw [← EuclideanSpace.real_norm_sq_eq, Real.sqrt_sq (norm_nonneg _)]

/-- A nonzero vector has positive Euclidean length `√(v ⬝ᵥ v)`. -/
theorem sqrt_dotProduct_self_pos {ι : Type*} [Fintype ι] {v : ι → ℝ} (hv : v ≠ 0) :
    0 < Real.sqrt (v ⬝ᵥ v) :=
  Real.sqrt_pos.mpr (lt_of_le_of_ne (dotProduct_self_nonneg v)
    (Ne.symm (fun h => hv (dotProduct_self_eq_zero.mp h))))

/-- Triangle inequality for the Euclidean length `√(v ⬝ v)`. Atlas `norm-lipschitz`. -/
theorem sqrt_dotProduct_add_le (u v : m → ℝ) :
    Real.sqrt ((u + v) ⬝ᵥ (u + v)) ≤ Real.sqrt (u ⬝ᵥ u) + Real.sqrt (v ⬝ᵥ v) := by
  rw [sqrt_dotProduct_self_eq_norm, sqrt_dotProduct_self_eq_norm, sqrt_dotProduct_self_eq_norm,
    WithLp.toLp_add]
  exact norm_add_le _ _

/-- Euclidean triangle inequality for a difference, `‖u - v‖ ≤ ‖u‖ + ‖v‖`, in the
`Real.sqrt (v ⬝ᵥ v)` spelling. -/
theorem sqrt_dotProduct_sub_le {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    Real.sqrt ((u - v) ⬝ᵥ (u - v)) ≤ Real.sqrt (u ⬝ᵥ u) + Real.sqrt (v ⬝ᵥ v) := by
  have h := sqrt_dotProduct_add_le u (-v)
  simpa only [sub_eq_add_neg, neg_dotProduct, dotProduct_neg, neg_neg] using h

/-! ### Spectral norm -/

section Spectral

variable [DecidableEq n]

/-- `‖Aᴴ‖₂ = ‖A‖₂`. Standard; atlas `norms-frob-spec`. -/
theorem specNorm_conjTranspose [DecidableEq m] (A : Matrix m n 𝕜) : specNorm Aᴴ = specNorm A :=
  Matrix.l2_opNorm_conjTranspose A

/-- Operator-norm bound in coordinates: `‖Ax‖₂² ≤ ‖A‖₂² ‖x‖₂²`, written with explicit sums.
Atlas `norms-frob-spec`. -/
theorem sum_norm_sq_mulVec_le_specNorm_sq (A : Matrix m n 𝕜) (x : n → 𝕜) :
    ∑ i, ‖(A *ᵥ x) i‖ ^ 2 ≤ specNorm A ^ 2 * ∑ j, ‖x j‖ ^ 2 := by
  have h := A.l2_opNorm_mulVec (WithLp.toLp 2 x)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  simpa [specNorm] using h2

/-- Operator-norm bound in coordinates over `ℝ`: `‖Ax‖₂² ≤ ‖A‖₂² ‖x‖₂²`, written with explicit
sums. Atlas `norms-frob-spec`. -/
theorem sum_sq_mulVec_le_specNorm_sq (A : Matrix m n ℝ) (x : n → ℝ) :
    ∑ i, (A *ᵥ x) i ^ 2 ≤ specNorm A ^ 2 * ∑ j, x j ^ 2 := by
  simpa using sum_norm_sq_mulVec_le_specNorm_sq A x

/-- Entrywise conjugation does not increase the spectral norm (it preserves it,
`specNorm_map_star`): `(conj A) x = conj (A (conj x))`. -/
theorem specNorm_map_star_le (A : Matrix m n 𝕜) : specNorm (A.map star) ≤ specNorm A := by
  unfold specNorm
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun x => ?_
  have h := A.l2_opNorm_mulVec (WithLp.toLp 2 (star x.ofLp))
  have hx : ‖(WithLp.toLp 2 (star x.ofLp) : EuclideanSpace 𝕜 n)‖ = ‖x‖ := by
    simp [EuclideanSpace.norm_eq]
  have hv : A.map star *ᵥ x.ofLp = star (A *ᵥ star x.ofLp) := by
    ext i
    simp [Matrix.mulVec, dotProduct, star_sum]
  have hy : ‖(Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) (A.map star) x‖ =
      ‖(EuclideanSpace.equiv m 𝕜).symm (A *ᵥ star x.ofLp)‖ := by
    simp only [EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    change ‖(A.map star *ᵥ x.ofLp) i‖ ^ 2 = ‖(A *ᵥ star x.ofLp) i‖ ^ 2
    rw [hv, Pi.star_apply, norm_star]
  rw [hy, ← hx]
  simpa using h

/-- Entrywise conjugation preserves the spectral norm: `‖conj A‖₂ = ‖A‖₂`. -/
theorem specNorm_map_star (A : Matrix m n 𝕜) : specNorm (A.map star) = specNorm A := by
  refine le_antisymm (specNorm_map_star_le A) ?_
  have h := specNorm_map_star_le (A.map star)
  have hA : (A.map star).map star = A := by ext i j; simp
  rwa [hA] at h

/-- `‖Aᵀ‖₂ = ‖A‖₂`, since `Aᵀ` is the entrywise conjugate of `Aᴴ`. Standard; atlas
`norms-frob-spec`. -/
theorem specNorm_transpose [DecidableEq m] (A : Matrix m n 𝕜) : specNorm Aᵀ = specNorm A := by
  have h : Aᵀ = Aᴴ.map star := by ext i j; simp
  rw [h, specNorm_map_star, specNorm_conjTranspose]

/-- `‖0‖₂ = 0`. Atlas `norm-lipschitz` (helper). -/
theorem specNorm_zero : specNorm (0 : Matrix m n 𝕜) = 0 :=
  norm_zero

/-- Submultiplicativity `‖AB‖₂ ≤ ‖A‖₂ ‖B‖₂`. Standard; atlas `norms-frob-spec`.
atlas: norms-frob-spec -/
theorem specNorm_mul_le [DecidableEq p] (A : Matrix m n 𝕜) (B : Matrix n p 𝕜) :
    specNorm (A * B) ≤ specNorm A * specNorm B :=
  Matrix.l2_opNorm_mul A B

/-- Mixed inequality `‖AB‖_F² ≤ ‖A‖₂² ‖B‖_F²` (apply the operator bound to each column of `B`).
Standard (e.g. Golub–Van Loan, 4th ed. §2.3); atlas `norms-frob-spec`.
atlas: norms-frob-spec -/
theorem frobSq_mul_le_specNorm_sq_mul_frobSq (A : Matrix m n 𝕜) (B : Matrix n p 𝕜) :
    frobSq (A * B) ≤ specNorm A ^ 2 * frobSq B := by
  rw [frobSq_eq_sum_norm_sq, frobSq_eq_sum_norm_sq, Finset.sum_comm,
    Finset.sum_comm (f := fun i j => ‖B i j‖ ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have := sum_norm_sq_mulVec_le_specNorm_sq A (fun k => B k j)
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

/-- Mixed inequality `‖AB‖_F² ≤ ‖A‖_F² ‖B‖₂²` (transpose of the previous one).
Standard (e.g. Golub–Van Loan, 4th ed. §2.3); atlas `norms-frob-spec`.
atlas: norms-frob-spec -/
theorem frobSq_mul_le_frobSq_mul_specNorm_sq [DecidableEq p] (A : Matrix m n 𝕜)
    (B : Matrix n p 𝕜) :
    frobSq (A * B) ≤ frobSq A * specNorm B ^ 2 := by
  rw [← frobSq_transpose, Matrix.transpose_mul, ← frobSq_transpose A, ← specNorm_transpose B,
    mul_comm]
  exact frobSq_mul_le_specNorm_sq_mul_frobSq Bᵀ Aᵀ

/-- Mixed inequality `‖AB‖_F ≤ ‖A‖₂ ‖B‖_F`. Atlas `norms-frob-spec`. -/
theorem frobNorm_mul_le_specNorm_mul_frobNorm (A : Matrix m n 𝕜) (B : Matrix n p 𝕜) :
    frobNorm (A * B) ≤ specNorm A * frobNorm B := by
  refine le_of_pow_le_pow_left₀ two_ne_zero
    (mul_nonneg (specNorm_nonneg A) (frobNorm_nonneg B)) ?_
  rw [mul_pow, frobNorm_sq, frobNorm_sq]
  exact frobSq_mul_le_specNorm_sq_mul_frobSq A B

/-- Mixed inequality `‖AB‖_F ≤ ‖A‖_F ‖B‖₂`. Atlas `norms-frob-spec`. -/
theorem frobNorm_mul_le_frobNorm_mul_specNorm [DecidableEq p] (A : Matrix m n 𝕜)
    (B : Matrix n p 𝕜) :
    frobNorm (A * B) ≤ frobNorm A * specNorm B := by
  refine le_of_pow_le_pow_left₀ two_ne_zero
    (mul_nonneg (frobNorm_nonneg A) (specNorm_nonneg B)) ?_
  rw [mul_pow, frobNorm_sq, frobNorm_sq]
  exact frobSq_mul_le_frobSq_mul_specNorm_sq A B

/-- The spectral norm of the identity is at most `1` (it is `1` when the index type is
nonempty and `0` when it is empty). Standard; atlas `norms-frob-spec`. -/
theorem specNorm_one_le : specNorm (1 : Matrix n n 𝕜) ≤ 1 := by
  rw [specNorm_eq_norm, ← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simp

/-- A matrix with orthonormal columns (`PᴴP = I`) has spectral norm at most `1`. The hypothesis
is `NLAlib.HasOrthonormalCols P` unfolded. Standard; atlas `norms-frob-spec`. -/
theorem specNorm_le_one_of_orthonormal {P : Matrix m n 𝕜} (hP : Pᴴ * P = 1) :
    specNorm P ≤ 1 := by
  rw [specNorm_eq_norm]
  have h : ‖P‖ * ‖P‖ ≤ 1 := by
    have h1 := Matrix.l2_opNorm_conjTranspose_mul_self P
    rw [hP] at h1
    rw [← h1]
    exact specNorm_one_le
  nlinarith [norm_nonneg P]

/-- Spectral isometry on the range of a matrix with orthonormal columns: if `PᴴP = I` and
`X = P (Pᴴ X)` (i.e. `range X ⊆ range P`), then `‖PᴴX‖₂ = ‖X‖₂`. Standard (used in
Chen–Persson, proof of `lem:tGN-core`, as `‖Q⊥ᵀA⊥‖ = ‖A⊥‖`); atlas `norms-frob-spec`. -/
theorem specNorm_conjTranspose_mul_of_eq_mul [DecidableEq p] {P : Matrix m n 𝕜}
    (hP : Pᴴ * P = 1) {X : Matrix m p 𝕜} (hX : X = P * (Pᴴ * X)) :
    specNorm (Pᴴ * X) = specNorm X := by
  classical
  have hP1 : specNorm P ≤ 1 := specNorm_le_one_of_orthonormal hP
  have hPt : specNorm Pᴴ ≤ 1 := by rw [specNorm_conjTranspose]; exact hP1
  apply le_antisymm
  · calc specNorm (Pᴴ * X) ≤ specNorm Pᴴ * specNorm X := specNorm_mul_le _ _
      _ ≤ 1 * specNorm X := by gcongr; exact specNorm_nonneg _
      _ = specNorm X := one_mul _
  · calc specNorm X = specNorm (P * (Pᴴ * X)) := by rw [← hX]
      _ ≤ specNorm P * specNorm (Pᴴ * X) := specNorm_mul_le _ _
      _ ≤ 1 * specNorm (Pᴴ * X) := by gcongr; exact specNorm_nonneg _
      _ = specNorm (Pᴴ * X) := one_mul _

/-- `‖A‖₂ ≤ ‖A‖_F`. Standard (Golub–Van Loan, 4th ed. eq. (2.3.7)); atlas `norms-frob-spec`.
atlas: norms-frob-spec -/
theorem specNorm_le_frobNorm (A : Matrix m n 𝕜) : specNorm A ≤ frobNorm A := by
  unfold specNorm
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (frobNorm_nonneg A) fun x => ?_
  have h := sum_norm_sq_mulVec_le_frobSq A x.ofLp
  have hx : ∑ j, ‖x.ofLp j‖ ^ 2 = ‖x‖ ^ 2 := (EuclideanSpace.norm_sq_eq x).symm
  have hy : ‖(Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A x‖ ^ 2 =
      ∑ i, ‖(A *ᵥ x.ofLp) i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  rw [hx, ← frobNorm_sq, ← mul_pow, ← hy] at h
  exact le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg (frobNorm_nonneg A) (norm_nonneg x)) h

/-- `‖A‖₂² ≤ ‖A‖_F²`. Atlas `norms-frob-spec`. -/
theorem specNorm_sq_le_frobSq (A : Matrix m n 𝕜) : specNorm A ^ 2 ≤ frobSq A := by
  rw [← frobNorm_sq]
  exact pow_le_pow_left₀ (specNorm_nonneg A) (specNorm_le_frobNorm A) 2

/-- Submultiplicativity of the Frobenius norm, squared: `‖AB‖_F² ≤ ‖A‖_F² ‖B‖_F²`.
Atlas `norms-frob-spec`. -/
theorem frobSq_mul_le (A : Matrix m n 𝕜) (B : Matrix n p 𝕜) :
    frobSq (A * B) ≤ frobSq A * frobSq B :=
  (frobSq_mul_le_specNorm_sq_mul_frobSq A B).trans
    (mul_le_mul_of_nonneg_right (specNorm_sq_le_frobSq A) (frobSq_nonneg B))

/-- Submultiplicativity of the Frobenius norm: `‖AB‖_F ≤ ‖A‖_F ‖B‖_F`. Atlas `norms-frob-spec`. -/
theorem frobNorm_mul_le (A : Matrix m n 𝕜) (B : Matrix n p 𝕜) :
    frobNorm (A * B) ≤ frobNorm A * frobNorm B :=
  (frobNorm_mul_le_specNorm_mul_frobNorm A B).trans
    (mul_le_mul_of_nonneg_right (specNorm_le_frobNorm A) (frobNorm_nonneg B))

/-- Quadratic-form bound by the spectral norm: `|xᵀ M x| ≤ ‖M‖₂ ‖x‖²` over `ℝ`. Helper for the
Gram form of `ose-def`; atlas `norms-frob-spec`. -/
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
(Golub–Van Loan, 4th ed. §2.3); atlas `norms-frob-spec`.
atlas: norms-frob-spec -/
theorem specNorm_add_le (A B : Matrix m n 𝕜) : specNorm (A + B) ≤ specNorm A + specNorm B :=
  norm_add_le A B

/-- `‖-A‖₂ = ‖A‖₂`. Atlas `norms-frob-spec`. -/
theorem specNorm_neg (A : Matrix m n 𝕜) : specNorm (-A) = specNorm A := norm_neg A

/-- `‖A - B‖₂ = ‖B - A‖₂`. Atlas `norms-frob-spec`. -/
theorem specNorm_sub_comm (A B : Matrix m n 𝕜) : specNorm (A - B) = specNorm (B - A) :=
  norm_sub_rev A B

/-- Triangle inequality for a difference: `‖A - B‖₂ ≤ ‖A‖₂ + ‖B‖₂`. Atlas `norms-frob-spec`. -/
theorem specNorm_sub_le (A B : Matrix m n 𝕜) : specNorm (A - B) ≤ specNorm A + specNorm B :=
  norm_sub_le A B

/-- `‖AAᴴ‖₂ = ‖A‖₂²`, written for the row Gram matrix. Standard (the C*-identity); atlas
`norms-frob-spec`.
atlas: norms-frob-spec -/
theorem specNorm_mul_conjTranspose_self [DecidableEq m] (A : Matrix m n 𝕜) :
    specNorm (A * Aᴴ) = specNorm A ^ 2 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self Aᴴ
  rw [Matrix.conjTranspose_conjTranspose] at h
  rw [specNorm_eq_norm, h, sq, ← specNorm_eq_norm, specNorm_conjTranspose]

/-- An orthogonal projector (Hermitian idempotent `P`) has spectral norm at most `1`
(it is `0` or `1`). Proof: `‖P‖₂ = ‖PᴴP‖₂ = ‖P‖₂²`. Standard (Golub–Van Loan, 4th ed. §2.5.1);
atlas `norms-frob-spec`, `projection-facts`.
atlas: projection-facts -/
theorem _root_.Matrix.IsHermitian.specNorm_le_one_of_isIdempotentElem {P : Matrix n n 𝕜}
    (hs : P.IsHermitian) (hp : IsIdempotentElem P) : specNorm P ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self P
  rw [hs.eq, show P * P = P from hp] at h
  rw [specNorm_eq_norm]
  have h0 := norm_nonneg P
  by_contra hlt
  rw [not_le] at hlt
  nlinarith

/-- The residual `A − Q(QᴴA) = (I − QQᴴ)A` (`NLAlib.projResidual Q A`, which unfolds to this
expression) has spectral norm at most `‖A‖₂` when `QᴴQ = I` (`NLAlib.HasOrthonormalCols Q`
unfolded). Stated without `residual` because `NLAlib.Matrix.Subspaces.Projections` imports this file.
Standard (HMT 2011, §8.4); atlas `projection-facts`.
atlas: norms-frob-spec -/
theorem specNorm_sub_mul_conjTranspose_mul_le [DecidableEq p] {Q : Matrix m p 𝕜}
    (hQ : Qᴴ * Q = 1) (A : Matrix m n 𝕜) : specNorm (A - Q * (Qᴴ * A)) ≤ specNorm A := by
  classical
  set P : Matrix m m 𝕜 := 1 - Q * Qᴴ with hP
  have hs : P.IsHermitian := by
    simp [hP, Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
  have hp : IsIdempotentElem P := by
    change P * P = P
    have hQQ : Q * Qᴴ * (Q * Qᴴ) = Q * Qᴴ := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ, hQ, Matrix.one_mul]
    rw [hP, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hQQ]
    abel
  have hPA : A - Q * (Qᴴ * A) = P * A := by
    rw [hP, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  rw [hPA]
  calc specNorm (P * A) ≤ specNorm P * specNorm A := specNorm_mul_le P A
    _ ≤ 1 * specNorm A :=
      mul_le_mul_of_nonneg_right (hs.specNorm_le_one_of_isIdempotentElem hp)
        (specNorm_nonneg A)
    _ = specNorm A := one_mul _

/-- Block bound for row-orthogonal summands: if `XYᴴ = 0` then
`‖X + Y‖₂² ≤ ‖X‖₂² + ‖Y‖₂²`, because `(X + Y)(X + Y)ᴴ = XXᴴ + YYᴴ`. Standard (used in HMT 2011,
proof of Thm 9.1); atlas `norms-frob-spec`.
atlas: norms-frob-spec -/
theorem specNorm_add_sq_le_of_mul_conjTranspose_eq_zero {X Y : Matrix m n 𝕜} (h : X * Yᴴ = 0) :
    specNorm (X + Y) ^ 2 ≤ specNorm X ^ 2 + specNorm Y ^ 2 := by
  classical
  have h' : Y * Xᴴ = 0 := by
    rw [← Matrix.conjTranspose_conjTranspose (Y * Xᴴ), Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, h, Matrix.conjTranspose_zero]
  have hG : (X + Y) * (X + Y)ᴴ = X * Xᴴ + Y * Yᴴ := by
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h, h']
    abel
  rw [← specNorm_mul_conjTranspose_self, ← specNorm_mul_conjTranspose_self,
    ← specNorm_mul_conjTranspose_self, hG]
  exact specNorm_add_le _ _

/-- Block bound for column-orthogonal summands: if `XᴴY = 0` then
`‖X + Y‖₂² ≤ ‖X‖₂² + ‖Y‖₂²` (conjugate transpose of
`specNorm_add_sq_le_of_mul_conjTranspose_eq_zero`). Standard; atlas `norms-frob-spec`. -/
theorem specNorm_add_sq_le_of_conjTranspose_mul_eq_zero {X Y : Matrix m n 𝕜} (h : Xᴴ * Y = 0) :
    specNorm (X + Y) ^ 2 ≤ specNorm X ^ 2 + specNorm Y ^ 2 := by
  classical
  have h' : Xᴴ * Yᴴᴴ = 0 := by rw [Matrix.conjTranspose_conjTranspose]; exact h
  have := specNorm_add_sq_le_of_mul_conjTranspose_eq_zero h'
  rwa [← Matrix.conjTranspose_add, specNorm_conjTranspose, specNorm_conjTranspose,
    specNorm_conjTranspose] at this

/-! ### Euclidean quadratic forms and Gram errors (over `𝕜`) -/

omit [DecidableEq n] in
/-- The squared Euclidean norm is the real part of the self dot product:
`‖x‖² = Re (x̄ ⬝ x)` over `ℝ` or `ℂ`. Source: the Euclidean inner product definition; supports
`leverage-sampling-ose`. -/
theorem norm_toLp_sq_eq_re_star_dotProduct (x : n → 𝕜) :
    ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ ^ 2 = RCLike.re (star x ⬝ᵥ x) := by
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜), EuclideanSpace.inner_toLp_toLp, dotProduct_comm]

omit [DecidableEq n] in
/-- The squared Euclidean norm of a real vector is its self dot product: `‖x‖₂² = x ⬝ x`. The
real bridge between `‖WithLp.toLp 2 x‖` and the dot-product spelling (STANDARDS §3). -/
theorem norm_toLp_sq_eq_dotProduct_self (x : n → ℝ) :
    ‖WithLp.toLp 2 x‖ ^ 2 = x ⬝ᵥ x := by
  rw [norm_toLp_sq_eq_re_star_dotProduct, star_trivial, RCLike.re_to_real]

omit [DecidableEq n] in
/-- The Euclidean norm of a real vector is the square root of its self dot product. -/
theorem norm_toLp_eq_sqrt_dotProduct_self (x : n → ℝ) :
    ‖WithLp.toLp 2 x‖ = √(x ⬝ᵥ x) := by
  rw [← norm_toLp_sq_eq_dotProduct_self, Real.sqrt_sq (norm_nonneg _)]

/-- A square matrix's quadratic form is bounded by its spectral norm times the vector's squared
Euclidean norm: `|Re (x̄ ⬝ Hx)| ≤ ‖H‖₂ ‖x‖₂²`. Cauchy–Schwarz and the operator norm definition;
supports `leverage-sampling-ose`. -/
theorem abs_re_star_dotProduct_mulVec_le_specNorm (H : Matrix n n 𝕜) (x : n → 𝕜) :
    |RCLike.re (star x ⬝ᵥ (H *ᵥ x))| ≤ specNorm H *
      ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ ^ 2 := by
  rw [specNorm_eq_norm]
  have hin : inner 𝕜 (WithLp.toLp 2 x : EuclideanSpace 𝕜 n)
      (WithLp.toLp 2 (H *ᵥ x) : EuclideanSpace 𝕜 n) = star x ⬝ᵥ (H *ᵥ x) := by
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  have hh := norm_inner_le_norm (𝕜 := 𝕜) (WithLp.toLp 2 x : EuclideanSpace 𝕜 n)
    (WithLp.toLp 2 (H *ᵥ x) : EuclideanSpace 𝕜 n)
  rw [hin] at hh
  calc _ ≤ ‖star x ⬝ᵥ (H *ᵥ x)‖ := RCLike.abs_re_le_norm _
    _ ≤ _ := hh
    _ ≤ ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ *
        (‖H‖ * ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖) := by
      gcongr
      exact H.l2_opNorm_mulVec (WithLp.toLp 2 x)
    _ = _ := by ring

/-- A Gram error bounded by `ε`, `‖TᴴT − I‖₂ ≤ ε`, keeps every squared Euclidean norm
`‖Tx‖₂²` between `(1−ε)‖x‖₂²` and `(1+ε)‖x‖₂²`, over `ℝ` or `ℂ`. Woodruff 2014, §2.1
(subspace embeddings from Gram errors); supports `leverage-sampling-ose`. -/
theorem norm_mulVec_sq_bounds_of_specNorm_gram_sub_one_le (T : Matrix m n 𝕜) {ε : ℝ}
    (h : specNorm (Tᴴ * T - 1) ≤ ε) (x : n → 𝕜) :
    (1 - ε) * ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ ^ 2 ≤
        ‖(WithLp.toLp 2 (T *ᵥ x) : EuclideanSpace 𝕜 m)‖ ^ 2 ∧
      ‖(WithLp.toLp 2 (T *ᵥ x) : EuclideanSpace 𝕜 m)‖ ^ 2 ≤
        (1 + ε) * ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ ^ 2 := by
  have hq : RCLike.re (star x ⬝ᵥ ((Tᴴ * T - 1) *ᵥ x)) =
      ‖(WithLp.toLp 2 (T *ᵥ x) : EuclideanSpace 𝕜 m)‖ ^ 2 -
        ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ ^ 2 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, map_sub,
      norm_toLp_sq_eq_re_star_dotProduct, norm_toLp_sq_eq_re_star_dotProduct,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
  have hh := (abs_re_star_dotProduct_mulVec_le_specNorm (Tᴴ * T - 1) x).trans
    (mul_le_mul_of_nonneg_right h (sq_nonneg _))
  rw [hq, abs_le] at hh
  constructor <;> nlinarith

omit [DecidableEq n] in
/-- Real vectors embedded in `𝕜` coordinates (`ℝ` or `ℂ`) have the same Euclidean norm.
Source: entrywise squared norms; supports atlas `srht-ose`. -/
theorem norm_toLp_ofReal_eq (x : n → ℝ) :
    ‖(WithLp.toLp 2 (fun j => algebraMap ℝ 𝕜 (x j)) : EuclideanSpace 𝕜 n)‖ =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [RCLike.algebraMap_eq_ofReal, RCLike.norm_ofReal, Real.norm_eq_abs]

/-- The real spectral norm is bounded by the spectral norm of the extension of the matrix to
`𝕜` (`ℝ` or `ℂ`): `‖A‖₂ ≤ ‖A.map (algebraMap ℝ 𝕜)‖₂`. Restricting the extended operator to real
vectors; supports `srht-ose`. -/
theorem specNorm_le_specNorm_map_ofReal (A : Matrix m n ℝ) :
    specNorm A ≤ specNorm (A.map (algebraMap ℝ 𝕜)) := by
  rw [specNorm_eq_norm, specNorm_eq_norm, Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have h := (A.map (algebraMap ℝ 𝕜)).l2_opNorm_mulVec
    (WithLp.toLp 2 (fun j => algebraMap ℝ 𝕜 (x.ofLp j)) : EuclideanSpace 𝕜 n)
  have hv : A.map (algebraMap ℝ 𝕜) *ᵥ (fun j => algebraMap ℝ 𝕜 (x.ofLp j)) =
      fun i => algebraMap ℝ 𝕜 ((A *ᵥ x.ofLp) i) := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
  rw [hv] at h
  change ‖(WithLp.toLp 2 (fun i => algebraMap ℝ 𝕜 ((A *ᵥ x.ofLp) i)) : EuclideanSpace 𝕜 m)‖ ≤
    ‖A.map (algebraMap ℝ 𝕜)‖ *
      ‖(WithLp.toLp 2 (fun j => algebraMap ℝ 𝕜 (x.ofLp j)) : EuclideanSpace 𝕜 n)‖ at h
  rw [norm_toLp_ofReal_eq, norm_toLp_ofReal_eq] at h
  exact h

end Spectral

end NLAlib
