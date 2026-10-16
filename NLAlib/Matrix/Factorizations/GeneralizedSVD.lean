import NLAlib.Matrix.Spectral.NormalizedPSDPair
import Mathlib.Data.Matrix.ColumnRowPartitioned
/-!+# Normalized GSVD with the common-kernel block

An invertible change of domain coordinates diagonalizes both Gram matrices.
The diagonal pairs lie on the unit quarter-circle on the active coordinates
and vanish together on the common kernel. The active-coordinate count is
exactly the rank of the stacked matrix. Coordinates are labeled by their
active set; reordering this set first gives the usual `q` leading columns.

Source: Golub–Van Loan (2013), §8.7; matrix-toolkit re-derivation §27.
Atlas: `gsvd-normalized-pair`.
-/
noncomputable section
open Matrix
open scoped Matrix ComplexOrder
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*}
  [Fintype m] [Fintype n] [Fintype p] [DecidableEq n]

/-- Normalized generalized singular coordinates, including common-kernel
coordinates. The invertible domain matrix is not assumed unitary. -/
structure IsNormalizedGSVD (A : Matrix m n 𝕜) (L : Matrix p n 𝕜)
    (X : Matrix n n 𝕜) (c s : n → ℝ) : Prop where
  invertible : IsUnit X
  left_gram : Xᴴ * (Aᴴ * A) * X = diagonal (fun i => (c i ^ 2 : 𝕜))
  right_gram : Xᴴ * (Lᴴ * L) * X = diagonal (fun i => (s i ^ 2 : 𝕜))
  left_nonneg : ∀ i, 0 ≤ c i
  right_nonneg : ∀ i, 0 ≤ s i
  normalized : ∀ i, c i ^ 2 + s i ^ 2 = 0 ∨ c i ^ 2 + s i ^ 2 = 1

/-- Every real or complex matrix pair has a normalized GSVD, including
arbitrary rank deficiency and an arbitrary common kernel.
atlas: gsvd-normalized-pair (partial) -/
theorem exists_isNormalizedGSVD (A : Matrix m n 𝕜) (L : Matrix p n 𝕜) :
    ∃ X c s, IsNormalizedGSVD A L X c s := by
  obtain ⟨X, a, b, hX, hA, hL, ha, hb, hab⟩ :=
    exists_normalized_psd_pair_congruence
      (Matrix.posSemidef_conjTranspose_mul_self A) (Matrix.posSemidef_conjTranspose_mul_self L)
  refine ⟨X, fun i => Real.sqrt (a i), fun i => Real.sqrt (b i), hX, ?_, ?_,
    fun i => Real.sqrt_nonneg _, fun i => Real.sqrt_nonneg _, ?_⟩
  · simpa only [← RCLike.ofReal_pow, Real.sq_sqrt (ha _)] using hA
  · simpa only [← RCLike.ofReal_pow, Real.sq_sqrt (hb _)] using hL
  · simpa only [Real.sq_sqrt (ha _), Real.sq_sqrt (hb _)] using hab

/-- The stacked Gram matrix in normalized GSVD coordinates. -/
theorem IsNormalizedGSVD.stack_gram {A : Matrix m n 𝕜} {L : Matrix p n 𝕜}
    {X : Matrix n n 𝕜} {c s : n → ℝ} (h : IsNormalizedGSVD A L X c s) :
    Xᴴ * ((Matrix.fromRows A L)ᴴ * Matrix.fromRows A L) * X =
      diagonal (fun i => ((c i ^ 2 + s i ^ 2 : ℝ) : 𝕜)) := by
  rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromRows,
    Matrix.mul_add, Matrix.add_mul, h.left_gram, h.right_gram, Matrix.diagonal_add]
  simp only [map_add, map_pow]

/-- The number of active generalized singular pairs equals the actual
stacked rank; all zero and empty block endpoints are included.
atlas: gsvd-normalized-pair (partial) -/
theorem IsNormalizedGSVD.rank_stack_eq_card_active {A : Matrix m n 𝕜} {L : Matrix p n 𝕜}
    {X : Matrix n n 𝕜} {c s : n → ℝ} (h : IsNormalizedGSVD A L X c s) :
    (Matrix.fromRows A L).rank = Fintype.card {i // c i ^ 2 + s i ^ 2 = 1} := by
  classical
  have he := congrArg Matrix.rank h.stack_gram
  rw [Matrix.rank_mul_eq_left_of_isUnit_det X _ ((Matrix.isUnit_iff_isUnit_det X).mp h.invertible),
    Matrix.rank_mul_eq_right_of_isUnit_det Xᴴ _ ((Matrix.isUnit_iff_isUnit_det Xᴴ).mp
      ((Matrix.isUnit_conjTranspose X).mpr h.invertible)), Matrix.rank_conjTranspose_mul_self,
    Matrix.rank_diagonal] at he
  convert he using 1
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro i
  rcases h.normalized i with hi | hi <;> simp [hi]

/-- Normalized coordinates describe the entire common kernel: exactly
the active coordinates must vanish. This identifies the zero-column block.
atlas: gsvd-normalized-pair (partial) -/
theorem IsNormalizedGSVD.common_kernel_iff {A : Matrix m n 𝕜} {L : Matrix p n 𝕜}
    {X : Matrix n n 𝕜} {c s : n → ℝ} (h : IsNormalizedGSVD A L X c s) (y : n → 𝕜) :
    (A *ᵥ (X *ᵥ y) = 0 ∧ L *ᵥ (X *ᵥ y) = 0) ↔
      ∀ i, c i ^ 2 + s i ^ 2 = 1 → y i = 0 := by
  let C := Matrix.fromRows A L
  have hstack : (A *ᵥ (X *ᵥ y) = 0 ∧ L *ᵥ (X *ᵥ y) = 0) ↔ C *ᵥ (X *ᵥ y) = 0 := by
    change (A *ᵥ (X *ᵥ y) = 0 ∧ L *ᵥ (X *ᵥ y) = 0) ↔
      Matrix.fromRows A L *ᵥ (X *ᵥ y) = 0
    rw [Matrix.fromRows_mulVec]
    constructor
    · rintro ⟨hA, hL⟩; ext i; cases i <;> simp [hA, hL]
    · intro hh
      constructor
      · ext i; exact congrFun hh (Sum.inl i)
      · ext i; exact congrFun hh (Sum.inr i)
  rw [hstack, ← Matrix.conjTranspose_mul_self_mulVec_eq_zero C]
  have hi : Function.Injective Xᴴ.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_conjTranspose X).mpr h.invertible)
  rw [← hi.eq_iff]
  rw [Matrix.mulVec_zero, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h.stack_gram]
  rw [funext_iff]
  simp only [Matrix.mulVec_diagonal, Pi.zero_apply]
  constructor
  · intro hh i hi
    simpa only [hi, RCLike.ofReal_one, one_mul] using hh i
  · intro hh i
    rcases h.normalized i with hi | hi
    · rw [hi, RCLike.ofReal_zero, zero_mul]
    · rw [hi, RCLike.ofReal_one, one_mul, hh i hi]

/-- The nonzero left generalized singular columns are orthonormal after
division by their generalized singular values. -/
theorem IsNormalizedGSVD.left_orthonormal {A : Matrix m n 𝕜} {L : Matrix p n 𝕜}
    {X : Matrix n n 𝕜} {c s : n → ℝ} (h : IsNormalizedGSVD A L X c s) :
    HasOrthonormalCols (Matrix.of (fun i (j : {j // 0 < c j}) =>
      (A * X) i j / (c j : 𝕜))) := by
  classical
  have hg : (A * X)ᴴ * (A * X) = diagonal (fun i => (c i ^ 2 : 𝕜)) := by
    simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using h.left_gram
  ext i j
  have hij := congrArg (fun M : Matrix n n 𝕜 => M i j) hg
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply] at hij
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    star_div₀, RCLike.star_def, RCLike.conj_ofReal, div_mul_div_comm,
    ← Finset.sum_div, Matrix.one_apply]
  simp only [RCLike.star_def] at hij
  by_cases he : i = j
  · subst j
    simp only [ite_true] at hij ⊢
    rw [hij]
    have hc : (c i : 𝕜) ≠ 0 := by exact_mod_cast ne_of_gt i.property
    push_cast
    field_simp
  · have hv : i.val ≠ j.val := fun hh => he (Subtype.ext hh)
    simp only [hv, ite_false] at hij
    rw [hij]
    simp [he]

/-- The right generalized singular columns have the analogous orthonormal
normalization, with zero columns omitted. -/
theorem IsNormalizedGSVD.right_orthonormal {A : Matrix m n 𝕜} {L : Matrix p n 𝕜}
    {X : Matrix n n 𝕜} {c s : n → ℝ} (h : IsNormalizedGSVD A L X c s) :
    HasOrthonormalCols (Matrix.of (fun i (j : {j // 0 < s j}) =>
      (L * X) i j / (s j : 𝕜))) := by
  have hs : IsNormalizedGSVD L A X s c :=
    ⟨h.invertible, h.right_gram, h.left_gram, h.right_nonneg, h.left_nonneg,
      fun i => by simpa only [add_comm] using h.normalized i⟩
  exact hs.left_orthonormal

/-- A zero generalized singular value really means a zero transformed
data column, not just a zero entry in the Gram matrix. -/
theorem IsNormalizedGSVD.left_col_eq_zero {A : Matrix m n 𝕜} {L : Matrix p n 𝕜}
    {X : Matrix n n 𝕜} {c s : n → ℝ} (h : IsNormalizedGSVD A L X c s)
    (i : n) (hi : c i = 0) : (A * X).col i = 0 := by
  have hg : (A * X)ᴴ * (A * X) = diagonal (fun i => (c i ^ 2 : 𝕜)) := by
    simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using h.left_gram
  have he : ((A * X)ᴴ * (A * X)) *ᵥ Pi.single i 1 = 0 := by
    rw [hg, Matrix.diagonal_mulVec_single]
    simp [hi]
  have hh := (Matrix.conjTranspose_mul_self_mulVec_eq_zero (A * X) (Pi.single i 1)).mp he
  simpa only [Matrix.mulVec_single, MulOpposite.op_one, one_smul] using hh

/-- The analogous zero-penalty-column property. -/
theorem IsNormalizedGSVD.right_col_eq_zero {A : Matrix m n 𝕜} {L : Matrix p n 𝕜}
    {X : Matrix n n 𝕜} {c s : n → ℝ} (h : IsNormalizedGSVD A L X c s)
    (i : n) (hi : s i = 0) : (L * X).col i = 0 := by
  have hs : IsNormalizedGSVD L A X s c :=
    ⟨h.invertible, h.right_gram, h.left_gram, h.right_nonneg, h.left_nonneg,
      fun i => by simpa only [add_comm] using h.normalized i⟩
  exact hs.left_col_eq_zero i hi

end NLAlib
