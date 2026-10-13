import NLAlib.Matrix.Basic.MoorePenroseTransformations
import NLAlib.Matrix.Norms.SpectralNormBounds
import NLAlib.Matrix.Subspaces.ProjectorBlocks
/-!
# The orthogonal projector onto the range of a matrix

* `rangeProjector B = B B⁺` (Moore–Penrose inverse): the orthogonal projector onto `range B`,
  defined at every rank and shape (`rangeProjector_eq_mul_moorePenroseInverse`). It is Hermitian,
  idempotent, fixes `B` (`rangeProjector_mul`), has the rank of `B`, and is `QQᴴ` for a frame `Q`
  with orthonormal columns (`rangeProjector_eq_mul_conjTranspose_of_hasOrthonormalCols`) and
  `B(BᴴB)⁻¹Bᴴ` for full column rank (`rangeProjector_eq_mul_inv_gram_conjTranspose`).
* `columnSpace B`: `range B` as a subspace of `EuclideanSpace 𝕜 m`; the projector is Mathlib's
  Hilbert orthogonal projection onto it (`toEuclideanLin_rangeProjector`).
* Nested ranges compose (`rangeProjector_mul_rangeProjector_of_mul_eq`), and the residual
  `A − rangeProjector B · A` is a contraction in the spectral and Frobenius norms, monotone in
  the range (`specNorm_sub_rangeProjector_mul_le_of_mul_eq`, `frobSq_…`).

Golub–Van Loan 2013, §5.5.2 and §2.5; Horn–Johnson 2013, §7.3 (Problem 7.3.P7).
Consumers: volume sampling (`LowRank/Sampling`), polynomial filters, block Krylov.
-/

noncomputable section
open scoped Matrix InnerProductSpace
namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n k l : Type*} [Fintype m] [Fintype n] [Fintype k]
  [Fintype l] [DecidableEq m] [DecidableEq n] [DecidableEq k] [DecidableEq l]

omit [DecidableEq m] in
/-- The column space `range B` of `B : Matrix m n 𝕜` as a subspace of `EuclideanSpace 𝕜 m`. -/
def columnSpace (B : Matrix m n 𝕜) : Submodule 𝕜 (EuclideanSpace 𝕜 m) :=
  LinearMap.range (Matrix.toEuclideanLin B)

omit [DecidableEq m] [DecidableEq n] in
/-- The **orthogonal projector onto `range B`**: `B B⁺` with the Moore–Penrose inverse, defined at
every rank and shape (the zero matrix for `B = 0`). Golub–Van Loan 2013, §5.5.2. -/
def rangeProjector (B : Matrix m n 𝕜) : Matrix m m 𝕜 := B * moorePenroseInverse B

omit [DecidableEq m] [DecidableEq n] in
theorem rangeProjector_eq_mul_moorePenroseInverse (B : Matrix m n 𝕜) :
    rangeProjector B = B * moorePenroseInverse B := rfl

omit [DecidableEq m] [DecidableEq n] in
/-- The range projector is Hermitian. -/
theorem rangeProjector_isHermitian (B : Matrix m n 𝕜) : (rangeProjector B).IsHermitian :=
  mul_moorePenroseInverse_isHermitian B

omit [DecidableEq m] [DecidableEq n] in
/-- The range projector is idempotent. -/
theorem rangeProjector_isIdempotentElem (B : Matrix m n 𝕜) :
    IsIdempotentElem (rangeProjector B) :=
  mul_moorePenroseInverse_isIdempotentElem B

omit [DecidableEq m] [DecidableEq n] in
theorem rangeProjector_mul_self (B : Matrix m n 𝕜) :
    rangeProjector B * rangeProjector B = rangeProjector B :=
  rangeProjector_isIdempotentElem B

omit [DecidableEq m] [DecidableEq n] in
/-- The projector fixes every column of `B`: `(B B⁺) B = B`. -/
theorem rangeProjector_mul (B : Matrix m n 𝕜) : rangeProjector B * B = B :=
  mul_moorePenroseInverse_mul B

omit [DecidableEq m] [DecidableEq n] in
/-- The row-space projector fixes `B` on the right: `B · rangeProjector Bᴴ = B`. -/
theorem mul_rangeProjector_conjTranspose (B : Matrix m n 𝕜) :
    B * rangeProjector Bᴴ = B := by
  have hh := congrArg Matrix.conjTranspose (rangeProjector_mul Bᴴ)
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    (rangeProjector_isHermitian Bᴴ).eq] using hh

omit [DecidableEq m] [DecidableEq n] in
/-- The range of the projector is the range of `B` (coordinate form). -/
theorem range_mulVecLin_rangeProjector (B : Matrix m n 𝕜) :
    LinearMap.range (rangeProjector B).mulVecLin = LinearMap.range B.mulVecLin :=
  range_mul_moorePenroseInverse_eq B

omit [DecidableEq m] [DecidableEq n] in
/-- The projector has the rank of `B`. -/
theorem rank_rangeProjector (B : Matrix m n 𝕜) : (rangeProjector B).rank = B.rank := by
  unfold Matrix.rank
  rw [range_mulVecLin_rangeProjector]

omit [DecidableEq m] [DecidableEq n] in
/-- `rangeProjector B` fixes every matrix whose range lies in `range B`. -/
theorem rangeProjector_mul_of_range_le {B : Matrix m n 𝕜} {Y : Matrix m k 𝕜}
    (h : LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin) :
    rangeProjector B * Y = Y := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  obtain ⟨y, hy⟩ := (range_mulVecLin_rangeProjector B).ge
    (h (show Y *ᵥ x ∈ LinearMap.range Y.mulVecLin from ⟨x, rfl⟩))
  rw [← Matrix.mulVec_mulVec, ← hy, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
    rangeProjector_mul_self]

omit [DecidableEq m] [DecidableEq n] [DecidableEq k] in
/-- Nested ranges make the projectors compose: if `rangeProjector Q` fixes `Y` then
`rangeProjector Q · rangeProjector Y = rangeProjector Y`. -/
theorem rangeProjector_mul_rangeProjector_of_mul_eq {Q : Matrix m k 𝕜} {Y : Matrix m l 𝕜}
    (h : rangeProjector Q * Y = Y) :
    rangeProjector Q * rangeProjector Y = rangeProjector Y := by
  rw [rangeProjector_eq_mul_moorePenroseInverse Y, ← Matrix.mul_assoc, h]

omit [DecidableEq m] in
/-- For a frame `Q` with orthonormal columns the range projector is `QQᴴ`. -/
theorem rangeProjector_eq_mul_conjTranspose_of_hasOrthonormalCols {Q : Matrix m n 𝕜}
    (hQ : HasOrthonormalCols Q) : rangeProjector Q = Q * Qᴴ := by
  rw [rangeProjector, moorePenroseInverse_eq_pinvL Q (by rw [hQ.conjTranspose_mul_self];
    exact isUnit_one), pinvL, hQ.conjTranspose_mul_self, Matrix.inv_one, Matrix.one_mul]

omit [DecidableEq m] in
/-- For full column rank the range projector is the inverse-Gram formula `B(BᴴB)⁻¹Bᴴ`.
Golub–Van Loan 2013, §5.5.2. -/
theorem rangeProjector_eq_mul_inv_gram_conjTranspose (B : Matrix m n 𝕜)
    (hG : IsUnit (Bᴴ * B)) : rangeProjector B = B * (Bᴴ * B)⁻¹ * Bᴴ := by
  rw [rangeProjector, moorePenroseInverse_eq_pinvL B hG, pinvL, Matrix.mul_assoc]

/-! ### The Hilbert-space projector -/

omit [DecidableEq m] [DecidableEq n] in
/-- The range projector is Mathlib's orthogonal projection onto `columnSpace B`. -/
theorem toEuclideanLin_rangeProjector (B : Matrix m n 𝕜) :
    Matrix.toEuclideanLin (rangeProjector B) = (columnSpace B).starProjection.toLinearMap := by
  apply LinearMap.ext
  intro x
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · refine ⟨Matrix.toEuclideanLin (moorePenroseInverse B) x, ?_⟩
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]
    rfl
  · rw [Submodule.mem_orthogonal]
    rintro u ⟨y, rfl⟩
    have hadj : Matrix.toEuclideanLin B = LinearMap.adjoint (Matrix.toEuclideanLin Bᴴ) := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, Matrix.conjTranspose_conjTranspose]
    rw [hadj, LinearMap.adjoint_inner_left, ← LinearMap.adjoint_inner_right, ← hadj]
    have hzero : Matrix.toEuclideanLin Bᴴ (x - Matrix.toEuclideanLin (rangeProjector B) x) = 0 := by
      rw [map_sub, ← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]
      change Matrix.toEuclideanLin Bᴴ x - Matrix.toEuclideanLin (Bᴴ * rangeProjector B) x = 0
      have h : Bᴴ * rangeProjector B = Bᴴ := by
        have hh := congrArg Matrix.conjTranspose (rangeProjector_mul B)
        simpa only [Matrix.conjTranspose_mul, (rangeProjector_isHermitian B).eq] using hh
      rw [h, sub_self]
    rw [← LinearMap.adjoint_inner_right, ← hadj]
    simp [hzero]

omit [DecidableEq m] [DecidableEq n] in
/-- The range of the projector is the column space (Hilbert form). -/
theorem range_toEuclideanLin_rangeProjector (B : Matrix m n 𝕜) :
    LinearMap.range (Matrix.toEuclideanLin (rangeProjector B)) = columnSpace B := by
  rw [toEuclideanLin_rangeProjector]
  exact Submodule.range_starProjection _

omit [DecidableEq m] in
/-- The column space is the span of the columns. -/
theorem columnSpace_eq_span_columns (B : Matrix m n 𝕜) :
    columnSpace B = Submodule.span 𝕜
      (Set.range (fun j => (WithLp.toLp 2 (B.col j) : EuclideanSpace 𝕜 m))) := by
  change LinearMap.range (Matrix.toEuclideanLin B) = _
  rw [← Submodule.map_top, ← (EuclideanSpace.basisFun n 𝕜).toBasis.span_eq,
    Submodule.map_span, ← Set.range_comp]
  have hf : (Matrix.toEuclideanLin B) ∘ (EuclideanSpace.basisFun n 𝕜).toBasis =
      (fun j => (WithLp.toLp 2 (B.col j) : EuclideanSpace 𝕜 m)) := by
    funext j
    simp only [Function.comp_def, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      Matrix.toLpLin_apply, EuclideanSpace.single, PiLp.ofLp_single,
      Matrix.mulVec_single]
    simp
  exact congrArg (Submodule.span 𝕜) (congrArg Set.range hf)

omit [DecidableEq m] in
/-- The rank is the dimension of the column space. -/
theorem rank_eq_finrank_columnSpace (B : Matrix m n 𝕜) :
    B.rank = Module.finrank 𝕜 (columnSpace B) := by
  unfold columnSpace
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.rank_eq_finrank_range_toLin B
    (EuclideanSpace.basisFun m 𝕜).toBasis (EuclideanSpace.basisFun n 𝕜).toBasis

/-! ### Norm bounds -/

omit [DecidableEq n] in
/-- The complementary projector is a spectral contraction: `‖I − rangeProjector B‖₂ ≤ 1`. -/
theorem specNorm_one_sub_rangeProjector_le_one (B : Matrix m n 𝕜) :
    specNorm ((1 : Matrix m m 𝕜) - rangeProjector B) ≤ 1 :=
  specNorm_one_sub_projector_le_one (rangeProjector_isHermitian B)
    (rangeProjector_isIdempotentElem B)

omit [DecidableEq n] [DecidableEq k] in
/-- The range residual contracts the spectral norm: `‖A − (BB⁺)A‖₂ ≤ ‖A‖₂`. -/
theorem specNorm_sub_rangeProjector_mul_le (B : Matrix m k 𝕜) (A : Matrix m n 𝕜) :
    specNorm (A - rangeProjector B * A) ≤ specNorm A := by
  rw [show A - rangeProjector B * A = (1 - rangeProjector B) * A by
    rw [Matrix.sub_mul, Matrix.one_mul]]
  exact (specNorm_mul_le _ _).trans
    ((mul_le_mul_of_nonneg_right (specNorm_one_sub_rangeProjector_le_one B)
      (specNorm_nonneg A)).trans_eq (one_mul _))

omit [DecidableEq n] [DecidableEq k] in
/-- The range residual contracts the Frobenius square: `‖A − (BB⁺)A‖_F² ≤ ‖A‖_F²`. -/
theorem frobSq_sub_rangeProjector_mul_le (B : Matrix m k 𝕜) (A : Matrix m n 𝕜) :
    frobSq (A - rangeProjector B * A) ≤ frobSq A := by
  rw [show A - rangeProjector B * A = (1 - rangeProjector B) * A by
    rw [Matrix.sub_mul, Matrix.one_mul]]
  exact frobSq_one_sub_projector_mul_le (rangeProjector_isHermitian B)
    (rangeProjector_isIdempotentElem B) A

omit [DecidableEq n] [DecidableEq k] [DecidableEq l] in
/-- A larger range has no larger spectral residual: if `rangeProjector Q` fixes `Y` then
`‖A − (QQ⁺)A‖₂ ≤ ‖A − (YY⁺)A‖₂`. -/
theorem specNorm_sub_rangeProjector_mul_le_of_mul_eq {Q : Matrix m k 𝕜} {Y : Matrix m l 𝕜}
    (h : rangeProjector Q * Y = Y) (A : Matrix m n 𝕜) :
    specNorm (A - rangeProjector Q * A) ≤ specNorm (A - rangeProjector Y * A) := by
  have hp := rangeProjector_mul_rangeProjector_of_mul_eq h
  have he : A - rangeProjector Q * A =
      (A - rangeProjector Y * A) - rangeProjector Q * (A - rangeProjector Y * A) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hp]
    abel
  rw [he]
  exact specNorm_sub_rangeProjector_mul_le _ _

omit [DecidableEq n] [DecidableEq k] [DecidableEq l] in
/-- A larger range has no larger Frobenius residual square. -/
theorem frobSq_sub_rangeProjector_mul_le_of_mul_eq {Q : Matrix m k 𝕜} {Y : Matrix m l 𝕜}
    (h : rangeProjector Q * Y = Y) (A : Matrix m n 𝕜) :
    frobSq (A - rangeProjector Q * A) ≤ frobSq (A - rangeProjector Y * A) := by
  have hp := rangeProjector_mul_rangeProjector_of_mul_eq h
  have he : A - rangeProjector Q * A =
      (A - rangeProjector Y * A) - rangeProjector Q * (A - rangeProjector Y * A) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hp]
    abel
  rw [he]
  exact frobSq_sub_rangeProjector_mul_le _ _

end NLAlib
