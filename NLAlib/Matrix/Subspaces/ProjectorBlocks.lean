import NLAlib.Matrix.Subspaces.ProjectionGaps
/-!
# Orthogonal projector block accounting

Exact Frobenius Pythagoras identities for orthogonal projectors (Hermitian idempotents over
`[RCLike 𝕜]`): the complement is a projector (`one_sub_projector`), it is a spectral contraction
(`specNorm_one_sub_projector_le_one`), left and right projection split the Frobenius square
(`frobSq_projector_mul_add_complement`, `frobSq_mul_projector_add_complement`), the four-block
decomposition and the "three of four blocks" bound that keeps the `√2` constant in pseudoinverse
perturbation. Also the Frobenius trace form `frobSq_eq_re_trace_mul_conjTranspose` and
additivity over row-orthogonal summands. Stewart–Sun 1990, §III.3.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

open scoped ComplexOrder in
omit [DecidableEq n] in
/-- A Hermitian idempotent is positive semidefinite: it is its own Gram matrix.
This includes zero-dimensional projectors over either `RCLike` field. -/
theorem _root_.Matrix.IsHermitian.posSemidef_of_isIdempotentElem {P : Matrix n n 𝕜}
    (hs : P.IsHermitian) (hp : IsIdempotentElem P) : P.PosSemidef := by
  have hGram : Pᴴ * P = P := by rw [hs.eq]; exact hp
  rw [← hGram]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [DecidableEq m] [DecidableEq n] in
/-- Right projection captures the real trace of the Gram matrix on that projector.
This is the trace form of Frobenius orthogonal projection. -/
theorem frobSq_mul_projector_eq_re_trace_mul {P : Matrix n n 𝕜}
    (hs : P.IsHermitian) (hp : IsIdempotentElem P) (A : Matrix m n 𝕜) :
    frobSq (A * P) = RCLike.re (P * (Aᴴ * A)).trace := by
  rw [frobSq, frobInner_eq_trace, Matrix.conjTranspose_mul, hs.eq]
  calc
    _ = RCLike.re ((P * (Aᴴ * A)) * P).trace := by simp only [Matrix.mul_assoc]
    _ = RCLike.re (P * (P * (Aᴴ * A))).trace := by rw [Matrix.trace_mul_comm]
    _ = _ := by rw [← Matrix.mul_assoc P P, show P * P = P from hp]

omit [DecidableEq m] [DecidableEq n] in
/-- `‖A‖_F² = Re tr(AAᴴ)` (row Gram form of `frobSq_eq_re_trace_conjTranspose_mul_self`). -/
theorem frobSq_eq_re_trace_mul_conjTranspose (A : Matrix m n 𝕜) :
    frobSq A = RCLike.re (A * Aᴴ).trace := by
  rw [← frobSq_conjTranspose, frobSq_eq_re_trace_conjTranspose_mul_self,
    Matrix.conjTranspose_conjTranspose]

omit [DecidableEq m] [DecidableEq n] in
/-- Row-orthogonal summands (`XYᴴ = 0`) have additive Frobenius squares:
`‖X + Y‖_F² = ‖X‖_F² + ‖Y‖_F²`. -/
theorem frobSq_add_of_mul_conjTranspose_eq_zero {X Y : Matrix m n 𝕜} (h : X * Yᴴ = 0) :
    frobSq (X + Y) = frobSq X + frobSq Y := by
  apply frobSq_add_of_frobInner_eq_zero
  rw [frobInner_eq_re_trace_mul_conjTranspose, h, Matrix.trace_zero, map_zero]

omit [DecidableEq m] [DecidableEq n] in
/-- Column-orthogonal summands (`XᴴY = 0`) have additive Frobenius squares. -/
theorem frobSq_add_of_conjTranspose_mul_eq_zero {X Y : Matrix m n 𝕜} (h : Xᴴ * Y = 0) :
    frobSq (X + Y) = frobSq X + frobSq Y := by
  apply frobSq_add_of_frobInner_eq_zero
  rw [frobInner_eq_trace, h, Matrix.trace_zero, map_zero]

/-- The complement of an orthogonal projector is an orthogonal projector. Stewart–Sun 1990,
§I.5. -/
theorem one_sub_projector_isHermitian_isIdempotentElem {P : Matrix n n 𝕜}
    (hs : P.IsHermitian) (hp : IsIdempotentElem P) :
    (1 - P).IsHermitian ∧ IsIdempotentElem (1 - P) := by
  refine ⟨Matrix.isHermitian_one.sub hs, ?_⟩
  change (1 - P) * (1 - P) = 1 - P
  have hi : P * P = P := hp
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hi]
  abel

/-- An orthogonal complementary projector is a spectral contraction: `‖I − P‖₂ ≤ 1`.
Stewart–Sun 1990, §I.5. -/
theorem specNorm_one_sub_projector_le_one {P : Matrix n n 𝕜}
    (hs : P.IsHermitian) (hp : IsIdempotentElem P) : specNorm (1 - P) ≤ 1 := by
  have hh := one_sub_projector_isHermitian_isIdempotentElem hs hp
  exact Matrix.IsHermitian.specNorm_le_one_of_isIdempotentElem hh.1 hh.2

omit [DecidableEq n] in
/-- Left projection and its complement split the Frobenius square exactly:
`‖QZ‖_F² + ‖(I − Q)Z‖_F² = ‖Z‖_F²`. Stewart–Sun 1990, §III.3. -/
theorem frobSq_projector_mul_add_complement {Q : Matrix m m 𝕜}
    (hs : Q.IsHermitian) (hp : IsIdempotentElem Q) (Z : Matrix m n 𝕜) :
    frobSq (Q * Z) + frobSq ((1 - Q) * Z) = frobSq Z := by
  have hc := one_sub_projector_isHermitian_isIdempotentElem hs hp
  have hq : frobSq (Q * Z) = frobInner Z (Q * Z) := by
    rw [frobSq, frobInner_mul_mul, hs.eq, show Q * Q = Q from hp]
  have hqc : frobSq ((1 - Q) * Z) = frobInner Z ((1 - Q) * Z) := by
    rw [frobSq, frobInner_mul_mul, hc.1.eq, show (1 - Q) * (1 - Q) = 1 - Q from hc.2]
  rw [hq, hqc, ← frobInner_add_right, ← Matrix.add_mul]
  simp only [add_sub_cancel, Matrix.one_mul]
  rfl

omit [DecidableEq m] in
/-- Right projection and its complement split the Frobenius square exactly:
`‖ZP‖_F² + ‖Z(I − P)‖_F² = ‖Z‖_F²`. Stewart–Sun 1990, §III.3. -/
theorem frobSq_mul_projector_add_complement {P : Matrix n n 𝕜}
    (hs : P.IsHermitian) (hp : IsIdempotentElem P) (Z : Matrix m n 𝕜) :
    frobSq (Z * P) + frobSq (Z * (1 - P)) = frobSq Z := by
  have hh := frobSq_projector_mul_add_complement hs hp Zᴴ
  rw [← frobSq_conjTranspose (Z * P), ← frobSq_conjTranspose (Z * (1 - P))]
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hs.eq,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one, frobSq_conjTranspose] using hh

omit [DecidableEq n] in
/-- A projection residual `(I − P)A` contracts the Frobenius square: `‖(I − P)A‖_F² ≤ ‖A‖_F²`. -/
theorem frobSq_one_sub_projector_mul_le {P : Matrix m m 𝕜}
    (hs : P.IsHermitian) (hp : IsIdempotentElem P) (A : Matrix m n 𝕜) :
    frobSq ((1 - P) * A) ≤ frobSq A := by
  have h := frobSq_projector_mul_add_complement hs hp A
  linarith [frobSq_nonneg (P * A)]

/-- The exact orthogonal four-block Frobenius decomposition. Stewart–Sun 1990,
§III.3; no rank or nonempty-dimension condition is needed. -/
theorem frobSq_eq_four_projector_blocks {Q : Matrix m m 𝕜} {P : Matrix n n 𝕜}
    (hQs : Q.IsHermitian) (hQi : IsIdempotentElem Q)
    (hPs : P.IsHermitian) (hPi : IsIdempotentElem P) (Z : Matrix m n 𝕜) :
    frobSq Z = frobSq (Q * Z * P) + frobSq (Q * Z * (1 - P)) +
      frobSq ((1 - Q) * Z * P) + frobSq ((1 - Q) * Z * (1 - P)) := by
  have hq := frobSq_projector_mul_add_complement hQs hQi Z
  have hp := frobSq_mul_projector_add_complement hPs hPi (Q * Z)
  have hc := frobSq_mul_projector_add_complement hPs hPi ((1 - Q) * Z)
  linarith

/-- The three compressed perturbation squares sum to at most twice the
full Frobenius square; only the lower-right block is counted twice.
Stewart–Sun 1990, §III.3 (the sharp pseudoinverse bookkeeping). -/
theorem frobSq_three_compressed_blocks_le_two_mul {Q : Matrix m m 𝕜}
    {P : Matrix n n 𝕜} (hQs : Q.IsHermitian) (hQi : IsIdempotentElem Q)
    (hPs : P.IsHermitian) (hPi : IsIdempotentElem P) (Z : Matrix m n 𝕜) :
    frobSq (Q * Z * P) + frobSq ((1 - Q) * Z) + frobSq (Z * (1 - P)) ≤ 2 * frobSq Z := by
  have hfour := frobSq_eq_four_projector_blocks hQs hQi hPs hPi Z
  have hleft := frobSq_mul_projector_add_complement hPs hPi ((1 - Q) * Z)
  have hright := frobSq_projector_mul_add_complement hQs hQi (Z * (1 - P))
  simp only [← Matrix.mul_assoc] at hright
  have hnon := frobSq_nonneg (Q * Z * P)
  have hnon2 := frobSq_nonneg (Q * Z * (1 - P))
  have hnon3 := frobSq_nonneg ((1 - Q) * Z * P)
  linarith

end NLAlib
