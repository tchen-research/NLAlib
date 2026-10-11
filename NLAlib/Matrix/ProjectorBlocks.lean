import NLAlib.Matrix.ProjectionGaps

/-!
# Orthogonal projector block accounting

Exact Frobenius Pythagoras identities for left, right, and four-block
splittings. These preserve the square-root-two pseudoinverse constant.
Source: Stewart–Sun §III.3.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The complement of an orthogonal projector is also an orthogonal
projector. Stewart–Sun §I.5. -/
theorem one_sub_projector_isSymm_isIdempotentElem {P : Matrix n n ℝ}
    (hs : P.IsSymm) (hp : IsIdempotentElem P) :
    (1-P).IsSymm ∧ IsIdempotentElem (1-P) := by
  constructor
  · simp [Matrix.IsSymm, hs.eq]
  · change (1-P)*(1-P)=1-P
    have hi : P*P=P := hp
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hi]
    abel

/-- An orthogonal complementary projector is a spectral contraction.
Stewart–Sun §I.5. -/
theorem specNorm_one_sub_projector_le_one {P : Matrix n n ℝ}
    (hs : P.IsSymm) (hp : IsIdempotentElem P) : specNorm (1-P) ≤ 1 := by
  have hh := one_sub_projector_isSymm_isIdempotentElem hs hp
  exact specNorm_le_one_of_isSymm_of_isIdempotentElem hh.1 hh.2

omit [DecidableEq n] in
/-- Left projection and its complement split the Frobenius square exactly.
Stewart–Sun §III.3. -/
theorem frobSq_projector_mul_add_complement {Q : Matrix m m ℝ}
    (hs : Q.IsSymm) (hp : IsIdempotentElem Q) (Z : Matrix m n ℝ) :
    frobSq (Q*Z)+frobSq ((1-Q)*Z)=frobSq Z := by
  have hc := one_sub_projector_isSymm_isIdempotentElem hs hp
  have hq : frobSq (Q*Z)=frobInner Z (Q*Z) := by
    rw [frobSq, frobInner_mul_mul, hs.eq, show Q*Q=Q from hp]
  have hqc : frobSq ((1-Q)*Z)=frobInner Z ((1-Q)*Z) := by
    rw [frobSq, frobInner_mul_mul, hc.1.eq, show (1-Q)*(1-Q)=1-Q from hc.2]
  rw [hq, hqc, ← frobInner_add_right, ← Matrix.add_mul]
  simp only [add_sub_cancel, Matrix.one_mul]
  rfl

omit [DecidableEq m] in
/-- Right projection and its complement split the Frobenius square exactly.
Stewart–Sun §III.3. -/
theorem frobSq_mul_projector_add_complement {P : Matrix n n ℝ}
    (hs : P.IsSymm) (hp : IsIdempotentElem P) (Z : Matrix m n ℝ) :
    frobSq (Z*P)+frobSq (Z*(1-P))=frobSq Z := by
  have hh := frobSq_projector_mul_add_complement hs hp Zᵀ
  rw [← frobSq_transpose (Z*P), ← frobSq_transpose (Z*(1-P))]
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hs.eq,
    Matrix.transpose_sub, Matrix.transpose_one, frobSq_transpose] using hh

/-- The exact orthogonal four-block Frobenius decomposition. Stewart–Sun
§III.3; no rank or nonempty-dimension condition is needed. -/
theorem frobSq_eq_four_projector_blocks {Q : Matrix m m ℝ} {P : Matrix n n ℝ}
    (hQs : Q.IsSymm) (hQi : IsIdempotentElem Q)
    (hPs : P.IsSymm) (hPi : IsIdempotentElem P) (Z : Matrix m n ℝ) :
    frobSq Z = frobSq (Q*Z*P)+frobSq (Q*Z*(1-P))+
      frobSq ((1-Q)*Z*P)+frobSq ((1-Q)*Z*(1-P)) := by
  have hq := frobSq_projector_mul_add_complement hQs hQi Z
  have hp := frobSq_mul_projector_add_complement hPs hPi (Q*Z)
  have hc := frobSq_mul_projector_add_complement hPs hPi ((1-Q)*Z)
  linarith

/-- The three compressed perturbation squares sum to at most twice the
full Frobenius square; only the lower-right block is counted twice.
Stewart–Sun §III.3, sharp pseudoinverse bookkeeping. -/
theorem frobSq_three_compressed_blocks_le_two_mul {Q : Matrix m m ℝ}
    {P : Matrix n n ℝ} (hQs : Q.IsSymm) (hQi : IsIdempotentElem Q)
    (hPs : P.IsSymm) (hPi : IsIdempotentElem P) (Z : Matrix m n ℝ) :
    frobSq (Q*Z*P)+frobSq ((1-Q)*Z)+frobSq (Z*(1-P)) ≤ 2*frobSq Z := by
  have hfour := frobSq_eq_four_projector_blocks hQs hQi hPs hPi Z
  have hleft := frobSq_mul_projector_add_complement hPs hPi ((1-Q)*Z)
  have hright := frobSq_projector_mul_add_complement hQs hQi (Z*(1-P))
  simp only [← Matrix.mul_assoc] at hright
  have hnon := frobSq_nonneg (Q*Z*P)
  have hnon2 := frobSq_nonneg (Q*Z*(1-P))
  have hnon3 := frobSq_nonneg ((1-Q)*Z*P)
  linarith

end NLAlib
