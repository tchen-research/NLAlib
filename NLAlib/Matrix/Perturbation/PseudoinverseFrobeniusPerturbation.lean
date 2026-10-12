import NLAlib.Matrix.Perturbation.PseudoinverseBlocks
import NLAlib.Matrix.Subspaces.ProjectionFrobeniusGaps
import NLAlib.Matrix.Subspaces.ProjectorBlocks
/-!
# Sharp Frobenius pseudoinverse perturbation

Equal-rank gap symmetry and exact four-block Pythagoras count the compressed
perturbations only twice, retaining the advertised square-root-two constant.
Source: Wedin (1973), Stewart–Sun §III.3;
atlas `pseudoinverse-perturbation`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The central pseudoinverse difference block retains both perturbation
projectors in its Frobenius estimate. Stewart–Sun §III.3. -/
theorem frobSq_pinv_mul_sub_mul_pinv_le_compressed (A B : Matrix m n ℝ) :
    frobSq (moorePenroseInverse B*(B-A)*moorePenroseInverse A) ≤
      specNorm (moorePenroseInverse A)^2*specNorm (moorePenroseInverse B)^2*
        frobSq ((B*moorePenroseInverse B)*(B-A)*(moorePenroseInverse A*A)) := by
  let a := moorePenroseInverse A
  let b := moorePenroseInverse B
  let C := (B*b)*(B-A)*(a*A)
  have ha : (a*A)*a=a := moorePenroseInverse_mul_moorePenroseInverse A
  have hb : b*(B*b)=b := by
    simpa only [b, Matrix.mul_assoc] using moorePenroseInverse_mul_moorePenroseInverse B
  have heq : b*(B-A)*a = b*C*a := by
    conv_rhs =>
      dsimp only [C]
      rw [← Matrix.mul_assoc b (B*b*(B-A)) (a*A),
        ← Matrix.mul_assoc b (B*b) (B-A), hb,
        Matrix.mul_assoc (b*(B-A)) (a*A) a, ha]
  change frobSq (b*(B-A)*a) ≤ specNorm a^2*specNorm b^2*frobSq C
  rw [heq, Matrix.mul_assoc]
  calc
    _ ≤ specNorm b^2*frobSq (C*a) := frobSq_mul_le_specNorm_sq_mul_frobSq _ _
    _ ≤ specNorm b^2*(frobSq C*specNorm a^2) :=
      mul_le_mul_of_nonneg_left (frobSq_mul_le_frobSq_mul_specNorm_sq _ _) (sq_nonneg _)
    _ = _ := by ring

/-- The upper-right inverse block uses equal-rank Frobenius gap symmetry
before bounding the compressed perturbation. Stewart–Sun §III.3. -/
theorem frobSq_pinv_mul_complement_columnProjector_le {A B : Matrix m n ℝ}
    (hr : A.rank=B.rank) :
    frobSq (moorePenroseInverse B*(1-A*moorePenroseInverse A)) ≤
      specNorm (moorePenroseInverse A)^2*specNorm (moorePenroseInverse B)^2*
        frobSq ((1-B*moorePenroseInverse B)*(B-A)) := by
  let a := moorePenroseInverse A
  let b := moorePenroseInverse B
  let PA := A*a
  let PB := B*b
  have hPAs : PA.IsSymm := mul_moorePenroseInverse_isSymm A
  have hPAi : IsIdempotentElem PA := mul_moorePenroseInverse_isIdempotentElem A
  have hPBs : PB.IsSymm := mul_moorePenroseInverse_isSymm B
  have hPBi : IsIdempotentElem PB := mul_moorePenroseInverse_isIdempotentElem B
  have hpr : PA.rank=PB.rank := by
    rw [rank_mul_moorePenroseInverse, rank_mul_moorePenroseInverse]
    exact hr
  have hb : b*PB=b := by
    simpa only [b, PB, Matrix.mul_assoc] using moorePenroseInverse_mul_moorePenroseInverse B
  have heq : b*(1-PA)=b*(PB*(1-PA)) := by rw [← Matrix.mul_assoc, hb]
  change frobSq (b*(1-PA)) ≤ specNorm a^2*specNorm b^2*frobSq ((1-PB)*(B-A))
  rw [heq]
  calc
    _ ≤ specNorm b^2*frobSq (PB*(1-PA)) := frobSq_mul_le_specNorm_sq_mul_frobSq _ _
    _ = specNorm b^2*frobSq ((1-PB)*PA) := by
      rw [frobSq_projector_mul_complement_eq_complement_mul_of_rank_eq hPAs hPAi hPBs hPBi hpr]
    _ = specNorm b^2*frobSq ((1-PB)*(B-A)*a) := by
      rw [complement_columnProjector_mul_columnProjector_eq A B, frobSq_neg]
    _ ≤ specNorm b^2*(frobSq ((1-PB)*(B-A))*specNorm a^2) :=
      mul_le_mul_of_nonneg_left (frobSq_mul_le_frobSq_mul_specNorm_sq _ _) (sq_nonneg _)
    _ = _ := by ring

/-- The lower-left inverse block likewise retains the compressed
perturbation, using equal-rank row-space gap symmetry. Stewart–Sun §III.3. -/
theorem frobSq_complement_rowProjector_mul_pinv_le {A B : Matrix m n ℝ}
    (hr : A.rank=B.rank) :
    frobSq ((1-moorePenroseInverse B*B)*moorePenroseInverse A) ≤
      specNorm (moorePenroseInverse A)^2*specNorm (moorePenroseInverse B)^2*
        frobSq ((B-A)*(1-moorePenroseInverse A*A)) := by
  let a := moorePenroseInverse A
  let b := moorePenroseInverse B
  let QA := a*A
  let QB := b*B
  have hQAs : QA.IsSymm := moorePenroseInverse_mul_isSymm A
  have hQAi : IsIdempotentElem QA := moorePenroseInverse_mul_isIdempotentElem A
  have hQBs : QB.IsSymm := moorePenroseInverse_mul_isSymm B
  have hQBi : IsIdempotentElem QB := moorePenroseInverse_mul_isIdempotentElem B
  have hqr : QA.rank=QB.rank := by
    rw [rank_moorePenroseInverse_mul, rank_moorePenroseInverse_mul]
    exact hr
  have ha : QA*a=a := moorePenroseInverse_mul_moorePenroseInverse A
  have heq : (1-QB)*a=(1-QB)*QA*a := by rw [Matrix.mul_assoc, ha]
  change frobSq ((1-QB)*a) ≤ specNorm a^2*specNorm b^2*frobSq ((B-A)*(1-QA))
  rw [heq]
  calc
    _ ≤ frobSq ((1-QB)*QA)*specNorm a^2 := frobSq_mul_le_frobSq_mul_specNorm_sq _ _
    _ = frobSq (QB*(1-QA))*specNorm a^2 := by
      rw [← frobSq_projector_mul_complement_eq_complement_mul_of_rank_eq hQAs hQAi hQBs hQBi hqr]
    _ = frobSq (b*((B-A)*(1-QA)))*specNorm a^2 := by
      rw [rowProjector_mul_complement_rowProjector_eq A B, Matrix.mul_assoc]
    _ ≤ (specNorm b^2*frobSq ((B-A)*(1-QA)))*specNorm a^2 :=
      mul_le_mul_of_nonneg_right (frobSq_mul_le_specNorm_sq_mul_frobSq _ _) (sq_nonneg _)
    _ = _ := by ring

/-- The equal-rank pseudoinverse difference Frobenius square is bounded
by twice the squared inverse-norm product times perturbation square.
Wedin (1973); the exact four-block counting includes zero rank. -/
theorem frobSq_moorePenroseInverse_sub_le_two_mul_of_rank_eq {A B : Matrix m n ℝ}
    (hr : A.rank=B.rank) :
    frobSq (moorePenroseInverse B-moorePenroseInverse A) ≤
      2*specNorm (moorePenroseInverse A)^2*specNorm (moorePenroseInverse B)^2*frobSq (B-A) := by
  let a := moorePenroseInverse A
  let b := moorePenroseInverse B
  let PA := A*a
  let PB := B*b
  let QA := a*A
  let QB := b*B
  have hblk := moorePenroseInverse_sub_blocks A B
  change QB*(b-a)*PA= -b*(B-A)*a ∧ QB*(b-a)*(1-PA)=b*(1-PA) ∧
    (1-QB)*(b-a)*PA= -(1-QB)*a ∧ (1-QB)*(b-a)*(1-PA)=0 at hblk
  have hfour := frobSq_eq_four_projector_blocks
    (moorePenroseInverse_mul_isSymm B) (moorePenroseInverse_mul_isIdempotentElem B)
    (mul_moorePenroseInverse_isSymm A) (mul_moorePenroseInverse_isIdempotentElem A) (b-a)
  change frobSq (b-a)=frobSq (QB*(b-a)*PA)+frobSq (QB*(b-a)*(1-PA))+
    frobSq ((1-QB)*(b-a)*PA)+frobSq ((1-QB)*(b-a)*(1-PA)) at hfour
  rw [hblk.1, Matrix.neg_mul, Matrix.neg_mul, frobSq_neg, hblk.2.1,
    hblk.2.2.1, Matrix.neg_mul, frobSq_neg, hblk.2.2.2, frobSq_zero, add_zero] at hfour
  have h11 := frobSq_pinv_mul_sub_mul_pinv_le_compressed A B
  have h12 := frobSq_pinv_mul_complement_columnProjector_le hr
  have h21 := frobSq_complement_rowProjector_mul_pinv_le hr
  have hthree := frobSq_three_compressed_blocks_le_two_mul
    (mul_moorePenroseInverse_isSymm B) (mul_moorePenroseInverse_isIdempotentElem B)
    (moorePenroseInverse_mul_isSymm A) (moorePenroseInverse_mul_isIdempotentElem A) (B-A)
  have hcoeff : 0 ≤ specNorm a^2*specNorm b^2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hm := mul_le_mul_of_nonneg_left hthree hcoeff
  change frobSq (b-a) ≤ 2*specNorm a^2*specNorm b^2*frobSq (B-A)
  change frobSq (b*(B-A)*a) ≤ specNorm a^2*specNorm b^2*frobSq (PB*(B-A)*QA) at h11
  change frobSq (b*(1-PA)) ≤ specNorm a^2*specNorm b^2*frobSq ((1-PB)*(B-A)) at h12
  change frobSq ((1-QB)*a) ≤ specNorm a^2*specNorm b^2*frobSq ((B-A)*(1-QA)) at h21
  nlinarith

/-- Equal-rank pseudoinverse perturbation with the exact `sqrt(2)`
Frobenius coefficient. Wedin (1973), Stewart–Sun §III.3; no rank-zero exception.
atlas: pseudoinverse-perturbation (partial) -/
theorem frobNorm_moorePenroseInverse_sub_le_sqrt_two_mul_of_rank_eq {A B : Matrix m n ℝ}
    (hr : A.rank=B.rank) :
    frobNorm (moorePenroseInverse B-moorePenroseInverse A) ≤
      Real.sqrt 2*specNorm (moorePenroseInverse A)*specNorm (moorePenroseInverse B)*frobNorm (B-A) := by
  have hh := frobSq_moorePenroseInverse_sub_le_two_mul_of_rank_eq hr
  rw [← frobNorm_sq, ← frobNorm_sq] at hh
  have hc : 0 ≤ Real.sqrt 2*specNorm (moorePenroseInverse A)*specNorm (moorePenroseInverse B)*frobNorm (B-A) :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (specNorm_nonneg _))
      (specNorm_nonneg _)) (frobNorm_nonneg _)
  have hs : (Real.sqrt 2*specNorm (moorePenroseInverse A)*specNorm (moorePenroseInverse B)*frobNorm (B-A))^2 =
      2*specNorm (moorePenroseInverse A)^2*specNorm (moorePenroseInverse B)^2*frobNorm (B-A)^2 := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  apply le_of_pow_le_pow_left₀ two_ne_zero hc
  rw [hs]
  exact hh

end NLAlib
