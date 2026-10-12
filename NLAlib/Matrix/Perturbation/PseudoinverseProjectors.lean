import NLAlib.Matrix.Subspaces.ProjectionGaps
import NLAlib.Matrix.Basic.MoorePenroseRank
/-!
# Perturbation of Moore–Penrose range projectors

Equal rank identifies the two one-sided projection gaps, giving the minimum
of the two pseudoinverse norm coefficients. Stewart–Sun §III.3;
atlas `pseudoinverse-perturbation`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The column projector distance at equal rank is controlled by the first
pseudoinverse norm. Stewart–Sun §III.3, with arbitrary finite indices.
atlas: pseudoinverse-perturbation (partial) -/
theorem specNorm_sub_columnProjector_le_pinv_mul_specNorm {A B : Matrix m n ℝ}
    (hr : A.rank=B.rank) :
    specNorm (A*moorePenroseInverse A-B*moorePenroseInverse B) ≤
      specNorm (moorePenroseInverse A)*specNorm (B-A) := by
  let PA := A*moorePenroseInverse A
  let PB := B*moorePenroseInverse B
  have hPAs : PA.IsSymm := mul_moorePenroseInverse_isSymm A
  have hPAi : IsIdempotentElem PA := mul_moorePenroseInverse_isIdempotentElem A
  have hPBs : PB.IsSymm := mul_moorePenroseInverse_isSymm B
  have hPBi : IsIdempotentElem PB := mul_moorePenroseInverse_isIdempotentElem B
  have hpr : PA.rank=PB.rank := by
    rw [rank_mul_moorePenroseInverse, rank_mul_moorePenroseInverse]
    exact hr
  change specNorm (PA-PB) ≤ _
  rw [specNorm_sub_projector_eq_complement_mul_of_rank_eq hPAs hPAi hPBs hPBi hpr]
  have hPBb : PB*B=B := mul_moorePenroseInverse_mul B
  have heq : (1-PB)*PA = -((1-PB)*(B-A)*moorePenroseInverse A) := by
    have hz : (1-PB)*B = 0 := by simp [Matrix.sub_mul, hPBb]
    simp only [Matrix.mul_sub, Matrix.sub_mul, hz, Matrix.zero_mul,
      PA, Matrix.mul_assoc]
    abel
  rw [heq, specNorm_neg]
  have hc : specNorm (1-PB) ≤ 1 := by
    apply specNorm_le_one_of_isSymm_of_isIdempotentElem
    · simp [Matrix.IsSymm, hPBs.eq]
    · change (1-PB)*(1-PB)=1-PB
      have hi : PB*PB=PB := hPBi
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hi]
      abel
  calc
    _ ≤ specNorm ((1-PB)*(B-A))*specNorm (moorePenroseInverse A) := specNorm_mul_le _ _
    _ ≤ (specNorm (1-PB)*specNorm (B-A))*specNorm (moorePenroseInverse A) :=
      mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _)
    _ ≤ (1*specNorm (B-A))*specNorm (moorePenroseInverse A) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (specNorm_nonneg (B-A))) (specNorm_nonneg _)
    _ = _ := by ring

/-- Equal-rank column-space projector perturbation with the sharp minimum
pseudoinverse coefficient. Stewart–Sun 1990, §III.3, Thm III.3.8; Wedin 1973, Lemma 4.2
(projector form); both zero matrices are included.
atlas: pseudoinverse-perturbation (partial) -/
theorem specNorm_sub_columnProjector_le_min_pinv_mul_specNorm {A B : Matrix m n ℝ}
    (hr : A.rank=B.rank) :
    specNorm (A*moorePenroseInverse A-B*moorePenroseInverse B) ≤
      min (specNorm (moorePenroseInverse A)) (specNorm (moorePenroseInverse B))*specNorm (B-A) := by
  have ha := specNorm_sub_columnProjector_le_pinv_mul_specNorm hr
  have hb := specNorm_sub_columnProjector_le_pinv_mul_specNorm hr.symm
  rw [specNorm_sub_comm, specNorm_sub_comm A B] at hb
  rcases le_total (specNorm (moorePenroseInverse A)) (specNorm (moorePenroseInverse B)) with h | h
  · simpa only [min_eq_left h] using ha
  · simpa only [min_eq_right h] using hb

/-- Equal-rank row-space projectors obey the same sharp minimum coefficient,
by taking transposes. Stewart–Sun §III.3.
atlas: pseudoinverse-perturbation (partial) -/
theorem specNorm_sub_rowProjector_le_min_pinv_mul_specNorm {A B : Matrix m n ℝ}
    (hr : A.rank=B.rank) :
    specNorm (moorePenroseInverse A*A-moorePenroseInverse B*B) ≤
      min (specNorm (moorePenroseInverse A)) (specNorm (moorePenroseInverse B))*specNorm (B-A) := by
  have hh := specNorm_sub_columnProjector_le_min_pinv_mul_specNorm
    (A := Aᵀ) (B := Bᵀ) (by simpa only [Matrix.rank_transpose] using hr)
  rw [moorePenroseInverse_transpose, moorePenroseInverse_transpose,
    specNorm_transpose, specNorm_transpose, ← Matrix.transpose_sub,
    ← Matrix.transpose_mul, ← Matrix.transpose_mul, ← Matrix.transpose_sub,
    specNorm_transpose, specNorm_transpose] at hh
  exact hh

omit [DecidableEq m] [DecidableEq n] in
/-- The orthogonal row-space projector has the same rank as the original
matrix, by the transpose column-space range equality. -/
theorem rank_moorePenroseInverse_mul (A : Matrix m n ℝ) :
    (moorePenroseInverse A*A).rank=A.rank := by
  have hh := rank_mul_moorePenroseInverse Aᵀ
  rw [moorePenroseInverse_transpose, ← Matrix.transpose_mul, Matrix.rank_transpose,
    Matrix.rank_transpose] at hh
  exact hh

end NLAlib
