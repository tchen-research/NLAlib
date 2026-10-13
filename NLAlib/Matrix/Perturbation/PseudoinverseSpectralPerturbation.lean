import NLAlib.Matrix.Perturbation.PseudoinverseBlocks
import NLAlib.Matrix.Subspaces.ProjectorBlocks
import NLAlib.Matrix.Perturbation.GoldenRatioBlock
/-!
# Sharp spectral pseudoinverse perturbation

The golden-ratio block lemma gives the exact general-rank and equal-rank
spectral constants. Projector gaps use the minimum inverse-norm coefficient.
Source: Wedin (1973), Stewart–Sun §III.3;
atlas `pseudoinverse-perturbation`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- A product of nonnegative coefficients is at most the larger square.
Scalar coefficient step in Wedin's general-rank pseudoinverse bound. -/
theorem mul_le_max_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a*b ≤ max (a^2) (b^2) := by
  rcases le_total a b with h | h
  · exact (by nlinarith : a*b ≤ b^2).trans (le_max_right _ _)
  · exact (by nlinarith : a*b ≤ a^2).trans (le_max_left _ _)

omit [DecidableEq m] in
/-- Spectral norm of a three-factor product, used to expose the exact
inverse coefficients in Wedin's block estimates. -/
theorem specNorm_mul_mul_le {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q] (X : Matrix m n ℝ) (Y : Matrix n p ℝ)
    (Z : Matrix p q ℝ) : specNorm (X*Y*Z) ≤ specNorm X*specNorm Y*specNorm Z :=
  (specNorm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _))

/-- General-rank pseudoinverse perturbation with the exact golden ratio:
`‖B⁺ - A⁺‖₂ ≤ ((1 + √5)/2) max(‖A⁺‖₂², ‖B⁺‖₂²) ‖B - A‖₂`.
Wedin 1973, Thm 4.1; Stewart–Sun 1990, Thm III.3.8 (`μ = (1 + √5)/2` for the spectral norm);
rectangular, empty, and rank-changing matrices are all allowed.
atlas: pseudoinverse-perturbation (partial) -/
theorem specNorm_moorePenroseInverse_sub_le_goldenRatio_max_sq (A B : Matrix m n ℝ) :
    specNorm (moorePenroseInverse B-moorePenroseInverse A) ≤
      Real.goldenRatio*max (specNorm (moorePenroseInverse A)^2)
        (specNorm (moorePenroseInverse B)^2)*specNorm (B-A) := by
  let a := moorePenroseInverse A
  let b := moorePenroseInverse B
  let P := A*a
  let Q := b*B
  let e := specNorm (B-A)
  let d := max (specNorm a^2) (specNorm b^2)*e
  have hPs : P.IsHermitian := mul_moorePenroseInverse_isHermitian A
  have hPi : IsIdempotentElem P := mul_moorePenroseInverse_isIdempotentElem A
  have hQs : Q.IsHermitian := moorePenroseInverse_mul_isHermitian B
  have hQi : IsIdempotentElem Q := moorePenroseInverse_mul_isIdempotentElem B
  have hPnorm := specNorm_one_sub_projector_le_one hPs hPi
  have hQnorm := specNorm_one_sub_projector_le_one hQs hQi
  have hblk := moorePenroseInverse_sub_blocks A B
  change Q*(b-a)*P= -b*(B-A)*a ∧ Q*(b-a)*(1-P)=b*(1-P) ∧
    (1-Q)*(b-a)*P= -(1-Q)*a ∧ (1-Q)*(b-a)*(1-P)=0 at hblk
  have hd : 0 ≤ d := mul_nonneg (le_trans (sq_nonneg _) (le_max_left _ _)) (specNorm_nonneg _)
  have h11 : specNorm (Q*(b-a)*P) ≤ d := by
    rw [hblk.1, Matrix.neg_mul, Matrix.neg_mul, specNorm_neg]
    have hbnd := specNorm_mul_mul_le b (B-A) a
    have hab := mul_le_max_sq_of_nonneg (specNorm_nonneg a) (specNorm_nonneg b)
    have hh := mul_le_mul_of_nonneg_right hab (specNorm_nonneg (B-A))
    change _ ≤ max (specNorm a^2) (specNorm b^2)*e
    dsimp only [e] at *
    nlinarith
  have h12 : specNorm (Q*(b-a)*(1-P)) ≤ d := by
    rw [hblk.2.1, moorePenroseInverse_mul_complement_columnProjector_eq A B]
    change specNorm (b*bᵀ*(B-A)ᵀ*(1-P)) ≤ _
    have hbnd := specNorm_mul_le (b*bᵀ*(B-A)ᵀ) (1-P)
    have htrip := specNorm_mul_mul_le b bᵀ (B-A)ᵀ
    rw [specNorm_transpose, specNorm_transpose] at htrip
    have hcont := mul_le_mul_of_nonneg_left hPnorm (specNorm_nonneg (b*bᵀ*(B-A)ᵀ))
    have hmax := mul_le_mul_of_nonneg_right (le_max_right (specNorm a^2) (specNorm b^2)) (specNorm_nonneg (B-A))
    dsimp only [d, e]
    nlinarith
  have h21 : specNorm ((1-Q)*(b-a)*P) ≤ d := by
    rw [hblk.2.2.1, neg_complement_rowProjector_mul_moorePenroseInverse_eq A B]
    change specNorm ((1-Q)*(B-A)ᵀ*aᵀ*a) ≤ _
    have hbnd := specNorm_mul_mul_le ((1-Q)*(B-A)ᵀ) aᵀ a
    have hfirst := specNorm_mul_le (1-Q) (B-A)ᵀ
    rw [specNorm_transpose] at hfirst
    rw [specNorm_transpose] at hbnd
    have hcont := mul_le_mul_of_nonneg_right hQnorm (specNorm_nonneg (B-A))
    have hmax := mul_le_mul_of_nonneg_right (le_max_left (specNorm a^2) (specNorm b^2)) (specNorm_nonneg (B-A))
    dsimp only [d, e]
    nlinarith [specNorm_nonneg a]
  have hh := specNorm_le_goldenRatio_mul_of_zero_complement_block hPs hPi hQs hQi hd hblk.2.2.2 h11 h12 h21
  simpa only [d, e, a, b, mul_assoc] using hh

/-- Equal-rank pseudoinverse perturbation with the exact golden-ratio
product coefficient: `‖B⁺ - A⁺‖₂ ≤ ((1 + √5)/2) ‖A⁺‖₂ ‖B⁺‖₂ ‖B - A‖₂` when `rank A = rank B`.
Wedin 1973, Thm 4.1; Stewart–Sun 1990, §III.3, Thm III.3.8. Rank zero is included.
atlas: pseudoinverse-perturbation (partial) -/
theorem specNorm_moorePenroseInverse_sub_le_goldenRatio_mul_of_rank_eq
    {A B : Matrix m n ℝ} (hr : A.rank=B.rank) :
    specNorm (moorePenroseInverse B-moorePenroseInverse A) ≤
      Real.goldenRatio*specNorm (moorePenroseInverse A)*specNorm (moorePenroseInverse B)*specNorm (B-A) := by
  let a := moorePenroseInverse A
  let b := moorePenroseInverse B
  let PA := A*a
  let PB := B*b
  let QA := a*A
  let QB := b*B
  let d := specNorm a*specNorm b*specNorm (B-A)
  have hPAs : PA.IsHermitian := mul_moorePenroseInverse_isHermitian A
  have hPAi : IsIdempotentElem PA := mul_moorePenroseInverse_isIdempotentElem A
  have hPBs : PB.IsHermitian := mul_moorePenroseInverse_isHermitian B
  have hPBi : IsIdempotentElem PB := mul_moorePenroseInverse_isIdempotentElem B
  have hQAs : QA.IsHermitian := moorePenroseInverse_mul_isHermitian A
  have hQAi : IsIdempotentElem QA := moorePenroseInverse_mul_isIdempotentElem A
  have hQBs : QB.IsHermitian := moorePenroseInverse_mul_isHermitian B
  have hQBi : IsIdempotentElem QB := moorePenroseInverse_mul_isIdempotentElem B
  have hblk := moorePenroseInverse_sub_blocks A B
  change QB*(b-a)*PA= -b*(B-A)*a ∧ QB*(b-a)*(1-PA)=b*(1-PA) ∧
    (1-QB)*(b-a)*PA= -(1-QB)*a ∧ (1-QB)*(b-a)*(1-PA)=0 at hblk
  have hd : 0 ≤ d := mul_nonneg (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)) (specNorm_nonneg _)
  have h11 : specNorm (QB*(b-a)*PA) ≤ d := by
    rw [hblk.1, Matrix.neg_mul, Matrix.neg_mul, specNorm_neg]
    have hh := specNorm_mul_mul_le b (B-A) a
    dsimp only [d]
    nlinarith
  have h12 : specNorm (QB*(b-a)*(1-PA)) ≤ d := by
    rw [hblk.2.1]
    have hbPB : b*PB=b := by
      simpa only [b, PB, Matrix.mul_assoc] using moorePenroseInverse_mul_moorePenroseInverse B
    have heq : b*(1-PA)=b*(PB*(1-PA)) := by rw [← Matrix.mul_assoc, hbPB]
    rw [heq]
    have hgap : specNorm (PB*(1-PA)) ≤ specNorm (PA-PB) := by
      rw [specNorm_sub_projector_eq_max hPAs hPAi hPBs hPBi]
      exact le_max_right _ _
    have hdist : specNorm (PA-PB) ≤ specNorm a*specNorm (B-A) :=
      specNorm_sub_columnProjector_le_pinv_mul_specNorm hr
    calc
      _ ≤ specNorm b*specNorm (PB*(1-PA)) := specNorm_mul_le _ _
      _ ≤ specNorm b*(specNorm a*specNorm (B-A)) :=
        mul_le_mul_of_nonneg_left (hgap.trans hdist) (specNorm_nonneg _)
      _ = d := by dsimp only [d]; ring
  have h21 : specNorm ((1-QB)*(b-a)*PA) ≤ d := by
    rw [hblk.2.2.1, Matrix.neg_mul, specNorm_neg]
    have hQAa : QA*a=a := moorePenroseInverse_mul_moorePenroseInverse A
    have heq : (1-QB)*a=(1-QB)*QA*a := by rw [Matrix.mul_assoc, hQAa]
    rw [heq]
    have hgap : specNorm ((1-QB)*QA) ≤ specNorm (QA-QB) := by
      rw [specNorm_sub_projector_eq_max hQAs hQAi hQBs hQBi]
      exact le_max_left _ _
    have hdist : specNorm (QA-QB) ≤ specNorm b*specNorm (B-A) := by
      have hh := specNorm_sub_rowProjector_le_min_pinv_mul_specNorm hr
      exact hh.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (specNorm_nonneg _))
    calc
      _ ≤ specNorm ((1-QB)*QA)*specNorm a := specNorm_mul_le _ _
      _ ≤ (specNorm b*specNorm (B-A))*specNorm a :=
        mul_le_mul_of_nonneg_right (hgap.trans hdist) (specNorm_nonneg _)
      _ = d := by dsimp only [d]; ring
  have hh := specNorm_le_goldenRatio_mul_of_zero_complement_block hPAs hPAi hQBs hQBi hd hblk.2.2.2 h11 h12 h21
  simpa only [d, a, b, mul_assoc] using hh

end NLAlib
