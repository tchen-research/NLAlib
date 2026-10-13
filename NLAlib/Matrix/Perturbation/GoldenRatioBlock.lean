import NLAlib.Matrix.Subspaces.ProjectionGaps
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# The golden-ratio norm bound for a three-block operator

An orthogonal two-by-two operator decomposition with a zero lower-right
block has norm at most the golden ratio times its largest remaining block
norm. This is the sharp scalar step in Wedin's pseudoinverse perturbation.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- The scalar two-by-two golden-ratio inequality, by completion of a square.
Wedin (1973), orthogonal block proof. -/
theorem add_sq_add_sq_le_goldenRatio_sq_mul (s t : ℝ) :
    (s+t)^2+s^2 ≤ Real.goldenRatio^2*(s^2+t^2) := by
  have heq : Real.goldenRatio*(Real.goldenRatio^2*(s^2+t^2)-((s+t)^2+s^2)) =
      (s-Real.goldenRatio*t)^2 := by
    linear_combination ((Real.goldenRatio+1)*s^2+Real.goldenRatio*t^2)*Real.goldenRatio_sq
  have hh : 0 ≤ Real.goldenRatio*(Real.goldenRatio^2*(s^2+t^2)-((s+t)^2+s^2)) :=
    heq.symm ▸ sq_nonneg _
  have := (mul_nonneg_iff_of_pos_left Real.goldenRatio_pos).mp hh
  linarith

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Three orthogonal blocks bounded by `d`, with zero fourth block, give
the sharp golden-ratio operator norm bound. Wedin (1973), Stewart–Sun §III.3.
The projectors and zero block specify structure, not a perturbation conclusion. -/
theorem specNorm_le_goldenRatio_mul_of_zero_complement_block {Z : Matrix m n ℝ}
    {P : Matrix n n ℝ} {Q : Matrix m m ℝ}
    (hPh : P.IsHermitian) (hPi : IsIdempotentElem P)
    (hQh : Q.IsHermitian) (hQi : IsIdempotentElem Q)
    {d : ℝ} (hd : 0 ≤ d) (h00 : (1-Q)*Z*(1-P)=0)
    (h11 : specNorm (Q*Z*P) ≤ d) (h12 : specNorm (Q*Z*(1-P)) ≤ d)
    (h21 : specNorm ((1-Q)*Z*P) ≤ d) : specNorm Z ≤ Real.goldenRatio*d := by
  have hPs : P.IsSymm := Matrix.isHermitian_iff_isSymm.mp hPh
  have hQs : Q.IsSymm := Matrix.isHermitian_iff_isSymm.mp hQh
  have hPP : P*P=P := hPi
  have hPc : (1-P)*(1-P)=1-P := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP]
    abel
  have hsplit1 : Q*Z = Q*Z*P+Q*Z*(1-P) := by simp only [Matrix.mul_sub, Matrix.mul_one]; abel
  have hsplit2 : (1-Q)*Z=(1-Q)*Z*P := by
    have hh : (1-Q)*Z=(1-Q)*Z*P+(1-Q)*Z*(1-P) := by
      simp only [Matrix.mul_sub, Matrix.mul_one]
      abel
    simpa only [h00, add_zero] using hh
  apply specNorm_le_of_mulVec_sq_le (mul_nonneg Real.goldenRatio_pos.le hd)
  intro x
  let s := Real.sqrt ((P*ᵥx) ⬝ᵥ (P*ᵥx))
  let t := Real.sqrt (((1-P)*ᵥx) ⬝ᵥ ((1-P)*ᵥx))
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have hs2 : s^2=(P*ᵥx) ⬝ᵥ (P*ᵥx) := Real.sq_sqrt (dotProduct_self_nonneg _)
  have ht2 : t^2=((1-P)*ᵥx) ⬝ᵥ ((1-P)*ᵥx) := Real.sq_sqrt (dotProduct_self_nonneg _)
  have hbound (T : Matrix m n ℝ) (hT : specNorm T ≤ d) (v : n → ℝ) :
      Real.sqrt ((T*ᵥv) ⬝ᵥ (T*ᵥv)) ≤ d*Real.sqrt (v ⬝ᵥ v) :=
    (sqrt_mulVec_dotProduct_le_specNorm_mul T v).trans
      (mul_le_mul_of_nonneg_right hT (Real.sqrt_nonneg _))
  have hu := hbound (Q*Z*P) h11 (P*ᵥx)
  have hv := hbound (Q*Z*(1-P)) h12 ((1-P)*ᵥx)
  have hw := hbound ((1-Q)*Z*P) h21 (P*ᵥx)
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, hPP, hPc] at hu hv hw
  simp only [← Matrix.mul_assoc] at hu hv hw
  have hu' : Real.sqrt (((Q*Z)*ᵥx) ⬝ᵥ ((Q*Z)*ᵥx)) ≤ d*(s+t) := by
    rw [hsplit1, Matrix.add_mulVec]
    have hh := sqrt_dotProduct_add_le ((Q*Z*P)*ᵥx) ((Q*Z*(1-P))*ᵥx)
    change _ ≤ d*s at hu
    change _ ≤ d*t at hv
    nlinarith
  have hw' : Real.sqrt ((((1-Q)*Z)*ᵥx) ⬝ᵥ (((1-Q)*Z)*ᵥx)) ≤ d*s := by
    rw [hsplit2]
    exact hw
  have hq2 : ((Q*Z)*ᵥx) ⬝ᵥ ((Q*Z)*ᵥx) ≤ d^2*(s+t)^2 := by
    have hp := pow_le_pow_left₀ (Real.sqrt_nonneg _) hu' 2
    rw [Real.sq_sqrt (dotProduct_self_nonneg _), mul_pow] at hp
    exact hp
  have hqc2 : (((1-Q)*Z)*ᵥx) ⬝ᵥ (((1-Q)*Z)*ᵥx) ≤ d^2*s^2 := by
    have hp := pow_le_pow_left₀ (Real.sqrt_nonneg _) hw' 2
    rw [Real.sq_sqrt (dotProduct_self_nonneg _), mul_pow] at hp
    exact hp
  have hout := dotProduct_projector_add_complement hQs hQi (Z*ᵥx)
  simp only [Matrix.mulVec_mulVec] at hout
  have hin := dotProduct_projector_add_complement hPs hPi x
  rw [← hs2, ← ht2] at hin
  have hg := mul_le_mul_of_nonneg_left (add_sq_add_sq_le_goldenRatio_sq_mul s t) (sq_nonneg d)
  nlinarith [hout, hin, hg]

end NLAlib
