/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Spectral.SVD
import NLAlib.Matrix.Subspaces.OrthogonalProducts
import NLAlib.Matrix.Subspaces.ProjectorBlocks

/-! # One Frequent Directions singular-value shrinkage transition

The output drops the left SVD factor, as required to restore a zero last row.
All statements hold for every full SVD witness, including repeated singular values
and zero loss. The first right singular columns form an actual thin frame.
Source: Ghashami–Liberty–Phillips–Woodruff (2016), Algorithm 2.1 and Properties 1–3.
Atlas: `singular-value-shrinkage-certificate`.
-/

noncomputable section
open Matrix
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {ℓ d : ℕ}

/-- The squared smallest row singular value removed by a Frequent Directions step. -/
def fdShrinkageLoss (C : Matrix (Fin ℓ) (Fin d) 𝕜) : ℝ :=
  singularValues C (ℓ - 1) ^ 2

/-- The row sketch produced by an SVD step: the left singular factor is dropped. -/
def fdShrinkageRows (C : Matrix (Fin ℓ) (Fin d) 𝕜) (V : Matrix (Fin d) (Fin d) 𝕜) :
    Matrix (Fin ℓ) (Fin d) 𝕜 :=
  (rectDiag (fun i => Real.sqrt (singularValues C i ^ 2 - fdShrinkageLoss C)) :
    Matrix (Fin ℓ) (Fin d) 𝕜) * Vᴴ

/-- The first `ℓ` columns of the full right singular frame, expressed without padding. -/
def fdRightFrame (V : Matrix (Fin d) (Fin d) 𝕜) : Matrix (Fin d) (Fin ℓ) 𝕜 :=
  V * (rectDiag (fun _ => 1) : Matrix (Fin d) (Fin ℓ) 𝕜)

@[simp] theorem fdShrinkageLoss_nonneg (C : Matrix (Fin ℓ) (Fin d) 𝕜) :
    0 ≤ fdShrinkageLoss C := sq_nonneg _

/-- Every row singular value lies above the amount removed at the last row. -/
theorem fdShrinkage_radicand_nonneg (C : Matrix (Fin ℓ) (Fin d) 𝕜)
    (hℓ : 0 < ℓ) (i : Fin ℓ) : 0 ≤ singularValues C i ^ 2 - fdShrinkageLoss C := by
  have hi : (i : ℕ) ≤ ℓ - 1 := by omega
  have hs := singularValues_antitone C hi
  have hn := singularValues_nonneg C (ℓ - 1)
  exact sub_nonneg.mpr (pow_le_pow_left₀ hn hs 2)

/-- Restricting a full right singular basis gives a thin orthonormal frame, provided `ℓ≤d`. -/
theorem fdRightFrame_hasOrthonormalCols {V : Matrix (Fin d) (Fin d) 𝕜}
    (hV : HasOrthonormalCols V) (hℓd : ℓ ≤ d) : HasOrthonormalCols (fdRightFrame (ℓ := ℓ) V) := by
  have hE : HasOrthonormalCols (rectDiag (fun _ => 1) : Matrix (Fin d) (Fin ℓ) 𝕜) := by
    rw [HasOrthonormalCols, conjTranspose_rectDiag_mul_rectDiag]
    ext i j
    have hi : (i : ℕ) < d := lt_of_lt_of_le i.isLt hℓd
    simp [hi, Matrix.diagonal_apply, Matrix.one_apply]
  exact hV.mul hE

private theorem fdRightFrame_mul_conjTranspose (V : Matrix (Fin d) (Fin d) 𝕜) :
    fdRightFrame (ℓ := ℓ) V * (fdRightFrame (ℓ := ℓ) V)ᴴ =
      V * Matrix.diagonal (fun j : Fin d => if (j : ℕ) < ℓ then (1 : 𝕜) else 0) * Vᴴ := by
  simp only [fdRightFrame, Matrix.conjTranspose_mul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (rectDiag (fun _ => 1)),
    rectDiag_mul_conjTranspose_rectDiag]
  simp only [one_pow, RCLike.ofReal_one]
  simp only [Matrix.mul_assoc]

/-- The exact covariance loss of the actual drop-U output is `δ Vthin Vthinᴴ`.
Ghashami–Liberty–Phillips–Woodruff (2016), Algorithm 2.1, Properties 1–3.
atlas: singular-value-shrinkage-certificate (partial)-/
theorem IsSVD.fdShrinkage_gram_loss {C : Matrix (Fin ℓ) (Fin d) 𝕜}
    {U : Matrix (Fin ℓ) (Fin ℓ) 𝕜} {V : Matrix (Fin d) (Fin d) 𝕜} (h : IsSVD C U V)
    (hℓ : 0 < ℓ) (_hℓd : ℓ ≤ d) :
    Cᴴ * C - (fdShrinkageRows C V)ᴴ * fdShrinkageRows C V =
      fdShrinkageLoss C • (fdRightFrame (ℓ := ℓ) V * (fdRightFrame (ℓ := ℓ) V)ᴴ) := by
  let S : Matrix (Fin ℓ) (Fin d) 𝕜 :=
    rectDiag (fun i => Real.sqrt (singularValues C i ^ 2 - fdShrinkageLoss C))
  have hB : (fdShrinkageRows C V)ᴴ * fdShrinkageRows C V = V * (Sᴴ * S) * Vᴴ := by
    simp only [fdShrinkageRows, S, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hDiag : Matrix.diagonal (fun j : Fin d => ((singularValues C j ^ 2 : ℝ) : 𝕜)) - Sᴴ * S =
      fdShrinkageLoss C • Matrix.diagonal (fun j : Fin d => if (j : ℕ) < ℓ then (1 : 𝕜) else 0) := by
    rw [show Sᴴ * S = Matrix.diagonal (fun j : Fin d => if (j : ℕ) < ℓ then
      ((Real.sqrt (singularValues C j ^ 2 - fdShrinkageLoss C) ^ 2 : ℝ) : 𝕜) else 0) from
      conjTranspose_rectDiag_mul_rectDiag _]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : (i : ℕ) < ℓ
      · have hn := fdShrinkage_radicand_nonneg C hℓ (⟨i, hi⟩ : Fin ℓ)
        simp only [Matrix.sub_apply, Matrix.diagonal_apply_eq, if_pos hi,
          Matrix.smul_apply, Real.sq_sqrt hn, RCLike.real_smul_eq_coe_mul, mul_one]
        rw [← RCLike.ofReal_sub]
        congr 1
        ring
      · have hz : singularValues C i = 0 := singularValues_eq_zero_of_height_le C
          (by simpa only [Fintype.card_fin] using not_lt.mp hi)
        simp [hi, hz]
    · simp [Matrix.sub_apply, hij]
  rw [h.conjTranspose_mul_self, hB, ← Matrix.sub_mul, ← Matrix.mul_sub, hDiag,
    Matrix.mul_smul, Matrix.smul_mul, fdRightFrame_mul_conjTranspose]

/-- The covariance loss is PSD and at most `δ I`; the thin frame projector is retained.
Ghashami–Liberty–Phillips–Woodruff (2016), Properties 1–2.
atlas: singular-value-shrinkage-certificate (partial)-/
theorem IsSVD.fdShrinkage_gram_loss_bounds {C : Matrix (Fin ℓ) (Fin d) 𝕜}
    {U : Matrix (Fin ℓ) (Fin ℓ) 𝕜} {V : Matrix (Fin d) (Fin d) 𝕜} (h : IsSVD C U V)
    (hℓ : 0 < ℓ) (hℓd : ℓ ≤ d) :
    0 ≤ Cᴴ * C - (fdShrinkageRows C V)ᴴ * fdShrinkageRows C V ∧
      Cᴴ * C - (fdShrinkageRows C V)ᴴ * fdShrinkageRows C V ≤
        fdShrinkageLoss C • (1 : Matrix (Fin d) (Fin d) 𝕜) := by
  let F := fdRightFrame (ℓ := ℓ) V
  have hF := fdRightFrame_hasOrthonormalCols h.conjTranspose_mul_right hℓd
  have hs : (F * Fᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self F
  have hp : IsIdempotentElem (F * Fᴴ) := by
    change (F * Fᴴ) * (F * Fᴴ) = F * Fᴴ
    calc
      _ = F * (Fᴴ * F) * Fᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hF.conjTranspose_mul_self, Matrix.mul_one]
  have hQ := one_sub_projector_isHermitian_isIdempotentElem hs hp
  have hQPSD := hQ.1.posSemidef_of_isIdempotentElem hQ.2
  have hPPSD := hs.posSemidef_of_isIdempotentElem hp
  rw [h.fdShrinkage_gram_loss hℓ hℓd]
  constructor
  · exact (hPPSD.smul (fdShrinkageLoss_nonneg C)).nonneg
  · rw [Matrix.le_iff, ← smul_sub]
    exact hQPSD.smul (fdShrinkageLoss_nonneg C)

/-- The squared Frobenius loss is exactly capacity times the removed squared singular value.
Ghashami–Liberty–Phillips–Woodruff (2016), Property 3, with the corrected exact identity.
atlas: singular-value-shrinkage-certificate (partial)-/
theorem IsSVD.fdShrinkage_frobSq_loss {C : Matrix (Fin ℓ) (Fin d) 𝕜}
    {U : Matrix (Fin ℓ) (Fin ℓ) 𝕜} {V : Matrix (Fin d) (Fin d) 𝕜} (h : IsSVD C U V)
    (hℓ : 0 < ℓ) (hℓd : ℓ ≤ d) :
    frobSq C - frobSq (fdShrinkageRows C V) = (ℓ : ℝ) * fdShrinkageLoss C := by
  have hF := fdRightFrame_hasOrthonormalCols h.conjTranspose_mul_right hℓd
  have ht := congrArg (fun M : Matrix (Fin d) (Fin d) 𝕜 => RCLike.re M.trace)
    (h.fdShrinkage_gram_loss hℓ hℓd)
  simp only [Matrix.trace_sub, map_sub, ← frobSq_eq_re_trace_conjTranspose_mul_self,
    Matrix.trace_smul, RCLike.smul_re] at ht
  rw [Matrix.trace_mul_comm, hF.conjTranspose_mul_self, Matrix.trace_one, RCLike.natCast_re,
    Fintype.card_fin, mul_comm] at ht
  exact ht

/-- The last output row vanishes after every step, including a zero shrinkage amount.
This is why the actual FD transition drops the left singular factor.
atlas: singular-value-shrinkage-certificate (partial) -/
theorem fdShrinkageRows_last_eq_zero (C : Matrix (Fin ℓ) (Fin d) 𝕜)
    (V : Matrix (Fin d) (Fin d) 𝕜) (hℓ : 0 < ℓ) (j : Fin d) :
    fdShrinkageRows C V ⟨ℓ - 1, by omega⟩ j = 0 := by
  simp [fdShrinkageRows, Matrix.mul_apply, rectDiag_apply_ofReal, fdShrinkageLoss]

/-- A rank-deficient capacity-ℓ input has zero shrinkage loss.
atlas: singular-value-shrinkage-certificate (partial) -/
theorem fdShrinkageLoss_eq_zero_of_rank_lt (C : Matrix (Fin ℓ) (Fin d) 𝕜)
    (hC : C.rank < ℓ) : fdShrinkageLoss C = 0 := by
  rw [fdShrinkageLoss, singularValues_eq_zero_of_rank_le C (by omega), zero_pow (by decide : 2 ≠ 0)]

end NLAlib
