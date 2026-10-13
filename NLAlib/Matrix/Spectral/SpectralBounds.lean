import NLAlib.Matrix.Spectral.Core
import NLAlib.Matrix.Spectral.SingularValueSpectrum
import NLAlib.Matrix.Norms.Reindex
import Mathlib.Tactic

/-!
# Extreme singular values and the spectral norm

The extreme singular values on arbitrary finite index types: `singularValues_zero_eq_specNorm`
(`σ₀ = ‖A‖₂`), `singularValues_le_specNorm`, `specNorm_sq_eq_specNorm_conjTranspose_mul_self`
(`‖A‖₂² = ‖AᴴA‖₂`), the Gram-error identity `specNorm_gram_sub_one_eq_norm_singularValues_sq_sub_one`
and `singularValues_last_pos_iff_rank_eq_card` (the last singular value is positive exactly at
full column rank). Source: Horn–Johnson 2013, §2.6 and §5.6. Atlas: `svd`, `norms-frob-spec`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- The spectral norm squared is the norm of the Gram matrix `AᴴA`, over `ℝ` or `ℂ`, including
empty dimensions. Atlas: `norms-frob-spec`, `svd`.
atlas: norms-frob-spec -/
theorem specNorm_sq_eq_specNorm_conjTranspose_mul_self {𝕜 : Type*} [RCLike 𝕜]
    (A : Matrix m n 𝕜) : specNorm A ^ 2 = specNorm (Aᴴ * A) := by
  open scoped Matrix.Norms.L2Operator in unfold specNorm
  rw [sq, ← Matrix.l2_opNorm_conjTranspose_mul_self]

/-- `‖A‖₂² = ‖AᵀA‖₂` for a real matrix (`specNorm_sq_eq_specNorm_conjTranspose_mul_self` at `ℝ`).
Kept for the real consumers of the transpose spelling. -/
theorem specNorm_sq_eq_specNorm_transpose_mul_self (A : Matrix m n ℝ) :
    specNorm A ^ 2 = specNorm (Aᵀ * A) := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact specNorm_sq_eq_specNorm_conjTranspose_mul_self A

end NLAlib

namespace NLAlib

/-- The largest sorted singular value equals the spectral norm, on arbitrary finite index
types and over `ℝ` or `ℂ`. The padded singular-value convention also covers matrices with zero
rows or columns. Horn–Johnson 2013, §5.6. Atlas: `svd`, `norms-frob-spec`.
atlas: norm-lipschitz -/
theorem singularValues_zero_eq_specNorm {m n 𝕜 : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n 𝕜) : singularValues A 0 = specNorm A := by
  by_cases hn : Fintype.card n = 0
  · have : IsEmpty n := Fintype.card_eq_zero_iff.mp hn
    have hA : A = 0 := by ext i j; exact isEmptyElim j
    rw [singularValues_eq_zero_of_width_le A (by omega), hA, specNorm_zero]
  · have hnpos : 0 < Fintype.card n := Nat.pos_of_ne_zero hn
    obtain ⟨U, V, hSVD⟩ := exists_isSVD A
    have hGram : specNorm (Aᴴ * A) =
        ‖(fun j : Fin (Fintype.card n) => ((singularValues A j ^ 2 : ℝ) : 𝕜))‖ := by
      rw [hSVD.conjTranspose_mul_self,
        specNorm_mul_conjTranspose_right_of_hasOrthonormalCols hSVD.conjTranspose_mul_right,
        specNorm_mul_left_of_hasOrthonormalCols hSVD.conjTranspose_mul_right,
        specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
    have hMax : ‖(fun j : Fin (Fintype.card n) => ((singularValues A j ^ 2 : ℝ) : 𝕜))‖ =
        singularValues A 0 ^ 2 := by
      apply le_antisymm
      · apply (pi_norm_le_iff_of_nonneg (sq_nonneg _)).2
        intro j
        rw [RCLike.norm_ofReal, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (singularValues_nonneg A j)
          (singularValues_antitone A (Nat.zero_le _)) 2
      · have h0 := norm_le_pi_norm
          (fun j : Fin (Fintype.card n) => ((singularValues A j ^ 2 : ℝ) : 𝕜)) ⟨0, hnpos⟩
        change ‖((singularValues A 0 ^ 2 : ℝ) : 𝕜)‖ ≤ _ at h0
        rw [RCLike.norm_ofReal, abs_of_nonneg (sq_nonneg (singularValues A 0))] at h0
        exact h0
    have hSq := specNorm_sq_eq_specNorm_conjTranspose_mul_self A
    rw [hGram, hMax] at hSq
    nlinarith [singularValues_nonneg A 0, specNorm_nonneg A]

/-- Every padded singular value is bounded by the spectral norm, on arbitrary finite index
types and over `ℝ` or `ℂ`. Horn–Johnson §5.6; atlas `norms-frob-spec`, `svd`. -/
theorem singularValues_le_specNorm {m n 𝕜 : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues A k ≤ specNorm A :=
  (singularValues_antitone A (Nat.zero_le k)).trans_eq (singularValues_zero_eq_specNorm A)

/-- A Gram error has the norm of the list `σᵢ² − 1`, for every domain
singular value (including zero singular values and empty dimensions).
Atlas: `ose-def`, `svd`. -/
theorem specNorm_gram_sub_one_eq_norm_singularValues_sq_sub_one {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    specNorm (Aᵀ * A - 1) = ‖(fun j : Fin n => singularValues A j ^ 2 - 1)‖ := by
  obtain ⟨U, V, hSVD⟩ := exists_isSVD A
  have hdiag : (Matrix.diagonal (fun j : Fin n => singularValues A j ^ 2 - 1)) =
      Matrix.diagonal (fun j : Fin n => singularValues A j ^ 2) - 1 := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_sub]
  have hGram : Aᵀ * A - 1 =
      V * Matrix.diagonal (fun j : Fin n => singularValues A j ^ 2 - 1) * Vᵀ := by
    rw [show Aᵀ * A = V * Matrix.diagonal (fun j : Fin n => singularValues A j ^ 2) * Vᵀ from
        hSVD.conjTranspose_mul_self, hdiag, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, show V * Vᵀ = 1 from hSVD.mul_conjTranspose_right]
  rw [hGram, ← Matrix.conjTranspose_eq_transpose_of_trivial V,
    specNorm_mul_conjTranspose_right_of_hasOrthonormalCols (P := V) hSVD.conjTranspose_mul_right,
    specNorm_mul_left_of_hasOrthonormalCols (P := V) hSVD.conjTranspose_mul_right,
    specNorm_eq_norm, Matrix.l2_opNorm_diagonal]

/-- The SVD gives the squared length as a weighted sum in right-singular
coordinates. Atlas: `svd`, `norm-lipschitz`. -/
theorem IsSVD.mulVec_dotProduct_mulVec_eq_sum {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {p q : ℕ}
    {A : Matrix m n ℝ} {U : Matrix m (Fin p) ℝ}
    {V : Matrix n (Fin q) ℝ} (hSVD : IsSVD A U V) (x : n → ℝ) :
    (A *ᵥ x) ⬝ᵥ (A *ᵥ x) =
      ∑ j : Fin q, singularValues A j ^ 2 * ((Vᵀ *ᵥ x) j) ^ 2 := by
  rw [show (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ ((Aᵀ * A) *ᵥ x) from
      star_mulVec_dotProduct_mulVec_self A x,
    show Aᵀ * A = V * Matrix.diagonal (fun j : Fin q => singularValues A j ^ 2) * Vᵀ from
      hSVD.conjTranspose_mul_self,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro j _
  ring

end NLAlib

namespace NLAlib

/-- The last singular value in the list indexed by the number of columns is positive exactly
when the matrix has full column rank (`rank A = card n`, with at least one column).
Horn–Johnson 2013, §2.6. -/
theorem singularValues_last_pos_iff_rank_eq_card {m n 𝕜 : Type*} [RCLike 𝕜] [Fintype m]
    [Fintype n] [DecidableEq n] (A : Matrix m n 𝕜) (hn : 0 < Fintype.card n) :
    0 < singularValues A (Fintype.card n - 1) ↔ A.rank = Fintype.card n := by
  rw [singularValues_pos_iff]
  have hr := A.rank_le_card_width
  omega

end NLAlib
