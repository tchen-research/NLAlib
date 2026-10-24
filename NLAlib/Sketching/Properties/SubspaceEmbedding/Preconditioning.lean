import NLAlib.Sketching.Properties.SubspaceEmbedding.SubspaceEmbedding
import NLAlib.Matrix.Factorizations.QR
import NLAlib.Matrix.Norms.SpectralNormBounds
import NLAlib.Matrix.Perturbation.ConditionNumber

/-!
# Conditioning after sketch normalization

If a sketch embeds the range of `A` and `S A M` has orthonormal columns, the singular-value
condition number of `A M` is at most `sqrt ((1 + ε) / (1 - ε))`. A thin QR factorization of
`S A` supplies `M = R⁻¹`. The proof uses the existing native epsilon-embedding interface and
the Moore–Penrose projector contraction; no sketch law is needed.

Source: Martinsson–Tropp 2020, §10.5. Adapted from `NLA-lib/NLAlib`,
`Regression/Embedding.lean`, commit `6a845a2ec27f37c1a98118c107a06a13ce45273d`
(Apache-2.0), to the backend's native definitions. Atlas: `sketch-and-precondition`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {k m d e : Type*} [Fintype k] [Fintype m] [Fintype d] [Fintype e]
  [DecidableEq m] [DecidableEq e]

/-- Normalizing an embedded matrix gives a well-conditioned matrix: if `S A M` has
orthonormal columns, the rectangular Moore–Penrose condition number of `A M` is at most
`sqrt ((1 + ε) / (1 - ε))`. The normalization forces full column rank, so this is the
usual largest-to-smallest singular-value ratio in nonempty dimensions. Empty columns give
condition number zero. Martinsson–Tropp 2020, §10.5; adapted from the generic-constant
normalization theorem in frontend commit `6a845a2ec27f37c1a98118c107a06a13ce45273d`.
-/
theorem IsSubspaceEmbedding.moorePenroseConditionNumber_mul_le
    {S : Matrix k m ℝ} {A : Matrix m d ℝ} {M : Matrix d e ℝ} {ε : ℝ}
    (h : IsSubspaceEmbedding S A ε) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hM : HasOrthonormalCols (S * A * M)) :
    moorePenroseConditionNumber (A * M) ≤ Real.sqrt ((1 + ε) / (1 - ε)) := by
  let B := A * M
  have hSB : HasOrthonormalCols (S * B) := by
    simpa only [B, Matrix.mul_assoc] using hM
  have hB := h.mul_right M
  change IsSubspaceEmbedding S B ε at hB
  have hcoords (x : e → ℝ) :
      (1 - ε) * ((B *ᵥ x) ⬝ᵥ (B *ᵥ x)) ≤ x ⬝ᵥ x ∧
        x ⬝ᵥ x ≤ (1 + ε) * ((B *ᵥ x) ⬝ᵥ (B *ᵥ x)) := by
    have hx : (S *ᵥ (B *ᵥ x)) ⬝ᵥ (S *ᵥ (B *ᵥ x)) = x ⬝ᵥ x := by
      simpa only [star_trivial, Matrix.mulVec_mulVec] using
        star_mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols hSB x
    simpa only [hx] using hB x
  have ha : 0 < 1 - ε := sub_pos.mpr hε1
  have hb : 0 ≤ 1 + ε := by linarith
  have hnorm : specNorm B ≤ Real.sqrt (1 / (1 - ε)) := by
    apply specNorm_le_of_mulVec_sq_le (Real.sqrt_nonneg _)
    intro x
    rw [Real.sq_sqrt (by positivity : 0 ≤ 1 / (1 - ε))]
    calc
      (B *ᵥ x) ⬝ᵥ (B *ᵥ x) ≤ (x ⬝ᵥ x) / (1 - ε) :=
        (le_div_iff₀ ha).2 (by nlinarith [(hcoords x).1])
      _ = 1 / (1 - ε) * (x ⬝ᵥ x) := by ring
  have hP : specNorm (B * moorePenroseInverse B) ≤ 1 :=
    (mul_moorePenroseInverse_isHermitian B).specNorm_le_one_of_isIdempotentElem
      (mul_moorePenroseInverse_isIdempotentElem B)
  have hPv (x : m → ℝ) :
      ((B * moorePenroseInverse B) *ᵥ x) ⬝ᵥ ((B * moorePenroseInverse B) *ᵥ x) ≤
        x ⬝ᵥ x := by
    have hp := sum_sq_mulVec_le_specNorm_sq (B * moorePenroseInverse B) x
    have hp2 : specNorm (B * moorePenroseInverse B) ^ 2 ≤ 1 := by
      nlinarith [specNorm_nonneg (B * moorePenroseInverse B)]
    have hx := dotProduct_self_nonneg x
    simp only [dotProduct, ← pow_two] at hp hx ⊢
    nlinarith
  have hpinv : specNorm (moorePenroseInverse B) ≤ Real.sqrt (1 + ε) := by
    apply specNorm_le_of_mulVec_sq_le (Real.sqrt_nonneg _)
    intro x
    rw [Real.sq_sqrt hb]
    have hx := (hcoords (moorePenroseInverse B *ᵥ x)).2
    rw [Matrix.mulVec_mulVec] at hx
    exact hx.trans (mul_le_mul_of_nonneg_left (hPv x) hb)
  change specNorm B * specNorm (moorePenroseInverse B) ≤ _
  calc
    specNorm B * specNorm (moorePenroseInverse B) ≤
        Real.sqrt (1 / (1 - ε)) * Real.sqrt (1 + ε) :=
      mul_le_mul hnorm hpinv (specNorm_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt ((1 + ε) / (1 - ε)) := by
      rw [← Real.sqrt_mul (by positivity : 0 ≤ 1 / (1 - ε))]
      congr 1
      ring

/-- A thin QR factorization of a subspace embedding preconditions `A` with condition number
at most `sqrt ((1 + ε) / (1 - ε))`. The invertibility of `R` and the orthonormality of `Q`
ensure full column rank, so the rectangular Moore–Penrose quantity is the ordinary singular
ratio. Martinsson–Tropp 2020, §10.5; frontend commit
`6a845a2ec27f37c1a98118c107a06a13ce45273d`, `Regression/Embedding.lean`.
atlas: sketch-and-precondition -/
theorem IsSubspaceEmbedding.moorePenroseConditionNumber_mul_inv_le_of_isQR
    [LinearOrder d] {S : Matrix k m ℝ} {A : Matrix m d ℝ} {Q : Matrix k d ℝ}
    {R : Matrix d d ℝ} {ε : ℝ} (h : IsSubspaceEmbedding S A ε)
    (hε : 0 ≤ ε) (hε1 : ε < 1) (hQR : IsQR (S * A) Q R) (hR : IsUnit R) :
    moorePenroseConditionNumber (A * R⁻¹) ≤ Real.sqrt ((1 + ε) / (1 - ε)) := by
  apply h.moorePenroseConditionNumber_mul_le hε hε1
  have hQ : S * A * R⁻¹ = Q := by
    rw [hQR.eq, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det R).mp hR), Matrix.mul_one]
  rw [hQ]
  exact hQR.orth

end NLAlib
