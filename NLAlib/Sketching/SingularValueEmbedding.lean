import NLAlib.Sketching.Gram
import NLAlib.Matrix.SpectralBounds

/-!
# The singular-value form of a subspace embedding

Atlas: `ose-def`, `svd`. The finite list is indexed by the domain dimension,
so zero singular values of a wide matrix are included. Empty frames give
an empty list and the equivalence remains valid.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

/-- A Gram error bound is equivalent to bounds on every sorted squared
singular value. Atlas: `ose-def`, `svd`. -/
theorem specNorm_gram_sub_one_le_iff_singularValues_sq {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    specNorm (Aᵀ * A - 1) ≤ ε ↔
      ∀ j : Fin n, 1 - ε ≤ singularValues A j ^ 2 ∧ singularValues A j ^ 2 ≤ 1 + ε := by
  rw [specNorm_gram_sub_one_eq_norm_singularValues_sq_sub_one,
    pi_norm_le_iff_of_nonneg hε]
  apply forall_congr'
  intro j
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> rintro ⟨hlo, hup⟩ <;> constructor <;> linarith

/-- Complete singular-value OSE equivalence for `0 ≤ ε ≤ 1`: the sketch
preserves the subspace iff every domain singular value of `S U` lies in
`[√(1−ε), √(1+ε)]`. Atlas: `ose-def`, `svd`. Includes empty dimensions. -/
theorem isSubspaceEmbedding_iff_singularValues {k m d : ℕ}
    {S : Matrix (Fin k) (Fin m) ℝ} {U : Matrix (Fin m) (Fin d) ℝ}
    (hU : HasOrthonormalCols U) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    IsSubspaceEmbedding S U ε ↔ ∀ j : Fin d,
      Real.sqrt (1 - ε) ≤ singularValues (S * U) j ∧
        singularValues (S * U) j ≤ Real.sqrt (1 + ε) := by
  rw [isSubspaceEmbedding_iff_specNorm_transpose_mul_self_sub_one_le hU hε,
    specNorm_gram_sub_one_le_iff_singularValues_sq (S * U) hε]
  apply forall_congr'
  intro j
  have hlo0 : 0 ≤ 1 - ε := by linarith
  have hup0 : 0 ≤ 1 + ε := by linarith
  have hlo := Real.sq_sqrt hlo0
  have hup := Real.sq_sqrt hup0
  have hs := singularValues_nonneg (S * U) j
  have hls := Real.sqrt_nonneg (1 - ε)
  have hus := Real.sqrt_nonneg (1 + ε)
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith

end NLAlib
