import NLAlib.Matrix.PrincipalMinors
import NLAlib.Matrix.GramColumnDeterminant
import NLAlib.LowRank.VolumeCounting
import NLAlib.Matrix.ColumnNorms
import NLAlib.Matrix.SvdBlocks

/-!
# Determinant-weighted column volume sampling

Finite determinant weights and their spectral normalizer define volume sampling
at every size up to the matrix rank, with empty determinant one. The projector
uses the arbitrary-rank Moore--Penrose inverse.
Source: Deshpande--Rademacher--Vempala--Wang (2006); manuscript `sa:volume`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {m n : ℕ}

/-- The columns indexed by a finite subset, retaining their original labels.
Source: manuscript `sa:volume`, its column submatrix `A_S`. -/
def volumeSampleColumns (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin n)) :
    Matrix (Fin m) S ℝ := A.submatrix id Subtype.val

/-- The Gram determinant weight of a sampled column set; the empty determinant is one.
Source: manuscript `sa:volume`, its weight `w(S)`. -/
def volumeSamplingWeight (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin n)) : ℝ :=
  ((volumeSampleColumns A S)ᵀ * volumeSampleColumns A S).det

/-- The finite sum of all prescribed-size volume weights.
Source: manuscript `sa:volume`, its normalizer `Z_k`. -/
def volumeSamplingNormalizer (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ Finset.univ.powersetCard k, volumeSamplingWeight A S

/-- The finite determinant-weighted expected squared projection residual.
Source: manuscript `sa:volume-theorem`; the normalized distribution is used when
`k ≤ rank A`, where its normalizer is proved positive. -/
def volumeSamplingExpectedFrobSq (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ Finset.univ.powersetCard k, volumeSamplingWeight A S / volumeSamplingNormalizer A k *
    frobSq (A - volumeSampleColumns A S * moorePenroseInverse (volumeSampleColumns A S) * A)

/-- Column Gram matrices are the matching principal submatrices of the full Gram.
Source: manuscript `sa:volume`, Gram-minor representation of the sampling weights. -/
theorem transpose_volumeSampleColumns_mul_eq_submatrix
    (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin n)) :
    (volumeSampleColumns A S)ᵀ * volumeSampleColumns A S =
      (Aᵀ * A).submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n) := rfl

/-- Every volume-sampling Gram weight is nonnegative, at every rank.
Source: manuscript `sa:volume`, positivity of `w(S)`. -/
theorem volumeSamplingWeight_nonneg (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin n)) :
    0 ≤ volumeSamplingWeight A S := by
  apply Matrix.PosSemidef.det_nonneg
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The volume normalizer is the elementary spectral sum of squared singular values.
Source: manuscript `sa:volume`, determinant coefficient identity.
The singular values are zero-indexed and padded beyond the matrix rank. -/
theorem volumeSamplingNormalizer_eq_sum_prod_singularValues_sq
    (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    volumeSamplingNormalizer A k =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ i ∈ S, singularValues A i ^ 2 := by
  obtain ⟨U, V, h⟩ := exists_isSVD A
  have hn := sum_det_principal_minors_eq_sum_prod_of_orthogonal_diagonalization
    h.transpose_mul_right h.transpose_mul_self k
  simpa only [volumeSamplingNormalizer, volumeSamplingWeight,
    transpose_volumeSampleColumns_mul_eq_submatrix] using hn

/-- Volume sampling is a normalized finite distribution at every prescribed size up
to the input rank. Source: manuscript `sa:volume`, positivity of `Z_k`.
The empty-set and rank-zero endpoints are included. -/
theorem volumeSamplingNormalizer_pos (A : Matrix (Fin m) (Fin n) ℝ) {k : ℕ}
    (hk : k ≤ A.rank) : 0 < volumeSamplingNormalizer A k := by
  have hkn : k ≤ n := hk.trans A.rank_le_width
  let S : Finset (Fin n) := Finset.univ.image (Fin.castLE hkn)
  have hCard : S.card = k := by
    dsimp only [S]
    rw [Finset.card_image_of_injective _ (Fin.castLE_injective hkn),
      Finset.card_univ, Fintype.card_fin]
  have hS : S ∈ (Finset.univ : Finset (Fin n)).powersetCard k :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hCard⟩
  have hProd : 0 < ∏ i ∈ S, singularValues A i ^ 2 := by
    apply Finset.prod_pos
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨j, _, rfl⟩
    apply sq_pos_of_pos
    exact (singularValues_pos_iff A _).mpr (j.isLt.trans_le hk)
  rw [volumeSamplingNormalizer_eq_sum_prod_singularValues_sq]
  apply Finset.sum_pos'
  · intro T _
    exact Finset.prod_nonneg fun i _ => sq_nonneg _
  · exact ⟨S, hS, hProd⟩

/-- Adding an outside column multiplies the volume weight by its squared projection
residual. Source: manuscript `sa:volume-column`; Deshpande et al. (2006).
The determinant identity includes a dependent starting column set. -/
theorem volumeSamplingWeight_mul_frobSq_col_eq_insert
    (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin n)) {j : Fin n} (hj : j ∉ S) :
    volumeSamplingWeight A S * frobSq
      (A.submatrix id (fun _ : Fin 1 => j) - volumeSampleColumns A S *
        moorePenroseInverse (volumeSampleColumns A S) * A.submatrix id (fun _ : Fin 1 => j)) =
      volumeSamplingWeight A (insert j S) := by
  let B := volumeSampleColumns A S
  let v := A.submatrix id (fun _ : Fin 1 => j)
  let eSet : ↥(insert j S) ≃ S ⊕ PUnit :=
    (Equiv.setCongr (Finset.coe_insert j S)).trans (Equiv.Set.insert hj)
  let e : S ⊕ Fin 1 ≃ ↥(insert j S) :=
    (Equiv.sumCongr (Equiv.refl S) (Equiv.ofUnique (Fin 1) PUnit)).trans eSet.symm
  have hM : Matrix.fromCols B v = (volumeSampleColumns A (insert j S)).submatrix id e := by
    ext i c
    cases c with
    | inl c =>
      simp [B, volumeSampleColumns, e, eSet]
      rfl
    | inr c =>
      simp [v, volumeSampleColumns, e, eSet]
      rfl
  have hGram : (Matrix.fromCols B v)ᵀ * Matrix.fromCols B v =
      ((volumeSampleColumns A (insert j S))ᵀ * volumeSampleColumns A (insert j S)).submatrix e e := by
    rw [hM]
    rfl
  calc volumeSamplingWeight A S * frobSq (v - B * moorePenroseInverse B * v) =
      ((Matrix.fromCols B v)ᵀ * Matrix.fromCols B v).det :=
      (det_gram_fromCols_eq_mul_frobSq_sub_projector B v).symm
    _ = _ := by rw [hGram, Matrix.det_submatrix_equiv_self]; rfl

/-- A determinant-weighted projection error is the sum of the weights after adding
one outside column. Source: manuscript `sa:volume-theorem`, first summation step. -/
theorem volumeSamplingWeight_mul_frobSq_eq_sum_insert
    (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin n)) :
    volumeSamplingWeight A S *
      frobSq (A - volumeSampleColumns A S * moorePenroseInverse (volumeSampleColumns A S) * A) =
      ∑ j, if j ∉ S then volumeSamplingWeight A (insert j S) else 0 := by
  let B := volumeSampleColumns A S
  let P := B * moorePenroseInverse B
  change volumeSamplingWeight A S * frobSq (A - P * A) = _
  rw [frobSq_eq_sum_frobSq_single_columns, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  let v := A.submatrix id (fun _ : Fin 1 => j)
  have hcol : (A - P * A).submatrix id (fun _ : Fin 1 => j) = v - P * v := rfl
  rw [hcol]
  by_cases hj : j ∈ S
  · have hpv : P * v = v := by
      ext i c
      exact congrArg (fun M : Matrix (Fin m) S ℝ => M i ⟨j, hj⟩)
        (mul_moorePenroseInverse_mul B)
    simp only [hpv, sub_self, frobSq_zero, mul_zero, if_neg (not_not.mpr hj)]
  · rw [if_pos hj]
    exact volumeSamplingWeight_mul_frobSq_col_eq_insert A S hj

/-- The finite volume-sampling expected projection error is exactly `(k+1)Z_(k+1)/Z_k`.
For `k ≤ rank A`, the proved positive normalizer makes this the actual expectation.
Source: manuscript `sa:volume-theorem`; Deshpande et al. (2006), exact error formula.
The empty-set and exact-rank endpoints are included by the same finite identity.
atlas: volume-sampling (partial) -/
theorem volumeSamplingExpectedFrobSq_eq_mul_normalizer_succ_div
    (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    volumeSamplingExpectedFrobSq A k =
      (k + 1 : ℝ) * volumeSamplingNormalizer A (k + 1) / volumeSamplingNormalizer A k := by
  unfold volumeSamplingExpectedFrobSq
  simp only [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  simp only [volumeSamplingWeight_mul_frobSq_eq_sum_insert]
  rw [sum_powersetCard_sum_insert_eq]
  rfl

/-- The exact expected volume-sampling error is at most `k+1` times the actual best
rank-`k` squared Frobenius error. Source: manuscript `sa:volume-theorem`;
Deshpande et al. (2006). The law is defined exactly on `0 ≤ k ≤ rank A`;
rank zero, the empty sample, and the exact-rank endpoint are all included.
atlas: volume-sampling (partial) -/
theorem volumeSamplingExpectedFrobSq_le_mul_bestRankFrobSq
    (A : Matrix (Fin m) (Fin n) ℝ) {k : ℕ} (hk : k ≤ A.rank) :
    volumeSamplingExpectedFrobSq A k ≤ (k + 1 : ℝ) * bestRankFrobSq k A := by
  have hZ := volumeSamplingNormalizer_pos A hk
  have hratio : volumeSamplingNormalizer A (k + 1) ≤
      singularValueTailSq A k * volumeSamplingNormalizer A k := by
    rw [volumeSamplingNormalizer_eq_sum_prod_singularValues_sq,
      volumeSamplingNormalizer_eq_sum_prod_singularValues_sq, singularValueTailSq_eq_sum_width]
    exact sum_powersetCard_prod_succ_le_tail_mul_sum_prod
      (fun i : Fin n => singularValues A i ^ 2) (fun i => sq_nonneg _) k
  have hdiv : volumeSamplingNormalizer A (k + 1) / volumeSamplingNormalizer A k ≤
      singularValueTailSq A k := (div_le_iff₀ hZ).mpr hratio
  rw [volumeSamplingExpectedFrobSq_eq_mul_normalizer_succ_div, mul_div_assoc,
    bestRankFrobSq_eq_singularValueTailSq]
  exact mul_le_mul_of_nonneg_left hdiv (by positivity)

/-- The finite expected squared volume-sampling residual is nonnegative.
Source: manuscript `sa:volume-theorem`, nonnegative finite expectation. -/
theorem volumeSamplingExpectedFrobSq_nonneg (A : Matrix (Fin m) (Fin n) ℝ) {k : ℕ}
    (hk : k ≤ A.rank) : 0 ≤ volumeSamplingExpectedFrobSq A k := by
  apply Finset.sum_nonneg
  intro S _
  exact mul_nonneg (div_nonneg (volumeSamplingWeight_nonneg A S)
    (volumeSamplingNormalizer_pos A hk).le) (frobSq_nonneg _)

/-- Sampling exactly the input rank has zero expected residual, hence zero residual
on every positive-probability outcome of the finite volume law.
Source: manuscript `sa:volume-theorem`, exact-rank endpoint.
atlas: volume-sampling (partial) -/
theorem volumeSamplingExpectedFrobSq_rank_eq_zero (A : Matrix (Fin m) (Fin n) ℝ) :
    volumeSamplingExpectedFrobSq A A.rank = 0 := by
  have h := volumeSamplingExpectedFrobSq_le_mul_bestRankFrobSq A (k := A.rank) le_rfl
  have htail : singularValueTailSq A A.rank = 0 := by
    unfold singularValueTailSq
    apply Finset.sum_eq_zero
    intro i _
    split_ifs with hi
    · rw [singularValues_eq_zero_of_rank_le A hi]
      simp
    · rfl
  rw [bestRankFrobSq_eq_singularValueTailSq, htail, mul_zero] at h
  exact le_antisymm h (volumeSamplingExpectedFrobSq_nonneg A le_rfl)

/-- Every positive-probability exact-rank volume sample reproduces the whole matrix.
Source: manuscript `sa:volume-theorem`, the almost-sure exact-rank conclusion.
This finite-support formulation includes rank zero and the empty sample.
atlas: volume-sampling (partial) -/
theorem sub_volumeSample_projector_mul_eq_zero_of_card_eq_rank
    (A : Matrix (Fin m) (Fin n) ℝ) {S : Finset (Fin n)}
    (hS : S.card = A.rank) (hw : 0 < volumeSamplingWeight A S) :
    A - volumeSampleColumns A S * moorePenroseInverse (volumeSampleColumns A S) * A = 0 := by
  have hzero := volumeSamplingExpectedFrobSq_rank_eq_zero A
  unfold volumeSamplingExpectedFrobSq at hzero
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun T _ => mul_nonneg (div_nonneg (volumeSamplingWeight_nonneg A T)
      (volumeSamplingNormalizer_pos A le_rfl).le) (frobSq_nonneg _))).mp hzero S
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩)
  have hc : 0 < volumeSamplingWeight A S / volumeSamplingNormalizer A A.rank :=
    div_pos hw (volumeSamplingNormalizer_pos A le_rfl)
  exact (frobSq_eq_zero_iff _).mp ((mul_eq_zero.mp hterm).resolve_left hc.ne')

end NLAlib
