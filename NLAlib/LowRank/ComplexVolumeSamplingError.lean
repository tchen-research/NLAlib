import NLAlib.LowRank.ComplexVolumeSamplingLaw
import NLAlib.Matrix.ComplexGramColumnDeterminant
import NLAlib.LowRank.VolumeCounting

/-!
# Exact error of actual complex volume sampling

The complex insertion determinant identity and finite subset counting prove
the genuine normalized-law expectation and its sorted Gram tail bound.
Source: Deshpande–Rademacher–Vempala–Wang (2006); `sa:volume-theorem`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Classical Matrix Matrix.Norms.Frobenius ComplexOrder
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [Fintype n] in
/-- Adding an outside complex column multiplies its determinant weight by
the squared actual orthogonal projection residual. Dependent starting
columns are included. Source: `sa:volume-column`. -/
theorem complexVolumeSamplingWeight_mul_col_norm_sq_eq_insert
    (A : Matrix m n ℂ) (S : Finset n) {j : n} (hj : j ∉ S) :
    complexVolumeSamplingWeight A S *
      ‖A.submatrix id (fun _ : Fin 1 => j) -
        complexColumnProjector (complexVolumeSampleColumns A S) *
          A.submatrix id (fun _ : Fin 1 => j)‖ ^ 2 =
      complexVolumeSamplingWeight A (insert j S) := by
  let B := complexVolumeSampleColumns A S
  let v := A.submatrix id (fun _ : Fin 1 => j)
  let eSet : ↥(insert j S) ≃ S ⊕ PUnit :=
    (Equiv.setCongr (Finset.coe_insert j S)).trans (Equiv.Set.insert hj)
  let e : S ⊕ Fin 1 ≃ ↥(insert j S) :=
    (Equiv.sumCongr (Equiv.refl S) (Equiv.ofUnique (Fin 1) PUnit)).trans eSet.symm
  have hM : Matrix.fromCols B v = (complexVolumeSampleColumns A (insert j S)).submatrix id e := by
    ext i c
    cases c with
    | inl c =>
      simp [B, complexVolumeSampleColumns, e, eSet]
      rfl
    | inr c =>
      simp [v, complexVolumeSampleColumns, e, eSet]
      rfl
  have hGram : (Matrix.fromCols B v)ᴴ * Matrix.fromCols B v =
      ((complexVolumeSampleColumns A (insert j S))ᴴ *
        complexVolumeSampleColumns A (insert j S)).submatrix e e := by
    rw [hM]
    rfl
  calc
    _ = ((Matrix.fromCols B v)ᴴ * Matrix.fromCols B v).det.re :=
      (det_gram_fromCols_eq_mul_frobenius_norm_sq_sub_complexColumnProjector B v).symm
    _ = _ := by rw [hGram, Matrix.det_submatrix_equiv_self]; rfl

/-- The actual complex determinant-weighted Frobenius residual is the sum
of weights after inserting an outside column. Source: `sa:volume-theorem`. -/
theorem complexVolumeSamplingWeight_mul_residual_norm_sq_eq_sum_insert
    (A : Matrix m n ℂ) (S : Finset n) :
    complexVolumeSamplingWeight A S * ‖complexVolumeSamplingResidual A S‖ ^ 2 =
      ∑ j, if j ∉ S then complexVolumeSamplingWeight A (insert j S) else 0 := by
  let B := complexVolumeSampleColumns A S
  let P := complexColumnProjector B
  change complexVolumeSamplingWeight A S * ‖A - P * A‖ ^ 2 = _
  rw [frobenius_norm_sq_eq_sum_single_columns, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  let v := A.submatrix id (fun _ : Fin 1 => j)
  have hcol : (A - P * A).submatrix id (fun _ : Fin 1 => j) = v - P * v := rfl
  rw [hcol]
  by_cases hj : j ∈ S
  · have hpv : P * v = v := by
      ext i c
      exact congrArg (fun M : Matrix m S ℂ => M i ⟨j, hj⟩) (complexColumnProjector_mul B)
    simp only [hpv, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
      if_neg (not_not.mpr hj)]
  · rw [if_pos hj]
    exact complexVolumeSamplingWeight_mul_col_norm_sq_eq_insert A S hj

/-- The actual normalized complex volume law has exact expected error
`(k+1) Z_(k+1)/Z_k`, without any desired determinant or projector premise.
Source: `sa:volume-theorem`; rank-zero and empty-sample endpoints included.
atlas: volume-sampling (partial) -/
theorem integral_complexVolumeSampling_residual_norm_sq_eq_normalizer_ratio
    (A : Matrix m n ℂ) {k : ℕ} (hk : k ≤ A.rank) :
    (∫ S, ‖complexVolumeSamplingResidual A S‖ ^ 2 ∂complexVolumeSamplingLaw A hk) =
      (k + 1 : ℝ) * complexVolumeSamplingNormalizer A (k + 1) /
        complexVolumeSamplingNormalizer A k := by
  rw [integral_complexVolumeSamplingLaw]
  simp only [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  simp only [complexVolumeSamplingWeight_mul_residual_norm_sq_eq_sum_insert]
  rw [sum_powersetCard_sum_insert_eq]
  rfl

/-- The exact actual-law expectation is the stated elementary Gram spectral
ratio. Source: `sa:volume-theorem`, its exact complex error formula.
atlas: volume-sampling (partial) -/
theorem integral_complexVolumeSampling_residual_norm_sq_eq_elementary_ratio
    (A : Matrix m n ℂ) {k : ℕ} (hk : k ≤ A.rank) :
    (∫ S, ‖complexVolumeSamplingResidual A S‖ ^ 2 ∂complexVolumeSamplingLaw A hk) =
      (k + 1 : ℝ) * complexGramElementary A (k + 1) / complexGramElementary A k := by
  rw [integral_complexVolumeSampling_residual_norm_sq_eq_normalizer_ratio,
    complexVolumeSamplingNormalizer_eq_elementary, complexVolumeSamplingNormalizer_eq_elementary]

/-- The actual complex expectation is at most `k+1` times the genuine
sorted Gram spectral tail. Source: `sa:volume-theorem`.
atlas: volume-sampling (partial) -/
theorem integral_complexVolumeSampling_residual_norm_sq_le_mul_tail
    (A : Matrix m n ℂ) {k : ℕ} (hk : k ≤ A.rank) :
    (∫ S, ‖complexVolumeSamplingResidual A S‖ ^ 2 ∂complexVolumeSamplingLaw A hk) ≤
      (k + 1 : ℝ) * complexGramTail A k := by
  have hZ := (complexGramElementary_pos_iff A k).mpr hk
  have hr : complexGramElementary A (k + 1) ≤ complexGramTail A k * complexGramElementary A k := by
    rw [complexGramElementary_eq_sum_prod_sorted, complexGramElementary_eq_sum_prod_sorted,
      complexGramTail]
    exact sum_powersetCard_prod_succ_le_tail_mul_sum_prod
      (complexGramEigenvalues A) (complexGramEigenvalues_nonneg A) k
  rw [integral_complexVolumeSampling_residual_norm_sq_eq_elementary_ratio, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hZ).mpr hr) (by positivity)

/-- Sampling exactly the complex input rank has zero actual expected error.
Source: `sa:volume-theorem`, exact-rank endpoint.
atlas: volume-sampling (partial) -/
theorem integral_complexVolumeSampling_residual_norm_sq_rank_eq_zero (A : Matrix m n ℂ) :
    (∫ S, ‖complexVolumeSamplingResidual A S‖ ^ 2 ∂complexVolumeSamplingLaw A (le_refl A.rank)) = 0 := by
  rw [integral_complexVolumeSampling_residual_norm_sq_eq_elementary_ratio,
    complexGramElementary_eq_zero_of_rank_lt A (Nat.lt_succ_self A.rank), mul_zero, zero_div]

/-- Every positive-probability exact-rank outcome has exactly zero complex
projection residual. Source: `sa:volume-theorem`, finite-support endpoint. -/
theorem complexVolumeSamplingResidual_eq_zero_of_card_eq_rank
    (A : Matrix m n ℂ) {S : Finset n} (hS : S.card = A.rank)
    (hw : 0 < complexVolumeSamplingWeight A S) : complexVolumeSamplingResidual A S = 0 := by
  have hzero := integral_complexVolumeSampling_residual_norm_sq_rank_eq_zero A
  rw [integral_complexVolumeSamplingLaw] at hzero
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun T _ =>
    mul_nonneg (div_nonneg (complexVolumeSamplingWeight_nonneg A T)
      ((complexVolumeSamplingNormalizer_pos_iff A A.rank).mpr le_rfl).le) (sq_nonneg _))).mp hzero S
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩)
  have hp : 0 < complexVolumeSamplingWeight A S / complexVolumeSamplingNormalizer A A.rank :=
    div_pos hw ((complexVolumeSamplingNormalizer_pos_iff A A.rank).mpr le_rfl)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hterm).resolve_left hp.ne'))

end NLAlib
