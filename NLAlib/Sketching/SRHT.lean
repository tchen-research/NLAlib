import NLAlib.Sketching.SRHTCore
import NLAlib.Sketching.SRHTParameters
import NLAlib.Concentration.Matrix.SamplingWithoutReplacementTails
import NLAlib.ForMathlib.Probability.FiniteProductEvents
import NLAlib.Matrix.WalshFin

/-!
# Classical SRHT with one shared diagonal and actual distinct-row sampling

The finite product law, literal `√(n/k) R H D` matrix, Gaussian-linearization
row bound, proved without-replacement Chernoff inequality and full-row
recovery close the classical source statement. Source: `sh:srht-ose`.
Atlas: `srht-ose`.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory
open scoped Classical Matrix Matrix.Norms.L2Operator ENNReal ComplexOrder
namespace NLAlib

/-- The actual classical SRHT law: one independent uniform sign cube and
one uniform exact-size row subset. Source: `sh:srht-ose`. -/
def srhtLaw {n k : ℕ} (hk : k ≤ n) :
    Measure ((Fin n → Bool) × ExactRowSubset (Fin n) k) :=
  (rademacherCubePMF (Fin n)).toMeasure.prod
    (uniformExactRowSubsetPMF (show k ≤ Fintype.card (Fin n) by simpa using hk)).toMeasure

instance srhtLaw_isProbabilityMeasure {n k : ℕ} (hk : k ≤ n) :
    IsProbabilityMeasure (srhtLaw hk) := by
  unfold srhtLaw
  infer_instance

/-- Conditional on a deterministic flattened frame, the literal distinct
row sketch satisfies the matrix Chernoff bound. All rank-one, mean and
eigenvalue hypotheses are proved from that frame. Source: `sh:srht-ose`. -/
theorem measure_srht_gram_failure_le_of_flat_rows
    {n d k : ℕ} [NeZero n] [NeZero d] (hk0 : 0 < k) (hk : k ≤ n)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : Hᵀ * H = 1)
    (U : Matrix (Fin n) (Fin d) ℝ) (hU : HasOrthonormalCols U)
    (ξ : Fin n → Bool) {L ε : ℝ} (hL : 0 < L)
    (hflat : ∀ j, (n : ℝ) * (srhtSignedFrame H U ξ j ⬝ᵥ srhtSignedFrame H U ξ j) ≤ L)
    (hε : 0 < ε) (hε1 : ε < 1) :
    ((uniformExactRowSubsetPMF (show k ≤ Fintype.card (Fin n) by simpa using hk)).toMeasure
      {T | ε < specNorm ((srhtSketch H ξ T * U)ᵀ * (srhtSketch H ξ T * U) - 1)}).toReal ≤
      2 * d * Real.exp (-(ε ^ 2) * k / (3 * L)) := by
  let V := srhtSignedFrame H U ξ
  let A := srhtPopulationAtom V
  have hPSD (j : Fin n) : (A j).PosSemidef := srhtPopulationAtom_posSemidef V j
  have hbound (j : Fin n) : 0 ≤ lambdaMin (A j) ∧ lambdaMax (A j) ≤ L := by
    refine ⟨lambdaMin_nonneg_of_posSemidef (hPSD j), ?_⟩
    have ht := trace_srhtPopulationAtom V j
    exact (lambdaMax_le_trace_of_posSemidef (hPSD j)).trans (by rw [ht]; exact hflat j)
  have hmean := mean_srhtPopulationAtom V (hasOrthonormalCols_srhtSignedFrame H hH U hU ξ)
  have hc := measure_spectralNorm_uniform_subset_sub_one_le hk0
    (show k ≤ Fintype.card (Fin n) by simpa using hk) A L hL
    (fun j => (hPSD j).isHermitian) hbound hmean hε hε1
  have hsub : {T : ExactRowSubset (Fin n) k | ε <
      specNorm ((srhtSketch H ξ T * U)ᵀ * (srhtSketch H ξ T * U) - 1)} ⊆
      {T | ε ≤ spectralNorm ((1 / (k : ℝ)) • ∑ j ∈ T.val, A j - 1)} := by
    intro T hT
    have hm : (((srhtSketch H ξ T * U)ᵀ * (srhtSketch H ξ T * U) - 1).map Complex.ofReal) =
        (1 / (k : ℝ)) • ∑ j ∈ T.val, A j - 1 := by
      rw [Matrix.map_sub Complex.ofReal Complex.ofReal_sub, map_ofReal_srhtSketch_gram]
      congr 1
      ext a b
      by_cases hab : a = b <;> simp [Matrix.map_apply, Matrix.one_apply, hab]
    have hnorm := specNorm_le_spectralNorm_map_ofReal
      ((srhtSketch H ξ T * U)ᵀ * (srhtSketch H ξ T * U) - 1)
    rw [hm] at hnorm
    exact hT.le.trans hnorm
  exact (measureReal_mono hsub).trans hc

/-- The source's exact sample count makes the conditional failure at most
`δ/2`. Source: `sh:srht-ose`. -/
theorem srht_tail_le_half_of_sample_size {d k : ℕ} (hd : 0 < d)
    {L ε δ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hδ : 0 < δ)
    (hsize : 3 * L / ε ^ 2 * Real.log (4 * d / δ) ≤ k) :
    2 * d * Real.exp (-(ε ^ 2) * k / (3 * L)) ≤ δ / 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog : Real.log (4 * d / δ) ≤ ε ^ 2 * k / (3 * L) := by
    have hh := mul_le_mul_of_nonneg_left hsize (show 0 ≤ ε ^ 2 / (3 * L) by positivity)
    have he : ε ^ 2 / (3 * L) * (3 * L / ε ^ 2 * Real.log (4 * d / δ)) =
        Real.log (4 * d / δ) := by field_simp
    rw [he] at hh
    calc
      _ ≤ ε ^ 2 / (3 * L) * (k : ℝ) := hh
      _ = _ := by ring
  calc
    _ ≤ 2 * d * Real.exp (-Real.log (4 * d / δ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      simpa only [neg_div, neg_mul] using neg_le_neg hlog
    _ = _ := by
      rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 4 * (d : ℝ) / δ)]
      field_simp
      ring

/-- Classical SRHT with its original sharp additive row bound. It uses the
literal fixed shared `D`, uniform distinct rows independent of `D`, and the
exact `3L ε⁻² log(4d/δ)` row threshold. Source: `sh:srht-ose`.
atlas: srht-ose -/
theorem measure_srht_gram_failure_le_of_sharp_sample_size
    {n d k : ℕ} [NeZero n] [NeZero d] (hk0 : 0 < k) (hk : k ≤ n)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : Hᵀ * H = 1)
    (hHflat : ∀ i j, H i j ^ 2 = 1 / (n : ℝ))
    (U : Matrix (Fin n) (Fin d) ℝ) (hU : HasOrthonormalCols U)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsize : 3 * srhtSharpRowBound n d δ / ε ^ 2 * Real.log (4 * d / δ) ≤ k) :
    (srhtLaw hk {ω | ε < specNorm
      ((srhtSketch H ω.1 ω.2 * U)ᵀ * (srhtSketch H ω.1 ω.2 * U) - 1)}).toReal ≤ δ := by
  let L := srhtSharpRowBound n d δ
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hL : 0 < L := by
    apply sq_pos_of_pos
    exact add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr hdR) (Real.sqrt_nonneg _)
  let E : Set (Fin n → Bool) := {ξ | ∃ j : Fin n,
    L < (n : ℝ) * (srhtSignedFrame H U ξ j ⬝ᵥ srhtSignedFrame H U ξ j)}
  have hE := measure_srhtSharpRowBound_failure_le H hHflat U hU hδ hδ1
  have hcond (ξ : Fin n → Bool) (hξ : ξ ∉ E) :
      ((uniformExactRowSubsetPMF (show k ≤ Fintype.card (Fin n) by simpa using hk)).toMeasure
        {T | ε < specNorm ((srhtSketch H ξ T * U)ᵀ * (srhtSketch H ξ T * U) - 1)}).toReal ≤
          δ / 2 := by
    have hrows (j : Fin n) : (n : ℝ) *
        (srhtSignedFrame H U ξ j ⬝ᵥ srhtSignedFrame H U ξ j) ≤ L := by
      by_contra hnot
      exact hξ ⟨j, lt_of_not_ge hnot⟩
    exact (measure_srht_gram_failure_le_of_flat_rows hk0 hk H hH U hU ξ hL hrows hε hε1).trans
      (srht_tail_le_half_of_sample_size (Nat.pos_of_ne_zero (NeZero.ne d)) hL hε hδ hsize)
  have hh := measureReal_prod_le_bad_add (rademacherCubePMF (Fin n)).toMeasure
    (uniformExactRowSubsetPMF (show k ≤ Fintype.card (Fin n) by simpa using hk)).toMeasure E
    {ω | ε < specNorm ((srhtSketch H ω.1 ω.2 * U)ᵀ * (srhtSketch H ω.1 ω.2 * U) - 1)}
    (show 0 ≤ δ / 2 by positivity) hcond
  exact hh.trans (by linarith)

/-- The manuscript's displayed Hanson–Wright row bound and row count imply
the classical SRHT OSE under the actual without-replacement law.
Source: operator re-derivation `sh:srht-ose`, exact displayed coefficients.
atlas: srht-ose -/
theorem measure_srht_gram_failure_le_of_manuscript_sample_size
    {n d k : ℕ} [NeZero n] [NeZero d] (hk0 : 0 < k) (hk : k ≤ n)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : Hᵀ * H = 1)
    (hHflat : ∀ i j, H i j ^ 2 = 1 / (n : ℝ))
    (U : Matrix (Fin n) (Fin d) ℝ) (hU : HasOrthonormalCols U)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsize : 3 * srhtManuscriptRowBound n d δ / ε ^ 2 * Real.log (4 * d / δ) ≤ k) :
    (srhtLaw hk {ω | ε < specNorm
      ((srhtSketch H ω.1 ω.2 * U)ᵀ * (srhtSketch H ω.1 ω.2 * U) - 1)}).toReal ≤ δ := by
  apply measure_srht_gram_failure_le_of_sharp_sample_size hk0 hk H hH hHflat U hU
    hε hε1 hδ hδ1
  refine le_trans ?_ hsize
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hlog : 0 ≤ Real.log (4 * d / δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]
    linarith
  gcongr
  exact srhtSharpRowBound_le_manuscript hδ hδ1

/-- The source's literal capped row prescription, using all rows if its
displayed threshold exceeds the population. Source: `sh:srht-ose`. -/
def srhtCappedRowCount (n d : ℕ) (ε δ : ℝ) : ℕ :=
  min n ⌈3 * srhtManuscriptRowBound n d δ / ε ^ 2 * Real.log (4 * d / δ)⌉₊

/-- The actual capped prescription always selects at most the population.
Source: `sh:srht-ose`. -/
theorem srhtCappedRowCount_le (n d : ℕ) (ε δ : ℝ) :
    srhtCappedRowCount n d ε δ ≤ n := min_le_left _ _

/-- Full-row recovery has exactly zero failure probability under the actual
sign and subset law. Source: `sh:srht-ose`, including zero input rank. -/
theorem measure_srht_full_rows_failure_eq_zero {n d : ℕ} [NeZero n]
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : Hᵀ * H = 1)
    (U : Matrix (Fin n) (Fin d) ℝ) (hU : HasOrthonormalCols U)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (srhtLaw (le_refl n) {ω | ε < specNorm
      ((srhtSketch H ω.1 ω.2 * U)ᵀ * (srhtSketch H ω.1 ω.2 * U) - 1)}).toReal = 0 := by
  have he : {ω : (Fin n → Bool) × ExactRowSubset (Fin n) n | ε < specNorm
      ((srhtSketch H ω.1 ω.2 * U)ᵀ * (srhtSketch H ω.1 ω.2 * U) - 1)} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, transpose_srhtSketch_full_rows_mul_self H hH U hU,
      sub_self, specNorm_eq_norm, norm_zero, Set.mem_empty_iff_false, iff_false]
    exact not_lt.mpr hε
  rw [he, measure_empty, ENNReal.toReal_zero]

/-- Rank-zero frames have zero Gram failure deterministically for every
width, so no positive-rank concentration parameter is formed.
Source: `sh:srht-ose`, empty subspace endpoint. -/
theorem measure_srht_zero_rank_failure_eq_zero {n k : ℕ} (hk : k ≤ n)
    (H : Matrix (Fin n) (Fin n) ℝ) (U : Matrix (Fin n) (Fin 0) ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (srhtLaw hk {ω | ε < specNorm
      ((srhtSketch H ω.1 ω.2 * U)ᵀ * (srhtSketch H ω.1 ω.2 * U) - 1)}).toReal = 0 := by
  have he : {ω : (Fin n → Bool) × ExactRowSubset (Fin n) k | ε < specNorm
      ((srhtSketch H ω.1 ω.2 * U)ᵀ * (srhtSketch H ω.1 ω.2 * U) - 1)} = ∅ := by
    ext ω
    have hM : (srhtSketch H ω.1 ω.2 * U)ᵀ * (srhtSketch H ω.1 ω.2 * U) - 1 = 0 :=
      Subsingleton.elim _ _
    simp only [Set.mem_ofPred_eq, hM, specNorm_eq_norm, norm_zero,
      Set.mem_empty_iff_false, iff_false]
    exact not_lt.mpr hε
  rw [he, measure_empty, ENNReal.toReal_zero]

/-- The genuine capped classical SRHT prescription satisfies the source
failure bound, with exact recovery in the full-row branch. The equality
`hcount` applies this to `srhtCappedRowCount` directly.
Source: `sh:srht-ose`; atlas `srht-ose`. -/
theorem measure_srht_capped_gram_failure_le
    {n d k : ℕ} [NeZero n] [NeZero d]
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : Hᵀ * H = 1)
    (hHflat : ∀ i j, H i j ^ 2 = 1 / (n : ℝ))
    (U : Matrix (Fin n) (Fin d) ℝ) (hU : HasOrthonormalCols U)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hcount : k = srhtCappedRowCount n d ε δ) (hk : k ≤ n) :
    (srhtLaw hk {ω | ε < specNorm
      ((srhtSketch H ω.1 ω.2 * U)ᵀ * (srhtSketch H ω.1 ω.2 * U) - 1)}).toReal ≤ δ := by
  by_cases hfull : k = n
  · clear hcount
    subst k
    rw [measure_srht_full_rows_failure_eq_zero H hH U hU hε.le]
    exact hδ.le
  let T := 3 * srhtManuscriptRowBound n d δ / ε ^ 2 * Real.log (4 * d / δ)
  have hkn : k = ⌈T⌉₊ := by
    change k = min n ⌈T⌉₊ at hcount
    rcases le_total n ⌈T⌉₊ with h | h
    · rw [min_eq_left h] at hcount
      exact False.elim (hfull hcount)
    · simpa only [min_eq_right h] using hcount
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hsharp : 0 < srhtSharpRowBound n d δ := by
    apply sq_pos_of_pos
    apply add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_nonneg _)
  have hL : 0 < srhtManuscriptRowBound n d δ :=
    hsharp.trans_le (srhtSharpRowBound_le_manuscript hδ hδ1)
  have hlog : 0 < Real.log (4 * d / δ) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hδ]
    linarith
  have hT : 0 < T := by dsimp only [T]; positivity
  apply measure_srht_gram_failure_le_of_manuscript_sample_size
    (by rw [hkn]; exact Nat.ceil_pos.mpr hT) hk H hH hHflat U hU hε hε1 hδ hδ1
  change T ≤ (k : ℝ)
  rw [hkn]
  exact Nat.le_ceil T

/-- The genuine binary Walsh transform and one shared sign diagonal give
the classical SRHT theorem on dimensions `n=2^b`, with the manuscript's
exact row-count constants and uniform distinct-row sampling.
Source: `sh:srht-ose`; atlas `srht-ose`. -/
theorem measure_walsh_srht_gram_failure_le
    {b d k : ℕ} [NeZero d] (hk0 : 0 < k) (hk : k ≤ 2 ^ b)
    (U : Matrix (Fin (2 ^ b)) (Fin d) ℝ) (hU : HasOrthonormalCols U)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsize : 3 * srhtManuscriptRowBound (2 ^ b) d δ / ε ^ 2 * Real.log (4 * d / δ) ≤ k) :
    (srhtLaw hk {ω | ε < specNorm
      ((srhtSketch (walshMatrixFin b) ω.1 ω.2 * U)ᵀ *
        (srhtSketch (walshMatrixFin b) ω.1 ω.2 * U) - 1)}).toReal ≤ δ := by
  have : NeZero (2 ^ b) := ⟨pow_ne_zero _ (by norm_num)⟩
  exact measure_srht_gram_failure_le_of_manuscript_sample_size hk0 hk
    (walshMatrixFin b) (walshMatrixFin_transpose_mul_self b) (walshMatrixFin_apply_sq b)
    U hU hε hε1 hδ hδ1 hsize

/-- Applying the literal capped width directly, without an extra cardinality
hypothesis, gives the classical SRHT OSE including its full-row branch.
Source: `sh:srht-ose`; atlas `srht-ose`. -/
theorem measure_srht_gram_failure_le_with_capped_width
    {n d : ℕ} [NeZero n] [NeZero d]
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : Hᵀ * H = 1)
    (hHflat : ∀ i j, H i j ^ 2 = 1 / (n : ℝ))
    (U : Matrix (Fin n) (Fin d) ℝ) (hU : HasOrthonormalCols U)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (srhtLaw (srhtCappedRowCount_le n d ε δ) {ω | ε < specNorm
      ((srhtSketch H ω.1 ω.2 * U)ᵀ * (srhtSketch H ω.1 ω.2 * U) - 1)}).toReal ≤ δ :=
  measure_srht_capped_gram_failure_le H hH hHflat U hU hε hε1 hδ hδ1 rfl
    (srhtCappedRowCount_le n d ε δ)

/-- The actual Walsh transform with the literal capped width satisfies the
classical OSE, with exact recovery when the prescription selects all rows.
Source: `sh:srht-ose`; atlas `srht-ose`. -/
theorem measure_walsh_srht_gram_failure_le_with_capped_width
    {b d : ℕ} [NeZero d]
    (U : Matrix (Fin (2 ^ b)) (Fin d) ℝ) (hU : HasOrthonormalCols U)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (srhtLaw (srhtCappedRowCount_le (2 ^ b) d ε δ) {ω | ε < specNorm
      ((srhtSketch (walshMatrixFin b) ω.1 ω.2 * U)ᵀ *
        (srhtSketch (walshMatrixFin b) ω.1 ω.2 * U) - 1)}).toReal ≤ δ := by
  have : NeZero (2 ^ b) := ⟨pow_ne_zero _ (by norm_num)⟩
  exact measure_srht_gram_failure_le_with_capped_width (walshMatrixFin b)
    (walshMatrixFin_transpose_mul_self b) (walshMatrixFin_apply_sq b) U hU hε hε1 hδ hδ1

end NLAlib
