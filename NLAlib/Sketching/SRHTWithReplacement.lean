import NLAlib.Sketching.SRHT
import NLAlib.Concentration.Matrix.UniformIidSampling

/-!
# Classical one-diagonal SRHT with actual sampling with replacement

The source's variant uses an actual iid uniform label sequence, preserving
the same shared `D` and additive row bound, with unrestricted positive
width. Source: `sh:srht-ose`; atlas `srht-ose`.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory
open scoped Classical Matrix Matrix.Norms.L2Operator ENNReal ComplexOrder
namespace NLAlib

/-- The literal row selector for an iid sequence, permitting repeats.
Source: `sh:srht-ose`, with-replacement variant. -/
def srhtSequenceRowSelector {n k : ℕ} (I : Fin k → Fin n) : Matrix (Fin k) (Fin n) ℝ :=
  fun a j => if j = I a then 1 else 0

/-- The actual with-replacement classical `√(n/k) R H D` matrix.
Source: `sh:srht-ose`; one shared sign diagonal. -/
def srhtWithReplacementSketch {n k : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (ξ : Fin n → Bool) (I : Fin k → Fin n) : Matrix (Fin k) (Fin n) ℝ :=
  Real.sqrt ((n : ℝ) / k) •
    (srhtSequenceRowSelector I * H * Matrix.diagonal (fun i => rademacherBoolSign (ξ i)))

/-- The actual independent product law for the sign diagonal and iid row
sequence. Source: `sh:srht-ose`, with-replacement variant. -/
def srhtWithReplacementLaw (n k : ℕ) [NeZero n] :
    Measure ((Fin n → Bool) × (Fin k → Fin n)) :=
  (rademacherCubePMF (Fin n)).toMeasure.prod
    (PMF.uniformOfFintype (Fin k → Fin n)).toMeasure

instance srhtWithReplacementLaw_isProbabilityMeasure (n k : ℕ) [NeZero n] :
    IsProbabilityMeasure (srhtWithReplacementLaw n k) := by
  unfold srhtWithReplacementLaw
  infer_instance

/-- The literal iid sketch selects and rescales the transformed frame row.
Source: `sh:srht-ose`, with-replacement variant. -/
theorem srhtWithReplacementSketch_mul_apply {n k d : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ) (U : Matrix (Fin n) (Fin d) ℝ)
    (ξ : Fin n → Bool) (I : Fin k → Fin n) (a : Fin k) (b : Fin d) :
    (srhtWithReplacementSketch H ξ I * U) a b = Real.sqrt ((n : ℝ) / k) *
      srhtSignedFrame H U ξ (I a) b := by
  simp only [srhtWithReplacementSketch, Matrix.smul_mul, Matrix.smul_apply,
    smul_eq_mul, Matrix.mul_assoc, srhtSignedFrame]
  have hs : ∀ V : Matrix (Fin n) (Fin d) ℝ,
      (srhtSequenceRowSelector I * V) a b = V (I a) b := by
    intro V
    simp [srhtSequenceRowSelector, Matrix.mul_apply, ite_mul]
  rw [hs]

/-- The complex Chernoff iid population mean is exactly the extension of
the actual real sketch Gram matrix. Source: `sh:srht-ose`. -/
theorem map_ofReal_srhtWithReplacementSketch_gram {n k d : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ) (U : Matrix (Fin n) (Fin d) ℝ)
    (ξ : Fin n → Bool) (I : Fin k → Fin n) :
    ((srhtWithReplacementSketch H ξ I * U)ᵀ * (srhtWithReplacementSketch H ξ I * U)).map
      Complex.ofReal = (1 / (k : ℝ)) • ∑ a, srhtPopulationAtom (srhtSignedFrame H U ξ) (I a) := by
  have hG : (srhtWithReplacementSketch H ξ I * U)ᵀ * (srhtWithReplacementSketch H ξ I * U) =
      ((n : ℝ) / k) • ∑ a, Matrix.vecMulVec (srhtSignedFrame H U ξ (I a))
        (srhtSignedFrame H U ξ (I a)) := by
    ext a b
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, Matrix.smul_apply, Matrix.sum_apply,
      Matrix.vecMulVec_apply, smul_eq_mul]
    simp_rw [srhtWithReplacementSketch_mul_apply]
    have hm (j : Fin k) :
        (Real.sqrt ((n : ℝ) / k) * srhtSignedFrame H U ξ (I j) a) *
        (Real.sqrt ((n : ℝ) / k) * srhtSignedFrame H U ξ (I j) b) =
        ((n : ℝ) / k) * (srhtSignedFrame H U ξ (I j) a * srhtSignedFrame H U ξ (I j) b) := by
      calc
        _ = Real.sqrt ((n : ℝ) / k) ^ 2 *
            (srhtSignedFrame H U ξ (I j) a * srhtSignedFrame H U ξ (I j) b) := by ring
        _ = _ := by rw [Real.sq_sqrt (show 0 ≤ (n : ℝ) / k by positivity)]
    simp_rw [hm]
    exact (Finset.mul_sum _ _ _).symm
  rw [hG]
  ext a b
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.sum_apply, srhtPopulationAtom,
    Matrix.vecMulVec_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_sum,
    Pi.star_apply, Complex.star_def, Complex.conj_ofReal, Complex.real_smul,
    ← Finset.mul_sum, Complex.ofReal_div, Complex.ofReal_one]
  ring

/-- Conditional on actual flattened rows, the literal iid SRHT has the
same matrix Chernoff failure bound, without a population width restriction.
Source: `sh:srht-ose`, with-replacement variant. -/
theorem measure_srhtWithReplacement_gram_failure_le_of_flat_rows
    {n d k : ℕ} [NeZero n] [NeZero d] (hk : 0 < k)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : Hᵀ * H = 1)
    (U : Matrix (Fin n) (Fin d) ℝ) (hU : HasOrthonormalCols U)
    (ξ : Fin n → Bool) {L ε : ℝ} (hL : 0 < L)
    (hflat : ∀ j, (n : ℝ) * (srhtSignedFrame H U ξ j ⬝ᵥ srhtSignedFrame H U ξ j) ≤ L)
    (hε : 0 < ε) (hε1 : ε < 1) :
    ((PMF.uniformOfFintype (Fin k → Fin n)).toMeasure
      {I | ε < specNorm ((srhtWithReplacementSketch H ξ I * U)ᵀ *
        (srhtWithReplacementSketch H ξ I * U) - 1)}).toReal ≤
      2 * d * Real.exp (-(ε ^ 2) * k / (3 * L)) := by
  let V := srhtSignedFrame H U ξ
  let A := srhtPopulationAtom V
  have hPSD (j : Fin n) : (A j).PosSemidef := srhtPopulationAtom_posSemidef V j
  have hbound (j : Fin n) : 0 ≤ lambdaMin (A j) ∧ lambdaMax (A j) ≤ L := by
    refine ⟨lambdaMin_nonneg_of_posSemidef (hPSD j), ?_⟩
    have ht := trace_srhtPopulationAtom V j
    exact (lambdaMax_le_trace_of_posSemidef (hPSD j)).trans (by rw [ht]; exact hflat j)
  have hmean := mean_srhtPopulationAtom V (hasOrthonormalCols_srhtSignedFrame H hH U hU ξ)
  have hc := measure_spectralNorm_uniform_iid_sub_one_le hk A L hL
    (fun j => (hPSD j).isHermitian) hbound hmean hε hε1
  have hsub : {I : Fin k → Fin n | ε < specNorm ((srhtWithReplacementSketch H ξ I * U)ᵀ *
      (srhtWithReplacementSketch H ξ I * U) - 1)} ⊆
      {I | ε ≤ spectralNorm ((1 / (k : ℝ)) • ∑ a, A (I a) - 1)} := by
    intro I hI
    have hm : (((srhtWithReplacementSketch H ξ I * U)ᵀ *
        (srhtWithReplacementSketch H ξ I * U) - 1).map Complex.ofReal) =
        (1 / (k : ℝ)) • ∑ a, A (I a) - 1 := by
      rw [Matrix.map_sub Complex.ofReal Complex.ofReal_sub, map_ofReal_srhtWithReplacementSketch_gram]
      congr 1
      ext a b
      by_cases hab : a = b <;> simp [Matrix.map_apply, Matrix.one_apply, hab]
    have hn := specNorm_le_spectralNorm_map_ofReal
      ((srhtWithReplacementSketch H ξ I * U)ᵀ * (srhtWithReplacementSketch H ξ I * U) - 1)
    rw [hm] at hn
    exact hI.le.trans hn
  exact (measureReal_mono hsub).trans hc

/-- The genuine with-replacement classical SRHT theorem has the same sharp
additive row threshold and exact row count, with arbitrary positive width.
Source: `sh:srht-ose`, with-replacement variant. Atlas `srht-ose`. -/
theorem measure_srhtWithReplacement_gram_failure_le_of_sharp_sample_size
    {n d k : ℕ} [NeZero n] [NeZero d] (hk : 0 < k)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : Hᵀ * H = 1)
    (hHflat : ∀ i j, H i j ^ 2 = 1 / (n : ℝ))
    (U : Matrix (Fin n) (Fin d) ℝ) (hU : HasOrthonormalCols U)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsize : 3 * srhtSharpRowBound n d δ / ε ^ 2 * Real.log (4 * d / δ) ≤ k) :
    (srhtWithReplacementLaw n k {ω | ε < specNorm
      ((srhtWithReplacementSketch H ω.1 ω.2 * U)ᵀ *
        (srhtWithReplacementSketch H ω.1 ω.2 * U) - 1)}).toReal ≤ δ := by
  let L := srhtSharpRowBound n d δ
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hL : 0 < L := by
    apply sq_pos_of_pos
    exact add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr hdR) (Real.sqrt_nonneg _)
  let E : Set (Fin n → Bool) := {ξ | ∃ j : Fin n,
    L < (n : ℝ) * (srhtSignedFrame H U ξ j ⬝ᵥ srhtSignedFrame H U ξ j)}
  have hE := measure_srhtSharpRowBound_failure_le H hHflat U hU hδ hδ1
  have hcond (ξ : Fin n → Bool) (hξ : ξ ∉ E) :
      ((PMF.uniformOfFintype (Fin k → Fin n)).toMeasure
        {I | ε < specNorm ((srhtWithReplacementSketch H ξ I * U)ᵀ *
          (srhtWithReplacementSketch H ξ I * U) - 1)}).toReal ≤ δ / 2 := by
    have hrows (j : Fin n) : (n : ℝ) *
        (srhtSignedFrame H U ξ j ⬝ᵥ srhtSignedFrame H U ξ j) ≤ L := by
      by_contra hnot
      exact hξ ⟨j, lt_of_not_ge hnot⟩
    exact (measure_srhtWithReplacement_gram_failure_le_of_flat_rows hk H hH U hU ξ
      hL hrows hε hε1).trans
      (srht_tail_le_half_of_sample_size (Nat.pos_of_ne_zero (NeZero.ne d)) hL hε hδ hsize)
  have hh := measureReal_prod_le_bad_add (rademacherCubePMF (Fin n)).toMeasure
    (PMF.uniformOfFintype (Fin k → Fin n)).toMeasure E
    {ω | ε < specNorm ((srhtWithReplacementSketch H ω.1 ω.2 * U)ᵀ *
      (srhtWithReplacementSketch H ω.1 ω.2 * U) - 1)}
    (show 0 ≤ δ / 2 by positivity) hcond
  exact hh.trans (by linarith)

/-- The manuscript's exact coarser row bound also gives the actual iid
classical SRHT theorem with unrestricted positive width.
Source: `sh:srht-ose`, with-replacement variant. Atlas `srht-ose`. -/
theorem measure_srhtWithReplacement_gram_failure_le_of_manuscript_sample_size
    {n d k : ℕ} [NeZero n] [NeZero d] (hk : 0 < k)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : Hᵀ * H = 1)
    (hHflat : ∀ i j, H i j ^ 2 = 1 / (n : ℝ))
    (U : Matrix (Fin n) (Fin d) ℝ) (hU : HasOrthonormalCols U)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsize : 3 * srhtManuscriptRowBound n d δ / ε ^ 2 * Real.log (4 * d / δ) ≤ k) :
    (srhtWithReplacementLaw n k {ω | ε < specNorm
      ((srhtWithReplacementSketch H ω.1 ω.2 * U)ᵀ *
        (srhtWithReplacementSketch H ω.1 ω.2 * U) - 1)}).toReal ≤ δ := by
  apply measure_srhtWithReplacement_gram_failure_le_of_sharp_sample_size hk H hH hHflat U hU
    hε hε1 hδ hδ1
  refine le_trans ?_ hsize
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hlog : 0 ≤ Real.log (4 * d / δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]
    linarith
  gcongr
  exact srhtSharpRowBound_le_manuscript hδ hδ1

/-- The with-replacement variant specializes to the genuine Walsh transform,
with its unrestricted positive width and the manuscript's exact constants.
Source: `sh:srht-ose`; atlas `srht-ose`. -/
theorem measure_walsh_srhtWithReplacement_gram_failure_le
    {b d k : ℕ} [NeZero d] (hk : 0 < k)
    (U : Matrix (Fin (2 ^ b)) (Fin d) ℝ) (hU : HasOrthonormalCols U)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsize : 3 * srhtManuscriptRowBound (2 ^ b) d δ / ε ^ 2 * Real.log (4 * d / δ) ≤ k) :
    (srhtWithReplacementLaw (2 ^ b) k {ω | ε < specNorm
      ((srhtWithReplacementSketch (walshMatrixFin b) ω.1 ω.2 * U)ᵀ *
        (srhtWithReplacementSketch (walshMatrixFin b) ω.1 ω.2 * U) - 1)}).toReal ≤ δ := by
  have : NeZero (2 ^ b) := ⟨pow_ne_zero _ (by norm_num)⟩
  exact measure_srhtWithReplacement_gram_failure_le_of_manuscript_sample_size hk
    (walshMatrixFin b) (walshMatrixFin_transpose_mul_self b) (walshMatrixFin_apply_sq b)
    U hU hε hε1 hδ hδ1 hsize

/-- Rank zero has exact zero error at every width under the actual iid row
and shared-sign law. Source: `sh:srht-ose`, empty subspace endpoint. -/
theorem measure_srhtWithReplacement_zero_rank_failure_eq_zero
    {n k : ℕ} [NeZero n] (H : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin 0) ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    (srhtWithReplacementLaw n k {ω | ε < specNorm
      ((srhtWithReplacementSketch H ω.1 ω.2 * U)ᵀ *
        (srhtWithReplacementSketch H ω.1 ω.2 * U) - 1)}).toReal = 0 := by
  have he : {ω : (Fin n → Bool) × (Fin k → Fin n) | ε < specNorm
      ((srhtWithReplacementSketch H ω.1 ω.2 * U)ᵀ *
        (srhtWithReplacementSketch H ω.1 ω.2 * U) - 1)} = ∅ := by
    ext ω
    have hM : (srhtWithReplacementSketch H ω.1 ω.2 * U)ᵀ *
        (srhtWithReplacementSketch H ω.1 ω.2 * U) - 1 = 0 := Subsingleton.elim _ _
    simp only [Set.mem_ofPred_eq, hM, specNorm_eq_norm, norm_zero,
      Set.mem_empty_iff_false, iff_false]
    exact not_lt.mpr hε
  rw [he, measure_empty, ENNReal.toReal_zero]

end NLAlib
