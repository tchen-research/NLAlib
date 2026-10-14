import NLAlib.Sketching.Structured.KhatriRaoEmbedding
import NLAlib.Sketching.Structured.KhatriRaoMoments
import NLAlib.RandomMatrix.Covariance.KhatriRaoMoments
import NLAlib.Probability.Concentration.Matrix.RankOneCovariance
import NLAlib.Probability.Concentration.Matrix.RankOneStep

/-!
# Sharp upper sample budget for Khatri–Rao embeddings

The actual independent vector-factor model satisfies the sharp embedding
budget through the finite rank-one trace-moment argument. All directional
moments, centering and iid process hypotheses are proved from the factor
laws; the final theorem has no moment-certificate assumptions.

Source: Heidary, *The Sharp Logarithmic Cost of Khatri–Rao Subspace
Embeddings*, Theorem 2.1, moment derivation.
<https://github.com/DiarHaidary/Results/blob/main/manuscripts/08-Khatri-Rao-Embeddings-and-Approximation/Khatri_Rao_Embeddings_and_Approximation_Focused.pdf>
-/

noncomputable section

open MeasureTheory Matrix

namespace NLAlib

/-- The coefficient controlling both variance and large-row scales in the
Khatri–Rao covariance moment estimate. Its dependence is only on tensor
order and the directional sub-Gaussian parameter. -/
def khatriRaoCovarianceScaleConstant (d : ℕ) (K : ℝ) : ℝ :=
  2 * Real.sqrt (4 * khatriRaoVarianceBudget d (max 1 K) 1) +
    32 * 2 ^ (d - 1) * 2 ^ (d - 2) * (max 1 K) ^ (2 * d)

/-- An explicit sufficient constant in the sharp Khatri–Rao embedding
sample budget. It is deliberately unoptimized and independent of all mode
dimensions, subspace rank, accuracy and confidence. -/
def khatriRaoSharpEmbeddingConstant (d : ℕ) (K : ℝ) : ℝ :=
  khatriRaoEmbeddingConstant d (Real.exp 1 * khatriRaoCovarianceScaleConstant d K)

/-- The explicit sharp embedding sample-budget constant is positive for
every tensor order and every real parameter.
atlas: khatri-rao-sharp-growth (partial) -/
theorem khatriRaoSharpEmbeddingConstant_pos (d : ℕ) (K : ℝ) :
    0 < khatriRaoSharpEmbeddingConstant d K := by
  unfold khatriRaoSharpEmbeddingConstant khatriRaoEmbeddingConstant
    khatriRaoCovarianceScaleConstant khatriRaoVarianceBudget
  positivity

private theorem covariance_scale_bound {d r q m : ℕ} (hd : 2 ≤ d) (hm : 1 ≤ m)
    {K : ℝ} (hK : 0 ≤ K) :
    (2 * Real.sqrt ((q : ℝ) * (4 * khatriRaoVarianceBudget d K r) * m) +
      2 * (q : ℝ) * (2 * khatriRaoMomentRadius d K r (2 * q))) / m ≤
      (2 * Real.sqrt (4 * khatriRaoVarianceBudget d K 1) +
        32 * 2 ^ (d - 1) * 2 ^ (d - 2) * K ^ (2 * d)) *
      (Real.sqrt ((q : ℝ) * r / m) + (q : ℝ) ^ (d - 1) * ((r : ℝ) + q) / m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hrad : 0 ≤ (q : ℝ) * r / m := by positivity
  let V := khatriRaoVarianceBudget d K 1
  let ρ : ℝ := 32 * 2 ^ (d - 1) * 2 ^ (d - 2) * K ^ (2 * d)
  have hV : 0 ≤ V := by dsimp [V, khatriRaoVarianceBudget]; positivity
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have harg : (q : ℝ) * (4 * khatriRaoVarianceBudget d K r) * m =
      (4 * V * ((q : ℝ) * r / m)) * (m : ℝ) ^ 2 := by
    dsimp [V, khatriRaoVarianceBudget]
    field_simp
    ring
  have hvar : 2 * Real.sqrt ((q : ℝ) * (4 * khatriRaoVarianceBudget d K r) * m) / m =
      2 * Real.sqrt (4 * V) * Real.sqrt ((q : ℝ) * r / m) := by
    rw [harg, Real.sqrt_mul (mul_nonneg (by positivity) hrad),
      Real.sqrt_mul (by positivity : 0 ≤ 4 * V), Real.sqrt_sq_eq_abs, abs_of_pos hmR]
    field_simp
  have hlin : 2 * (q : ℝ) * (2 * khatriRaoMomentRadius d K r (2 * q)) ≤
      ρ * (q : ℝ) ^ (d - 1) * ((r : ℝ) + q) := by
    have hlast : (r : ℝ) + 4 * (2 * q : ℕ) ≤ 8 * ((r : ℝ) + q) := by
      push_cast
      nlinarith [show (0 : ℝ) ≤ r from Nat.cast_nonneg r]
    have hmul := mul_le_mul_of_nonneg_left hlast
      (by positivity : 0 ≤ 4 * (q : ℝ) * 2 ^ (d - 1) * K ^ (2 * d) *
        ((2 * q : ℕ) : ℝ) ^ (d - 2))
    have hpow : (q : ℝ) * (q : ℝ) ^ (d - 2) = (q : ℝ) ^ (d - 1) := by
      rw [mul_comm, ← pow_succ, show d - 2 + 1 = d - 1 by omega]
    dsimp [khatriRaoMomentRadius, ρ]
    push_cast at hmul ⊢
    rw [mul_pow] at hmul
    rw [mul_pow]
    convert hmul using 1 <;> first | rfl | (rw [← hpow]; ring) | ring
  rw [add_div, hvar]
  have hldiv : 2 * (q : ℝ) * (2 * khatriRaoMomentRadius d K r (2 * q)) / m ≤
      ρ * ((q : ℝ) ^ (d - 1) * ((r : ℝ) + q) / m) := by
    convert div_le_div_of_nonneg_right hlin hmR.le using 1 <;> first | rfl | ring
  have hcross : 0 ≤ (2 * Real.sqrt (4 * V)) *
      ((q : ℝ) ^ (d - 1) * ((r : ℝ) + q) / m) + ρ * Real.sqrt ((q : ℝ) * r / m) := by
    positivity
  change _ ≤ (2 * Real.sqrt (4 * V) + ρ) * _
  calc
    _ ≤ 2 * Real.sqrt (4 * V) * Real.sqrt ((q : ℝ) * r / m) +
        ρ * ((q : ℝ) ^ (d - 1) * ((r : ℝ) + q) / m) := add_le_add le_rfl hldiv
    _ = (2 * Real.sqrt (4 * V) + ρ) *
        (Real.sqrt ((q : ℝ) * r / m) + (q : ℝ) ^ (d - 1) * ((r : ℝ) + q) / m) -
        ((2 * Real.sqrt (4 * V)) * ((q : ℝ) ^ (d - 1) * ((r : ℝ) + q) / m) +
          ρ * Real.sqrt ((q : ℝ) * r / m)) := by ring
    _ ≤ _ := sub_le_self _ hcross

/-- Independent isotropic directionally sub-Gaussian vector factors give
the sharp Khatri–Rao subspace-embedding sample budget at every confidence.
Coordinates within one factor may be dependent. Source: Heidary, Theorem
2.1, with an explicit unoptimized constant from the finite-moment derivation.
atlas: khatri-rao-sharp-growth (partial) -/
theorem measureReal_not_isSubspaceEmbedding_khatriRaoSketch_le
    {d r m : ℕ} {n : Fin d → ℕ} (hd : 2 ≤ d) (hr : 1 ≤ r) (hm : 1 ≤ m)
    (ν : ∀ j : Fin d, Measure (Fin (n j) → ℝ))
    [∀ j, IsProbabilityMeasure (ν j)] {K : ℝ} (hK : 0 < K)
    (hpsi : ∀ j (u : Fin (n j) → ℝ), ‖WithLp.toLp 2 u‖ = 1 →
      ∫⁻ g, ENNReal.ofReal (Real.exp ((u ⬝ᵥ g / K) ^ 2)) ∂ν j ≤ 2)
    (hsecond : ∀ j (a b : Fin (n j)),
      ∫ g, g a * g b ∂ν j = if a = b then 1 else 0)
    (U : Matrix (∀ j : Fin d, Fin (n j)) (Fin r) ℝ) (hU : HasOrthonormalCols U)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hbudget : khatriRaoSharpEmbeddingConstant d K *
      ((r : ℝ) * Real.log (4 * r / δ) / ε ^ 2 +
        ((r : ℝ) * Real.log (4 * r / δ) ^ (d - 1) +
          Real.log (4 * r / δ) ^ d) / ε) ≤ m) :
    (khatriRaoSampleLaw ν m).real
      {g | ¬ IsSubspaceEmbedding (khatriRaoSketch g) U ε} ≤ δ := by
  let y : (∀ j : Fin d, Fin (n j) → ℝ) → Fin r → ℝ :=
    fun g => Uᵀ *ᵥ khatriRaoProbe g
  let κ : ℝ := max 1 K
  let v := khatriRaoVarianceBudget d κ r
  let q := khatriRaoMomentOrder r δ
  let R := khatriRaoMomentRadius d κ r (2 * q)
  let C := khatriRaoCovarianceScaleConstant d K
  have hκ : 1 ≤ κ := le_max_left _ _
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hy : Measurable y := by unfold y khatriRaoProbe Matrix.mulVec dotProduct; fun_prop
  have hdir (p : ℕ) (hp : 1 ≤ p) (a : Fin r → ℝ) :
      Integrable (fun g => (a ⬝ᵥ y g) ^ (2 * p)) (Measure.pi ν) ∧
        (∫ g, (a ⬝ᵥ y g) ^ (2 * p) ∂Measure.pi ν) ≤
          (2 * (p.factorial : ℝ) * κ ^ (2 * p)) ^ d * (a ⬝ᵥ a) ^ p := by
    have h := integrable_and_integral_pow_two_mul_dotProduct_projected_khatriRaoProbe_le
      ν hK hpsi U hU (p := p) (by omega) a
    refine ⟨h.1, h.2.trans ?_⟩
    rw [show ‖WithLp.toLp 2 a‖ ^ (2 * p) = (‖WithLp.toLp 2 a‖ ^ 2) ^ p by rw [pow_mul],
      norm_toLp_sq_eq_dotProduct_self]
    gcongr
    · exact pow_nonneg (dotProduct_self_nonneg a) p
    · exact le_max_right 1 K
  have hmom (p : ℕ) : Integrable (fun g => (y g ⬝ᵥ y g) ^ p) (Measure.pi ν) := by
    by_cases hp : p = 0
    · subst p; simp
    have hnorm := integrable_and_integral_norm_mulVec_pow_two_mul_le y hy.aemeasurable
      (p := p) (by omega) (show 0 ≤ (2 * (p.factorial : ℝ) * κ ^ (2 * p)) ^ d by positivity)
      (fun a => by simpa only [pow_mul, norm_toLp_sq_eq_dotProduct_self] using hdir p (by omega) a)
      (1 : Matrix (Fin r) (Fin r) ℝ)
    simpa only [Matrix.one_mulVec, pow_mul, norm_toLp_sq_eq_dotProduct_self] using hnorm.1
  have hys (i j : Fin r) : ∫ g, y g i * y g j ∂Measure.pi ν = if i = j then 1 else 0 :=
    integral_projected_khatriRaoProbe_mul_projected_khatriRaoProbe ν hsecond U hU i j
  have hqb := khatriRaoMomentOrder_bounds hr hδ hδ1
  have hv : 2 ≤ v := two_le_khatriRaoVarianceBudget hr hκ
  have hvpos : 0 < v := by linarith
  have hR : 1 ≤ R := one_le_khatriRaoMomentRadius (by dsimp [q]; omega : 1 ≤ 2 * q) hκ
  have hstep p (hp : 1 ≤ p) (hpq : p ≤ q) (A : Matrix (Fin r) (Fin r) ℝ)
      (hA : A.IsHermitian) :=
    (integrable_and_integral_trace_add_centered_rankOne_pow_le y hy hys hA hp hv hR
      (fun l hl2 hlp x => by
        have hraw := integrable_and_integral_rankOneProbe_le_factorial hr hl2 hd y hy hκpos.le hdir x
        refine ⟨hraw.1, hraw.2.trans ?_⟩
        gcongr
        · exact dotProduct_self_nonneg x
        · unfold khatriRaoMomentRadius
          positivity
        · exact khatriRaoMomentRadius_mono hκpos.le (show l ≤ 2 * q by omega))).2
  let N : ℝ := 2 * Real.sqrt ((q : ℝ) * (4 * v) * m) + 2 * (q : ℝ) * (2 * R)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hC : 0 ≤ C := by dsimp [C, khatriRaoCovarianceScaleConstant]; positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hscale : Real.exp 1 * (N / m) ≤ ε := by
    have hprof := covariance_scale_bound (r := r) (q := q) hd hm hκpos.le
    have hmul := mul_le_mul_of_nonneg_left hprof (Real.exp_pos 1).le
    apply hmul.trans
    have ht := one_lt_log_four_mul_rank_div hr hδ hδ1
    have hb := mul_sqrt_add_pow_div_le_of_khatriRao_budget (by omega)
      (mul_nonneg (Real.exp_pos 1).le hC) (Nat.cast_nonneg r) hmR (by linarith)
      (Nat.cast_nonneg q) hqb.2.2 hε hbudget
    simpa only [C, khatriRaoCovarianceScaleConstant, κ, mul_assoc] using hb
  have hratio : N / ((m : ℝ) * ε) ≤ 1 / Real.exp 1 := by
    apply (div_le_div_iff₀ (mul_pos hmR hε) (Real.exp_pos 1)).2
    have hmultiply := mul_le_mul_of_nonneg_right hscale hmR.le
    field_simp at hmultiply
    nlinarith
  have htail := measureReal_lt_specNorm_smul_rankOneCovarianceSum_le hy hmom
    (show 0 < r by omega) (show 0 < 4 * v by positivity)
    (show 0 ≤ 2 * R by linarith) hqb.1 hm hε hstep
  have hpow := pow_le_pow_left₀ (div_nonneg hN (mul_nonneg hmR.le hε.le)) hratio (2 * q)
  have hexp : (1 / Real.exp 1) ^ (2 * q) = Real.exp (-2 * (q : ℝ)) := by
    rw [one_div, ← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hconf := rank_mul_exp_neg_two_mul_khatriRaoMomentOrder_le hr hδ hδ1
  have hfail : (khatriRaoSampleLaw ν m).real
      {g | ε < specNorm ((m : ℝ)⁻¹ • rankOneCovarianceSum y g)} ≤ δ := by
    apply htail.trans
    apply (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg r)).trans
    rw [hexp]
    exact hconf.trans (by linarith)
  have hevent : {g : Fin m → ∀ j : Fin d, Fin (n j) → ℝ |
        ¬ IsSubspaceEmbedding (khatriRaoSketch g) U ε} ⊆
      {g | ε < specNorm ((m : ℝ)⁻¹ • rankOneCovarianceSum y g)} := by
    intro g hg
    change ¬ IsSubspaceEmbedding (khatriRaoSketch g) U ε at hg
    change ε < specNorm ((m : ℝ)⁻¹ • rankOneCovarianceSum y g)
    rw [isSubspaceEmbedding_iff_specNorm_transpose_mul_self_sub_one_le hU hε.le] at hg
    rw [transpose_khatriRaoSketch_mul_self_sub_one (by omega)] at hg
    simpa only [rankOneCovarianceSum, centeredRankOneCovariance, y, not_le] using hg
  exact (measureReal_mono hevent).trans hfail

end NLAlib
