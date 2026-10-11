import NLAlib.Sketching.SamplingMultiplication
import NLAlib.Concentration.Matrix.SamplingSpectralBounds
import NLAlib.Matrix.ComplexEmbedding

/-!
# Leverage sampling with replacement

An actual finite product law samples rows and rescales by `1/√(k p_i)`.
Its rank-one Gram samples are proved isotropic and bounded before applying
the established complex matrix Chernoff theorem.
Source: operator re-derivation `sa:leverage-theorem`.
Atlas: `leverage-sampling-ose`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator
namespace NLAlib

/-- The actual row sampling and rescaling sketch: row `j` has its only
nonzero entry at the independently sampled index `ω j`.
Source: operator re-derivation `sa:leverage`. -/
def leverageSamplingSketch {n : Type*} [DecidableEq n] (p : n → ℝ≥0)
    {k : ℕ} (ω : Fin k → n) : Matrix (Fin k) n ℂ := fun j i =>
  if i = ω j then ((Real.sqrt ((k : ℝ) * p (ω j)))⁻¹ : ℂ) else 0

/-- Multiplying by the literal leverage sampling sketch selects and rescales
the rows. Source: operator re-derivation `sa:leverage`. -/
theorem leverageSamplingSketch_mul {n d : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n d ℂ) (p : n → ℝ≥0) {k : ℕ} (ω : Fin k → n) :
    leverageSamplingSketch p ω * U = sampledRowMatrix U p ω := by
  ext j a
  simp [Matrix.mul_apply, leverageSamplingSketch, sampledRowMatrix,
    Complex.real_smul]

/-- Conjugate transpose commutes with the real sampled-column rescaling.
Source: operator re-derivations `sa:leverage`, `sa:amm`. -/
theorem sampledRowMatrix_conjTranspose {n d : Type*}
    (U : Matrix n d ℂ) (p : n → ℝ≥0) {k : ℕ} (ω : Fin k → n) :
    (sampledRowMatrix U p ω)ᴴ = sampledColumnMatrix Uᴴ p ω := by
  ext a j
  simp [sampledRowMatrix, sampledColumnMatrix, Matrix.conjTranspose_apply]

/-- The sampled Gram matrix is the average of genuine inverse-probability
rank-one samples. Source: operator re-derivation `sa:leverage`. -/
theorem conjTranspose_leverageSamplingSketch_mul_self
    {n : Type*} [Fintype n] [DecidableEq n] {d : ℕ}
    (U : Matrix n (Fin d) ℂ) (p : n → ℝ≥0) {k : ℕ} (ω : Fin k → n) :
    (leverageSamplingSketch p ω * U)ᴴ * (leverageSamplingSketch p ω * U) =
      (1 / (k : ℝ)) • ∑ j, columnRowSample Uᴴ U p (ω j) := by
  rw [leverageSamplingSketch_mul, sampledRowMatrix_conjTranspose]
  exact sampledColumnMatrix_mul_sampledRowMatrix Uᴴ U p ω

/-- Leverage-dominating probabilities give the exact complex Gram failure
bound `2 d exp(-β k ε²/(3d))` for the literal finite sampling/rescaling algorithm.
The rank-one isotropy and eigenvalue bounds are derived from `UᴴU = I`
and the probability domination, including zero-probability rows.
Source: operator re-derivation `sa:leverage-theorem`, Tropp 2015, Chapter 5.
atlas: leverage-sampling-ose (partial) -/
theorem measure_le_spectralNorm_leverage_gram_sub_one
    {n : Type*} [Fintype n] [DecidableEq n] [MeasurableSpace n] [MeasurableSingletonClass n]
    {d k : ℕ} [NeZero d] (hk : 0 < k)
    (U : Matrix n (Fin d) ℂ) (hU : Uᴴ * U = 1)
    (p : n → ℝ≥0) (hp : ∑ i, p i = 1) {β : ℝ} (hβ : 0 < β)
    (hdom : ∀ i, β * (∑ a, ‖U i a‖ ^ 2) / d ≤ p i)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    (Measure.pi (fun _ : Fin k => finiteSamplingLaw p hp)
      {ω | ε ≤ spectralNorm
        ((leverageSamplingSketch p ω * U)ᴴ * (leverageSamplingSketch p ω * U) - 1)}).toReal ≤
      2 * d * Real.exp (-β * k * ε ^ 2 / (3 * d)) := by
  classical
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  let X : n → Matrix (Fin d) (Fin d) ℂ := columnRowSample Uᴴ U p
  have hPSD : ∀ i, (X i).PosSemidef := by
    intro i
    exact (Matrix.posSemidef_vecMulVec_star_self (U i)).smul
      (inv_nonneg.mpr (p i).coe_nonneg)
  have htrace : ∀ i, (X i).trace.re = (∑ a, ‖U i a‖ ^ 2) / p i := by
    intro i
    simp only [X, columnRowSample, Matrix.trace, Matrix.diag, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, Complex.smul_re,
      Complex.re_sum, smul_eq_mul]
    change (∑ a, (p i : ℝ)⁻¹ * (star (U i a) * U i a).re) = _
    have hnorm : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := by
      intro z
      have heq : (Complex.normSq z : ℂ) = star z * z := Complex.normSq_eq_conj_mul_self
      have hh := congrArg Complex.re heq
      simpa only [Complex.ofReal_re, Complex.normSq_eq_norm_sq] using hh.symm
    rw [div_eq_mul_inv, mul_comm _ (p i : ℝ)⁻¹, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [hnorm]
  have hbound : ∀ i, (X i).trace.re ≤ (d : ℝ) / β := by
    intro i
    rw [htrace]
    by_cases hi : (p i : ℝ) = 0
    · rw [hi, div_zero]
      positivity
    · have hip : 0 < (p i : ℝ) := lt_of_le_of_ne (p i).coe_nonneg (Ne.symm hi)
      rw [div_le_div_iff₀ hip hβ]
      have hh := hdom i
      rw [div_le_iff₀ hd] at hh
      nlinarith
  have hsupport : ∀ i, p i = 0 →
      Matrix.vecMulVec (fun a => Uᴴ a i) (fun b => U i b) = 0 := by
    intro i hi
    have hq : ∑ a, ‖U i a‖ ^ 2 = 0 := by
      have hh := hdom i
      rw [hi, NNReal.coe_zero, div_le_iff₀ hd, zero_mul] at hh
      have hnn : 0 ≤ ∑ a, ‖U i a‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      nlinarith
    have hrow : ∀ a, U i a = 0 := by
      intro a
      have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg ‖U i a‖)).mp hq
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp (hh a (Finset.mem_univ a)))
    ext a b
    simp [Matrix.vecMulVec_apply, hrow]
  let ν := finiteSamplingLaw p hp
  let M : Fin k → (Fin k → n) → Matrix (Fin d) (Fin d) ℂ := fun j ω => X (ω j)
  have hmean : ∀ j, ∫ ω, M j ω ∂Measure.pi (fun _ : Fin k => ν) = 1 := by
    intro j
    rw [show (fun ω => M j ω) = (fun ω : Fin k → n => X (ω j)) from rfl,
      integral_comp_eval (show AEStronglyMeasurable X ν from .of_discrete)]
    change (∫ i, X i ∂finiteSamplingLaw p hp) = 1
    rw [integral_finiteSamplingLaw]
    exact (sum_probability_smul_columnRowSample Uᴴ U p hsupport).trans hU
  have hind : iIndepFun M (Measure.pi (fun _ : Fin k => ν)) :=
    iIndepFun_pi (fun _ => (show AEMeasurable X ν from Measurable.of_discrete.aemeasurable))
  have hherm : ∀ j, ∀ᵐ ω ∂Measure.pi (fun _ : Fin k => ν), (M j ω).IsHermitian :=
    fun j => ae_of_all _ (fun ω => (hPSD (ω j)).isHermitian)
  have hb : ∀ j, ∀ᵐ ω ∂Measure.pi (fun _ : Fin k => ν),
      0 ≤ lambdaMin (M j ω) ∧ lambdaMax (M j ω) ≤ (d : ℝ) / β := by
    intro j
    exact ae_of_all _ (fun ω => ⟨lambdaMin_nonneg_of_posSemidef (hPSD (ω j)),
      (lambdaMax_le_trace_of_posSemidef (hPSD (ω j))).trans (hbound (ω j))⟩)
  obtain ⟨hl, hu⟩ := matrix_chernoff_sampling (Measure.pi (fun _ : Fin k => ν)) hk M
    ((d : ℝ) / β) (div_pos hd hβ) (fun _ => .of_discrete) hind hherm hb hmean hε0.le hε1
  have hsub : {ω | ε ≤ spectralNorm
      ((leverageSamplingSketch p ω * U)ᴴ * (leverageSamplingSketch p ω * U) - 1)} ⊆
      {ω | lambdaMin ((1 / (k : ℝ)) • ∑ j, M j ω) ≤ 1 - ε} ∪
      {ω | 1 + ε ≤ lambdaMax ((1 / (k : ℝ)) • ∑ j, M j ω)} := by
    intro ω hω
    have hh := lambdaMin_le_or_le_lambdaMax_of_le_spectralNorm_sub_one
      (Matrix.isHermitian_conjTranspose_mul_self (leverageSamplingSketch p ω * U)) hω
    simpa only [Set.mem_union, Set.mem_ofPred_eq,
      conjTranspose_leverageSamplingSketch_mul_self, M, X] using hh
  have hexp : Real.exp (-ε ^ 2 * k / (2 * ((d : ℝ) / β))) ≤
      Real.exp (-ε ^ 2 * k / (3 * ((d : ℝ) / β))) := by
    apply Real.exp_le_exp.mpr
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hprod : 0 ≤ ε ^ 2 * (k : ℝ) * ((d : ℝ) / β) := by positivity
    nlinarith only [hprod]
  calc
    _ ≤ (Measure.pi (fun _ : Fin k => ν)).real
      ({ω | lambdaMin ((1 / (k : ℝ)) • ∑ j, M j ω) ≤ 1 - ε} ∪
       {ω | 1 + ε ≤ lambdaMax ((1 / (k : ℝ)) • ∑ j, M j ω)}) := measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ (d : ℝ) * Real.exp (-ε ^ 2 * k / (2 * ((d : ℝ) / β))) +
        d * Real.exp (-ε ^ 2 * k / (3 * ((d : ℝ) / β))) := add_le_add hl hu
    _ ≤ 2 * d * Real.exp (-ε ^ 2 * k / (3 * ((d : ℝ) / β))) := by
      nlinarith [mul_le_mul_of_nonneg_left hexp hd.le]
    _ = _ := by congr 2; field_simp

/-- A leverage Gram success preserves squared norms throughout the full data
range. Source: operator re-derivation `sa:leverage-theorem`; complex norm form. -/
theorem norm_leverage_mulVec_sq_bounds_of_gram_le
    {n q : Type*} [Fintype n] [Fintype q] [DecidableEq n] {d k : ℕ}
    (U : Matrix n (Fin d) ℂ) (hU : Uᴴ * U = 1)
    (A : Matrix n q ℂ) (hUA : U * (Uᴴ * A) = A)
    (p : n → ℝ≥0) (ω : Fin k → n) {ε : ℝ}
    (h : spectralNorm
      ((leverageSamplingSketch p ω * U)ᴴ * (leverageSamplingSketch p ω * U) - 1) ≤ ε)
    (x : q → ℂ) :
    (1 - ε) * ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℂ n)‖ ^ 2 ≤
        ‖(WithLp.toLp 2 (leverageSamplingSketch p ω *ᵥ (A *ᵥ x)) :
          EuclideanSpace ℂ (Fin k))‖ ^ 2 ∧
      ‖(WithLp.toLp 2 (leverageSamplingSketch p ω *ᵥ (A *ᵥ x)) :
        EuclideanSpace ℂ (Fin k))‖ ^ 2 ≤
        (1 + ε) * ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℂ n)‖ ^ 2 := by
  let y := (Uᴴ * A) *ᵥ x
  have ha : U *ᵥ y = A *ᵥ x := by
    dsimp only [y]
    rw [Matrix.mulVec_mulVec, hUA]
  have hnorm : ‖(WithLp.toLp 2 (U *ᵥ y) : EuclideanSpace ℂ n)‖ ^ 2 =
      ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin d))‖ ^ 2 := by
    obtain ⟨hl, hu⟩ := norm_mulVec_sq_bounds_of_norm_gram_sub_one_le U
      (show ‖Uᴴ * U - 1‖ ≤ (0 : ℝ) by rw [hU, sub_self, norm_zero]) y
    simp only [sub_zero, add_zero, one_mul] at hl hu
    exact le_antisymm hu hl
  have hh := norm_mulVec_sq_bounds_of_norm_gram_sub_one_le
    (leverageSamplingSketch p ω * U) h y
  rw [← hnorm, ha, ← Matrix.mulVec_mulVec, ha] at hh
  exact hh

/-- The explicit sufficient sample count makes the source Chernoff tail at
most `δ`. Source: operator re-derivation `sa:leverage-theorem`. -/
theorem leverage_tail_le_of_sample_size {d k : ℕ} (hd : 0 < d)
    {β ε δ : ℝ} (hβ : 0 < β) (hε : 0 < ε) (hδ : 0 < δ)
    (hsize : 3 * (d : ℝ) / (β * ε ^ 2) * Real.log (2 * d / δ) ≤ k) :
    2 * d * Real.exp (-β * k * ε ^ 2 / (3 * d)) ≤ δ := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog : Real.log (2 * d / δ) ≤ β * k * ε ^ 2 / (3 * d) := by
    have hh := mul_le_mul_of_nonneg_left hsize
      (show 0 ≤ β * ε ^ 2 / (3 * d) by positivity)
    have hc : β * ε ^ 2 / (3 * d) *
        (3 * d / (β * ε ^ 2) * Real.log (2 * d / δ)) = Real.log (2 * d / δ) := by
      field_simp
    rw [hc] at hh
    calc
      _ ≤ β * ε ^ 2 / (3 * d) * (k : ℝ) := hh
      _ = _ := by ring
  calc
    _ ≤ 2 * d * Real.exp (-Real.log (2 * d / δ)) := by
      gcongr
      simpa only [neg_div, neg_mul] using neg_le_neg hlog
    _ = δ := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp

/-- The literal complex leverage sketch preserves every data-vector norm
with failure probability at most `δ` at the exact stated sample count.
The data range lies in the given orthonormal frame; probabilities may vanish
on zero-leverage rows. Source: operator re-derivation `sa:leverage-theorem`.
atlas: leverage-sampling-ose -/
theorem measure_leverage_embedding_failure_le_of_sample_size
    {n q : Type*} [Fintype n] [Fintype q] [DecidableEq n]
    [MeasurableSpace n] [MeasurableSingletonClass n]
    {d k : ℕ} [NeZero d] (hk : 0 < k)
    (U : Matrix n (Fin d) ℂ) (hU : Uᴴ * U = 1)
    (A : Matrix n q ℂ) (hUA : U * (Uᴴ * A) = A)
    (p : n → ℝ≥0) (hp : ∑ i, p i = 1) {β : ℝ} (hβ : 0 < β)
    (hdom : ∀ i, β * (∑ a, ‖U i a‖ ^ 2) / d ≤ p i)
    {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ)
    (hsize : 3 * (d : ℝ) / (β * ε ^ 2) * Real.log (2 * d / δ) ≤ k) :
    (Measure.pi (fun _ : Fin k => finiteSamplingLaw p hp)
      {ω | ∃ x : q → ℂ,
        ‖(WithLp.toLp 2 (leverageSamplingSketch p ω *ᵥ (A *ᵥ x)) :
          EuclideanSpace ℂ (Fin k))‖ ^ 2 <
          (1 - ε) * ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℂ n)‖ ^ 2 ∨
        (1 + ε) * ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℂ n)‖ ^ 2 <
          ‖(WithLp.toLp 2 (leverageSamplingSketch p ω *ᵥ (A *ᵥ x)) :
            EuclideanSpace ℂ (Fin k))‖ ^ 2}).toReal ≤ δ := by
  have hsub : {ω | ∃ x : q → ℂ,
        ‖(WithLp.toLp 2 (leverageSamplingSketch p ω *ᵥ (A *ᵥ x)) :
          EuclideanSpace ℂ (Fin k))‖ ^ 2 <
          (1 - ε) * ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℂ n)‖ ^ 2 ∨
        (1 + ε) * ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℂ n)‖ ^ 2 <
          ‖(WithLp.toLp 2 (leverageSamplingSketch p ω *ᵥ (A *ᵥ x)) :
            EuclideanSpace ℂ (Fin k))‖ ^ 2} ⊆
      {ω | ε ≤ spectralNorm
        ((leverageSamplingSketch p ω * U)ᴴ * (leverageSamplingSketch p ω * U) - 1)} := by
    intro ω hω
    obtain ⟨x, hx⟩ := hω
    by_contra hnot
    change ¬ε ≤ spectralNorm _ at hnot
    obtain ⟨hl, hu⟩ := norm_leverage_mulVec_sq_bounds_of_gram_le U hU A hUA p ω
      (not_le.mp hnot).le x
    rcases hx with hx | hx <;> linarith
  exact (measureReal_mono hsub).trans
    ((measure_le_spectralNorm_leverage_gram_sub_one hk U hU p hp hβ hdom hε0 hε1).trans
      (leverage_tail_le_of_sample_size (Nat.pos_of_ne_zero (NeZero.ne d)) hβ hε0 hδ hsize))

/-- A rank-zero range is preserved by every sketch deterministically, without
forming a normalized leverage law. Source: operator re-derivation `sa:leverage-theorem`.
atlas: leverage-sampling-ose -/
theorem norm_mulVec_sq_bounds_of_zero_range
    {n q k : Type*} [Fintype n] [Fintype q] [Fintype k]
    (S : Matrix k n ℂ) (A : Matrix n q ℂ) (U : Matrix n (Fin 0) ℂ)
    (hUA : U * (Uᴴ * A) = A) (ε : ℝ) (x : q → ℂ) :
    (1 - ε) * ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℂ n)‖ ^ 2 ≤
        ‖(WithLp.toLp 2 (S *ᵥ (A *ᵥ x)) : EuclideanSpace ℂ k)‖ ^ 2 ∧
      ‖(WithLp.toLp 2 (S *ᵥ (A *ᵥ x)) : EuclideanSpace ℂ k)‖ ^ 2 ≤
        (1 + ε) * ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℂ n)‖ ^ 2 := by
  have hA : A = 0 := by
    rw [← hUA]
    ext i j
    simp [Matrix.mul_apply]
  simp [hA]

end NLAlib
