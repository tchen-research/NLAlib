import NLAlib.Matrix.PowerRayleigh
import NLAlib.Gaussian.LogOverlapMoments

/-!
# Expected error of Gaussian random-start power iteration

The actual power iterate and Mathlib Rayleigh quotient satisfy the gap-free
logarithmic-overlap expectation bound. The zero-matrix relative error is zero.
Source: manuscript `rt:power`; KW (1992), random-start power method.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

/-- The relative error of the Rayleigh quotient of the actual `q`-th power iterate.
Source: manuscript `rt:power`; the zero-matrix value is zero by totalized division. -/
def powerRayleighRelativeError {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (b : ι → ℝ) (q : ℕ) : ℝ :=
  (specNorm A - (Matrix.toEuclideanCLM (𝕜 := ℝ) A).rayleighQuotient
    (WithLp.toLp 2 ((A ^ q) *ᵥ b))) / specNorm A

/-- The actual PSD power-method relative error lies in `[0,1]` at every start,
including a zero power iterate and a zero input matrix. Source: manuscript `rt:power`. -/
theorem powerRayleighRelativeError_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (b : ι → ℝ) (q : ℕ) :
    0 ≤ powerRayleighRelativeError A b q ∧ powerRayleighRelativeError A b q ≤ 1 := by
  by_cases hL : specNorm A = 0
  · simp only [powerRayleighRelativeError, hL, div_zero, le_refl, zero_le_one, and_self]
  · have hLp : 0 < specNorm A := (specNorm_nonneg A).lt_of_ne (Ne.symm hL)
    obtain ⟨h0, h1⟩ := rayleighQuotient_toEuclideanCLM_bounds hA ((A ^ q) *ᵥ b)
    constructor
    · exact div_nonneg (sub_nonneg.mpr h1) hLp.le
    · apply (div_le_one hLp).mpr
      linarith

/-- The actual power-method relative error is measurable as a function of the start.
Source: manuscript `rt:power`, finite polynomial-vector Rayleigh quotient. -/
theorem measurable_powerRayleighRelativeError {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (q : ℕ) : Measurable (fun b : ι → ℝ => powerRayleighRelativeError A b q) := by
  unfold powerRayleighRelativeError
  simp only [rayleighQuotient_toEuclideanCLM_eq, Matrix.mulVec, dotProduct]
  fun_prop

/-- Expected Gaussian random-start power error has the source's explicit gap-free
constant `min(1,(log(2N)+2)/(2q+1))`. Source: manuscript `rt:power`; KW (1992).
This theorem uses the actual Gaussian coordinate law and actual power iterate,
includes `q=0` and the zero matrix, and assumes no overlap moment.
atlas: random-start-power (partial) -/
theorem integral_powerRayleighRelativeError_pi_gaussianReal_le
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.PosSemidef) (q : ℕ) :
    (∫ b : Fin (n + 1) → ℝ, powerRayleighRelativeError A b q
      ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1)) ≤
      min 1 ((Real.log (2 * ((n + 1 : ℕ) : ℝ)) + 2) / ((2 * q + 1 : ℕ) : ℝ)) := by
  let μ := Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1
  let T := Real.log (2 * ((n + 1 : ℕ) : ℝ))
  let r := ((2 * q + 1 : ℕ) : ℝ)
  have hr : 0 < r := by dsimp only [r]; exact_mod_cast (by omega : 0 < 2 * q + 1)
  have hT : 0 ≤ T := by
    apply Real.log_nonneg
    have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 1)
    linarith
  have hfm := measurable_powerRayleighRelativeError A q
  have hfi : Integrable (fun b => powerRayleighRelativeError A b q) μ := by
    refine (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable ?_
    exact ae_of_all _ fun b => by
      rw [Real.norm_of_nonneg (powerRayleighRelativeError_bounds hA b q).1]
      exact (powerRayleighRelativeError_bounds hA b q).2
  have hOne : (∫ b, powerRayleighRelativeError A b q ∂μ) ≤ 1 := by
    have h := integral_mono hfi (integrable_const (1 : ℝ))
      (fun b => (powerRayleighRelativeError_bounds hA b q).2)
    simpa only [integral_const, probReal_univ, one_smul] using h
  apply le_min hOne
  by_cases hZero : specNorm A = 0
  · simp only [powerRayleighRelativeError, hZero, div_zero, integral_zero]
    exact div_nonneg (by linarith) hr.le
  · have hL : 0 < specNorm A := (specNorm_nonneg A).lt_of_ne (Ne.symm hZero)
    obtain ⟨i₀, hi⟩ := (IsGreatest.pi_norm hA.isHermitian.eigenvalues).1
    dsimp only at hi
    have h₀ : hA.isHermitian.eigenvalues i₀ = specNorm A := by
      rw [specNorm_eq_norm_eigenvalues hA.isHermitian, ← hi,
        Real.norm_of_nonneg (hA.eigenvalues_nonneg i₀)]
    let C := fun b : Fin (n + 1) → ℝ =>
      fun i => (hA.isHermitian.eigenvectorBasis i : Fin (n + 1) → ℝ) ⬝ᵥ b
    have hMP : MeasurePreserving C μ μ := by
      exact measurePreserving_eigenvectorBasis_dotProduct_pi_gaussianReal hA.isHermitian
    let L := fun c : Fin (n + 1) → ℝ => Real.log ((∑ i, c i ^ 2) / (c i₀) ^ 2)
    have hLm : Measurable L := by dsimp only [L]; fun_prop
    obtain ⟨hLI, hLV, _, _⟩ := integrable_and_integral_log_sum_div_sq_pi_gaussianReal_le n i₀
    have hLCI : Integrable (fun b => L (C b)) μ := by
      apply (integrable_map_measure hLm.aestronglyMeasurable hMP.measurable.aemeasurable).mp
      rwa [hMP.map_eq]
    have hLCV : (∫ b, L (C b) ∂μ) ≤ T + 2 := by
      have h := integral_map (μ := μ) hMP.measurable.aemeasurable hLm.aestronglyMeasurable
      rw [hMP.map_eq] at h
      exact h.symm.trans_le hLV
    have hHead := (measurePreserving_eval (fun _ : Fin (n + 1) => gaussianReal 0 1) i₀).comp hMP
    have hNZ : ∀ᵐ b ∂μ, C b i₀ ≠ 0 := by
      let := nullSingletonClass_gaussianReal (μ := 0) (v := 1) (by norm_num)
      have h := (gaussianReal 0 1).ae_ne 0
      rw [← hHead.map_eq] at h
      exact ae_of_ae_map hHead.measurable.aemeasurable h
    have hPoint : (fun b => powerRayleighRelativeError A b q) ≤ᵐ[μ] fun b => L (C b) / r := by
      filter_upwards [hNZ] with b hb
      have h := sub_rayleighQuotient_pow_div_specNorm_le_log_overlap_div hA hL i₀ h₀ b hb q
      rw [← sum_sq_eigenvectorBasis_dotProduct hA.isHermitian b] at h
      exact h
    have h := integral_mono_ae hfi (hLCI.div_const r) hPoint
    rw [integral_div] at h
    exact h.trans (div_le_div_of_nonneg_right hLCV hr.le)

/-- The Gaussian power-method expectation bound includes every matrix dimension,
with zero relative error for the empty and zero matrices. Source: manuscript `rt:power`.
atlas: random-start-power (partial) -/
theorem integral_powerRayleighRelativeError_pi_gaussianReal_le_all_dims
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) (q : ℕ) :
    (∫ b : Fin n → ℝ, powerRayleighRelativeError A b q
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) ≤
      min 1 ((Real.log (2 * (n : ℝ)) + 2) / ((2 * q + 1 : ℕ) : ℝ)) := by
  cases n with
  | zero =>
    have hzero : A = 0 := Subsingleton.elim _ _
    rw [hzero]
    simp only [powerRayleighRelativeError, specNorm_zero, div_zero, integral_zero,
      Nat.cast_zero, mul_zero, Real.log_zero, zero_add]
    apply le_min zero_le_one
    positivity
  | succ n => exact integral_powerRayleighRelativeError_pi_gaussianReal_le A hA q

/-- The gap-free power bound transports through an actual Gaussian starting-vector
law on an abstract probability space. Source: manuscript `rt:power`.
No measurability or integrability hypothesis is left to the caller beyond that law.
atlas: random-start-power (partial) -/
theorem integral_powerRayleighRelativeError_le_of_map_eq_pi_gaussianReal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) (q : ℕ) (G : Ω → Fin n → ℝ)
    (hG : μ.map G = Measure.pi fun _ : Fin n => gaussianReal 0 1) :
    (∫ ω, powerRayleighRelativeError A (G ω) q ∂μ) ≤
      min 1 ((Real.log (2 * (n : ℝ)) + 2) / ((2 * q + 1 : ℕ) : ℝ)) := by
  have hGm : AEMeasurable G μ := AEMeasurable.of_map_ne_zero
    (by rw [hG]; exact IsProbabilityMeasure.ne_zero _)
  have h := integral_map hGm (measurable_powerRayleighRelativeError A q).aestronglyMeasurable
  rw [hG] at h
  exact h.symm.trans_le (integral_powerRayleighRelativeError_pi_gaussianReal_le_all_dims A hA q)

/-- For positive iteration count and dimension at least two, the source's explicit
coarse power rate is `3 log(N)/q`. Source: manuscript `rt:power`, coarse corollary.
atlas: random-start-power (partial) -/
theorem integral_powerRayleighRelativeError_le_three_log_div
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) {q : ℕ} (hq : 1 ≤ q) (hn : 2 ≤ n)
    (G : Ω → Fin n → ℝ) (hG : μ.map G = Measure.pi fun _ : Fin n => gaussianReal 0 1) :
    (∫ ω, powerRayleighRelativeError A (G ω) q ∂μ) ≤ 3 * Real.log n / q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
  have hT : Real.log (2 * (n : ℝ)) + 2 ≤ 6 * Real.log n := by
    rw [Real.log_mul (by norm_num) hn0.ne']
    linarith
  have hr : (0 : ℝ) < ((2 * q + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * q + 1)
  have hc : (Real.log (2 * (n : ℝ)) + 2) / ((2 * q + 1 : ℕ) : ℝ) ≤ 3 * Real.log n / q := by
    apply (div_le_div_iff₀ hr hq0).mpr
    have h := mul_le_mul_of_nonneg_right hT hq0.le
    push_cast
    nlinarith
  exact ((integral_powerRayleighRelativeError_le_of_map_eq_pi_gaussianReal A hA q G hG).trans
    (min_le_right _ _)).trans hc

end NLAlib
