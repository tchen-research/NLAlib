import NLAlib.Krylov.MeasurableRitz
import NLAlib.Polynomial.LanczosFilterMean
import NLAlib.Gaussian.LogOverlapMoments

/-!
# Expected Lanczos error from logarithmic Gaussian overlap

The algorithm's value is the measurable supremum of the actual Krylov Rayleigh
quotients. A genuine even Chebyshev polynomial supplies the deterministic
comparison, and the Gaussian logarithmic moments give the source's explicit
gap-free expectation constant.
-/

noncomputable section
open Polynomial MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

/-- Relative error of the actual variational `q`-step Lanczos Ritz value.
Source: manuscript `rt:lanczos`; the zero-matrix relative error is zero. -/
def lanczosRayleighRelativeError {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (b : ι → ℝ) (q : ℕ) : ℝ :=
  (specNorm A - lanczosRitzValue A b q) / specNorm A

/-- The PSD Lanczos relative error lies in `[0,1]` at every start.
Source: manuscript `rt:lanczos`, variational bounds. -/
theorem lanczosRayleighRelativeError_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (b : ι → ℝ) (q : ℕ) :
    0 ≤ lanczosRayleighRelativeError A b q ∧ lanczosRayleighRelativeError A b q ≤ 1 := by
  by_cases hL : specNorm A = 0
  · simp only [lanczosRayleighRelativeError, hL, div_zero, le_refl, zero_le_one, and_self]
  · have hLp : 0 < specNorm A := (specNorm_nonneg A).lt_of_ne (Ne.symm hL)
    obtain ⟨h0, h1⟩ := lanczosRitzValue_bounds hA b q
    constructor
    · exact div_nonneg (sub_nonneg.mpr h1) hLp.le
    · apply (div_le_one hLp).mpr
      linarith

/-- The actual Lanczos relative error is measurable in its starting vector.
Source: manuscript `rt:random-start`, rational variational representation. -/
theorem measurable_lanczosRayleighRelativeError {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (q : ℕ) : Measurable (fun b : ι → ℝ => lanczosRayleighRelativeError A b q) :=
  (measurable_const.sub (measurable_lanczosRitzValue A q)).div_const _

/-- The actual variational Lanczos error obeys the squared logarithmic-overlap bound.
Source: manuscript `rt:lanczos`, polynomial Rayleigh comparison. No spectral gap
or simplicity of the largest eigenvalue is required.
atlas: random-start-power (partial) -/
theorem lanczosRayleighRelativeError_le_log_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (hL : 0 < specNorm A)
    (i₀ : ι) (h₀ : hA.isHermitian.eigenvalues i₀ = specNorm A) (b : ι → ℝ)
    (hb : (hA.isHermitian.eigenvectorBasis i₀ : ι → ℝ) ⬝ᵥ b ≠ 0)
    {q : ℕ} (hq : 2 ≤ q) :
    lanczosRayleighRelativeError A b q ≤
      4 * (1 + Real.log ((b ⬝ᵥ b) /
        ((hA.isHermitian.eigenvectorBasis i₀ : ι → ℝ) ⬝ᵥ b) ^ 2) / Real.log 2) ^ 2 /
          ((q - 1 : ℕ) : ℝ) ^ 2 := by
  let L := specNorm A
  have hLp : 0 < L := hL
  let c := fun i => (hA.isHermitian.eigenvectorBasis i : ι → ℝ) ⬝ᵥ b
  let d := fun i => hA.isHermitian.eigenvalues i / L
  have hd : ∀ i, d i ∈ Set.Icc 0 1 := by
    intro i
    constructor
    · exact div_nonneg (hA.eigenvalues_nonneg i) hLp.le
    · apply (div_le_one hLp).mpr
      have h := norm_le_pi_norm hA.isHermitian.eigenvalues i
      rw [Real.norm_of_nonneg (hA.eigenvalues_nonneg i),
        ← specNorm_eq_norm_eigenvalues hA.isHermitian] at h
      exact h
  have hd₀ : d i₀ = 1 := by dsimp only [d, L]; rw [h₀, div_self hL.ne']
  obtain ⟨p, hpDegree, hpOne, hpMean⟩ := exists_polynomial_filter_mean_le_log_sq d c i₀ hd hd₀ hb hq
  let P := p.comp (C (L⁻¹) * X)
  have hpEval : ∀ i, P.eval (hA.isHermitian.eigenvalues i) = p.eval (d i) := by
    intro i
    simp only [P, eval_comp, eval_mul, eval_C, eval_X, d, div_eq_mul_inv]
    rw [mul_comm L⁻¹]
  have hPDegree : P.natDegree ≤ q - 1 := by
    have hX : (C (L⁻¹) * X : ℝ[X]).natDegree ≤ 1 := natDegree_C_mul_le _ _ |>.trans natDegree_X_le
    exact natDegree_comp_le.trans ((Nat.mul_le_mul_left p.natDegree hX).trans
      (by simpa only [mul_one] using hpDegree))
  let y := aeval A P *ᵥ b
  have hy : y ∈ krylovSpace A b q := (mem_krylovSpace_iff_degree A b q _).mpr
    ⟨P, (degree_le_of_natDegree_le hPDegree).trans_lt (by exact_mod_cast (by omega : q - 1 < q)), rfl⟩
  have hD : y ⬝ᵥ y = ∑ i, p.eval (d i) ^ 2 * c i ^ 2 := by
    simpa only [y, hpEval] using dotProduct_aeval_mulVec_self_eq_sum hA.isHermitian P b
  have hN : y ⬝ᵥ (A *ᵥ y) = L * (∑ i, d i * p.eval (d i) ^ 2 * c i ^ 2) := by
    have h := quadForm_aeval_mulVec_eq_sum hA.isHermitian P b
    change y ⬝ᵥ (A *ᵥ y) = ∑ i, hA.isHermitian.eigenvalues i * P.eval (hA.isHermitian.eigenvalues i) ^ 2 * c i ^ 2 at h
    rw [h, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hpEval]
    dsimp only [d]
    field_simp [hLp.ne']
  have hDp : 0 < ∑ i, p.eval (d i) ^ 2 * c i ^ 2 := by
    have ht := Finset.single_le_sum (f := fun i => p.eval (d i) ^ 2 * c i ^ 2)
      (fun i _ => by positivity) (Finset.mem_univ i₀)
    rw [hd₀, hpOne, one_pow, one_mul] at ht
    exact (sq_pos_of_ne_zero hb).trans_le ht
  have hRQ : (Matrix.toEuclideanCLM (𝕜 := ℝ) A).rayleighQuotient (WithLp.toLp 2 y) =
      L * ((∑ i, d i * p.eval (d i) ^ 2 * c i ^ 2) / (∑ i, p.eval (d i) ^ 2 * c i ^ 2)) := by
    rw [rayleighQuotient_toEuclideanCLM_eq, hN, hD, mul_div_assoc]
  have hCompare := rayleighQuotient_le_lanczosRitzValue_of_mem hA b q hy
  have hError : lanczosRayleighRelativeError A b q ≤
      1 - (∑ i, d i * p.eval (d i) ^ 2 * c i ^ 2) / (∑ i, p.eval (d i) ^ 2 * c i ^ 2) := by
    dsimp only [lanczosRayleighRelativeError]
    rw [hRQ] at hCompare
    dsimp only [L] at hCompare
    apply (div_le_iff₀ hL).mpr
    nlinarith
  have hParseval : (∑ i, c i ^ 2) = b ⬝ᵥ b := sum_sq_eigenvectorBasis_dotProduct hA.isHermitian b
  rw [hParseval] at hpMean
  exact hError.trans hpMean

/-- The Gaussian random-start Lanczos method has the source's explicit gap-free
expectation rate, using the actual variational Krylov value and actual Gaussian law.
Source: manuscript `rt:lanczos`; KW (1992). All PSD matrices, repeated top eigenvalues,
and the zero matrix are included.
atlas: random-start-power -/
theorem integral_lanczosRayleighRelativeError_pi_gaussianReal_le
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.PosSemidef)
    {q : ℕ} (hq : 2 ≤ q) :
    (∫ b : Fin (n + 1) → ℝ, lanczosRayleighRelativeError A b q
      ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1)) ≤
      min 1 (4 * ((Real.log (2 * ((n + 1 : ℕ) : ℝ)) + 2 + Real.log 2) ^ 2 + 4) /
        ((Real.log 2) ^ 2 * ((q - 1 : ℕ) : ℝ) ^ 2)) := by
  let μ := Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1
  let T := Real.log (2 * ((n + 1 : ℕ) : ℝ))
  let h := Real.log 2
  let m := ((q - 1 : ℕ) : ℝ)
  have hh : 0 < h := Real.log_pos (by norm_num)
  have hm : 0 < m := by dsimp only [m]; exact_mod_cast (by omega : 0 < q - 1)
  have hfm := measurable_lanczosRayleighRelativeError A q
  have hfi : Integrable (fun b => lanczosRayleighRelativeError A b q) μ := by
    refine (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable ?_
    exact ae_of_all _ fun b => by
      rw [Real.norm_of_nonneg (lanczosRayleighRelativeError_bounds hA b q).1]
      exact (lanczosRayleighRelativeError_bounds hA b q).2
  have hOne : (∫ b, lanczosRayleighRelativeError A b q ∂μ) ≤ 1 := by
    have hBound := integral_mono hfi (integrable_const (1 : ℝ))
      (fun b => (lanczosRayleighRelativeError_bounds hA b q).2)
    simpa only [integral_const, probReal_univ, one_smul] using hBound
  apply le_min hOne
  by_cases hZero : specNorm A = 0
  · simp only [lanczosRayleighRelativeError, hZero, div_zero, integral_zero]
    positivity
  · have hL : 0 < specNorm A := (specNorm_nonneg A).lt_of_ne (Ne.symm hZero)
    obtain ⟨i₀, hi⟩ := (IsGreatest.pi_norm hA.isHermitian.eigenvalues).1
    dsimp only at hi
    have h₀ : hA.isHermitian.eigenvalues i₀ = specNorm A := by
      rw [specNorm_eq_norm_eigenvalues hA.isHermitian, ← hi,
        Real.norm_of_nonneg (hA.eigenvalues_nonneg i₀)]
    let C := fun b : Fin (n + 1) → ℝ =>
      fun i => (hA.isHermitian.eigenvectorBasis i : Fin (n + 1) → ℝ) ⬝ᵥ b
    let L := fun c : Fin (n + 1) → ℝ => Real.log ((∑ i, c i ^ 2) / (c i₀) ^ 2)
    have hMP : MeasurePreserving C μ μ :=
      measurePreserving_eigenvectorBasis_dotProduct_pi_gaussianReal hA.isHermitian
    have hLm : Measurable L := by dsimp only [L]; fun_prop
    have hL2m : Measurable (fun c => L c ^ 2) := hLm.pow_const 2
    obtain ⟨hLI, hLV, hLI2, hLV2⟩ := integrable_and_integral_log_sum_div_sq_pi_gaussianReal_le n i₀
    have hLCI : Integrable (fun b => L (C b)) μ := by
      apply (integrable_map_measure hLm.aestronglyMeasurable hMP.measurable.aemeasurable).mp
      rwa [hMP.map_eq]
    have hLCI2 : Integrable (fun b => L (C b) ^ 2) μ := by
      apply (integrable_map_measure hL2m.aestronglyMeasurable hMP.measurable.aemeasurable).mp
      rwa [hMP.map_eq]
    have hLCV : (∫ b, L (C b) ∂μ) ≤ T + 2 := by
      have he := integral_map (μ := μ) hMP.measurable.aemeasurable hLm.aestronglyMeasurable
      rw [hMP.map_eq] at he
      exact he.symm.trans_le hLV
    have hLCV2 : (∫ b, L (C b) ^ 2 ∂μ) ≤ T ^ 2 + 4 * T + 8 := by
      have he := integral_map (μ := μ) hMP.measurable.aemeasurable hL2m.aestronglyMeasurable
      rw [hMP.map_eq] at he
      exact he.symm.trans_le hLV2
    let F := fun b : Fin (n + 1) → ℝ => (1 + L (C b) / h) ^ 2
    have hFEq : ∀ b, F b = (L (C b) ^ 2 + 2 * h * L (C b) + h ^ 2) / h ^ 2 := by
      intro b
      dsimp only [F]
      field_simp [hh.ne']
      ring
    have hFI : Integrable F μ := by
      have hsum : Integrable (fun b => L (C b) ^ 2 + 2 * h * L (C b) + h ^ 2) μ :=
        (hLCI2.add (hLCI.const_mul (2 * h))).add (integrable_const _)
      exact (hsum.div_const (h ^ 2)).congr (ae_of_all _ fun b => (hFEq b).symm)
    have hFV : (∫ b, F b ∂μ) ≤ ((T + 2 + h) ^ 2 + 4) / h ^ 2 := by
      have he : (∫ b, F b ∂μ) =
          ((∫ b, L (C b) ^ 2 ∂μ) + 2 * h * (∫ b, L (C b) ∂μ) + h ^ 2) / h ^ 2 := by
        have hsI : Integrable (fun b => L (C b) ^ 2 + 2 * h * L (C b)) μ :=
          hLCI2.add (hLCI.const_mul (2 * h))
        have hAdd : (∫ b, L (C b) ^ 2 + 2 * h * L (C b) + h ^ 2 ∂μ) =
            (∫ b, L (C b) ^ 2 + 2 * h * L (C b) ∂μ) + ∫ _ : Fin (n + 1) → ℝ, h ^ 2 ∂μ :=
          integral_add hsI (integrable_const (h ^ 2))
        have hAdd2 : (∫ b, L (C b) ^ 2 + 2 * h * L (C b) ∂μ) =
            (∫ b, L (C b) ^ 2 ∂μ) + ∫ b, 2 * h * L (C b) ∂μ :=
          integral_add hLCI2 (hLCI.const_mul (2 * h))
        rw [integral_congr_ae (ae_of_all _ hFEq), integral_div, hAdd, hAdd2, integral_const_mul]
        simp only [integral_const, probReal_univ, one_smul]
      rw [he]
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      have hc := mul_le_mul_of_nonneg_left hLCV (by positivity : (0 : ℝ) ≤ 2 * h)
      nlinarith
    have hNZ := ae_eigenvectorBasis_dotProduct_ne_zero_pi_gaussianReal hA.isHermitian i₀
    have hPoint : (fun b => lanczosRayleighRelativeError A b q) ≤ᵐ[μ]
        fun b => 4 * F b / m ^ 2 := by
      filter_upwards [hNZ] with b hb
      have hs := lanczosRayleighRelativeError_le_log_sq hA hL i₀ h₀ b hb hq
      rw [← sum_sq_eigenvectorBasis_dotProduct hA.isHermitian b] at hs
      exact hs
    have hBound := integral_mono_ae hfi ((hFI.const_mul 4).div_const (m ^ 2)) hPoint
    rw [integral_div, integral_const_mul] at hBound
    refine hBound.trans ?_
    have hb := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hFV (by norm_num : (0 : ℝ) ≤ 4)) (sq_nonneg m)
    refine hb.trans_eq ?_
    dsimp only [T, h, m]
    ring

/-- The Gaussian Lanczos expectation theorem covers every matrix dimension.
Source: manuscript `rt:lanczos`; the empty matrix has zero relative error.
atlas: random-start-power -/
theorem integral_lanczosRayleighRelativeError_pi_gaussianReal_le_all_dims
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) {q : ℕ} (hq : 2 ≤ q) :
    (∫ b : Fin n → ℝ, lanczosRayleighRelativeError A b q
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) ≤
      min 1 (4 * ((Real.log (2 * (n : ℝ)) + 2 + Real.log 2) ^ 2 + 4) /
        ((Real.log 2) ^ 2 * ((q - 1 : ℕ) : ℝ) ^ 2)) := by
  cases n with
  | zero =>
    have hzero : A = 0 := Subsingleton.elim _ _
    rw [hzero]
    simp only [lanczosRayleighRelativeError, specNorm_zero, div_zero, integral_zero]
    apply le_min zero_le_one
    positivity
  | succ n => exact integral_lanczosRayleighRelativeError_pi_gaussianReal_le A hA hq

/-- The exact Lanczos constant transports through an actual Gaussian vector law
on any probability space. Source: manuscript `rt:lanczos`.
The rational variational representation supplies measurability.
atlas: random-start-power -/
theorem integral_lanczosRayleighRelativeError_le_of_map_eq_pi_gaussianReal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) {q : ℕ} (hq : 2 ≤ q)
    (G : Ω → Fin n → ℝ) (hG : μ.map G = Measure.pi fun _ : Fin n => gaussianReal 0 1) :
    (∫ ω, lanczosRayleighRelativeError A (G ω) q ∂μ) ≤
      min 1 (4 * ((Real.log (2 * (n : ℝ)) + 2 + Real.log 2) ^ 2 + 4) /
        ((Real.log 2) ^ 2 * ((q - 1 : ℕ) : ℝ) ^ 2)) := by
  have hGm : AEMeasurable G μ := AEMeasurable.of_map_ne_zero
    (by rw [hG]; exact IsProbabilityMeasure.ne_zero _)
  have he := integral_map hGm (measurable_lanczosRayleighRelativeError A q).aestronglyMeasurable
  rw [hG] at he
  exact he.symm.trans_le (integral_lanczosRayleighRelativeError_pi_gaussianReal_le_all_dims A hA hq)

end NLAlib
