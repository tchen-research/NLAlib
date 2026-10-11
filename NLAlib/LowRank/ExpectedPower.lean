import NLAlib.LowRank.PowerIteration
import NLAlib.LowRank.SpectralRangeFinder
import NLAlib.LowRank.OptimalError
import NLAlib.LowRank.GaussianSpectralEndpoints
import NLAlib.Matrix.SvdPowers
import NLAlib.Matrix.SpectralMeasurable
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

/-!
# Expected error of Gaussian subspace iteration

The deterministic power inequality and scalar Jensen transfer Gaussian range-finder
bounds to the original matrix. Odd Gram powers have their exact zero-padded singular
values. The source is HMT (2011), Theorem 10.7; manuscript `sa:expected-power`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- Measurable orthonormal frames give integrable spectral residuals bounded by the
input norm. Source: HMT (2011), expected-error integration; manuscript `sa:expected-power`. -/
theorem integrable_specNorm_residual_of_measurable_frame
    {Ω m n l : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n] [Fintype l]
    [DecidableEq m] [DecidableEq n] [DecidableEq l]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A : Matrix m n ℝ) (Q : Ω → Matrix m l ℝ)
    (hQ : ∀ i j, Measurable fun ω => Q ω i j)
    (hQo : ∀ᵐ ω ∂μ, HasOrthonormalCols (Q ω)) :
    Integrable (fun ω => specNorm (residual (Q ω) A)) μ := by
  refine (integrable_const (specNorm A)).mono'
    (measurable_specNorm_residual_of A hQ).aestronglyMeasurable ?_
  filter_upwards [hQo] with ω hω
  rw [Real.norm_of_nonneg (specNorm_nonneg _)]
  exact specNorm_sub_mul_transpose_mul_le hω A

/-- Scalar Jensen transfers the deterministic odd-power inequality to expectation.
Source: HMT (2011), proof of Theorem 10.7; manuscript `sa:power-inequality`.
No operator convexity is used and no integrability assumptions are left to callers. -/
theorem integral_specNorm_residual_le_rpow_integral
    {Ω m n l : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n] [Fintype l]
    [DecidableEq m] [DecidableEq n] [DecidableEq l]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A : Matrix m n ℝ) (Q : Ω → Matrix m l ℝ)
    (hQ : ∀ i j, Measurable fun ω => Q ω i j)
    (hQo : ∀ᵐ ω ∂μ, HasOrthonormalCols (Q ω)) (q : ℕ) :
    (∫ ω, specNorm (residual (Q ω) A) ∂μ) ≤
      (∫ ω, specNorm (residual (Q ω) ((A * Aᵀ) ^ q * A)) ∂μ) ^
        (1 / (2 * (q : ℝ) + 1)) := by
  let f := fun ω => specNorm (residual (Q ω) A)
  let g := fun ω => specNorm (residual (Q ω) ((A * Aᵀ) ^ q * A))
  let r := 2 * q + 1
  have hfi := integrable_specNorm_residual_of_measurable_frame A Q hQ hQo
  have hgi := integrable_specNorm_residual_of_measurable_frame ((A * Aᵀ) ^ q * A) Q hQ hQo
  have hfpi : Integrable (fun ω => f ω ^ r) μ := by
    refine (integrable_const (specNorm A ^ r)).mono'
      ((measurable_specNorm_residual_of A hQ).pow_const r).aestronglyMeasurable ?_
    filter_upwards [hQo] with ω hω
    rw [Real.norm_of_nonneg (pow_nonneg (specNorm_nonneg _) _)]
    exact pow_le_pow_left₀ (specNorm_nonneg _) (specNorm_sub_mul_transpose_mul_le hω A) r
  have hJ := (convexOn_pow r (𝕜 := ℝ)).map_integral_le (continuous_pow r).continuousOn
    isClosed_Ici (ae_of_all _ fun ω => specNorm_nonneg (residual (Q ω) A)) hfi hfpi
  have hfg : (fun ω => f ω ^ r) ≤ᵐ[μ] g := by
    filter_upwards [hQo] with ω hω
    exact specNorm_residual_pow_le hω A q
  have hle : (∫ ω, f ω ∂μ) ^ r ≤ ∫ ω, g ω ∂μ :=
    hJ.trans (integral_mono_ae hfpi hgi hfg)
  have hnonneg : 0 ≤ ∫ ω, f ω ∂μ := integral_nonneg fun ω => specNorm_nonneg _
  have hcast : 1 / (2 * (q : ℝ) + 1) = ((r : ℕ) : ℝ)⁻¹ := by
    dsimp [r]
    push_cast
    ring
  have hr : r ≠ 0 := by dsimp [r]; omega
  rw [hcast, ← Real.pow_rpow_inv_natCast (n := r) hnonneg hr]
  exact Real.rpow_le_rpow (pow_nonneg hnonneg r) hle (inv_nonneg.mpr (Nat.cast_nonneg r))

/-- A Gaussian sketch at least as wide as the matrix rank exactly spans its range,
and every supplied projector reproducing that sketch reproduces the matrix.
Source: HMT (2011), Proposition A.5; manuscript `sa:expected-power`, thin-SVD branch.
The statement includes rank zero and imposes no input-width restriction. -/
theorem ae_gaussian_projection_reproduces_of_rank_le
    {Ω l : Type*} [MeasurableSpace Ω] [Fintype l]
    {μ : Measure Ω} {m n t : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (G : Ω → Matrix (Fin n) (Fin t) ℝ)
    (hG : μ.map (fun ω => Matrix.of.symm (G ω)) = gaussianMatrix n t)
    (Q : Ω → Matrix (Fin m) l ℝ)
    (hQr : ∀ᵐ ω ∂μ, Q ω * ((Q ω)ᵀ * (A * G ω)) = A * G ω)
    (ht : A.rank ≤ t) : ∀ᵐ ω ∂μ, Q ω * ((Q ω)ᵀ * A) = A := by
  have hRank : ∀ᵐ ω ∂μ, (A * G ω).rank = A.rank := by
    simpa only [min_eq_left ht, Equiv.apply_symm_apply] using
      ae_rank_mul_gaussian_eq_min A (fun ω => Matrix.of.symm (G ω)) hG
  filter_upwards [hRank, hQr] with ω hr hproj
  have hRange := range_mulVecLin_mul_eq_of_rank_eq A (G ω) hr
  have hCols : ∀ j : Fin n, ∃ v : Fin t → ℝ, (A * G ω) *ᵥ v = A.col j := by
    intro j
    have hj : A.col j ∈ LinearMap.range A.mulVecLin := by
      rw [Matrix.range_mulVecLin]
      exact Submodule.subset_span ⟨j, rfl⟩
    rw [← hRange] at hj
    exact hj
  choose v hv using hCols
  let T : Matrix (Fin t) (Fin n) ℝ := fun i j => v j i
  have hAT : (A * G ω) * T = A := by
    ext i j
    exact congrFun (hv j) i
  have h := congrArg (fun M : Matrix (Fin m) (Fin t) ℝ => M * T) hproj
  simpa only [Matrix.mul_assoc, hAT] using h

/-- Expected Gaussian subspace-iteration error with the exact HMT spectral constants.
Source: HMT (2011), Theorem 10.7; manuscript `sa:expected-power-theorem`.
The one-row Gaussian endpoint and rank-zero case are included.
There is no restriction on the Gaussian width relative to matrix dimensions.
atlas: subspace-iteration-expected -/
theorem integral_specNorm_residual_gram_pow_gaussian_le
    {Ω l : Type*} [MeasurableSpace Ω] [Fintype l] [DecidableEq l]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {m n k p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hk : 1 ≤ k) (hp : 2 ≤ p)
    (G : Ω → Matrix (Fin n) (Fin (k + p)) ℝ)
    (hG : μ.map (fun ω => Matrix.of.symm (G ω)) = gaussianMatrix n (k + p))
    (Q : Ω → Matrix (Fin m) l ℝ) (hQ : ∀ i j, Measurable fun ω => Q ω i j)
    (hQo : ∀ᵐ ω ∂μ, HasOrthonormalCols (Q ω)) (q : ℕ)
    (hQr : ∀ᵐ ω ∂μ, Q ω * ((Q ω)ᵀ * (((A * Aᵀ) ^ q * A) * G ω)) =
      ((A * Aᵀ) ^ q * A) * G ω) :
    (∫ ω, specNorm (residual (Q ω) A) ∂μ) ≤
      ((1 + Real.sqrt (k / ((p : ℝ) - 1))) * singularValues A k ^ (2 * q + 1) +
        Real.exp 1 * Real.sqrt (k + p) / p *
          Real.sqrt (∑ i : Fin m, if k ≤ (i : ℕ) then
            singularValues A i ^ (2 * (2 * q + 1)) else 0)) ^ (1 / (2 * (q : ℝ) + 1)) := by
  let C := (A * Aᵀ) ^ q * A
  have hB0 : 0 ≤ (1 + Real.sqrt (k / ((p : ℝ) - 1))) *
      singularValues A k ^ (2 * q + 1) + Real.exp 1 * Real.sqrt (k + p) / p *
        Real.sqrt (∑ i : Fin m, if k ≤ (i : ℕ) then
          singularValues A i ^ (2 * (2 * q + 1)) else 0) := by
    have := singularValues_nonneg A k
    positivity
  by_cases ht : A.rank ≤ k + p
  · have hCt : C.rank ≤ k + p := by
      change ((A * Aᵀ) ^ q * A).rank ≤ k + p
      rwa [rank_gram_pow_mul]
    have hproj := ae_gaussian_projection_reproduces_of_rank_le C G hG Q hQr hCt
    have hzero : (fun ω => specNorm (residual (Q ω) A)) =ᵐ[μ] fun _ => 0 := by
      filter_upwards [hproj, hQo] with ω hω ho
      have hc : residual (Q ω) C = 0 := by simp only [residual, hω, sub_self]
      have hpow := specNorm_residual_pow_le ho A q
      change specNorm (residual (Q ω) A) ^ (2 * q + 1) ≤ specNorm (residual (Q ω) C) at hpow
      rw [hc, specNorm_zero] at hpow
      exact eq_zero_of_pow_eq_zero (le_antisymm hpow (pow_nonneg (specNorm_nonneg _) _))
    rw [integral_congr_ae hzero, integral_zero]
    exact Real.rpow_nonneg hB0 _
  · have hkn : k ≤ n := by have := A.rank_le_width; omega
    have hH := integral_specNorm_residual_le_singularValues_of_gaussian_of_pos
      C hk hp hkn G hG Q hQo hQr
    have htail : singularValueTailSq C k = ∑ i : Fin m, if k ≤ (i : ℕ) then
        singularValues A i ^ (2 * (2 * q + 1)) else 0 := by
      simp only [singularValueTailSq, C, singularValues_gram_pow_mul, ← pow_mul]
      exact Finset.sum_congr rfl fun i _ => by
        split_ifs
        · congr 1
          omega
        · rfl
    rw [htail, show singularValues C k = singularValues A k ^ (2 * q + 1) from
      singularValues_gram_pow_mul A q k] at hH
    exact (integral_specNorm_residual_le_rpow_integral A Q hQ hQo q).trans
      (Real.rpow_le_rpow (integral_nonneg fun ω => specNorm_nonneg _) hH (by positivity))

end NLAlib
