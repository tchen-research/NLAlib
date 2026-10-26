import NLAlib.RandomMatrix.Gaussian.Comparison.VarianceProfileProcess
import NLAlib.RandomMatrix.Gaussian.Moments.SymmetricProfileLowerMoments
import NLAlib.Matrix.Measurability.SpectralMeasurable
import NLAlib.Matrix.Norms.Net

/-!
# Reduction of the Gaussian operator norm to coordinate maxima

The actual symmetric Gaussian operator norm is reduced to the two finite
Gaussian maxima in the nonlinear variance-profile comparison. A fixed
quarter-net suffices; no limit or unproved process comparison is assumed.

Source: van Handel, arXiv:1502.05003v4, Theorem 4.1.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal

namespace NLAlib

variable {n : ℕ}

/-- The maximum weighted row radius of the first Gaussian row. -/
def varianceProfileRadiusMaximum (B : Matrix (Fin n) (Fin n) ℝ)
    (H : Matrix (Fin 2) (Fin n) ℝ) : ℝ :=
  ‖fun j => varianceProfileRadius B (H 0) j‖

/-- The maximum absolute coordinate of the Gaussian covariance correction. -/
def varianceProfileCorrectionMaximum (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.IsHermitian) (H : Matrix (Fin 2) (Fin n) ℝ) : ℝ :=
  ‖fun i => ∑ k, spectralAbsoluteFactor hB i k * H 1 k‖

/-- The Gaussian maximum of the weighted row radii is integrable, also
for zero rows and empty matrices. -/
theorem integrable_varianceProfileRadiusMaximum
    (B : Matrix (Fin n) (Fin n) ℝ) (hB0 : ∀ i j, 0 ≤ B i j) :
    Integrable (varianceProfileRadiusMaximum B) (gaussianMatrix (Fin 2) (Fin n)) := by
  have h : Integrable (fun H : Matrix (Fin 2) (Fin n) ℝ =>
      fun j => varianceProfileRadius B (H 0) j) (gaussianMatrix (Fin 2) (Fin n)) := by
    apply integrable_pi_iff.mpr
    intro j
    have hV : MemLp (fun H : Matrix (Fin 2) (Fin n) ℝ =>
        (WithLp.toLp 2 (fun i => Real.sqrt (B j i) * H 0 i) : EuclideanSpace ℝ (Fin n)))
        2 (gaussianMatrix (Fin 2) (Fin n)) := by
      rw [memLp_piLp_iff]
      intro i
      exact (memLp_gaussianMatrix_entry 0 i 2 (by simp)).const_mul _
    simpa only [varianceProfileRadius_eq_norm B hB0] using hV.norm.integrable (by norm_num)
  exact h.norm

/-- The maximum of the actual covariance-correction coordinates is
integrable, because every coordinate is a finite Gaussian linear form. -/
theorem integrable_varianceProfileCorrectionMaximum
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsHermitian) :
    Integrable (varianceProfileCorrectionMaximum B hB) (gaussianMatrix (Fin 2) (Fin n)) := by
  have h : MemLp (fun H : Matrix (Fin 2) (Fin n) ℝ =>
      fun i => ∑ k, spectralAbsoluteFactor hB i k * H 1 k)
      2 (gaussianMatrix (Fin 2) (Fin n)) := by
    apply memLp_pi_iff.mpr
    intro i
    exact memLp_finsetSum _ fun k _ =>
      (memLp_gaussianMatrix_entry 1 k 2 (by simp)).const_mul _
  exact h.norm.integrable (by norm_num)

/-- The native spectral norm of the actual symmetric Gaussian profile
matrix is integrable. Its Gaussian Frobenius moment supplies domination. -/
theorem integrable_specNorm_symmetricGaussianMatrix (b : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun G => specNorm (symmetricGaussianMatrix b G))
      (gaussianMatrix (Fin n) (Fin n)) := by
  have h := (memLp_schattenNormReal_symmetricGaussianMatrix b (p := 2) (by norm_num)).integrable
    (by norm_num)
  apply h.mono' (measurable_specNorm_of_entries (fun i j =>
    (Matrix.measurable_entry i j).comp (measurable_symmetricGaussianMatrix b))).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro G
  rw [Real.norm_of_nonneg (specNorm_nonneg _), schattenNormReal_two]
  exact specNorm_le_frobNorm _

/-- Every unit-ball value of the explicit process is controlled by its
two coordinate maxima. -/
theorem linForm_varianceProfileComparisonCoefficient_le_maxima
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsHermitian) (hB0 : ∀ i j, 0 ≤ B i j)
    (v : Fin n → ℝ) (hv : ∑ i, v i ^ 2 ≤ 1) (H : Matrix (Fin 2) (Fin n) ℝ) :
    linForm (varianceProfileComparisonCoefficient B hB v) H ≤
      2 * varianceProfileRadiusMaximum B H + varianceProfileCorrectionMaximum B hB H := by
  apply linForm_varianceProfileComparisonCoefficient_le B hB hB0 v hv H _ _
    (norm_nonneg _) (norm_nonneg _)
  · intro j
    exact (le_abs_self _).trans (norm_le_pi_norm (fun j => varianceProfileRadius B (H 0) j) j)
  · intro i
    exact (le_abs_self _).trans
      (norm_le_pi_norm (fun i => ∑ k, spectralAbsoluteFactor hB i k * H 1 k) i)

/-- The expected finite supremum of the explicit Gaussian process is
bounded by its actual weighted-radius and correction maxima. -/
theorem integral_iSup_comparison_le_maxima {ι : Type*} [Fintype ι] [Nonempty ι]
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsHermitian) (hB0 : ∀ i j, 0 ≤ B i j)
    (v : ι → Fin n → ℝ) (hv : ∀ t, ∑ i, v t i ^ 2 ≤ 1) :
    (∫ H, (⨆ t, linForm (varianceProfileComparisonCoefficient B hB (v t)) H)
      ∂gaussianMatrix (Fin 2) (Fin n)) ≤
      2 * (∫ H, varianceProfileRadiusMaximum B H ∂gaussianMatrix (Fin 2) (Fin n)) +
        ∫ H, varianceProfileCorrectionMaximum B hB H ∂gaussianMatrix (Fin 2) (Fin n) := by
  have hR := integrable_varianceProfileRadiusMaximum B hB0
  have hM := integrable_varianceProfileCorrectionMaximum B hB
  rw [← integral_const_mul, ← integral_add (hR.const_mul 2) hM]
  apply integral_mono
    (integrable_iSup_of_fintype _ (fun t => integrable_linForm_gaussianMatrix _)
      (fun t => (continuous_linForm _).measurable)) ((hR.const_mul 2).add hM)
  intro H
  apply ciSup_le
  intro t
  exact linForm_varianceProfileComparisonCoefficient_le_maxima B hB hB0 (v t) (hv t) H

/-- The expected native operator norm of the actual symmetric Gaussian
matrix is bounded by its two explicit Gaussian coordinate maxima. The
constant is uniform in the dimension and includes empty matrices. -/
theorem integral_specNorm_symmetricGaussianMatrix_le_comparison_maxima
    (b : Matrix (Fin n) (Fin n) ℝ) (hb : b.IsSymm) :
    (∫ G, specNorm (symmetricGaussianMatrix b G) ∂gaussianMatrix (Fin n) (Fin n)) ≤
      8 * (∫ H, varianceProfileRadiusMaximum (Matrix.of fun i j => b i j ^ 2) H
        ∂gaussianMatrix (Fin 2) (Fin n)) +
      4 * (∫ H, varianceProfileCorrectionMaximum (Matrix.of fun i j => b i j ^ 2)
        (isHermitian_varianceProfile_sq b hb) H ∂gaussianMatrix (Fin 2) (Fin n)) := by
  classical
  obtain ⟨N, hNunit, -, hNcover⟩ := exists_finset_sphere_net (Fin n) (ε := 1 / 4) (by norm_num)
  let I := Option {x // x ∈ N}
  let v : I → Fin n → ℝ := fun t => t.elim 0 (fun x => x.1)
  have hv (t : I) : ∑ i, v t i ^ 2 ≤ 1 := by
    cases t with
    | none => simp [v]
    | some x =>
      have h := hNunit x.1 x.2
      simpa only [dotProduct, v, Option.elim_some, ← sq] using h.le
  let P : Matrix (Fin n) (Fin n) ℝ → ℝ := fun G =>
    ⨆ t, quadForm (symmetricGaussianMatrix b G) (v t)
  let Q : Matrix (Fin n) (Fin n) ℝ → ℝ := fun G =>
    ⨆ t, -quadForm (symmetricGaussianMatrix b G) (v t)
  have hPi : Integrable P (gaussianMatrix (Fin n) (Fin n)) := by
    simp only [P, quadForm_symmetricGaussianMatrix_eq_linForm]
    exact integrable_iSup_of_fintype _ (fun t => integrable_linForm_gaussianMatrix _)
      (fun t => (continuous_linForm _).measurable)
  have hQi : Integrable Q (gaussianMatrix (Fin n) (Fin n)) := by
    have heq (t : I) (G : Matrix (Fin n) (Fin n) ℝ) :
        -quadForm (symmetricGaussianMatrix b G) (v t) =
          linForm (fun i j => -symmetricGaussianQuadraticCoefficient b (v t) i j) G := by
      rw [quadForm_symmetricGaussianMatrix_eq_linForm]
      simp only [linForm, neg_mul, Finset.sum_neg_distrib]
    change Integrable (fun G => ⨆ t, -quadForm (symmetricGaussianMatrix b G) (v t)) _
    simp_rw [heq]
    apply integrable_iSup_of_fintype _
    · intro t
      exact integrable_linForm_gaussianMatrix _
    · intro t
      exact (continuous_linForm _).measurable
  have hpoint (G : Matrix (Fin n) (Fin n) ℝ) :
      specNorm (symmetricGaussianMatrix b G) ≤ 2 * (P G + Q G) := by
    have hP0 : 0 ≤ P G := by
      have h := le_ciSup (Set.finite_range (fun t : I =>
        quadForm (symmetricGaussianMatrix b G) (v t))).bddAbove (none : I)
      simpa only [v, Option.elim_none, quadForm_zero_right] using h
    have hQ0 : 0 ≤ Q G := by
      have h := le_ciSup (Set.finite_range (fun t : I =>
        -quadForm (symmetricGaussianMatrix b G) (v t))).bddAbove (none : I)
      simpa only [v, Option.elim_none, quadForm_zero_right, neg_zero] using h
    have hbound := specNorm_le_div_of_net_quadForm
      (Matrix.isHermitian_iff_isSymm.mpr (symmetricGaussianMatrix_isSymm b G)) N
      (ε := 1 / 4) (M := P G + Q G) (by norm_num) (by norm_num) (add_nonneg hP0 hQ0)
      (fun x hx => by rw [← sqrt_dotProduct_self_eq_norm, hNunit x hx, Real.sqrt_one])
      (fun y hy => by
        have hy' : y ⬝ᵥ y = 1 := by rw [← norm_toLp_sq_eq_dotProduct_self, hy, one_pow]
        obtain ⟨x, hx, hxy⟩ := hNcover y hy'
        refine ⟨x, hx, ?_⟩
        rw [← norm_toLp_sq_eq_dotProduct_self] at hxy
        nlinarith [norm_nonneg (WithLp.toLp 2 (x - y) : EuclideanSpace ℝ (Fin n))])
      (fun x hx => by
        have hp := le_ciSup (Set.finite_range (fun t : I =>
          quadForm (symmetricGaussianMatrix b G) (v t))).bddAbove (some ⟨x, hx⟩ : I)
        have hq := le_ciSup (Set.finite_range (fun t : I =>
          -quadForm (symmetricGaussianMatrix b G) (v t))).bddAbove (some ⟨x, hx⟩ : I)
        change quadForm (symmetricGaussianMatrix b G) x ≤ P G at hp
        change -quadForm (symmetricGaussianMatrix b G) x ≤ Q G at hq
        exact abs_le.mpr ⟨by linarith, by linarith⟩)
    norm_num at hbound ⊢
    linarith
  have hnorm := integral_mono (integrable_specNorm_symmetricGaussianMatrix b)
    ((hPi.add hQi).const_mul 2) hpoint
  rw [integral_const_mul] at hnorm
  simp only [Pi.add_apply] at hnorm
  rw [integral_add hPi hQi] at hnorm
  have hmax := integral_iSup_comparison_le_maxima
    (Matrix.of fun i j => b i j ^ 2) (isHermitian_varianceProfile_sq b hb)
    (fun i j => sq_nonneg _) v hv
  have hplus := (integral_iSup_quadForm_symmetricGaussianMatrix_le_comparison b hb v).trans hmax
  have hminus := (integral_iSup_neg_quadForm_symmetricGaussianMatrix_le_comparison b hb v).trans hmax
  change (∫ G, P G ∂gaussianMatrix (Fin n) (Fin n)) ≤ _ at hplus
  change (∫ G, Q G ∂gaussianMatrix (Fin n) (Fin n)) ≤ _ at hminus
  linarith

end NLAlib
