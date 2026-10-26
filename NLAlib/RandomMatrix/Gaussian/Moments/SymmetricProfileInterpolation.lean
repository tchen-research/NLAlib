import NLAlib.RandomMatrix.Gaussian.Moments.SymmetricComplexProfile
import NLAlib.Matrix.Norms.SchattenFinitePartition
import NLAlib.Matrix.Functions.SchattenFiniteMeasureInterpolation
import NLAlib.Matrix.Functions.SymmetricProfileInterpolationFamily

/-!
# Interpolating actual Gaussian Schatten moments

Finite conditional means of the Gaussian matrix are real matrices. Taking
the symmetric coefficient multiplier of each such mean gives an analytic
finite-output family, because the multiplier is complex linear in its
coefficient profile. Finite-output Schatten interpolation and simple-function
`L^p` density then transfer the endpoint bounds to the actual Gaussian law.
No analytic integration or nonmeasurable singular-vector selection is needed.

Source: Latała--van Handel--Youssef, arXiv:1711.00807v2, Section 2.3.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix ENNReal

namespace NLAlib

variable {n : Type*} [Fintype n] [LinearOrder n]

open scoped Matrix.Norms.L2Operator in
/-- A strip-analytic coefficient family interpolates the actual matched
Gaussian Schatten moments at arbitrary finite endpoint exponents greater
than one. The finite endpoint hypotheses are actual Gaussian integrals;
the interpolation conclusion retains exactly the same Gaussian law. -/
theorem integral_schattenNormReal_symmetricComplexGaussianMatrix_rpow_root_le_of_boundary_bounds
    {θ p₀ p₁ p M₀ M₁ B : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hp₀ : 1 < p₀) (hp₁ : 1 < p₁) (hp : 1 < p)
    (hexp : 1 / p = (1 - θ) / p₀ + θ / p₁)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (F : ℂ → Matrix n n ℂ)
    (hF : DiffContOnCl ℂ F (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hbound : ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1, specNorm (F z) ≤ B)
    (hleft : ∀ t : ℝ,
      (∫ G, schattenNormReal (symmetricComplexGaussianMatrix (F ((t : ℂ) * Complex.I)) G) p₀ ^ p₀
        ∂gaussianMatrix n n) ^ (1 / p₀) ≤ M₀)
    (hright : ∀ t : ℝ,
      (∫ G, schattenNormReal (symmetricComplexGaussianMatrix (F (1 + (t : ℂ) * Complex.I)) G) p₁ ^ p₁
        ∂gaussianMatrix n n) ^ (1 / p₁) ≤ M₁) :
    (∫ G, schattenNormReal (symmetricComplexGaussianMatrix (F (θ : ℂ)) G) p ^ p
      ∂gaussianMatrix n n) ^ (1 / p) ≤ M₀ ^ (1 - θ) * M₁ ^ θ := by
  let μ := gaussianMatrix n n
  have hraw : Integrable (id : Matrix n n ℝ → Matrix n n ℝ) μ :=
    ((hasGaussianLaw_id_gaussianMatrix n n).memLp (by simp : (1 : ℝ≥0∞) ≠ ∞)).integrable le_rfl
  have hmem := memLp_symmetricComplexGaussianMatrix (F (θ : ℂ))
    (ENNReal.ofReal p) ENNReal.ofReal_ne_top
  rw [one_div]
  apply integral_schattenNormReal_rpow_root_le_of_finitePartitionMean_le hp.le hmem
    (M₀ ^ (1 - θ) * M₁ ^ θ) (mul_nonneg (Real.rpow_nonneg hM₀ _) (Real.rpow_nonneg hM₁ _))
  intro k cell hcell
  let a : Fin k → Matrix n n ℝ := finitePartitionMean μ cell id
  let H : Fin k → ℂ → Matrix n n ℂ := fun i z => symmetricComplexGaussianMatrix (F z) (a i)
  have hmean (z : ℂ) (i : Fin k) :
      finitePartitionMean μ cell (symmetricComplexGaussianMatrix (F z)) i = H i z := by
    let T := (symmetricComplexGaussianSampleLinearMap (F z)).toContinuousLinearMap
    exact finitePartitionMean_comp_continuousLinearMap cell hraw T i
  have hH (i : Fin k) : DiffContOnCl ℂ (H i) (Complex.HadamardThreeLines.verticalStrip 0 1) := by
    let L := (symmetricComplexGaussianMatrixLinearMap (a i)).toContinuousLinearMap
    exact ⟨L.differentiable.comp_differentiableOn hF.differentiableOn,
      L.continuous.comp_continuousOn hF.continuousOn⟩
  let C : Fin k → ℝ := fun i => ‖(symmetricComplexGaussianMatrixLinearMap (a i)).toContinuousLinearMap‖ * B
  have hHb (i : Fin k) (z : ℂ)
      (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1) : specNorm (H i z) ≤ C i := by
    let L := (symmetricComplexGaussianMatrixLinearMap (a i)).toContinuousLinearMap
    change ‖L (F z)‖ ≤ ‖L‖ * B
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (by simpa only [specNorm_eq_norm] using hbound z hz)
      (norm_nonneg L))
  have haverage (z : ℂ) (q : ℝ) (hq : 1 ≤ q) :
      (∑ i, μ.real (cell ⁻¹' {i}) * schattenNormReal (H i z) q ^ q) ^ (1 / q) ≤
        (∫ G, schattenNormReal (symmetricComplexGaussianMatrix (F z) G) q ^ q ∂μ) ^ (1 / q) := by
    have h : (∑ i, μ.real (cell ⁻¹' {i}) *
        schattenNormReal (finitePartitionMean μ cell (symmetricComplexGaussianMatrix (F z)) i) q ^ q) ≤
          ∫ G, schattenNormReal (symmetricComplexGaussianMatrix (F z) G) q ^ q ∂μ :=
      sum_mul_schattenNormReal_finitePartitionMean_rpow_le_integral cell hcell
        (f := symmetricComplexGaussianMatrix (F z))
        (integrable_symmetricComplexGaussianMatrix (F z)) hq hq
        (integrable_schattenNormReal_symmetricComplexGaussianMatrix_rpow (F z) hq)
    simp_rw [hmean] at h
    exact Real.rpow_le_rpow (Finset.sum_nonneg fun i _ =>
      mul_nonneg (measureReal_nonneg) (Real.rpow_nonneg (schattenNormReal_nonneg _ _) _)) h
      (one_div_nonneg.mpr (zero_le_one.trans hq))
  have hfinite := sum_mul_schattenNormReal_rpow_root_le_of_finite_boundary_bounds
    (fun i => μ.real (cell ⁻¹' {i})) (fun _ => measureReal_nonneg)
    hθ hp₀ hp₁ hp hexp H hH C hHb
    (fun t => (haverage _ p₀ hp₀.le).trans (hleft t))
    (fun t => (haverage _ p₁ hp₁.le).trans (hright t))
  rw [one_div] at hfinite
  have hsum :
      (∑ i, μ.real (cell ⁻¹' {i}) *
        schattenNormReal (finitePartitionMean μ cell (symmetricComplexGaussianMatrix (F (θ : ℂ))) i) p ^ p) =
      ∑ i, μ.real (cell ⁻¹' {i}) * schattenNormReal (H i (θ : ℂ)) p ^ p := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hmean]
  rw [hsum]
  exact hfinite

open scoped Matrix.Norms.L2Operator in
/-- Normalized row and entry profiles imply an actual Gaussian Schatten
moment bound for every real exponent strictly between two and a positive
even exponent. The endpoint estimates and interpolation family are proved
for the genuine Gaussian model, rather than assumed as moment hypotheses. -/
theorem integral_schattenNormReal_symmetricComplexGaussianMatrix_rpow_root_le_of_normalized_profiles
    (b : Matrix n n ℂ) (hb : b.IsSymm) (k : ℕ) (hk : 0 < k)
    (p : ℝ) (hp2 : 2 < p) (hkp : p < ((2 * k : ℕ) : ℝ))
    (θ : ℝ) (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hexp : 1 / p = (1 - θ) / 2 + θ / (((2 * k : ℕ) : ℝ)))
    (hrow : (∑ i, (∑ j, ‖b i j‖ ^ 2) ^ (p / 2)) ≤ 1)
    (hentry : (Real.sqrt ((2 * k : ℕ) : ℝ)) ^ (θ * p) * (∑ i, ∑ j, ‖b i j‖ ^ p) ≤ 1) :
    (∫ G, schattenNormReal (symmetricComplexGaussianMatrix b G) p ^ p
      ∂gaussianMatrix n n) ^ p⁻¹ ≤ 96 := by
  let q : ℝ := ((2 * k : ℕ) : ℝ)
  have hq : 1 < q := lt_trans (by linarith : (1 : ℝ) < p) hkp
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hc : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hhalf : q / 2 = k := by dsimp [q]; push_cast; ring
  obtain ⟨F, B, hF, hFs, hFc, _hB, hbnd, hleft, hrightRow, hrightEntry⟩ :=
    exists_entire_symmetric_profile_family hp2.le hq0 hθ hc hexp b hb hrow hentry
  have hleftMoment (t : ℝ) :
      (∫ G, schattenNormReal (symmetricComplexGaussianMatrix (F ((t : ℂ) * Complex.I)) G) 2 ^ (2 : ℝ)
        ∂gaussianMatrix n n) ^ (1 / (2 : ℝ)) ≤ 2 := by
    simp only [Real.rpow_two]
    rw [integral_schattenNormReal_symmetricComplexGaussianMatrix_sq _ (hFs _), ← Real.sqrt_eq_rpow]
    exact (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)).2 (by norm_num; exact hleft t)
  have hrightMoment (t : ℝ) :
      (∫ G, schattenNormReal (symmetricComplexGaussianMatrix (F (1 + (t : ℂ) * Complex.I)) G) q ^ q
        ∂gaussianMatrix n n) ^ (1 / q) ≤ 96 := by
    let A : ℝ := (∑ i, (∑ j, ‖F (1 + (t : ℂ) * Complex.I) i j‖ ^ 2) ^ k) ^ q⁻¹
    let E : ℝ := (∑ i, ∑ j, ‖F (1 + (t : ℂ) * Complex.I) i j‖ ^ q) ^ q⁻¹
    have hA : A ≤ 1 := by
      have h := Real.rpow_le_rpow
        (Finset.sum_nonneg fun _ _ => pow_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) _)
        (by simpa only [hhalf, Real.rpow_natCast] using hrightRow t) (inv_nonneg.mpr hq0.le)
      simpa only [Real.one_rpow] using h
    have hS : 0 ≤ ∑ i, ∑ j, ‖F (1 + (t : ℂ) * Complex.I) i j‖ ^ q :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
    have hcap : (∑ i, ∑ j, ‖F (1 + (t : ℂ) * Complex.I) i j‖ ^ q) ≤ (Real.sqrt q)⁻¹ ^ q := by
      apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hc q)).mp
      rw [← Real.mul_rpow hc.le (inv_nonneg.mpr hc.le), mul_inv_cancel₀ hc.ne', Real.one_rpow]
      exact hrightEntry t
    have hE : E ≤ (Real.sqrt q)⁻¹ := by
      have h := Real.rpow_le_rpow hS hcap (inv_nonneg.mpr hq0.le)
      simpa only [Real.rpow_rpow_inv (inv_nonneg.mpr hc.le) hq0.ne'] using h
    have hsqrt : Real.sqrt (k : ℝ) ≤ Real.sqrt q := by
      apply Real.sqrt_le_sqrt
      dsimp [q]
      exact_mod_cast (by omega : k ≤ 2 * k)
    have hprod : Real.sqrt k * E ≤ 1 := by
      calc
        _ ≤ Real.sqrt k * (Real.sqrt q)⁻¹ := mul_le_mul_of_nonneg_left hE (Real.sqrt_nonneg _)
        _ ≤ Real.sqrt q * (Real.sqrt q)⁻¹ := mul_le_mul_of_nonneg_right hsqrt (inv_nonneg.mpr hc.le)
        _ = _ := mul_inv_cancel₀ hc.ne'
    have heven := integral_schattenNormReal_symmetricComplexGaussianMatrix_pow_two_mul_root_le
      (F (1 + (t : ℂ) * Complex.I)) (hFs _) k hk
    have hmoment :
        (∫ G, schattenNormReal (symmetricComplexGaussianMatrix (F (1 + (t : ℂ) * Complex.I)) G) q ^ q
          ∂gaussianMatrix n n) ^ (1 / q) ≤ 48 * (A + Real.sqrt k * E) := by
      simpa only [q, A, E, Real.rpow_natCast, one_div] using heven
    exact hmoment.trans (by linarith)
  have hinterp :=
    integral_schattenNormReal_symmetricComplexGaussianMatrix_rpow_root_le_of_boundary_bounds
      hθ (by norm_num : (1 : ℝ) < 2) hq (by linarith : (1 : ℝ) < p)
      hexp (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 96) F
      ⟨hF.differentiableOn, hF.continuous.continuousOn⟩ hbnd hleftMoment hrightMoment
  rw [hFc, one_div] at hinterp
  apply hinterp.trans
  have h := Real.geom_mean_le_arith_mean2_weighted
    (sub_nonneg.mpr hθ.2.le) hθ.1.le (by norm_num : (0 : ℝ) ≤ 2)
    (by norm_num : (0 : ℝ) ≤ 96) (by ring : 1 - θ + θ = 1)
  exact h.trans (by nlinarith [hθ.2])

end NLAlib
