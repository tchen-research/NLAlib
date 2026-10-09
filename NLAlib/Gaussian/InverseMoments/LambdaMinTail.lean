/-
Ported from the Prove2me workspace (Gaussian Random Matrices series, solutions
`Sol_GaussianMatrix_wishart_lambda_min_cdf_rank_one`, `Sol_GaussianMatrix_tw_gamma_ratio_bound`,
`Sol_GaussianMatrix_wishart_lambda_min_tail`; theorem
`Thm_GaussianMatrix_wishart_lambda_min_cdf_density_bound`, which has no solution).
-/
import NLAlib.Gaussian.Basic
import NLAlib.Matrix.Spectral
import NLAlib.Concentration.Scalar.TailIntegral
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Lower tail of the smallest eigenvalue of a Wishart matrix

For an `r × k` standard Gaussian matrix `G` (`1 ≤ r ≤ k`), the smallest eigenvalue
`λ_min(G Gᵀ) = σ_min(Gᵀ)²` has the small-ball bound (Tropp–Webber 2023, (B.5)–(B.7);
Edelman 1988; Chen–Dongarra 2005)
`P[σ_min(Gᵀ)² ≤ t] ≤ (1/Γ(k-r+2)) (t (k+r)/2)^{(k-r+1)/2}`.

* `gaussianMatrix_one_sigmaMin_transpose_sq_le_eq`: for `r = 1`, `σ_min(Gᵀ)² = ‖g‖² ∼ χ²_k`,
  and its CDF is the `χ²_k` density integral, written in the shape of (B.5);
* `gaussianMatrix_sigmaMin_transpose_sq_le_le_lintegral` (**scaffold**): the density bound
  (B.5) for general `r`, the only unproved statement of the series;
* `gammaRatio_le`: the Gamma-function estimate (B.6) behind the simplification of (B.5);
* `gaussianMatrix_sigmaMin_transpose_sq_le_le`: the tail bound (B.7)
  (atlas `wishart-lambda-min-tail`).

Atlas: `wishart-lambda-min-tail`. Proof source: Prove2me workspace, Gaussian Random Matrices
series; the workspace's `sMin` is `NLAlib.sigmaMin` (same definition) and
`integral_power_exp_le` is `NLAlib.lintegral_rpow_mul_exp_le`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped Matrix

namespace NLAlib

/-! ### The rank-one case: the `χ²_k` law -/

/-- The product of `m` standard Gaussians has density `∏ᵢ φ(xᵢ)` w.r.t. Lebesgue measure. -/
private lemma pi_gaussianReal_eq_withDensity (m : ℕ) :
    Measure.pi (fun _ : Fin m => gaussianReal 0 1)
      = volume.withDensity
          (fun x : Fin m → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
  refine Measure.pi_eq (μ := fun _ : Fin m => gaussianReal 0 1) fun s hs => ?_
  have hS : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hS, ← lintegral_indicator hS]
  have hind : ∀ x : Fin m → ℝ,
      (Set.univ.pi s).indicator (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) x
        = ENNReal.ofReal (∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i)) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)]
      simp
  simp_rw [hind]
  have hint : Integrable (fun x : Fin m → ℝ => ∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i))
      volume := by
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun i => (s i).indicator (gaussianPDFReal 0 1))
      (fun i => (integrable_gaussianPDFReal 0 1).indicator (hs i))
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun x => Finset.prod_nonneg fun i _ =>
      Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) _)]
  rw [integral_fintype_prod_volume_eq_prod, ENNReal.ofReal_prod_of_nonneg
    (fun i _ => integral_nonneg fun y =>
      Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero, integral_indicator (hs i)]

private lemma prod_gaussianPDFReal {m : ℕ} (x : Fin m → ℝ) :
    ∏ i, gaussianPDFReal 0 1 (x i)
      = (Real.sqrt (2 * π))⁻¹ ^ m * Real.exp (-(∑ i, x i ^ 2) / 2) := by
  simp only [gaussianPDFReal, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Real.exp_sum]
  congr 2
  · simp
  · simp only [sub_zero, NNReal.coe_one, mul_one, neg_div]
    rw [Finset.sum_neg_distrib, Finset.sum_div]

private lemma sum_sq_ofLp {m : ℕ} (y : EuclideanSpace ℝ (Fin m)) :
    ∑ i, (WithLp.ofLp y) i ^ 2 = ‖y‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [Real.norm_eq_abs, sq_abs]

/-- Polar coordinates for a radial function of a standard Gaussian vector. -/
private lemma integral_radial_pi_gaussianReal (m : ℕ) (hm : 1 ≤ m) (φ : ℝ → ℝ) :
    ∫ x, φ (Real.sqrt (∑ i, x i ^ 2)) ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = m * (volume : Measure (EuclideanSpace ℝ (Fin m))).real (Metric.ball 0 1)
        * ((Real.sqrt (2 * π))⁻¹ ^ m
          * ∫ y in Ioi (0 : ℝ), y ^ (m - 1) * (Real.exp (-y ^ 2 / 2) * φ y)) := by
  rw [pi_gaussianReal_eq_withDensity, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 _),
    smul_eq_mul, prod_gaussianPDFReal]
  rw [← (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)).integral_comp']
  simp only [MeasurableEquiv.toLp_symm_apply]
  simp_rw [sum_sq_ofLp, Real.sqrt_sq (norm_nonneg _)]
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have : Nontrivial (EuclideanSpace ℝ (Fin m)) := inferInstance
  have := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin m)))
    (fun r => (Real.sqrt (2 * π))⁻¹ ^ m * Real.exp (-r ^ 2 / 2) * φ r)
  rw [this, finrank_euclideanSpace_fin, nsmul_eq_mul, smul_eq_mul]
  simp_rw [smul_eq_mul]
  have e : ∀ y : ℝ, y ^ (m - 1) * ((Real.sqrt (2 * π))⁻¹ ^ m * Real.exp (-y ^ 2 / 2) * φ y)
      = (Real.sqrt (2 * π))⁻¹ ^ m * (y ^ (m - 1) * (Real.exp (-y ^ 2 / 2) * φ y)) := fun y => by
    ring
  simp_rw [e]
  rw [integral_const_mul]
  ring

/-- `∫₀^∞ y^k e^{-y²/2} dy = (1/2)^{-(k+1)/2} (1/2) Γ((k+1)/2)`. -/
private lemma integral_pow_mul_exp_neg_sq_div_two (k : ℕ) :
    ∫ y in Ioi (0 : ℝ), y ^ k * Real.exp (-y ^ 2 / 2)
      = (1 / 2 : ℝ) ^ (-((k : ℝ) + 1) / 2) * (1 / 2) * Real.Gamma (((k : ℝ) + 1) / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (k : ℝ)) (b := 1 / 2)
    (by norm_num) (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith) (by norm_num)
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  rw [Real.rpow_natCast, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  congr 2
  ring

private lemma sigmaMin_transpose_sq_of_one {k : ℕ} (G : Fin 1 → Fin k → ℝ) :
    sigmaMin (Matrix.of G)ᵀ ^ 2 = ∑ j, G 0 j ^ 2 := by
  have hconst : ∀ x : {x : Fin 1 → ℝ // x ⬝ᵥ x = 1},
      Real.sqrt (((Matrix.of G)ᵀ *ᵥ x.1) ⬝ᵥ ((Matrix.of G)ᵀ *ᵥ x.1))
        = Real.sqrt (∑ j, G 0 j ^ 2) := by
    rintro ⟨x, hx⟩
    congr 1
    have hx0 : x 0 ^ 2 = 1 := by
      simpa [dotProduct, Fin.sum_univ_one, sq] using hx
    simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Matrix.of_apply,
      Fin.sum_univ_one]
    calc ∑ j, G 0 j * x 0 * (G 0 j * x 0) = ∑ j, G 0 j ^ 2 * x 0 ^ 2 :=
          Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j, G 0 j ^ 2 := by simp [hx0]
  have hne : Nonempty {x : Fin 1 → ℝ // x ⬝ᵥ x = 1} :=
    ⟨⟨fun _ => 1, by simp [dotProduct]⟩⟩
  unfold sigmaMin
  simp_rw [hconst]
  rw [ciInf_const, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

private lemma gaussianMatrix_one_preimage {k : ℕ} (T : Set (Fin k → ℝ)) (hT : MeasurableSet T) :
    (gaussianMatrix 1 k) ((fun G => G 0) ⁻¹' T)
      = (Measure.pi fun _ : Fin k => gaussianReal 0 1) T := by
  have h := measurePreserving_funUnique (Measure.pi fun _ : Fin k => gaussianReal 0 1) (Fin 1)
  unfold gaussianMatrix
  exact h.measure_preimage hT.nullMeasurableSet

/-- Change of variables `y = √λ`. -/
private lemma integral_Ioi_indicator_eq {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 ≤ t) :
    ∫ y in Ioi (0 : ℝ), y ^ (k - 1) * (Real.exp (-y ^ 2 / 2)
        * (Iic (Real.sqrt t)).indicator (fun _ => (1 : ℝ)) y)
      = (1 / 2) * ∫ x in Ioc (0 : ℝ) t, x ^ (((k : ℝ) - 2) / 2) * Real.exp (-x / 2) := by
  have h := integral_comp_rpow_Ioi
    (fun x : ℝ => (Iic t).indicator (fun x => (1 / 2 : ℝ) * (x ^ (((k : ℝ) - 2) / 2)
      * Real.exp (-x / 2))) x) (p := 2) (by norm_num)
  have hR : (1 / 2 : ℝ) * ∫ x in Ioc (0 : ℝ) t, x ^ (((k : ℝ) - 2) / 2) * Real.exp (-x / 2)
      = ∫ y in Ioi (0 : ℝ), (Iic t).indicator (fun x => (1 / 2 : ℝ) * (x ^ (((k : ℝ) - 2) / 2)
          * Real.exp (-x / 2))) y := by
    rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      Set.Iic_inter_Ioi, integral_const_mul]
  rw [hR, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) => ?_
  simp only [smul_eq_mul]
  have hiff : y ^ (2 : ℝ) ∈ Iic t ↔ y ∈ Iic (Real.sqrt t) := by
    rw [Real.rpow_two, Set.mem_Iic, Set.mem_Iic, Real.le_sqrt hy.le]
    exact ht
  by_cases hyt : y ∈ Iic (Real.sqrt t)
  · rw [Set.indicator_of_mem hyt, Set.indicator_of_mem (hiff.2 hyt)]
    have hpow : y ^ (k - 1) = y ^ ((2 : ℝ) - 1) * (y ^ (2 : ℝ)) ^ (((k : ℝ) - 2) / 2) := by
      rw [← Real.rpow_mul hy.le, ← Real.rpow_add hy, ← Real.rpow_natCast, Nat.cast_sub hk]
      congr 1; push_cast; ring
    rw [hpow, abs_two, Real.rpow_two]
    ring
  · rw [Set.indicator_of_notMem hyt, Set.indicator_of_notMem (fun h => hyt (hiff.1 h))]
    simp

/-- Constant identity: `c(1,k) · 2^{k/2} Γ(k/2) = 1` (Legendre duplication). -/
private lemma rankOne_const_mul {k : ℕ} (hk : 1 ≤ k) :
    2 ^ (((k : ℝ) - 2) / 2) * Real.Gamma (((k : ℝ) + 1) / 2)
        / (Real.Gamma (1 / 2) * Real.Gamma (k : ℝ))
      * ((1 / 2 : ℝ) ^ (-(((k - 1 : ℕ) : ℝ) + 1) / 2) * (1 / 2)
        * Real.Gamma ((((k - 1 : ℕ) : ℝ) + 1) / 2)) = 1 / 2 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hc : ((k - 1 : ℕ) : ℝ) + 1 = k := by rw [Nat.cast_sub hk]; push_cast; ring
  rw [hc]
  have hdup := Real.Gamma_mul_Gamma_add_half ((k : ℝ) / 2)
  rw [show (k : ℝ) / 2 + 1 / 2 = ((k : ℝ) + 1) / 2 by ring, show 2 * ((k : ℝ) / 2) = k by ring]
    at hdup
  have hhalf : (1 / 2 : ℝ) ^ (-(k : ℝ) / 2) = 2 ^ ((k : ℝ) / 2) := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    congr 1; ring
  rw [hhalf, Real.Gamma_one_half_eq]
  have gk := Real.Gamma_pos_of_pos (show (0 : ℝ) < k by linarith)
  have gk2 := Real.Gamma_pos_of_pos (show (0 : ℝ) < k / 2 by linarith)
  have hpi : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  have h2 : (2 : ℝ) ^ (((k : ℝ) - 2) / 2) * 2 ^ ((k : ℝ) / 2) * 2 ^ (1 - (k : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num),
      show ((k : ℝ) - 2) / 2 + k / 2 + (1 - k) = 0 by ring, Real.rpow_zero]
  rw [div_mul_eq_mul_div, div_eq_iff (by positivity)]
  calc 2 ^ (((k : ℝ) - 2) / 2) * Real.Gamma (((k : ℝ) + 1) / 2)
        * (2 ^ ((k : ℝ) / 2) * (1 / 2) * Real.Gamma ((k : ℝ) / 2))
      = 2 ^ (((k : ℝ) - 2) / 2) * 2 ^ ((k : ℝ) / 2) * (Real.Gamma ((k : ℝ) / 2)
          * Real.Gamma (((k : ℝ) + 1) / 2)) * (1 / 2) := by ring
    _ = 2 ^ (((k : ℝ) - 2) / 2) * 2 ^ ((k : ℝ) / 2) * 2 ^ (1 - (k : ℝ))
          * (Real.sqrt π * Real.Gamma k) * (1 / 2) := by rw [hdup]; ring
    _ = 1 / 2 * (Real.sqrt π * Real.Gamma k) := by rw [h2]; ring

/-- **The smallest Wishart eigenvalue for `r = 1`.** For a `1 × k` standard Gaussian matrix
`G` (`k ≥ 1`) and `t ≥ 0`, `σ_min(Gᵀ)² = ‖G‖² ∼ χ²_k`, and
`P[σ_min(Gᵀ)² ≤ t] = ∫₀ᵗ c(1,k) x^{(k-2)/2} e^{-x/2} dx` with
`c(1,k) = 2^{(k-2)/2} Γ((k+1)/2) / (Γ(1/2) Γ(k))` (`= 1/(2^{k/2} Γ(k/2))` by Legendre
duplication): the `χ²_k` CDF written in the shape of Tropp–Webber 2023, (B.5).

Tropp–Webber 2023, (B.5) in the case `r = 1` (where it is an equality); Edelman 1988.
Atlas: `wishart-lambda-min-tail` (sanity case). Proof: polar coordinates for the standard
Gaussian vector and the substitution `y = √x`. Ported from Prove2me solution
`GaussianMatrix.wishart_lambda_min_cdf_rank_one`. -/
theorem gaussianMatrix_one_sigmaMin_transpose_sq_le_eq {k : ℕ} (hk : 1 ≤ k) (t : ℝ)
    (ht : 0 ≤ t) :
    (gaussianMatrix 1 k) {G | sigmaMin (Matrix.of G)ᵀ ^ 2 ≤ t}
      = ∫⁻ x in Set.Ioc 0 t, ENNReal.ofReal
          (2 ^ (((k : ℝ) - 2) / 2) * Real.Gamma (((k : ℝ) + 1) / 2)
              / (Real.Gamma (1 / 2) * Real.Gamma (k : ℝ))
            * x ^ (((k : ℝ) - 2) / 2) * Real.exp (-x / 2)) := by
  set c : ℝ := 2 ^ (((k : ℝ) - 2) / 2) * Real.Gamma (((k : ℝ) + 1) / 2)
              / (Real.Gamma (1 / 2) * Real.Gamma (k : ℝ)) with hc
  set a : ℝ := ((k : ℝ) - 2) / 2 with ha
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha1 : -1 < a := by rw [ha]; linarith
  have hcpos : 0 ≤ c := by
    rw [hc]
    have := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
    have := Real.Gamma_pos_of_pos (show (0 : ℝ) < k by linarith)
    have := Real.Gamma_pos_of_pos (show (0 : ℝ) < ((k : ℝ) + 1) / 2 by linarith)
    positivity
  set T : Set (Fin k → ℝ) := {g | ∑ j, g j ^ 2 ≤ t} with hT
  have hTm : MeasurableSet T := measurableSet_le (by fun_prop) measurable_const
  have hset : {G : Fin 1 → Fin k → ℝ | sigmaMin (Matrix.of G)ᵀ ^ 2 ≤ t}
      = (fun G => G 0) ⁻¹' T := by
    ext G; simp [hT, sigmaMin_transpose_sq_of_one]
  rw [hset, gaussianMatrix_one_preimage T hTm]
  set ν := Measure.pi fun _ : Fin k => gaussianReal 0 1 with hν
  set φ : ℝ → ℝ := (Iic (Real.sqrt t)).indicator (fun _ => (1 : ℝ)) with hφ
  have hνT : ν.real T = ∫ x, φ (Real.sqrt (∑ i, x i ^ 2)) ∂ν := by
    rw [← integral_indicator_one hTm]
    congr 1; ext x
    have hs : Real.sqrt (∑ i, x i ^ 2) ∈ Iic (Real.sqrt t) ↔ x ∈ T := by
      rw [Set.mem_Iic, Real.sqrt_le_sqrt_iff ht]; rfl
    by_cases hx : x ∈ T
    · rw [Set.indicator_of_mem hx, hφ, Set.indicator_of_mem (hs.2 hx)]; rfl
    · rw [Set.indicator_of_notMem hx, hφ, Set.indicator_of_notMem (fun h => hx (hs.1 h))]
  have h1 := integral_radial_pi_gaussianReal k hk (fun _ => 1)
  have h2 := integral_radial_pi_gaussianReal k hk φ
  simp only [integral_const, smul_eq_mul, mul_one] at h1
  rw [measureReal_def, measure_univ, ENNReal.toReal_one] at h1
  rw [integral_pow_mul_exp_neg_sq_div_two] at h1
  rw [hφ, integral_Ioi_indicator_eq hk ht] at h2
  set I : ℝ := ∫ x in Ioc (0 : ℝ) t, x ^ a * Real.exp (-x / 2) with hI
  have hint : IntegrableOn (fun x : ℝ => x ^ a * Real.exp (-x / 2)) (Ioc 0 t) := by
    have hpow : IntegrableOn (fun x : ℝ => x ^ a) (Ioc 0 t) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).1
        (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t) ha1)
    refine hpow.mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx.1.le _)
      (Real.exp_pos _).le)]
    have h1 : 0 ≤ x ^ a := Real.rpow_nonneg hx.1.le _
    have h2 : Real.exp (-x / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [hx.1])
    nlinarith
  have hRHS : ∫⁻ x in Set.Ioc 0 t, ENNReal.ofReal (c * x ^ a * Real.exp (-x / 2))
      = ENNReal.ofReal (c * I) := by
    rw [hI, ← integral_const_mul, ofReal_integral_eq_lintegral_ofReal]
    · simp_rw [mul_assoc]
    · exact hint.const_mul c
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact mul_nonneg hcpos (mul_nonneg (Real.rpow_nonneg hx.1.le _) (Real.exp_pos _).le)
  rw [hRHS, ← ofReal_measureReal, hνT, h2]
  congr 1
  have hconst := rankOne_const_mul hk
  rw [← hc] at hconst
  set K := (k : ℝ) * (volume : Measure (EuclideanSpace ℝ (Fin k))).real (Metric.ball 0 1)
    * (Real.sqrt (2 * π))⁻¹ ^ k with hK
  set J := (1 / 2 : ℝ) ^ (-(((k - 1 : ℕ) : ℝ) + 1) / 2) * (1 / 2)
        * Real.Gamma ((((k - 1 : ℕ) : ℝ) + 1) / 2) with hJ
  have h1' : 1 = K * J := by rw [h1, hK]; ring
  calc (k : ℝ) * (volume : Measure (EuclideanSpace ℝ (Fin k))).real (Metric.ball 0 1)
        * ((Real.sqrt (2 * π))⁻¹ ^ k * (1 / 2 * I))
      = K * (1 / 2) * I := by rw [hK]; ring
    _ = K * (c * J) * I := by rw [hconst]
    _ = (K * J) * c * I := by ring
    _ = c * I := by rw [← h1']; ring

/-! ### The density bound (scaffold) -/

/-- **Density bound for the smallest Wishart eigenvalue** (Tropp–Webber 2023, (B.5); Edelman
1988, Chen–Dongarra 2005). For an `r × k` standard Gaussian matrix `G` with `1 ≤ r ≤ k` and
`t > 0`,
`P[σ_min(Gᵀ)² ≤ t] ≤ ∫₀ᵗ c(r,k) x^{(k-r-1)/2} e^{-x/2} dx` with
`c(r,k) = 2^{(k-r-1)/2} Γ((k+1)/2) / (Γ(r/2) Γ(k-r+1))`.

SCAFFOLD: wishart-lambda-min-tail. This is the only statement of the Prove2me Gaussian series
without a solution. Its proof needs the joint eigenvalue density of the real Wishart matrix
`G Gᵀ` (or Edelman's bound on the marginal density of `λ_min`), i.e. a change of variables to
the eigen-decomposition with the Vandermonde Jacobian, which Mathlib does not provide. The case
`r = 1` holds with equality (`gaussianMatrix_one_sigmaMin_transpose_sq_le_eq`). Statement
identical to Prove2me theorem `GaussianMatrix.wishart_lambda_min_cdf_density_bound`. -/
theorem gaussianMatrix_sigmaMin_transpose_sq_le_le_lintegral {r k : ℕ} (hr : 1 ≤ r)
    (hrk : r ≤ k) (t : ℝ) (ht : 0 < t) :
    (gaussianMatrix r k) {G | sigmaMin (Matrix.of G)ᵀ ^ 2 ≤ t}
      ≤ ∫⁻ x in Set.Ioc 0 t, ENNReal.ofReal
          (2 ^ (((k : ℝ) - r - 1) / 2) * Real.Gamma (((k : ℝ) + 1) / 2)
              / (Real.Gamma ((r : ℝ) / 2) * Real.Gamma ((k : ℝ) - r + 1))
            * x ^ (((k : ℝ) - r - 1) / 2) * Real.exp (-x / 2)) := by
  sorry

/-! ### The Gamma-ratio estimate -/

/-- Squared Gautschi inequality `Γ(z + 1/2)² ≤ z Γ(z)²`, from log-convexity of `Γ`. -/
private lemma Gamma_add_half_sq_le {z : ℝ} (hz : 0 < z) :
    Real.Gamma (z + 1 / 2) ^ 2 ≤ z * Real.Gamma z ^ 2 := by
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := z) (t := z + 1)
    (a := 1 / 2) (b := 1 / 2) hz (by linarith) (by norm_num) (by norm_num) (by norm_num)
  have he : (1 / 2 : ℝ) * z + 1 / 2 * (z + 1) = z + 1 / 2 := by ring
  rw [he] at h
  have hg := Real.Gamma_pos_of_pos hz
  have hg1 := Real.Gamma_pos_of_pos (show 0 < z + 1 by linarith)
  have h0 : 0 ≤ Real.Gamma (z + 1 / 2) := (Real.Gamma_pos_of_pos (by linarith)).le
  calc Real.Gamma (z + 1 / 2) ^ 2
      ≤ (Real.Gamma z ^ (1 / 2 : ℝ) * Real.Gamma (z + 1) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ h0 h 2
    _ = Real.Gamma z * Real.Gamma (z + 1) := by
        rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hg.le,
          Real.sq_sqrt hg1.le]
    _ = z * Real.Gamma z ^ 2 := by rw [Real.Gamma_add_one hz.ne']; ring

/-- Iterated Gautschi: `Γ((r+n)/2)² ≤ Γ(r/2)² ∏_{i<n} (r+i)/2`. -/
private lemma Gamma_half_sq_le_mul_prod {r : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    Real.Gamma (((r : ℝ) + n) / 2) ^ 2
      ≤ Real.Gamma ((r : ℝ) / 2) ^ 2 * ∏ i ∈ Finset.range n, (((r : ℝ) + i) / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
    have hz : (0 : ℝ) < ((r : ℝ) + n) / 2 := by positivity
    have hg := Gamma_add_half_sq_le hz
    have he : ((r : ℝ) + n) / 2 + 1 / 2 = ((r : ℝ) + ((n + 1 : ℕ) : ℝ)) / 2 := by
      push_cast; ring
    rw [he] at hg
    rw [Finset.prod_range_succ]
    calc Real.Gamma (((r : ℝ) + ((n + 1 : ℕ) : ℝ)) / 2) ^ 2
        ≤ ((r : ℝ) + n) / 2 * Real.Gamma (((r : ℝ) + n) / 2) ^ 2 := hg
      _ ≤ ((r : ℝ) + n) / 2 * (Real.Gamma ((r : ℝ) / 2) ^ 2
            * ∏ i ∈ Finset.range n, (((r : ℝ) + i) / 2)) :=
          mul_le_mul_of_nonneg_left ih hz.le
      _ = _ := by ring

/-- **AM–GM for an arithmetic progression.** For `r ≥ 0`,
`∏_{i=0}^{n} (r + i) ≤ ((2r + n)/2)^{n+1}` (pair `r + i` with `r + n - i`).

Helper for Tropp–Webber 2023, (B.6). Atlas: `wishart-lambda-min-tail` (helper). Ported from
the Prove2me solution `Sol_GaussianMatrix_tw_gamma_ratio_bound` (`prod_range_add_le`). -/
theorem prod_range_add_le_pow (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    ∏ i ∈ Finset.range (n + 1), (r + i) ≤ ((2 * r + n) / 2) ^ (n + 1) := by
  set M := (2 * r + n) / 2 with hM
  have hpos : ∀ i ∈ Finset.range (n + 1), 0 ≤ r + (i : ℝ) := fun i _ => by positivity
  have hP : 0 ≤ ∏ i ∈ Finset.range (n + 1), (r + (i : ℝ)) := Finset.prod_nonneg hpos
  have hMpos : 0 ≤ M := by rw [hM]; positivity
  have hrefl : ∏ i ∈ Finset.range (n + 1), (r + ((n - i : ℕ) : ℝ))
      = ∏ i ∈ Finset.range (n + 1), (r + (i : ℝ)) := by
    have := Finset.prod_range_reflect (fun i : ℕ => r + (i : ℝ)) (n + 1)
    simpa using this
  have hsq : (∏ i ∈ Finset.range (n + 1), (r + (i : ℝ))) ^ 2 ≤ (M ^ (n + 1)) ^ 2 := by
    rw [sq]
    calc (∏ i ∈ Finset.range (n + 1), (r + (i : ℝ))) * ∏ i ∈ Finset.range (n + 1), (r + (i : ℝ))
        = (∏ i ∈ Finset.range (n + 1), (r + (i : ℝ)))
            * ∏ i ∈ Finset.range (n + 1), (r + ((n - i : ℕ) : ℝ)) := by rw [hrefl]
      _ = ∏ i ∈ Finset.range (n + 1), ((r + (i : ℝ)) * (r + ((n - i : ℕ) : ℝ))) :=
          (Finset.prod_mul_distrib).symm
      _ ≤ ∏ _i ∈ Finset.range (n + 1), M ^ 2 := by
          apply Finset.prod_le_prod
          · intro i _; positivity
          · intro i hi
            have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
            rw [Nat.cast_sub hin, hM]
            nlinarith [sq_nonneg ((i : ℝ) - ((n : ℝ) - i))]
      _ = (M ^ (n + 1)) ^ 2 := by rw [Finset.prod_const, Finset.card_range, ← pow_mul,
            ← pow_mul, mul_comm]
  exact (pow_le_pow_iff_left₀ hP (pow_nonneg hMpos _) two_ne_zero).1 hsq

/-- **Gamma-ratio estimate.** For `1 ≤ r ≤ k`,
`2^{(k-r-1)/2} Γ((k+1)/2) / (Γ(r/2) Γ(k-r+1)) ≤ ((k+r)/2)^{(k-r+1)/2} / (2 Γ(k-r+1))`,
i.e. the constant of the density bound (B.5) is at most the constant of (B.6).

Tropp–Webber 2023, (B.6). Atlas: `wishart-lambda-min-tail` (helper). Proof: iterated Gautschi
inequality (log-convexity of `Γ`, Bohr–Mollerup) and AM–GM (`prod_range_add_le_pow`). Ported
from Prove2me solution `GaussianMatrix.tw_gamma_ratio_bound`. -/
theorem gammaRatio_le {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) :
    2 ^ (((k : ℝ) - r - 1) / 2) * Real.Gamma (((k : ℝ) + 1) / 2)
        / (Real.Gamma ((r : ℝ) / 2) * Real.Gamma ((k : ℝ) - r + 1))
      ≤ (((k : ℝ) + r) / 2) ^ (((k : ℝ) - r + 1) / 2) / (2 * Real.Gamma ((k : ℝ) - r + 1)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hrk
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  push_cast
  have e1 : ((r : ℝ) + n) - r - 1 = (n : ℝ) - 1 := by ring
  have e2 : ((r : ℝ) + n) - r + 1 = (n : ℝ) + 1 := by ring
  rw [e1, e2]
  set M : ℝ := ((r : ℝ) + n + r) / 2 with hM
  have hMpos : 0 < M := by rw [hM]; positivity
  have gR := Real.Gamma_pos_of_pos (show (0 : ℝ) < r / 2 by positivity)
  have gK := Real.Gamma_pos_of_pos (show (0 : ℝ) < ((r : ℝ) + n + 1) / 2 by positivity)
  have gN := Real.Gamma_pos_of_pos (show (0 : ℝ) < (n : ℝ) + 1 by positivity)
  have key : 2 ^ (n + 1) * Real.Gamma (((r : ℝ) + n + 1) / 2) ^ 2
      ≤ Real.Gamma ((r : ℝ) / 2) ^ 2 * M ^ (n + 1) := by
    have h1 := Gamma_half_sq_le_mul_prod hr (n + 1)
    have h2 := prod_range_add_le_pow (r : ℝ) hrpos.le n
    have hc : ((r : ℝ) + ((n + 1 : ℕ) : ℝ)) / 2 = ((r : ℝ) + n + 1) / 2 := by push_cast; ring
    rw [hc] at h1
    have hprod : ∏ i ∈ Finset.range (n + 1), (((r : ℝ) + i) / 2)
        = (∏ i ∈ Finset.range (n + 1), ((r : ℝ) + i)) / 2 ^ (n + 1) := by
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
    rw [hprod] at h1
    have hM' : (2 * (r : ℝ) + n) / 2 = M := by rw [hM]; ring
    rw [hM'] at h2
    have h2pos : (0 : ℝ) < 2 ^ (n + 1) := by positivity
    calc 2 ^ (n + 1) * Real.Gamma (((r : ℝ) + n + 1) / 2) ^ 2
        ≤ 2 ^ (n + 1) * (Real.Gamma ((r : ℝ) / 2) ^ 2
            * ((∏ i ∈ Finset.range (n + 1), ((r : ℝ) + i)) / 2 ^ (n + 1))) :=
          mul_le_mul_of_nonneg_left h1 h2pos.le
      _ = Real.Gamma ((r : ℝ) / 2) ^ 2 * ∏ i ∈ Finset.range (n + 1), ((r : ℝ) + i) := by
          field_simp
      _ ≤ Real.Gamma ((r : ℝ) / 2) ^ 2 * M ^ (n + 1) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  have hsqrt : (2 : ℝ) ^ (((n : ℝ) + 1) / 2) * Real.Gamma (((r : ℝ) + n + 1) / 2)
      ≤ Real.Gamma ((r : ℝ) / 2) * M ^ (((n : ℝ) + 1) / 2) := by
    have hx : ∀ x : ℝ, 0 ≤ x → x ^ (((n : ℝ) + 1) / 2) = Real.sqrt (x ^ (n + 1)) := by
      intro x hx
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
      congr 1; push_cast; ring
    rw [hx 2 (by norm_num), hx M hMpos.le]
    have := Real.sqrt_le_sqrt key
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq gK.le,
      Real.sqrt_mul (by positivity), Real.sqrt_sq gR.le] at this
    linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h2split : (2 : ℝ) ^ (((n : ℝ) + 1) / 2) = 2 ^ (((n : ℝ) - 1) / 2) * 2 := by
    rw [show ((n : ℝ) + 1) / 2 = ((n : ℝ) - 1) / 2 + 1 by ring, Real.rpow_add (by norm_num),
      Real.rpow_one]
  rw [h2split] at hsqrt
  have hgN := gN.le
  nlinarith [mul_le_mul_of_nonneg_right hsqrt hgN]

/-! ### The tail bound -/

/-- **Lower tail of the smallest Wishart eigenvalue.** For an `r × k` standard Gaussian matrix
`G` with `1 ≤ r ≤ k` and `t > 0`,
`P[λ_min(G Gᵀ) ≤ t] = P[σ_min(Gᵀ)² ≤ t] ≤ (1/Γ(k-r+2)) (t (k+r)/2)^{(k-r+1)/2}`.

Tropp–Webber 2023, (B.7); Chen–Dongarra 2005, Lemma 4.1. Atlas: `wishart-lambda-min-tail`.
Proof: the density bound (B.5)
(`gaussianMatrix_sigmaMin_transpose_sq_le_le_lintegral`, a scaffold), the Gamma-ratio estimate
(`gammaRatio_le`) and `∫₀ᵗ x^a e^{-x/2} dx ≤ t^{a+1}/(a+1)` (`lintegral_rpow_mul_exp_le`, atlas
`tail-integral`). Ported from Prove2me solution `GaussianMatrix.wishart_lambda_min_tail`. -/
theorem gaussianMatrix_sigmaMin_transpose_sq_le_le {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) (t : ℝ)
    (ht : 0 < t) :
    (gaussianMatrix r k) {G | sigmaMin (Matrix.of G)ᵀ ^ 2 ≤ t}
      ≤ ENNReal.ofReal ((1 / Real.Gamma ((k : ℝ) - r + 2))
          * (t * ((k : ℝ) + r) / 2) ^ (((k : ℝ) - r + 1) / 2)) := by
  set c5 : ℝ := 2 ^ (((k : ℝ) - r - 1) / 2) * Real.Gamma (((k : ℝ) + 1) / 2)
      / (Real.Gamma ((r : ℝ) / 2) * Real.Gamma ((k : ℝ) - r + 1)) with hc5
  set c6 : ℝ := (((k : ℝ) + r) / 2) ^ (((k : ℝ) - r + 1) / 2)
      / (2 * Real.Gamma ((k : ℝ) - r + 1)) with hc6
  set a : ℝ := ((k : ℝ) - r - 1) / 2 with ha
  have hrk' : (r : ℝ) ≤ k := by exact_mod_cast hrk
  have ha1 : -1 < a := by rw [ha]; linarith
  have hgN := Real.Gamma_pos_of_pos (show (0 : ℝ) < (k : ℝ) - r + 1 by linarith)
  have hc6pos : 0 ≤ c6 := by rw [hc6]; positivity
  have hD1 := gaussianMatrix_sigmaMin_transpose_sq_le_le_lintegral hr hrk t ht
  have hD2 : c5 ≤ c6 := gammaRatio_le hr hrk
  have hD3 := lintegral_rpow_mul_exp_le ha1 ht.le
  calc (gaussianMatrix r k) {G | sigmaMin (Matrix.of G)ᵀ ^ 2 ≤ t}
      ≤ ∫⁻ x in Set.Ioc 0 t, ENNReal.ofReal (c5 * x ^ a * Real.exp (-x / 2)) := hD1
    _ ≤ ∫⁻ x in Set.Ioc 0 t, ENNReal.ofReal c6 * ENNReal.ofReal (x ^ a * Real.exp (-x / 2)) := by
        refine setLIntegral_mono' measurableSet_Ioc fun x hx => ?_
        rw [← ENNReal.ofReal_mul hc6pos]
        apply ENNReal.ofReal_le_ofReal
        have : 0 ≤ x ^ a * Real.exp (-x / 2) :=
          mul_nonneg (Real.rpow_nonneg hx.1.le _) (Real.exp_pos _).le
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right hD2 this
    _ = ENNReal.ofReal c6 * ∫⁻ x in Set.Ioc 0 t, ENNReal.ofReal (x ^ a * Real.exp (-x / 2)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal c6 * ENNReal.ofReal (t ^ (a + 1) / (a + 1)) := by gcongr
    _ = ENNReal.ofReal ((1 / Real.Gamma ((k : ℝ) - r + 2))
          * (t * ((k : ℝ) + r) / 2) ^ (((k : ℝ) - r + 1) / 2)) := by
        rw [← ENNReal.ofReal_mul hc6pos]
        congr 1
        have hE : a + 1 = ((k : ℝ) - r + 1) / 2 := by rw [ha]; ring
        have hEpos : 0 < ((k : ℝ) - r + 1) / 2 := by linarith
        have hG2 : Real.Gamma ((k : ℝ) - r + 2)
            = ((k : ℝ) - r + 1) * Real.Gamma ((k : ℝ) - r + 1) := by
          rw [show (k : ℝ) - r + 2 = ((k : ℝ) - r + 1) + 1 by ring,
            Real.Gamma_add_one (by linarith)]
        have hsplit : (t * ((k : ℝ) + r) / 2) ^ (((k : ℝ) - r + 1) / 2)
            = t ^ (((k : ℝ) - r + 1) / 2) * (((k : ℝ) + r) / 2) ^ (((k : ℝ) - r + 1) / 2) := by
          rw [show t * ((k : ℝ) + r) / 2 = t * (((k : ℝ) + r) / 2) by ring,
            Real.mul_rpow ht.le (by positivity)]
        rw [hE, hsplit, hG2, hc6]
        field_simp

end NLAlib
