import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Positive Gaussian radial moments

Scalar Gaussian radial integration used by the operator quadratic-probe route.
Atlas: `gaussian-positive-moments`, helper of `inverse-wishart-spectral-moment`.
The radial machinery is shared with the rank-one Wishart sanity check.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace NLAlib

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

/-- Polar coordinates for a scalar radial test of a standard Gaussian vector.
Source: Gaussian polar integration; atlas `gaussian-positive-moments`.
This is only a scalar Gaussian identity, with no matrix eigenvalue density. -/
theorem integral_radial_pi_gaussianReal (m : ℕ) (hm : 1 ≤ m) (φ : ℝ → ℝ) :
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


private lemma integral_rpow_mul_exp_neg_sq_div_two (s : ℝ) (hs : -1 < s) :
    ∫ y in Ioi (0 : ℝ), y ^ s * Real.exp (-y ^ 2 / 2)
      = 2 ^ ((s + 1) / 2) * (1 / 2) * Real.Gamma ((s + 1) / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := s) (b := 1 / 2)
    (by norm_num) hs (by norm_num)
  have hhalf : (1 / 2 : ℝ) ^ (-(s + 1) / 2) = 2 ^ ((s + 1) / 2) := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    congr 1
    ring
  rw [hhalf] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  rw [Real.rpow_two]
  congr 2
  ring

/-- Every nonnegative real power of the squared Gaussian radius is integrable.
Source: Gaussian finite moments; atlas `gaussian-positive-moments`. -/
theorem integrable_rpow_sum_sq_pi_gaussianReal (m : ℕ) (q : ℝ) (hq : 0 ≤ q) :
    Integrable (fun x : Fin m → ℝ => (∑ i, x i ^ 2) ^ q)
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  let μ := Measure.pi fun _ : Fin m => gaussianReal 0 1
  have hLp : MemLp (fun x : Fin m → ℝ => WithLp.toLp 2 x)
      (ENNReal.ofReal (2 * q)) μ := by
    rw [memLp_piLp_iff]
    intro i
    have h := (memLp_id_gaussianReal' (μ := 0) (v := 1)
      (ENNReal.ofReal (2 * q)) ENNReal.ofReal_ne_top).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin m => gaussianReal 0 1) i)
    simpa using h
  have hint := hLp.integrable_norm_rpow'
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * q)] at hint
  refine hint.congr (ae_of_all _ fun x => ?_)
  change ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))‖ ^ (2 * q) = _
  rw [EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  congr 1
  ring

/-- Exact positive real moments of the squared Gaussian radius.
Source: scalar Gaussian radial integration; atlas `gaussian-positive-moments`.
This identity is the radial input to the operator inverse-Wishart probe bound. -/
theorem integral_rpow_sum_sq_pi_gaussianReal (m : ℕ) (hm : 1 ≤ m)
    (q : ℝ) (hq : 0 ≤ q) :
    ∫ x : Fin m → ℝ, (∑ i, x i ^ 2) ^ q
      ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = 2 ^ q * Real.Gamma ((m : ℝ) / 2 + q) / Real.Gamma ((m : ℝ) / 2) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub hm, Nat.cast_one]
  let K : ℝ := m * (volume : Measure (EuclideanSpace ℝ (Fin m))).real (Metric.ball 0 1)
    * (Real.sqrt (2 * π))⁻¹ ^ m
  have hnorm := integral_radial_pi_gaussianReal m hm (fun _ => 1)
  simp only [integral_const, smul_eq_mul, mul_one] at hnorm
  rw [measureReal_def, measure_univ, ENNReal.toReal_one] at hnorm
  have hbase : (∫ y in Ioi (0 : ℝ), y ^ (m - 1) * Real.exp (-y ^ 2 / 2))
      = 2 ^ ((m : ℝ) / 2) * (1 / 2) * Real.Gamma ((m : ℝ) / 2) := by
    have hfun : (∫ y in Ioi (0 : ℝ), y ^ (m - 1) * Real.exp (-y ^ 2 / 2))
        = ∫ y in Ioi (0 : ℝ), y ^ ((m : ℝ) - 1) * Real.exp (-y ^ 2 / 2) := by
      simp_rw [← hcast, Real.rpow_natCast]
    rw [hfun, integral_rpow_mul_exp_neg_sq_div_two _ (by linarith)]
    rw [show ((m : ℝ) - 1 + 1) / 2 = (m : ℝ) / 2 by ring]
  rw [hbase] at hnorm
  have hnorm' : 1 = K * (2 ^ ((m : ℝ) / 2) * (1 / 2) * Real.Gamma ((m : ℝ) / 2)) := by
    simpa only [K, mul_assoc] using hnorm
  have hmoment := integral_radial_pi_gaussianReal m hm (fun y => y ^ (2 * q))
  have hleft : (fun x : Fin m → ℝ => (Real.sqrt (∑ i, x i ^ 2)) ^ (2 * q))
      = (fun x : Fin m → ℝ => (∑ i, x i ^ 2) ^ q) := by
    funext x
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    congr 1
    ring
  rw [hleft] at hmoment
  have hright : (∫ y in Ioi (0 : ℝ), y ^ (m - 1) *
      (Real.exp (-y ^ 2 / 2) * y ^ (2 * q)))
      = 2 ^ ((m : ℝ) / 2 + q) * (1 / 2) * Real.Gamma ((m : ℝ) / 2 + q) := by
    have hfun : (∫ y in Ioi (0 : ℝ), y ^ (m - 1) *
        (Real.exp (-y ^ 2 / 2) * y ^ (2 * q)))
        = ∫ y in Ioi (0 : ℝ), y ^ ((m : ℝ) - 1 + 2 * q) * Real.exp (-y ^ 2 / 2) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
      rw [← Real.rpow_natCast, hcast, mul_left_comm, ← Real.rpow_add hy]
      ring
    rw [hfun, integral_rpow_mul_exp_neg_sq_div_two _ (by linarith)]
    congr 2 <;> congr 1 <;> ring
  rw [hright] at hmoment
  have hmoment' : (∫ x : Fin m → ℝ, (∑ i, x i ^ 2) ^ q
      ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1))
      = K * (2 ^ ((m : ℝ) / 2 + q) * (1 / 2) * Real.Gamma ((m : ℝ) / 2 + q)) := by
    rw [hmoment]
    simp [K]
    ring
  rw [hmoment', Real.rpow_add (by norm_num)]
  have hG : Real.Gamma ((m : ℝ) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  apply (eq_div_iff hG).2
  calc K * (2 ^ ((m : ℝ) / 2) * 2 ^ q * (1 / 2) * Real.Gamma ((m : ℝ) / 2 + q))
        * Real.Gamma ((m : ℝ) / 2)
      = (K * (2 ^ ((m : ℝ) / 2) * (1 / 2) * Real.Gamma ((m : ℝ) / 2)))
        * (2 ^ q * Real.Gamma ((m : ℝ) / 2 + q)) := by ring
    _ = _ := by rw [← hnorm', one_mul]

/-- The absolute scalar Gaussian moment at every nonnegative real order.
Source: scalar Gaussian Gamma integral; atlas `gaussian-positive-moments`.
This supplies the normalization of the operator quadratic probe. -/
theorem integral_abs_rpow_gaussianReal (q : ℝ) (hq : 0 ≤ q) :
    (∫ z : ℝ, |z| ^ (2 * q) ∂(gaussianReal 0 1))
      = 2 ^ q * Real.Gamma (q + 1 / 2) / Real.sqrt Real.pi := by
  have h := integral_rpow_sum_sq_pi_gaussianReal 1 (by omega) q hq
  have hfun : (fun x : Fin 1 → ℝ => (∑ i, x i ^ 2) ^ q)
      = (fun z : ℝ => |z| ^ (2 * q)) ∘ (fun x : Fin 1 → ℝ => x 0) := by
    funext x
    simp only [Fin.sum_univ_one, Function.comp_apply]
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
  rw [hfun] at h
  have heval : (∫ x : Fin 1 → ℝ, |x 0| ^ (2 * q)
      ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1))
      = ∫ z : ℝ, |z| ^ (2 * q) ∂(gaussianReal 0 1) := by
    rw [← integral_map (μ := Measure.pi fun _ : Fin 1 => gaussianReal 0 1)
      (φ := fun x : Fin 1 → ℝ => x 0) (f := fun z : ℝ => |z| ^ (2 * q))
      (measurable_pi_apply 0).aemeasurable
      (by fun_prop : Measurable (fun z : ℝ => |z| ^ (2 * q))).aestronglyMeasurable,
      (measurePreserving_eval (fun _ : Fin 1 => gaussianReal 0 1) 0).map_eq]
  change (∫ x : Fin 1 → ℝ, |x 0| ^ (2 * q) ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1)) = _ at h
  rw [heval] at h
  simpa only [Nat.cast_one, add_comm, Real.Gamma_one_half_eq] using h

end NLAlib
