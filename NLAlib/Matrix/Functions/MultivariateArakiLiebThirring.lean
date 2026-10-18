import NLAlib.Matrix.Functions.OrderedComplexPowers
import NLAlib.Matrix.Functions.OrderedExponentialInterpolation
import NLAlib.Matrix.Norms.SchattenPowers
import NLAlib.ForMathlib.Analysis.Complex.HirschmanMeasure
import NLAlib.ForMathlib.MeasureTheory.GeometricMean

/-!
# Multivariate Araki--Lieb--Thirring and singular regularization

The right boundary contains the actual ordered complex powers and the exact
Hirschman density. Positive logarithmic regularization retains zero values
without using the ordinary real logarithm's unrelated value at zero.
Source: Sutter--Berta--Tomamichel, arXiv:1604.03023v3, Theorem 3.2.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Complex Set MeasureTheory Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem abs_log_add_le {x C δ : ℝ} (hx : 0 ≤ x) (hC : x ≤ C) (hδ : 0 < δ) :
    |Real.log (x + δ)| ≤ |Real.log δ| + |Real.log (C + δ)| := by
  have hlo : Real.log δ ≤ Real.log (x + δ) :=
    Real.log_le_log hδ (by linarith)
  have hhi : Real.log (x + δ) ≤ Real.log (C + δ) :=
    Real.log_le_log (by linarith) (by linarith)
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (Real.log δ), abs_nonneg (Real.log (C + δ))]
  · linarith [le_abs_self (Real.log (C + δ)), abs_nonneg (Real.log δ)]

private theorem continuous_log_schatten_ordered_add
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.PosSemidef)
    {p δ : ℝ} (hp : 0 < p) (hδ : 0 < δ) :
    Continuous (fun t : ℝ => Real.log
      (schattenNormReal (orderedMatrixComplexPower L (1 + (t : ℂ) * I)) p + δ)) := by
  apply Continuous.log
  · exact ((continuous_schattenNormReal hp).comp
      (continuous_orderedMatrixComplexPower_right L hL)).add continuous_const
  · intro t
    exact ne_of_gt (add_pos_of_nonneg_of_pos (schattenNormReal_nonneg _ _) hδ)

private theorem integrable_hirschman_log_schatten_ordered_add
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.PosSemidef)
    {p r δ : ℝ} (hp : 0 < p) (hr : r ∈ Ioo (0 : ℝ) 1) (hδ : 0 < δ) :
    Integrable (fun t : ℝ => Real.hirschmanDensity r t * Real.log
      (schattenNormReal (orderedMatrixComplexPower L (1 + (t : ℂ) * I)) p + δ)) := by
  apply Real.integrable_hirschmanDensity_mul_of_bounded hr
    (continuous_log_schatten_ordered_add L hL hp hδ).measurable
  intro t
  exact abs_log_add_le (schattenNormReal_nonneg _ _)
    (schattenNormReal_orderedMatrixComplexPower_right_le L hL hp t) hδ

/-- Positive definite ALT in exponential form, before the logarithm is
removed. The right boundary uses exactly the displayed order of complex
powers and the source density. -/
theorem schattenNormReal_orderedMatrixComplexPower_rpow_le_exp_hirschman_of_posDef
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.PosDef)
    {p r : ℝ} (hp : 1 ≤ p) (hr : r ∈ Ioo (0 : ℝ) 1) :
    schattenNormReal (orderedMatrixComplexPower L (r : ℂ)) (p / r) ^ (1 / r) ≤
      Real.exp (∫ t : ℝ, Real.hirschmanDensity r t * Real.log
        (schattenNormReal (orderedMatrixComplexPower L (1 + (t : ℂ) * I)) p)) := by
  have h := schattenNormReal_orderedMatrixExp_le_exp_hirschman
    (L.map matrixLog) (isHermitian_mem_map_matrixLog L) hp hr
  simp_rw [← orderedMatrixComplexPower_eq_orderedMatrixExp_log L hL] at h
  have hpow := Real.rpow_le_rpow (schattenNormReal_nonneg _ _) h (one_div_nonneg.mpr hr.1.le)
  rw [← Real.exp_mul] at hpow
  have heq (x : ℝ) : (r * x) * (1 / r) = x := by field_simp [hr.1.ne']
  rw [heq] at hpow
  exact hpow

/-- Positive definite ALT admits every positive logarithmic regularization.
This is the stable inequality passed to the singular PSD boundary. -/
theorem schattenNormReal_orderedMatrixComplexPower_rpow_le_exp_log_add_of_posDef
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.PosDef)
    {p r δ : ℝ} (hp : 1 ≤ p) (hr : r ∈ Ioo (0 : ℝ) 1) (hδ : 0 < δ) :
    schattenNormReal (orderedMatrixComplexPower L (r : ℂ)) (p / r) ^ (1 / r) ≤
      Real.exp (∫ t : ℝ, Real.hirschmanDensity r t * Real.log
        (schattenNormReal (orderedMatrixComplexPower L (1 + (t : ℂ) * I)) p + δ)) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  by_cases hn : Nonempty n
  · let := hn
    apply (schattenNormReal_orderedMatrixComplexPower_rpow_le_exp_hirschman_of_posDef
      L hL hp hr).trans
    apply Real.exp_le_exp.mpr
    have hH := isHermitian_mem_map_matrixLog L
    have hint := Real.integrable_hirschmanDensity_mul_of_bounded hr
      (continuous_log_schattenNormReal_orderedMatrixExp_right _ hH hp0).measurable
      (abs_log_schattenNormReal_orderedMatrixExp_right_le _ hH hp0)
    simp_rw [← orderedMatrixComplexPower_eq_orderedMatrixExp_log L hL] at hint
    apply integral_mono hint
      (integrable_hirschman_log_schatten_ordered_add L (fun A hA => (hL A hA).posSemidef)
        hp0 hr hδ)
    intro t
    apply mul_le_mul_of_nonneg_left _ (Real.hirschmanDensity_pos hr t).le
    have hpos : 0 < schattenNormReal (orderedMatrixComplexPower L (1 + (t : ℂ) * I)) p := by
      rw [orderedMatrixComplexPower_eq_orderedMatrixExp_log L hL]
      exact (Real.exp_pos _).trans_le
        (exp_neg_sum_norm_le_schattenNormReal_orderedMatrixExp_right _ hH hp0 t)
    exact Real.log_le_log hpos (by linarith)
  · let : IsEmpty n := not_nonempty_iff.mp hn
    have hz : orderedMatrixComplexPower L (r : ℂ) = 0 := Subsingleton.elim _ _
    rw [hz, schattenNormReal_zero (div_pos hp0 hr.1), Real.zero_rpow (one_div_ne_zero hr.1.ne')]
    exact (Real.exp_pos _).le

/-- For a fixed positive logarithmic regularization, dominated convergence
passes from positive definite scalar shifts to the original PSD factors.
The dominating function is the actual Hirschman density times a constant. -/
theorem tendsto_integral_hirschman_log_orderedMatrixComplexPower_regularize
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.PosSemidef)
    {p r δ : ℝ} (hp : 0 < p) (hr : r ∈ Ioo (0 : ℝ) 1) (hδ : 0 < δ)
    {ε : ℕ → ℝ} (hε : ∀ k, ε k ∈ Icc (0 : ℝ) 1)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k => ∫ t : ℝ, Real.hirschmanDensity r t * Real.log
      (schattenNormReal (orderedMatrixComplexPower (regularizeMatrixList L (ε k))
        (1 + (t : ℂ) * I)) p + δ)) atTop
      (𝓝 (∫ t : ℝ, Real.hirschmanDensity r t * Real.log
        (schattenNormReal (orderedMatrixComplexPower L (1 + (t : ℂ) * I)) p + δ))) := by
  let C : ℝ := (Fintype.card n : ℝ) ^ (1 / p) * (L.map (fun A => ‖A‖ + 1)).prod
  let D : ℝ := |Real.log δ| + |Real.log (C + δ)|
  apply tendsto_integral_of_dominated_convergence (fun t => D * Real.hirschmanDensity r t)
  · intro k
    have hm := (continuous_log_schatten_ordered_add (regularizeMatrixList L (ε k))
      (posSemidef_mem_regularizeMatrixList L hL (hε k).1) hp hδ).measurable
    exact ((Real.continuous_hirschmanDensity hr).measurable.mul hm).aestronglyMeasurable
  · exact (Real.integrable_hirschmanDensity hr).const_mul D
  · intro k
    exact ae_of_all _ fun t => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.hirschmanDensity_pos hr t),
        Real.norm_eq_abs]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (abs_log_add_le (schattenNormReal_nonneg _ _)
          (schattenNormReal_orderedMatrixComplexPower_regularize_right_le L hL hp (hε k) t)
          hδ) (Real.hirschmanDensity_pos hr t).le
  · exact ae_of_all _ fun t => by
      have hm := (continuousAt_orderedMatrixComplexPower_regularize L
        (fun A hA => (hL A hA).isHermitian) (z := 1 + (t : ℂ) * I)
        (by simp)).tendsto.comp hεlim
      simp only [Function.comp_def, regularizeMatrixList_zero] at hm
      have hn := ((continuous_schattenNormReal hp).tendsto _).comp hm
      have hl := (Real.continuousAt_log
        (ne_of_gt (add_pos_of_nonneg_of_pos (schattenNormReal_nonneg _ _) hδ))).tendsto.comp
          (hn.add_const δ)
      exact hl.const_mul _

/-- Multivariate ALT for arbitrary PSD inputs, with every positive
logarithmic regularization on the right. The left side is exactly the
source's modulus raised to `1/r`, with its Schatten `p` norm.
This all-positive-regularizations form includes zero products and is passed
to the genuine extended logarithm without assuming logarithmic integrability.
atlas: multivariate-araki-lieb-thirring (partial) -/
theorem schattenNormReal_abs_rpow_orderedMatrixComplexPower_le_exp_log_add
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.PosSemidef)
    {p r δ : ℝ} (hp : 1 ≤ p) (hr : r ∈ Ioo (0 : ℝ) 1) (hδ : 0 < δ) :
    schattenNormReal (CFC.rpow (CFC.abs (orderedMatrixComplexPower L (r : ℂ))) (1 / r)) p ≤
      Real.exp (∫ t : ℝ, Real.hirschmanDensity r t * Real.log
        (schattenNormReal (orderedMatrixComplexPower L (1 + (t : ℂ) * I)) p + δ)) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hεpos (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have hε (k : ℕ) : ε k ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact (hεpos k).le
    · dsimp [ε]
      exact (div_le_one (show (0 : ℝ) < (k : ℝ) + 1 by positivity)).mpr
        (by linarith [show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k])
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hc := continuousAt_orderedMatrixComplexPower_regularize L
    (fun A hA => (hL A hA).isHermitian) (z := (r : ℂ)) (by simpa using hr.1)
  have hf := ((continuous_schattenNormReal (div_pos hp0 hr.1)).continuousAt.comp hc).rpow_const
    (Or.inr (one_div_nonneg.mpr hr.1.le))
  have hfl := hf.tendsto.comp hεlim
  simp only [Function.comp_def, regularizeMatrixList_zero] at hfl
  have hgl := Real.continuous_exp.tendsto _ |>.comp
    (tendsto_integral_hirschman_log_orderedMatrixComplexPower_regularize L hL hp0 hr hδ hε hεlim)
  rw [schattenNormReal_rpow_abs _ hp0 hr.1]
  apply le_of_tendsto_of_tendsto hfl hgl
  exact Eventually.of_forall fun k =>
    schattenNormReal_orderedMatrixComplexPower_rpow_le_exp_log_add_of_posDef
      (regularizeMatrixList L (ε k)) (posDef_mem_regularizeMatrixList L hL (hεpos k)) hp hr hδ

/-- The PSD ALT regularization bound written directly against the actual
probability measure with the source's explicit Hirschman density. -/
theorem schattenNormReal_abs_rpow_orderedMatrixComplexPower_le_exp_log_add_measure
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.PosSemidef)
    {p r δ : ℝ} (hp : 1 ≤ p) (hr : r ∈ Ioo (0 : ℝ) 1) (hδ : 0 < δ) :
    schattenNormReal (CFC.rpow (CFC.abs (orderedMatrixComplexPower L (r : ℂ))) (1 / r)) p ≤
      Real.exp (∫ t : ℝ, Real.log
        (schattenNormReal (orderedMatrixComplexPower L (1 + (t : ℂ) * I)) p + δ)
          ∂Real.hirschmanMeasure r) := by
  rw [Real.integral_hirschmanMeasure hr]
  simpa only [smul_eq_mul] using
    schattenNormReal_abs_rpow_orderedMatrixComplexPower_le_exp_log_add L hL hp hr hδ

/-- The PSD ALT modulus-power norm is bounded by the genuine geometric mean
of its actual ordered complex-power boundary norms. The geometric mean is
defined from the positive and negative extended-logarithmic integrals; an
infinite negative logarithmic part gives geometric mean zero.
atlas: multivariate-araki-lieb-thirring (partial) -/
theorem schattenNormReal_abs_rpow_orderedMatrixComplexPower_le_geometricMean
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.PosSemidef)
    {p r : ℝ} (hp : 1 ≤ p) (hr : r ∈ Ioo (0 : ℝ) 1) :
    ENNReal.ofReal
      (schattenNormReal (CFC.rpow (CFC.abs (orderedMatrixComplexPower L (r : ℂ))) (1 / r)) p) ≤
        geometricMean (Real.hirschmanMeasure r)
          (fun t : ℝ => schattenNormReal (orderedMatrixComplexPower L (1 + (t : ℂ) * I)) p) := by
  let : IsProbabilityMeasure (Real.hirschmanMeasure r) :=
    Real.isProbabilityMeasure_hirschmanMeasure hr
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let g : ℝ → ℝ := fun t =>
    schattenNormReal (orderedMatrixComplexPower L (1 + (t : ℂ) * I)) p
  let C : ℝ := (Fintype.card n : ℝ) ^ (1 / p) * (L.map (fun A => ‖A‖ + 1)).prod
  have hg : Measurable g := ((continuous_schattenNormReal hp0).comp
    (continuous_orderedMatrixComplexPower_right L hL)).measurable
  have hb (t : ℝ) : 0 ≤ g t ∧ g t ≤ C :=
    ⟨schattenNormReal_nonneg _ _, schattenNormReal_orderedMatrixComplexPower_right_le L hL hp0 t⟩
  have hC : 0 ≤ C := (hb 0).1.trans (hb 0).2
  change _ ≤ geometricMean (Real.hirschmanMeasure r) g
  apply le_geometricMean_of_le_exp_integral_log_add hg hC hb
  intro δ hδ
  exact ENNReal.ofReal_le_ofReal
    (schattenNormReal_abs_rpow_orderedMatrixComplexPower_le_exp_log_add_measure L hL hp hr hδ)

/-- The exact extended-log form of PSD multivariate ALT, using the native
extended logarithm and the source's explicit probability measure. -/
theorem log_schattenNormReal_abs_rpow_orderedMatrixComplexPower_le_extendedLogIntegral
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.PosSemidef)
    {p r : ℝ} (hp : 1 ≤ p) (hr : r ∈ Ioo (0 : ℝ) 1) :
    ENNReal.log (ENNReal.ofReal
      (schattenNormReal (CFC.rpow (CFC.abs (orderedMatrixComplexPower L (r : ℂ))) (1 / r)) p)) ≤
        extendedLogIntegral (Real.hirschmanMeasure r)
          (fun t : ℝ => schattenNormReal (orderedMatrixComplexPower L (1 + (t : ℂ) * I)) p) := by
  have h := ENNReal.log_le_log
    (schattenNormReal_abs_rpow_orderedMatrixComplexPower_le_geometricMean L hL hp hr)
  simpa only [geometricMean, EReal.log_exp] using h

/-- Multivariate Araki--Lieb--Thirring for the actual ordered product of PSD
real CFC powers, with the native extended convention `log 0 = -∞`.
The right side is the genuine positive-minus-negative logarithmic integral
against the explicit density `βr`; no integrability premise is imposed at zeros.
Source: Sutter--Berta--Tomamichel, Theorem 3.2, equations (30), (33).
atlas: multivariate-araki-lieb-thirring -/
theorem log_schattenNormReal_abs_rpow_prod_rpow_le_extendedLogIntegral
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.PosSemidef)
    {p r : ℝ} (hp : 1 ≤ p) (hr : r ∈ Ioo (0 : ℝ) 1) :
    ENNReal.log (ENNReal.ofReal
      (schattenNormReal (CFC.rpow (CFC.abs ((L.map (fun A => CFC.rpow A r)).prod)) (1 / r)) p)) ≤
        extendedLogIntegral (Real.hirschmanMeasure r)
          (fun t : ℝ => schattenNormReal (orderedMatrixComplexPower L (1 + (t : ℂ) * I)) p) := by
  simpa only [orderedMatrixComplexPower_ofReal_eq_prod_rpow L hL] using
    log_schattenNormReal_abs_rpow_orderedMatrixComplexPower_le_extendedLogIntegral L hL hp hr

end NLAlib
