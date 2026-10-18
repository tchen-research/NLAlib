import NLAlib.Matrix.Functions.OrderedExponentialInterpolation
import NLAlib.Matrix.Functions.OrderedExponentialModulus
import NLAlib.Matrix.Norms.SchattenPowers

/-! # Multivariate Golden--Thompson with the exact ordered integral

The finite-parameter interpolation bound is transported through the actual
CFC modulus power and the proved Banach-algebra product limit. Bounded
continuous right-boundary logarithms permit dominated convergence of the
explicit Hirschman densities. Products retain their original list order.
Source: Sutter--Berta--Tomamichel, arXiv:1604.03023v3, Corollary 3.3.
-/

noncomputable section
open Matrix Complex Set Filter MeasureTheory
open scoped Topology Matrix.Norms.L2Operator MatrixOrder
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The displayed Golden--Thompson integrand is actually Lebesgue integrable;
both logarithmic tails are controlled by the ordered product and its inverse.
atlas: multivariate-golden-thompson (partial) -/
theorem integrable_hirschmanDensityZero_mul_log_orderedMatrixExp
    (H : List (Matrix n n ℂ)) (hH : ∀ A ∈ H, A.IsHermitian)
    {p : ℝ} (hp : 0 < p) :
    Integrable (fun t : ℝ => Real.hirschmanDensityZero t *
      Real.log (schattenNormReal (orderedMatrixExp H (1 + (t : ℂ) * I)) p)) := by
  by_cases hn : Nonempty n
  · let := hn
    apply Real.integrable_hirschmanDensityZero.mul_bdd
      (continuous_log_schattenNormReal_orderedMatrixExp_right H hH hp).aestronglyMeasurable
    exact ae_of_all _ (fun t => by simpa only [Real.norm_eq_abs] using
      abs_log_schattenNormReal_orderedMatrixExp_right_le H hH hp t)
  · let : IsEmpty n := not_nonempty_iff.mp hn
    have hz (A : Matrix n n ℂ) : A = 0 := Subsingleton.elim _ _
    simp only [hz _, schattenNormReal_zero hp, Real.log_zero, mul_zero]
    exact integrable_zero _ _ _

/-- The exact finite-parameter bound for the actual modulus power of an
ordered exponential product. The empty matrix shape is included.
atlas: multivariate-golden-thompson (partial) -/
theorem schattenNormReal_rpow_abs_orderedMatrixExp_le_exp_hirschman
    (H : List (Matrix n n ℂ)) (hH : ∀ A ∈ H, A.IsHermitian)
    {p r : ℝ} (hp : 1 ≤ p) (hr : r ∈ Ioo (0 : ℝ) 1) :
    schattenNormReal (CFC.rpow (CFC.abs (orderedMatrixExp H (r : ℂ))) (1 / r)) p ≤
      Real.exp (∫ t : ℝ, Real.hirschmanDensity r t *
        Real.log (schattenNormReal (orderedMatrixExp H (1 + (t : ℂ) * I)) p)) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  rw [schattenNormReal_rpow_abs _ hp0 hr.1]
  apply (Real.rpow_le_rpow (schattenNormReal_nonneg _ _)
    (schattenNormReal_orderedMatrixExp_le_exp_hirschman H hH hp hr)
    (one_div_nonneg.mpr hr.1.le)).trans_eq
  rw [← Real.exp_mul]
  congr 1
  rw [mul_comm r _, mul_assoc, one_div, mul_inv_cancel₀ hr.1.ne', mul_one]

/-- The zero-safe norm form of multivariate Golden--Thompson, for every
finite matrix shape and every finite Schatten exponent at least one.
atlas: multivariate-golden-thompson (partial) -/
theorem schattenNormReal_matrixExp_sum_le_exp_integral_log_orderedMatrixExp
    (H : List (Matrix n n ℂ)) (hH : ∀ A ∈ H, A.IsHermitian)
    {p : ℝ} (hp : 1 ≤ p) :
    schattenNormReal (matrixExp H.sum) p ≤
      Real.exp (∫ t : ℝ, Real.hirschmanDensityZero t *
        Real.log (schattenNormReal (orderedMatrixExp H (1 + (t : ℂ) * I)) p)) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  by_cases hn : Nonempty n
  · let := hn
    let f : ℝ → ℝ := fun t =>
      Real.log (schattenNormReal (orderedMatrixExp H (1 + (t : ℂ) * I)) p)
    have hf : Continuous f := continuous_log_schattenNormReal_orderedMatrixExp_right H hH hp0
    have hb : ∀ᵐ t, ‖f t‖ ≤
        (H.map (fun A => ‖A‖)).sum + |Real.log ((Fintype.card n : ℝ) ^ (1 / p))| :=
      ae_of_all _ (fun t => by simpa only [Real.norm_eq_abs] using
        abs_log_schattenNormReal_orderedMatrixExp_right_le H hH hp0 t)
    have hparam : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (𝓝[>] 0) :=
      tendsto_inv_atTop_nhdsGT_zero.comp tendsto_natCast_atTop_atTop
    have hi := (Real.tendsto_integral_hirschmanDensity_smul_zero hf.aestronglyMeasurable hb).comp hparam
    simp only [smul_eq_mul, Function.comp_def] at hi
    have hright := Real.continuous_exp.continuousAt.tendsto.comp hi
    have hleft := (continuous_schattenNormReal hp0).continuousAt.tendsto.comp
      (tendsto_abs_orderedMatrixExp_pow H hH)
    apply le_of_tendsto_of_tendsto hleft hright
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with k hk
    have hk1 : (1 : ℝ) < k := by exact_mod_cast hk
    have hr : (k : ℝ)⁻¹ ∈ Ioo (0 : ℝ) 1 :=
      ⟨inv_pos.mpr (by linarith), inv_lt_one_of_one_lt₀ hk1⟩
    have h := schattenNormReal_rpow_abs_orderedMatrixExp_le_exp_hirschman H hH hp hr
    have hco : (((k : ℝ)⁻¹ : ℝ) : ℂ) = (k : ℂ)⁻¹ := by
      simp only [Complex.ofReal_inv, Complex.ofReal_natCast]
    rw [hco] at h
    simp only [one_div, inv_inv] at h
    rw [CFC.rpow_eq_pow,
      CFC.rpow_natCast (CFC.abs (orderedMatrixExp H (k : ℂ)⁻¹)) k (CFC.abs_nonneg _)] at h
    exact h
  · let : IsEmpty n := not_nonempty_iff.mp hn
    have hz : matrixExp H.sum = 0 := Subsingleton.elim _ _
    rw [hz, schattenNormReal_zero hp0]
    exact (Real.exp_pos _).le

/-- Multivariate Golden--Thompson with the exact probability density and
the actual ordered native matrix-exponential product. For empty matrix
shapes, both logarithmic sides use the native real zero convention; the
preceding norm form separately supplies the zero-safe inequality.
Source: Sutter--Berta--Tomamichel, Corollary 3.3, equations (32), (38).
atlas: multivariate-golden-thompson -/
theorem log_schattenNormReal_matrixExp_sum_le_integral_log_orderedMatrixExp
    (H : List (Matrix n n ℂ)) (hH : ∀ A ∈ H, A.IsHermitian)
    {p : ℝ} (hp : 1 ≤ p) :
    Real.log (schattenNormReal (matrixExp H.sum) p) ≤
      ∫ t : ℝ, Real.hirschmanDensityZero t *
        Real.log (schattenNormReal (orderedMatrixExp H (1 + (t : ℂ) * I)) p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  by_cases hn : Nonempty n
  · let := hn
    have hun : IsUnit (matrixExp H.sum) := by
      let : NormedAlgebra ℚ (Matrix n n ℂ) := .restrictScalars ℚ ℂ _
      exact NormedSpace.isUnit_exp H.sum
    have hnorm : 0 < schattenNormReal (matrixExp H.sum) p :=
      schattenNormReal_pos _ hp0 hun.ne_zero
    exact (Real.log_le_iff_le_exp hnorm).mpr
      (schattenNormReal_matrixExp_sum_le_exp_integral_log_orderedMatrixExp H hH hp)
  · let : IsEmpty n := not_nonempty_iff.mp hn
    have hz (A : Matrix n n ℂ) : A = 0 := Subsingleton.elim _ _
    simp only [hz _, schattenNormReal_zero hp0, Real.log_zero, mul_zero, integral_zero, le_rfl]

end NLAlib
