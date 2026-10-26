import NLAlib.RandomMatrix.Gaussian.Basic.SymmetricProfile
import NLAlib.Probability.Gaussian.Concentration.LowerTail
import NLAlib.Matrix.Norms.RowMixedNorm
import NLAlib.Matrix.Structured.ProfileRearrangementEnvelope
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Lower expected Gaussian row energies

Weighted Cauchy--Schwarz compares a Gaussian row length with the sum of
its absolute entries weighted by the deterministic coefficient row. All
entries have the same positive scalar absolute mean, so the expected row
length uniformly dominates its deterministic Euclidean profile.

Source: Latała--van Handel--Youssef, arXiv:1711.00807v2, Section 3.1.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal

namespace NLAlib

/-- A fixed positive lower bound for the mean absolute scalar Gaussian,
obtained by integrating its actual tail at threshold one. -/
def gaussianAbsoluteLowerConstant : ℝ :=
  Real.exp (-1) / Real.sqrt (2 * Real.pi) * Real.exp (-1)

/-- The scalar Gaussian absolute-mean lower constant is strictly positive. -/
theorem gaussianAbsoluteLowerConstant_pos : 0 < gaussianAbsoluteLowerConstant := by
  dsimp [gaussianAbsoluteLowerConstant]
  positivity

/-- The actual scalar Gaussian mean absolute value exceeds the fixed
positive lower constant. -/
theorem gaussianAbsoluteLowerConstant_le_integral_abs_gaussianReal :
    gaussianAbsoluteLowerConstant ≤ ∫ z : ℝ, |z| ∂gaussianReal 0 1 := by
  have htail := exp_neg_sq_div_sqrt_two_pi_le_gaussianReal_abs_tail 1 (by norm_num)
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun z : ℝ => abs_nonneg z)
      ((memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp)).norm.integrable (by norm_num)) 1
  norm_num only [one_pow, one_mul, id_eq, Real.norm_eq_abs] at htail hm
  exact htail.trans hm

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

omit [LinearOrder ι] in
private theorem rowMixedNorm_eq_norm_row_lengths (A : Matrix ι ι ℝ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    rowMixedNorm A p = ‖(WithLp.toLp p (fun i => Real.sqrt (rowSq A i)) : PiLp p (fun _ : ι => ℝ))‖ := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  by_cases hpt : p = ⊤
  · subst p
    rw [rowMixedNorm_top, PiLp.norm_eq_ciSup]
    congr 1
    funext i
    exact (Real.norm_of_nonneg (Real.sqrt_nonneg _)).symm
  · have hpr : 0 < p.toReal := ENNReal.toReal_pos
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hpt
    rw [rowMixedNorm_eq_sum A hpr, PiLp.norm_eq_sum hpr]
    simp only [Real.norm_of_nonneg (Real.sqrt_nonneg _)]

omit [LinearOrder ι] in
private theorem norm_toLp_mono_of_nonneg {p : ℝ≥0∞} (hp : 1 ≤ p)
    (x y : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) :
    ‖(WithLp.toLp p x : PiLp p (fun _ : ι => ℝ))‖ ≤
      ‖(WithLp.toLp p y : PiLp p (fun _ : ι => ℝ))‖ := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  by_cases hpt : p = ⊤
  · subst p
    rw [PiLp.norm_toLp, PiLp.norm_toLp]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg y)).mpr
    intro i
    rw [Real.norm_of_nonneg (hx i)]
    exact (hxy i).trans ((le_abs_self _).trans (norm_le_pi_norm y i))
  · have hpr : 0 < p.toReal := ENNReal.toReal_pos
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hpt
    rw [PiLp.norm_eq_sum hpr, PiLp.norm_eq_sum hpr]
    apply Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
    · apply Finset.sum_le_sum
      intro i _
      rw [Real.norm_of_nonneg (hx i), Real.norm_of_nonneg ((hx i).trans (hxy i))]
      exact Real.rpow_le_rpow (hx i) (hxy i) hpr.le
    · positivity

omit [LinearOrder ι] in
/-- At infinity, the mixed row norm is the ordinary finite Pi norm of
the Euclidean row lengths, also in empty dimension. -/
theorem rowMixedNorm_top_eq_pi_norm (A : Matrix ι ι ℝ) :
    rowMixedNorm A ⊤ = ‖fun i => Real.sqrt (rowSq A i)‖ := by
  simpa only [PiLp.norm_toLp] using rowMixedNorm_eq_norm_row_lengths A (p := ⊤) (by simp)

/-- Every actual Gaussian Euclidean row length is square integrable. -/
theorem memLp_sqrt_rowSq_symmetricGaussianMatrix (b : Matrix ι ι ℝ) (i : ι) :
    MemLp (fun G => Real.sqrt (rowSq (symmetricGaussianMatrix b G) i))
      2 (gaussianMatrix ι ι) := by
  have hV : MemLp (fun G : Matrix ι ι ℝ =>
      (WithLp.toLp 2 (fun j => symmetricGaussianMatrix b G i j) : EuclideanSpace ℝ ι))
      2 (gaussianMatrix ι ι) := by
    rw [memLp_piLp_iff]
    intro j
    exact memLp_symmetricGaussianMatrix_entry b i j 2 (by simp)
  have heq (G : Matrix ι ι ℝ) :
      ‖(WithLp.toLp 2 (fun j => symmetricGaussianMatrix b G i j) : EuclideanSpace ℝ ι)‖ =
        Real.sqrt (rowSq (symmetricGaussianMatrix b G) i) := by
    rw [← Real.sqrt_sq (norm_nonneg _), EuclideanSpace.norm_sq_eq]
    rfl
  simpa only [heq] using hV.norm

/-- Every realized finite Gaussian maximum row length is integrable. -/
theorem integrable_pi_norm_sqrt_rowSq_symmetricGaussianMatrix (b : Matrix ι ι ℝ) :
    Integrable (fun G => ‖fun i => Real.sqrt (rowSq (symmetricGaussianMatrix b G) i)‖)
      (gaussianMatrix ι ι) :=
  (integrable_pi_iff.mpr (fun i =>
    (memLp_sqrt_rowSq_symmetricGaussianMatrix b i).integrable (by norm_num))).norm

/-- An actual Gaussian entry has absolute mean equal to its coefficient
modulus times the standard scalar Gaussian absolute mean. -/
theorem integral_abs_symmetricGaussianMatrix_entry (b : Matrix ι ι ℝ) (hb : b.IsSymm) (i j : ι) :
    (∫ G, |symmetricGaussianMatrix b G i j| ∂gaussianMatrix ι ι) =
      |b i j| * ∫ z : ℝ, |z| ∂gaussianReal 0 1 := by
  simp_rw [symmetricGaussianMatrix_apply_of_isSymm b hb, abs_mul]
  rw [integral_const_mul, integral_comp_gaussianMatrix_entry_eq _ _ _ measurable_abs]

/-- The expected Euclidean length of each actual Gaussian row uniformly
dominates the Euclidean length of the deterministic coefficient row. -/
theorem gaussianAbsoluteLowerConstant_mul_sqrt_rowSq_le_integral
    (b : Matrix ι ι ℝ) (hb : b.IsSymm) (i : ι) :
    gaussianAbsoluteLowerConstant * Real.sqrt (∑ j, b i j ^ 2) ≤
      ∫ G, Real.sqrt (rowSq (symmetricGaussianMatrix b G) i) ∂gaussianMatrix ι ι := by
  let r := Real.sqrt (∑ j, b i j ^ 2)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = ∑ j, b i j ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hrow := (memLp_sqrt_rowSq_symmetricGaussianMatrix b i).integrable (by norm_num)
  have hentry (j : ι) : Integrable (fun G => |b i j| * |symmetricGaussianMatrix b G i j|)
      (gaussianMatrix ι ι) :=
    ((memLp_symmetricGaussianMatrix_entry b i j 2 (by simp)).integrable (by norm_num)).abs.const_mul _
  have hpoint (G : Matrix ι ι ℝ) :
      (∑ j, |b i j| * |symmetricGaussianMatrix b G i j|) ≤
        r * Real.sqrt (rowSq (symmetricGaussianMatrix b G) i) := by
    simpa only [r, rowSq, Real.norm_eq_abs, sq_abs] using
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun j => |b i j|)
        (fun j => |symmetricGaussianMatrix b G i j|)
  have hm := integral_mono (integrable_finsetSum _ (fun j _ => hentry j)) (hrow.const_mul r) hpoint
  rw [integral_finsetSum _ (fun j _ => hentry j), integral_const_mul] at hm
  have hleft : (∑ j, ∫ G, |b i j| * |symmetricGaussianMatrix b G i j| ∂gaussianMatrix ι ι) =
      r ^ 2 * (∫ z : ℝ, |z| ∂gaussianReal 0 1) := by
    simp only [integral_const_mul, integral_abs_symmetricGaussianMatrix_entry b hb,
      hrsq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_assoc, ← sq, sq_abs]
  rw [hleft] at hm
  have hnonneg : 0 ≤ ∫ G, Real.sqrt (rowSq (symmetricGaussianMatrix b G) i) ∂gaussianMatrix ι ι :=
    integral_nonneg fun G : Matrix ι ι ℝ => Real.sqrt_nonneg (rowSq (symmetricGaussianMatrix b G) i)
  have hlow := gaussianAbsoluteLowerConstant_le_integral_abs_gaussianReal
  change gaussianAbsoluteLowerConstant * r ≤ _
  rcases hr0.eq_or_lt with hz | hr
  · rw [← hz, mul_zero]
    exact hnonneg
  · have hmul : r * (gaussianAbsoluteLowerConstant * r) ≤
        r * (∫ G, Real.sqrt (rowSq (symmetricGaussianMatrix b G) i) ∂gaussianMatrix ι ι) := by
      nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hlow)]
    exact (mul_le_mul_iff_right₀ hr).mp hmul

/-- The deterministic mixed row profile is dominated by the expected
actual Gaussian mixed row norm, uniformly at every native exponent at
least one, including infinity. This is the row-energy contribution to
the full Gaussian row comparison. -/
theorem gaussianAbsoluteLowerConstant_mul_rowMixedNorm_le_integral
    (b : Matrix ι ι ℝ) (hb : b.IsSymm) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    gaussianAbsoluteLowerConstant * rowMixedNorm b p ≤
      ∫ G, rowMixedNorm (symmetricGaussianMatrix b G) p ∂gaussianMatrix ι ι := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  let F : Matrix ι ι ℝ → PiLp p (fun _ : ι => ℝ) := fun G =>
    WithLp.toLp p (fun i => Real.sqrt (rowSq (symmetricGaussianMatrix b G) i))
  let m : ι → ℝ := fun i => ∫ G, Real.sqrt (rowSq (symmetricGaussianMatrix b G) i) ∂gaussianMatrix ι ι
  have hi (i : ι) : Integrable (fun G => Real.sqrt (rowSq (symmetricGaussianMatrix b G) i))
      (gaussianMatrix ι ι) := (memLp_sqrt_rowSq_symmetricGaussianMatrix b i).integrable (by norm_num)
  have hF : Integrable F (gaussianMatrix ι ι) := integrable_piLp_iff.mpr hi
  have heq : (∫ G, F G ∂gaussianMatrix ι ι) = WithLp.toLp p m := by
    apply PiLp.ext
    intro i
    exact eval_integral_piLp hi i
  have hn := norm_integral_le_integral_norm (μ := gaussianMatrix ι ι) F
  rw [heq] at hn
  have hlen (i : ι) : rowSq b i = ∑ j, b i j ^ 2 := by
    simp only [rowSq, Real.norm_eq_abs, sq_abs]
  have hmono := norm_toLp_mono_of_nonneg hp
    (fun i => gaussianAbsoluteLowerConstant * Real.sqrt (rowSq b i)) m
      (fun i => mul_nonneg gaussianAbsoluteLowerConstant_pos.le (Real.sqrt_nonneg _))
        (fun i => by simpa only [hlen i] using
          gaussianAbsoluteLowerConstant_mul_sqrt_rowSq_le_integral b hb i)
  have hscale : ‖(WithLp.toLp p (fun i => gaussianAbsoluteLowerConstant * Real.sqrt (rowSq b i)) :
      PiLp p (fun _ : ι => ℝ))‖ = gaussianAbsoluteLowerConstant * rowMixedNorm b p := by
    rw [rowMixedNorm_eq_norm_row_lengths b hp]
    change ‖gaussianAbsoluteLowerConstant • (WithLp.toLp p (fun i => Real.sqrt (rowSq b i)) :
      PiLp p (fun _ : ι => ℝ))‖ = _
    rw [norm_smul, Real.norm_of_nonneg gaussianAbsoluteLowerConstant_pos.le]
  rw [hscale] at hmono
  have hnorm (G : Matrix ι ι ℝ) : ‖F G‖ = rowMixedNorm (symmetricGaussianMatrix b G) p :=
    (rowMixedNorm_eq_norm_row_lengths _ hp).symm
  simp_rw [hnorm] at hn
  exact hmono.trans hn

end NLAlib
