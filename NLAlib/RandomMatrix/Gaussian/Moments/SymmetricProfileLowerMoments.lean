import NLAlib.RandomMatrix.Gaussian.Basic.SymmetricProfile
import NLAlib.Matrix.Norms.RowSchattenBounds
import NLAlib.Matrix.Norms.SchattenContinuity
import NLAlib.ForMathlib.MeasureTheory.MomentInterpolation
import NLAlib.Probability.Gaussian.Moments.LowerMoments
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Lower Schatten moments of symmetric Gaussian variance profiles

The deterministic row-energy lower bound, scalar moment monotonicity, and
the exact entry variances give the variance-profile contribution for every
real exponent at least two. A selected entry in each row gives the second
contribution without requiring the selected entries to be independent.

All random matrices use the actual `symmetricGaussianMatrix` construction
under `gaussianMatrix n n`, and their finite Schatten moments are proved
integrable. Source: Latała--van Handel--Youssef, arXiv:1711.00807v2,
Theorem 1.1, lower bound.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal

namespace NLAlib

variable {n : Type*} [Fintype n] [LinearOrder n]

omit [LinearOrder n] in
private theorem norm_toLp_entries_eq_frobNorm (A : Matrix n n ℝ) :
    ‖(WithLp.toLp 2 (fun ij : n × n => A ij.1 ij.2) : EuclideanSpace ℝ (n × n))‖ =
      frobNorm A := by
  have hs : ‖(WithLp.toLp 2 (fun ij : n × n => A ij.1 ij.2) :
      EuclideanSpace ℝ (n × n))‖ ^ 2 = frobNorm A ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, frobNorm_sq, frobSq_eq_sum_norm_sq]
    simp only [Fintype.sum_prod_type]
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun ij : n × n => A ij.1 ij.2) :
    EuclideanSpace ℝ (n × n)), frobNorm_nonneg A]

/-- Every finite Schatten norm of exponent at least two of the actual
symmetric Gaussian variance-profile ensemble belongs to its matching `L^p`.
This follows from coordinatewise Gaussian moments and the Frobenius bound. -/
theorem memLp_schattenNormReal_symmetricGaussianMatrix
    (b : Matrix n n ℝ) {p : ℝ} (hp : 2 ≤ p) :
    MemLp (fun G => schattenNormReal (symmetricGaussianMatrix b G) p)
      (ENNReal.ofReal p) (gaussianMatrix n n) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  let V : Matrix n n ℝ → EuclideanSpace ℝ (n × n) := fun G =>
    WithLp.toLp 2 (fun ij : n × n => symmetricGaussianMatrix b G ij.1 ij.2)
  have hV : MemLp V (ENNReal.ofReal p) (gaussianMatrix n n) := by
    rw [memLp_piLp_iff]
    intro ij
    exact memLp_symmetricGaussianMatrix_entry b ij.1 ij.2 _ ENNReal.ofReal_ne_top
  have hmeas : AEStronglyMeasurable
      (fun G => schattenNormReal (symmetricGaussianMatrix b G) p) (gaussianMatrix n n) :=
    ((continuous_schattenNormReal hp0).measurable.comp
      (measurable_symmetricGaussianMatrix b)).aestronglyMeasurable
  apply hV.of_le hmeas
  apply Filter.Eventually.of_forall
  intro G
  rw [Real.norm_of_nonneg (schattenNormReal_nonneg _ _)]
  calc
    schattenNormReal (symmetricGaussianMatrix b G) p ≤
        schattenNormReal (symmetricGaussianMatrix b G) 2 :=
      schattenNormReal_le_schattenNormReal_of_le _ (by norm_num) hp
    _ = frobNorm (symmetricGaussianMatrix b G) := schattenNormReal_two _
    _ = ‖V G‖ := (norm_toLp_entries_eq_frobNorm _).symm

/-- The finite Schatten `p`-th moment of the actual symmetric Gaussian
variance-profile ensemble is integrable for every real `p ≥ 2`. -/
theorem integrable_schattenNormReal_symmetricGaussianMatrix_rpow
    (b : Matrix n n ℝ) {p : ℝ} (hp : 2 ≤ p) :
    Integrable (fun G => schattenNormReal (symmetricGaussianMatrix b G) p ^ p)
      (gaussianMatrix n n) := by
  have h := (memLp_schattenNormReal_symmetricGaussianMatrix b hp).integrable_norm_rpow'
  simpa only [ENNReal.toReal_ofReal (show 0 ≤ p by linarith), Real.norm_eq_abs,
    abs_of_nonneg (schattenNormReal_nonneg _ _)] using h

/-- The actual finite-exponent Schatten `p`-th power of the symmetric
Gaussian variance-profile ensemble is integrable in the standard norm API. -/
theorem integrable_schattenNorm_symmetricGaussianMatrix_rpow
    (b : Matrix n n ℝ) {p : ℝ} (hp : 2 ≤ p) :
    Integrable (fun G => schattenNorm (symmetricGaussianMatrix b G) (ENNReal.ofReal p) ^ p)
      (gaussianMatrix n n) := by
  simpa only [schattenNorm_ofReal _ (show 0 ≤ p by linarith)] using
    integrable_schattenNormReal_symmetricGaussianMatrix_rpow b hp

private theorem measurable_rowSq_symmetricGaussianMatrix (b : Matrix n n ℝ) (i : n) :
    Measurable (fun G => rowSq (symmetricGaussianMatrix b G) i) := by
  unfold rowSq
  apply Finset.measurable_sum
  intro j hj
  exact ((Matrix.measurable_entry i j).comp (measurable_symmetricGaussianMatrix b)).norm.pow_const 2

private theorem integrable_rowSq_symmetricGaussianMatrix (b : Matrix n n ℝ) (i : n) :
    Integrable (fun G => rowSq (symmetricGaussianMatrix b G) i) (gaussianMatrix n n) := by
  unfold rowSq
  apply integrable_finsetSum
  intro j hj
  have h := (memLp_symmetricGaussianMatrix_entry b i j 2 (by simp)).integrable_norm_pow'
  exact h

omit [LinearOrder n] in
private theorem rowSq_nonneg (A : Matrix n n ℝ) (i : n) : 0 ≤ rowSq A i :=
  Finset.sum_nonneg fun j _ => sq_nonneg ‖A i j‖

private theorem rowSq_rpow_le_schattenNormReal_rpow
    (A : Matrix n n ℝ) {p : ℝ} (hp : 2 ≤ p) (i : n) :
    rowSq A i ^ (p / 2) ≤ schattenNormReal A p ^ p := by
  have hterm : rowSq A i ^ (p / 2) ≤ ∑ j, rowSq A j ^ (p / 2) :=
    Finset.single_le_sum (fun j _ => Real.rpow_nonneg (rowSq_nonneg A j) (p / 2))
      (Finset.mem_univ i)
  exact hterm.trans (sum_rowSq_rpow_le_schattenNormReal_rpow A hp)

private theorem integrable_rowSq_symmetricGaussianMatrix_rpow
    (b : Matrix n n ℝ) {p : ℝ} (hp : 2 ≤ p) (i : n) :
    Integrable (fun G => rowSq (symmetricGaussianMatrix b G) i ^ (p / 2))
      (gaussianMatrix n n) := by
  apply (integrable_schattenNormReal_symmetricGaussianMatrix_rpow b hp).mono'
    ((measurable_rowSq_symmetricGaussianMatrix b i).pow_const _).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro G
  rw [Real.norm_of_nonneg (Real.rpow_nonneg
    (rowSq_nonneg (symmetricGaussianMatrix b G) i) (p / 2))]
  exact rowSq_rpow_le_schattenNormReal_rpow _ hp i

/-- The expected energy of each actual symmetric Gaussian row equals the
sum of squares of its profile coefficients. No row-entry independence is
needed for this second-moment identity. -/
theorem integral_rowSq_symmetricGaussianMatrix
    (b : Matrix n n ℝ) (hb : b.IsSymm) (i : n) :
    (∫ G, rowSq (symmetricGaussianMatrix b G) i ∂gaussianMatrix n n) =
      ∑ j, b i j ^ 2 := by
  simp only [rowSq, Real.norm_eq_abs, sq_abs]
  rw [integral_finsetSum _ (fun j _ =>
    (memLp_symmetricGaussianMatrix_entry b i j 2 (by simp)).integrable_sq)]
  exact Finset.sum_congr rfl fun j _ => integral_symmetricGaussianMatrix_entry_sq b hb i j

/-- The power sum of the variance-profile row energies is bounded by the
actual expected Schatten `p`-th power, for every real `p ≥ 2`. -/
theorem sum_rowSq_profile_rpow_le_integral_schattenNormReal_symmetricGaussianMatrix_rpow
    (b : Matrix n n ℝ) (hb : b.IsSymm) {p : ℝ} (hp : 2 ≤ p) :
    (∑ i, (∑ j, b i j ^ 2) ^ (p / 2)) ≤
      ∫ G, schattenNormReal (symmetricGaussianMatrix b G) p ^ p ∂gaussianMatrix n n := by
  have hq : 1 ≤ p / 2 := by linarith
  have hq0 : 0 < p / 2 := lt_of_lt_of_le zero_lt_one hq
  have hJ (i : n) : (∑ j, b i j ^ 2) ^ (p / 2) ≤
      ∫ G, rowSq (symmetricGaussianMatrix b G) i ^ (p / 2) ∂gaussianMatrix n n := by
    have hnn (G : Matrix n n ℝ) : 0 ≤ rowSq (symmetricGaussianMatrix b G) i :=
      rowSq_nonneg _ i
    have hroot := integral_rpow_root_le_of_nonneg_of_le
      (measurable_rowSq_symmetricGaussianMatrix b i).aestronglyMeasurable hnn
      zero_lt_one hq (integrable_rowSq_symmetricGaussianMatrix_rpow b hp i)
    simp only [Real.rpow_one, inv_one, integral_rowSq_symmetricGaussianMatrix b hb] at hroot
    have hpow := Real.rpow_le_rpow (Finset.sum_nonneg fun j _ => sq_nonneg _) hroot hq0.le
    rw [Real.rpow_inv_rpow
      (integral_nonneg fun G => Real.rpow_nonneg (hnn G) _) hq0.ne'] at hpow
    exact hpow
  calc
    _ ≤ ∑ i, ∫ G, rowSq (symmetricGaussianMatrix b G) i ^ (p / 2)
        ∂gaussianMatrix n n := Finset.sum_le_sum fun i _ => hJ i
    _ = ∫ G, ∑ i, rowSq (symmetricGaussianMatrix b G) i ^ (p / 2)
        ∂gaussianMatrix n n :=
      (integral_finsetSum _ (fun i _ => integrable_rowSq_symmetricGaussianMatrix_rpow b hp i)).symm
    _ ≤ _ := integral_mono
      (integrable_finsetSum _ (fun i _ => integrable_rowSq_symmetricGaussianMatrix_rpow b hp i))
      (integrable_schattenNormReal_symmetricGaussianMatrix_rpow b hp)
      (fun G => sum_rowSq_rpow_le_schattenNormReal_rpow _ hp)

/-- The absolute moment of an actual symmetric-profile entry factors into
its coefficient power and the scalar Gaussian moment. -/
theorem integral_abs_symmetricGaussianMatrix_entry_rpow
    (b : Matrix n n ℝ) (hb : b.IsSymm) (hb0 : ∀ i j, 0 ≤ b i j)
    {p : ℝ} (hp : 0 ≤ p) (i j : n) :
    (∫ G, |symmetricGaussianMatrix b G i j| ^ p ∂gaussianMatrix n n) =
      b i j ^ p * (∫ z : ℝ, |z| ^ p ∂gaussianReal 0 1) := by
  simp_rw [symmetricGaussianMatrix_apply_of_isSymm b hb, abs_mul,
    abs_of_nonneg (hb0 i j)]
  simp_rw [Real.mul_rpow (hb0 i j) (abs_nonneg _)]
  rw [integral_const_mul]
  congr 1
  exact integral_comp_gaussianMatrix_entry_eq (max i j) (min i j)
    (fun z : ℝ => |z| ^ p) (continuous_abs.rpow_const (fun _ => Or.inr hp)).measurable

private theorem integrable_abs_symmetricGaussianMatrix_entry_rpow
    (b : Matrix n n ℝ) {p : ℝ} (hp : 0 ≤ p) (i j : n) :
    Integrable (fun G => |symmetricGaussianMatrix b G i j| ^ p) (gaussianMatrix n n) := by
  have h := (memLp_symmetricGaussianMatrix_entry b i j (ENNReal.ofReal p)
    ENNReal.ofReal_ne_top).integrable_norm_rpow'
  simpa only [ENNReal.toReal_ofReal hp, Real.norm_eq_abs] using h

private theorem sum_selected_entry_abs_rpow_le_schattenNormReal_rpow
    (A : Matrix n n ℝ) (f : n → n) {p : ℝ} (hp : 2 ≤ p) :
    (∑ i, |A i (f i)| ^ p) ≤ schattenNormReal A p ^ p := by
  apply le_trans (Finset.sum_le_sum ?_) (sum_rowSq_rpow_le_schattenNormReal_rpow A hp)
  intro i hi
  have hentry : |A i (f i)| ^ 2 ≤ rowSq A i := by
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖A i j‖) (Finset.mem_univ (f i))
  have hid : |A i (f i)| ^ p = (|A i (f i)| ^ 2) ^ (p / 2) := by
    rw [← Real.rpow_natCast_mul (abs_nonneg _) 2 (p / 2)]
    congr 1
    ring
  rw [hid]
  exact Real.rpow_le_rpow (sq_nonneg _) hentry (by linarith)

/-- Selecting any one entry in each row gives a lower Schatten moment
contribution. The selected entries need not be mutually independent. -/
theorem integral_abs_rpow_gaussianReal_mul_sum_selected_profile_rpow_le
    (b : Matrix n n ℝ) (hb : b.IsSymm) (hb0 : ∀ i j, 0 ≤ b i j)
    (f : n → n) {p : ℝ} (hp : 2 ≤ p) :
    (∫ z : ℝ, |z| ^ p ∂gaussianReal 0 1) * (∑ i, b i (f i) ^ p) ≤
      ∫ G, schattenNormReal (symmetricGaussianMatrix b G) p ^ p ∂gaussianMatrix n n := by
  have hp0 : 0 ≤ p := by linarith
  have hi : Integrable (fun G => ∑ i, |symmetricGaussianMatrix b G i (f i)| ^ p)
      (gaussianMatrix n n) := integrable_finsetSum _ fun i _ =>
        integrable_abs_symmetricGaussianMatrix_entry_rpow b hp0 i (f i)
  calc
    _ = ∫ G, ∑ i, |symmetricGaussianMatrix b G i (f i)| ^ p ∂gaussianMatrix n n := by
      rw [integral_finsetSum _ (fun i _ =>
        integrable_abs_symmetricGaussianMatrix_entry_rpow b hp0 i (f i))]
      simp_rw [integral_abs_symmetricGaussianMatrix_entry_rpow b hb hb0 hp0]
      rw [← Finset.sum_mul, mul_comm]
    _ ≤ _ := integral_mono hi (integrable_schattenNormReal_symmetricGaussianMatrix_rpow b hp)
      (fun G => sum_selected_entry_abs_rpow_le_schattenNormReal_rpow _ f hp)

/-- The scalar Gaussian absolute moment times the row-maximum profile power
sum is bounded by the actual expected Schatten power. For nonnegative rows,
the Pi norm is exactly their largest profile coefficient. Empty dimension is
included without selecting a nonexistent column. -/
theorem integral_abs_rpow_gaussianReal_mul_sum_rowMax_profile_rpow_le
    (b : Matrix n n ℝ) (hb : b.IsSymm) (hb0 : ∀ i j, 0 ≤ b i j)
    {p : ℝ} (hp : 2 ≤ p) :
    (∫ z : ℝ, |z| ^ p ∂gaussianReal 0 1) * (∑ i, ‖b i‖ ^ p) ≤
      ∫ G, schattenNormReal (symmetricGaussianMatrix b G) p ^ p ∂gaussianMatrix n n := by
  classical
  rcases isEmpty_or_nonempty n with hn | hn
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero]
    exact integral_nonneg fun G => Real.rpow_nonneg (schattenNormReal_nonneg _ _) _
  have hmax (i : n) : ∃ j : n, b i j = ‖b i‖ := by
    obtain ⟨j, hj⟩ := (IsGreatest.pi_norm (b i)).1
    exact ⟨j, (Real.norm_of_nonneg (hb0 i j)) ▸ hj⟩
  choose f hf using hmax
  simpa only [hf] using
    integral_abs_rpow_gaussianReal_mul_sum_selected_profile_rpow_le b hb hb0 f hp

/-- The row variance profile contributes with constant one to the rooted
actual Schatten moment for every real `p ≥ 2`. -/
theorem rowSq_profile_root_le_integral_schattenNormReal_symmetricGaussianMatrix_rpow_root
    (b : Matrix n n ℝ) (hb : b.IsSymm) {p : ℝ} (hp : 2 ≤ p) :
    (∑ i, (∑ j, b i j ^ 2) ^ (p / 2)) ^ p⁻¹ ≤
      (∫ G, schattenNormReal (symmetricGaussianMatrix b G) p ^ p
        ∂gaussianMatrix n n) ^ p⁻¹ := by
  exact Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg
      (Finset.sum_nonneg fun j _ => sq_nonneg _) _)
    (sum_rowSq_profile_rpow_le_integral_schattenNormReal_symmetricGaussianMatrix_rpow b hb hp)
    (inv_nonneg.mpr (by linarith))

/-- The row-maximum profile times `sqrt p` is at most four times the actual
rooted Schatten moment. Scalar Gaussian moment growth gives the factor four;
the selected row entries are allowed to share Gaussian coordinates. -/
theorem sqrt_mul_rowMax_profile_root_le_four_mul_integral_schattenNormReal_symmetricGaussianMatrix_rpow_root
    (b : Matrix n n ℝ) (hb : b.IsSymm) (hb0 : ∀ i j, 0 ≤ b i j)
    {p : ℝ} (hp : 2 ≤ p) :
    Real.sqrt p * (∑ i, ‖b i‖ ^ p) ^ p⁻¹ ≤
      4 * (∫ G, schattenNormReal (symmetricGaussianMatrix b G) p ^ p
        ∂gaussianMatrix n n) ^ p⁻¹ := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hscalarNN : 0 ≤ ∫ z : ℝ, |z| ^ p ∂gaussianReal 0 1 :=
    integral_nonneg fun z => Real.rpow_nonneg (abs_nonneg _) _
  have hmaxNN : 0 ≤ ∑ i, ‖b i‖ ^ p :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  have hroot := Real.rpow_le_rpow (mul_nonneg hscalarNN hmaxNN)
    (integral_abs_rpow_gaussianReal_mul_sum_rowMax_profile_rpow_le b hb hb0 hp)
    (inv_nonneg.mpr hp0.le)
  rw [Real.mul_rpow hscalarNN hmaxNN] at hroot
  have hscalar := sqrt_div_four_le_integral_abs_rpow_root_gaussianReal hp
  have hmul := mul_le_mul_of_nonneg_right hscalar (Real.rpow_nonneg hmaxNN p⁻¹)
  nlinarith [hmul.trans hroot]

/-- The full lower variance-profile Schatten-moment bound holds for all real
`p ≥ 2`, with explicit universal constant `1/100`. For nonnegative profiles,
`‖b i‖` is exactly the maximum coefficient in row `i`, with the empty-row
convention zero. The law is the actual symmetric Gaussian construction and
its matching Schatten moment is integrable.
Source: Latała--van Handel--Youssef, arXiv:1711.00807v2, Theorem 1.1,
lower half, with a deliberately loose universal constant.
atlas: heterogeneous-gaussian-schatten-moments (partial) -/
theorem row_profile_le_integral_schattenNorm_symmetricGaussianMatrix_rpow_root
    (b : Matrix n n ℝ) (hb : b.IsSymm) (hb0 : ∀ i j, 0 ≤ b i j)
    {p : ℝ} (hp : 2 ≤ p) :
    (1 / 100 : ℝ) *
        ((∑ i, (∑ j, b i j ^ 2) ^ (p / 2)) ^ p⁻¹ +
          Real.sqrt p * (∑ i, ‖b i‖ ^ p) ^ p⁻¹) ≤
      (∫ G, schattenNorm (symmetricGaussianMatrix b G) (ENNReal.ofReal p) ^ p
        ∂gaussianMatrix n n) ^ p⁻¹ := by
  have hp0 : 0 ≤ p := by linarith
  simp only [schattenNorm_ofReal _ hp0]
  have hvariance :=
    rowSq_profile_root_le_integral_schattenNormReal_symmetricGaussianMatrix_rpow_root b hb hp
  have hmaximum :=
    sqrt_mul_rowMax_profile_root_le_four_mul_integral_schattenNormReal_symmetricGaussianMatrix_rpow_root
      b hb hb0 hp
  have hrootNN : 0 ≤ (∫ G, schattenNormReal (symmetricGaussianMatrix b G) p ^ p
      ∂gaussianMatrix n n) ^ p⁻¹ :=
    Real.rpow_nonneg (integral_nonneg fun G =>
      Real.rpow_nonneg (schattenNormReal_nonneg _ _) _) _
  linarith

end NLAlib
