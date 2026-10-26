import NLAlib.RandomMatrix.Gaussian.Moments.SymmetricProfileUpperMoments
import NLAlib.RandomMatrix.Gaussian.Moments.SymmetricProfileLowerMoments
import NLAlib.Matrix.Norms.WithComplexSchatten
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Complex symmetric Gaussian coefficient profiles

The same canonical lower-triangular real Gaussian coordinates can multiply
complex symmetric coefficients. Splitting real and imaginary parts retains
the real profile theorem and gives the complex even endpoint required for
interpolation. All finite moments and Bochner integrability are proved for
the actual Gaussian law.

Source: Latała--van Handel--Youssef, arXiv:1711.00807v2, §2.3.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal

namespace NLAlib

variable {n : Type*} [Fintype n] [LinearOrder n]

/-- A complex symmetric coefficient profile multiplied by the canonical
lower-triangular coordinates of one genuine real standard Gaussian matrix. -/
def symmetricComplexGaussianMatrix (b : Matrix n n ℂ) (G : Matrix n n ℝ) : Matrix n n ℂ :=
  Matrix.of fun i j => b (max i j) (min i j) * (G (max i j) (min i j) : ℂ)

omit [Fintype n] in
/-- The coefficient construction is pointwise symmetric, using the same
real Gaussian coordinate on both sides of the diagonal. -/
theorem symmetricComplexGaussianMatrix_isSymm (b : Matrix n n ℂ) (G : Matrix n n ℝ) :
    (symmetricComplexGaussianMatrix b G).IsSymm := by
  ext i j
  simp [symmetricComplexGaussianMatrix, max_comm j i, min_comm j i]

omit [Fintype n] in
/-- For a symmetric complex profile the coefficient at each copied entry
is the original profile entry. -/
theorem symmetricComplexGaussianMatrix_apply_of_isSymm
    (b : Matrix n n ℂ) (hb : b.IsSymm) (G : Matrix n n ℝ) (i j : n) :
    symmetricComplexGaussianMatrix b G i j = b i j * (G (max i j) (min i j) : ℂ) := by
  by_cases hij : i ≤ j
  · simp [symmetricComplexGaussianMatrix, max_eq_right hij, min_eq_left hij, hb.apply i j]
  · simp [symmetricComplexGaussianMatrix, max_eq_left (le_of_not_ge hij),
      min_eq_right (le_of_not_ge hij)]

/-- For a fixed real Gaussian sample, the complex symmetric construction is
complex linear in its coefficient matrix. No coefficient symmetry is needed
to define this map. -/
def symmetricComplexGaussianMatrixLinearMap (G : Matrix n n ℝ) :
    Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun := fun b => symmetricComplexGaussianMatrix b G
  map_add' := by intro a b; ext i j; simp [symmetricComplexGaussianMatrix, add_mul]
  map_smul' := by intro c b; ext i j; simp [symmetricComplexGaussianMatrix]; ring

/-- For fixed complex coefficients the ensemble is real linear in the raw
real Gaussian sample. Atom averaging can therefore be moved before this map. -/
def symmetricComplexGaussianSampleLinearMap (b : Matrix n n ℂ) :
    Matrix n n ℝ →ₗ[ℝ] Matrix n n ℂ where
  toFun := symmetricComplexGaussianMatrix b
  map_add' := by intro G H; ext i j; simp [symmetricComplexGaussianMatrix, mul_add]
  map_smul' := by intro c G; ext i j; simp [symmetricComplexGaussianMatrix]; ring

open scoped Matrix.Norms.L2Operator in
/-- The complex coefficient ensemble is a genuine real Gaussian random
matrix, as a continuous real linear image of the standard Gaussian matrix. -/
theorem hasGaussianLaw_symmetricComplexGaussianMatrix (b : Matrix n n ℂ) :
    HasGaussianLaw (symmetricComplexGaussianMatrix b) (gaussianMatrix n n) := by
  exact (hasGaussianLaw_id_gaussianMatrix n n).map
    (symmetricComplexGaussianSampleLinearMap b).toContinuousLinearMap

open scoped Matrix.Norms.L2Operator in
/-- The actual complex Gaussian profile matrix belongs to every finite
`L^p` space. In particular all its Bochner moments exist. -/
theorem memLp_symmetricComplexGaussianMatrix (b : Matrix n n ℂ)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (symmetricComplexGaussianMatrix b) p (gaussianMatrix n n) :=
  (hasGaussianLaw_symmetricComplexGaussianMatrix b).memLp hp

open scoped Matrix.Norms.L2Operator in
/-- The actual complex Gaussian profile matrix is Bochner integrable. -/
theorem integrable_symmetricComplexGaussianMatrix (b : Matrix n n ℂ) :
    Integrable (symmetricComplexGaussianMatrix b) (gaussianMatrix n n) :=
  (memLp_symmetricComplexGaussianMatrix b 1 (by simp)).integrable le_rfl

open scoped Matrix.Norms.L2Operator in
/-- The complex profile map is measurable for the actual Gaussian sample
space. This also follows directly from its continuous real linear formula. -/
theorem measurable_symmetricComplexGaussianMatrix (b : Matrix n n ℂ) :
    Measurable (symmetricComplexGaussianMatrix b) :=
  (symmetricComplexGaussianSampleLinearMap b).toContinuousLinearMap.continuous.measurable

private theorem schattenNormReal_map_complex (A : Matrix n n ℝ) (p : ℝ) :
    schattenNormReal (A.map Complex.ofReal) p = schattenNormReal A p := by
  have hs (i : ℕ) : singularValues (A.map Complex.ofReal) i = singularValues A i :=
    singularValues_map_ofReal (𝕜 := ℂ) A i
  simp only [schattenNormReal, hs]

omit [Fintype n] in
private theorem symmetricComplexGaussianMatrix_eq_real_add_imag
    (b : Matrix n n ℂ) (G : Matrix n n ℝ) :
    symmetricComplexGaussianMatrix b G =
      (symmetricGaussianMatrix (b.map Complex.re) G).map Complex.ofReal +
        Complex.I • (symmetricGaussianMatrix (b.map Complex.im) G).map Complex.ofReal := by
  ext i j
  simp only [symmetricComplexGaussianMatrix, symmetricGaussianMatrix, Matrix.map_apply,
    Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

private theorem schattenNormReal_symmetricComplexGaussianMatrix_le
    (b : Matrix n n ℂ) (G : Matrix n n ℝ) {p : ℝ} (hp : 1 ≤ p) :
    schattenNormReal (symmetricComplexGaussianMatrix b G) p ≤
      schattenNormReal (symmetricGaussianMatrix (b.map Complex.re) G) p +
        schattenNormReal (symmetricGaussianMatrix (b.map Complex.im) G) p := by
  rw [symmetricComplexGaussianMatrix_eq_real_add_imag]
  apply (schattenNormReal_add_le_complex _ _ hp).trans
  rw [schattenNormReal_smul_complex _ _ (zero_lt_one.trans_le hp), Complex.norm_I,
    one_mul, schattenNormReal_map_complex, schattenNormReal_map_complex]

open scoped Matrix.Norms.L2Operator in
/-- Every positive finite Schatten norm of the complex profile ensemble
belongs to every finite `L^q` space. Both exponents are independent, and the
bound follows from the actual real and imaginary Gaussian profiles. -/
theorem memLp_schattenNormReal_symmetricComplexGaussianMatrix
    (b : Matrix n n ℂ) {p : ℝ} (hp : 1 ≤ p) (q : ℝ≥0∞) (hq : q ≠ ∞) :
    MemLp (fun G => schattenNormReal (symmetricComplexGaussianMatrix b G) p)
      q (gaussianMatrix n n) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hmatrix := memLp_symmetricComplexGaussianMatrix b q hq
  have hmeas : AEStronglyMeasurable
      (fun G => schattenNormReal (symmetricComplexGaussianMatrix b G) p) (gaussianMatrix n n) :=
    ((continuous_schattenNormReal hp0).measurable.comp
    (measurable_symmetricComplexGaussianMatrix b)).aestronglyMeasurable
  have hbound (G : Matrix n n ℝ) :
      schattenNormReal (symmetricComplexGaussianMatrix b G) p ≤
        (Fintype.card n : ℝ) ^ (1 / p) * specNorm (symmetricComplexGaussianMatrix b G) :=
    schattenNormReal_le_card_rpow_mul_specNorm _ hp0
  exact (hmatrix.norm.const_mul ((Fintype.card n : ℝ) ^ (1 / p))).of_le hmeas
    (Filter.Eventually.of_forall fun G => by
      rw [Real.norm_of_nonneg (schattenNormReal_nonneg _ _),
        Real.norm_of_nonneg (by positivity)]
      exact hbound G)

/-- Every finite positive Schatten moment of the actual complex profile
ensemble is integrable. -/
theorem integrable_schattenNormReal_symmetricComplexGaussianMatrix_rpow
    (b : Matrix n n ℂ) {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun G => schattenNormReal (symmetricComplexGaussianMatrix b G) p ^ p)
      (gaussianMatrix n n) := by
  have hh := (memLp_schattenNormReal_symmetricComplexGaussianMatrix b hp
    (ENNReal.ofReal p) ENNReal.ofReal_ne_top).integrable_norm_rpow'
  simpa only [ENNReal.toReal_ofReal (zero_le_one.trans hp), Real.norm_eq_abs,
    abs_of_nonneg (schattenNormReal_nonneg _ _)] using hh

/-- Exact `L²(S₂)` isometry of the complex symmetric Gaussian coefficient
multiplier. Every matrix entry is counted once in the ordinary Frobenius
power sum, including both copies of an off-diagonal coefficient. -/
theorem integral_schattenNormReal_symmetricComplexGaussianMatrix_sq
    (b : Matrix n n ℂ) (hb : b.IsSymm) :
    (∫ G, schattenNormReal (symmetricComplexGaussianMatrix b G) 2 ^ 2
      ∂gaussianMatrix n n) = ∑ i, ∑ j, ‖b i j‖ ^ 2 := by
  have hnorm (A : Matrix n n ℂ) : schattenNormReal A 2 ^ 2 = frobSq A := by
    simpa only [Nat.mul_one, Nat.cast_ofNat, pow_one,
      ← frobSq_eq_re_trace_conjTranspose_mul_self] using
      schattenNormReal_pow_even_eq_re_trace_gram A (r := 1) (by omega)
  have hi (i j : n) : Integrable
      (fun G : Matrix n n ℝ => ‖b i j‖ ^ 2 * G (max i j) (min i j) ^ 2)
      (gaussianMatrix n n) :=
    (memLp_gaussianMatrix_entry (max i j) (min i j) 2 (by norm_num)).integrable_sq.const_mul _
  simp_rw [hnorm, frobSq_eq_sum_norm_sq,
    symmetricComplexGaussianMatrix_apply_of_isSymm b hb, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, integral_gaussianMatrix_entry_sq_eq_one, mul_one]

omit [LinearOrder n] in
private theorem component_profile_root_le
    (b : Matrix n n ℂ) (c : Matrix n n ℝ) (hc : ∀ i j, |c i j| ≤ ‖b i j‖)
    (k : ℕ) (hk : 0 < k) :
    ((∑ i, (∑ j, c i j ^ 2) ^ k) ^ (((2 * k : ℕ) : ℝ)⁻¹) +
        Real.sqrt k * (∑ i, ‖c i‖ ^ (2 * k)) ^ (((2 * k : ℕ) : ℝ)⁻¹)) ≤
      ((∑ i, (∑ j, ‖b i j‖ ^ 2) ^ k) ^ (((2 * k : ℕ) : ℝ)⁻¹) +
        Real.sqrt k * (∑ i, ∑ j, ‖b i j‖ ^ (2 * k)) ^ (((2 * k : ℕ) : ℝ)⁻¹)) := by
  classical
  let q := 2 * k
  have hq : 0 < q := by dsimp [q]; omega
  have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hrow : (∑ i, (∑ j, c i j ^ 2) ^ k) ≤ ∑ i, (∑ j, ‖b i j‖ ^ 2) ^ k := by
    apply Finset.sum_le_sum
    intro i _
    apply pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => sq_nonneg _) _ k
    apply Finset.sum_le_sum
    intro j _
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (c i j)) (hc i j) 2
  have hcap : (∑ i, ‖c i‖ ^ q) ≤ ∑ i, ∑ j, ‖b i j‖ ^ q := by
    apply Finset.sum_le_sum
    intro i _
    let S : ℝ := ∑ j, ‖b i j‖ ^ q
    have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => pow_nonneg (norm_nonneg _) _
    have hrootpow : (S ^ ((q : ℝ)⁻¹)) ^ q = S := by
      rw [← Real.rpow_natCast, Real.rpow_inv_rpow hS hqr.ne']
    have hn : ‖c i‖ ≤ S ^ ((q : ℝ)⁻¹) := by
      apply (pi_norm_le_iff_of_nonneg (Real.rpow_nonneg hS _)).mpr
      intro j
      apply (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.rpow_nonneg hS _) hq.ne').mp
      rw [hrootpow, Real.norm_eq_abs]
      exact (pow_le_pow_left₀ (abs_nonneg _) (hc i j) q).trans
        (Finset.single_le_sum (fun j _ => pow_nonneg (norm_nonneg _) q) (Finset.mem_univ j))
    exact (pow_le_pow_left₀ (norm_nonneg _) hn q).trans_eq hrootpow
  apply add_le_add
  · exact Real.rpow_le_rpow
      (Finset.sum_nonneg fun i _ => pow_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _) _) hrow
      (by positivity)
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => pow_nonneg (norm_nonneg _) q)
        hcap (by positivity)) (Real.sqrt_nonneg _)

private theorem lpNorm_nonneg_eq_even_root
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ) (hfnn : ∀ x, 0 ≤ f x)
    {q : ℕ} (hq : 0 < q) :
    lpNorm f (ENNReal.ofReal (q : ℝ)) μ = (∫ x, f x ^ q ∂μ) ^ ((q : ℝ)⁻¹) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) ENNReal.ofReal_ne_top hf]
  simp only [ENNReal.toReal_ofReal (Nat.cast_nonneg q), Real.norm_eq_abs,
    abs_of_nonneg (hfnn _), Real.rpow_natCast]

/-- Sharp even-moment upper endpoint for the actual complex symmetric
Gaussian multiplier. The two deterministic terms are its row `ℓ₂` profile
and total entry `ℓ_(2k)` profile. The universal constant `48` comes from the
proved real constant `24` and the real/imaginary decomposition. No matrix
dimension factor is introduced. -/
theorem integral_schattenNormReal_symmetricComplexGaussianMatrix_pow_two_mul_root_le
    (b : Matrix n n ℂ) (hb : b.IsSymm) (k : ℕ) (hk : 0 < k) :
    (∫ G, schattenNormReal (symmetricComplexGaussianMatrix b G) (2 * k : ℕ) ^ (2 * k)
      ∂gaussianMatrix n n) ^ (((2 * k : ℕ) : ℝ)⁻¹) ≤
      48 * ((∑ i, (∑ j, ‖b i j‖ ^ 2) ^ k) ^ (((2 * k : ℕ) : ℝ)⁻¹) +
        Real.sqrt k * (∑ i, ∑ j, ‖b i j‖ ^ (2 * k)) ^ (((2 * k : ℕ) : ℝ)⁻¹)) := by
  let q := 2 * k
  have hq : 0 < q := by dsimp [q]; omega
  have hq₂ : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by dsimp [q]; omega)
  have hq₁ : 1 ≤ (q : ℝ) := by linarith
  let f : Matrix n n ℝ → ℝ := fun G =>
    schattenNormReal (symmetricGaussianMatrix (b.map Complex.re) G) q
  let g : Matrix n n ℝ → ℝ := fun G =>
    schattenNormReal (symmetricGaussianMatrix (b.map Complex.im) G) q
  let h : Matrix n n ℝ → ℝ := fun G =>
    schattenNormReal (symmetricComplexGaussianMatrix b G) q
  have hf := memLp_schattenNormReal_symmetricGaussianMatrix (b.map Complex.re) hq₂
  have hg := memLp_schattenNormReal_symmetricGaussianMatrix (b.map Complex.im) hq₂
  have hh := memLp_schattenNormReal_symmetricComplexGaussianMatrix b hq₁
    (ENNReal.ofReal (q : ℝ)) ENNReal.ofReal_ne_top
  have hmono : lpNorm h (ENNReal.ofReal (q : ℝ)) (gaussianMatrix n n) ≤
      lpNorm (f + g) (ENNReal.ofReal (q : ℝ)) (gaussianMatrix n n) := by
    apply lpNorm_mono_real (hf.add hg)
    intro G
    rw [Real.norm_of_nonneg (schattenNormReal_nonneg _ _)]
    exact schattenNormReal_symmetricComplexGaussianMatrix_le b G hq₁
  have htri := lpNorm_add_le hf (g := g) (ENNReal.one_le_ofReal.mpr hq₁)
  rw [lpNorm_nonneg_eq_even_root h hh.aestronglyMeasurable
      (fun _ => schattenNormReal_nonneg _ _) hq] at hmono
  rw [lpNorm_nonneg_eq_even_root f hf.aestronglyMeasurable
      (fun _ => schattenNormReal_nonneg _ _) hq,
    lpNorm_nonneg_eq_even_root g hg.aestronglyMeasurable
      (fun _ => schattenNormReal_nonneg _ _) hq] at htri
  have hbre : (b.map Complex.re).IsSymm := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, hb.apply i j]
  have hbim : (b.map Complex.im).IsSymm := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, hb.apply i j]
  have hfr := integral_schattenNormReal_symmetricGaussianMatrix_pow_two_mul_root_le
    (b.map Complex.re) hbre k hk
  have hgr := integral_schattenNormReal_symmetricGaussianMatrix_pow_two_mul_root_le
    (b.map Complex.im) hbim k hk
  have hfre := component_profile_root_le b (b.map Complex.re)
    (fun i j => Complex.abs_re_le_norm (b i j)) k hk
  have hgim := component_profile_root_le b (b.map Complex.im)
    (fun i j => Complex.abs_im_le_norm (b i j)) k hk
  change (∫ G, h G ^ q ∂gaussianMatrix n n) ^ ((q : ℝ)⁻¹) ≤ _
  have hsum := (hmono.trans htri).trans (add_le_add hfr hgr)
  nlinarith [hfre, hgim]

end NLAlib
