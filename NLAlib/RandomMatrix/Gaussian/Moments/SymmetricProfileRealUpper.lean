import NLAlib.RandomMatrix.Gaussian.Moments.SymmetricComplexProfile
import NLAlib.RandomMatrix.Gaussian.Moments.SymmetricProfileInterpolation
import NLAlib.Matrix.Norms.EntryRowProfileBounds

/-!
# All-real-exponent upper Gaussian Schatten moments

Normalize the row and entry profile at a target real exponent, interpolate
between the exact second moment and a larger even moment, and restore the
scale. The final real-matrix statement uses the source's row-variance and
row-maximum profiles, with an explicit dimension-free universal constant.

Source: Latała--van Handel--Youssef, arXiv:1711.00807v2, Theorem 1.1 and §2.3.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix ENNReal

namespace NLAlib

private theorem exists_even_reciprocal_interpolation {p : ℝ} (hp : 2 < p) :
    ∃ (k : ℕ) (θ : ℝ), 0 < k ∧ p < ((2 * k : ℕ) : ℝ) ∧
      ((2 * k : ℕ) : ℝ) ≤ 4 * p ∧ θ ∈ Ioo (0 : ℝ) 1 ∧
      1 / p = (1 - θ) / 2 + θ / ((2 * k : ℕ) : ℝ) := by
  let k := ⌈p / 2⌉₊ + 1
  let q : ℝ := (2 * k : ℕ)
  have hk : 0 < k := by dsimp [k]; omega
  have hqlo : p < q := by
    have hh := Nat.le_ceil (p / 2)
    dsimp [k, q]
    push_cast
    linarith
  have hqhi : q ≤ 4 * p := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ p / 2 by linarith)
    dsimp [q, k]
    push_cast
    linarith
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := hp0.trans hqlo
  have hpi : 1 / p < (1 : ℝ) / 2 := by
    apply (div_lt_div_iff₀ hp0 (by norm_num)).mpr
    linarith
  have hqi : 1 / q < 1 / p := by
    apply (div_lt_div_iff₀ hq0 hp0).mpr
    linarith
  let d : ℝ := 1 / 2 - 1 / q
  let a : ℝ := 1 / 2 - 1 / p
  have hd : 0 < d := by dsimp [d]; linarith
  have ha : 0 < a := by dsimp [a]; linarith
  have had : a < d := by dsimp [a, d]; linarith
  let θ := a / d
  have hθ : θ ∈ Ioo (0 : ℝ) 1 := ⟨div_pos ha hd, (div_lt_one hd).mpr had⟩
  have hmul : θ * d = a := div_mul_cancel₀ a hd.ne'
  refine ⟨k, θ, hk, hqlo, hqhi, hθ, ?_⟩
  change 1 / p = (1 - θ) / 2 + θ / q
  dsimp [d, a] at hmul
  simp only [div_eq_mul_inv] at hmul ⊢
  nlinarith

variable {n : Type*} [Fintype n] [LinearOrder n]

omit [Fintype n] in
private theorem symmetricComplexGaussianMatrix_profile_real_smul
    (b : Matrix n n ℂ) (G : Matrix n n ℝ) (c : ℝ) :
    symmetricComplexGaussianMatrix (c • b) G = c • symmetricComplexGaussianMatrix b G := by
  ext i j
  simp only [symmetricComplexGaussianMatrix, Matrix.of_apply, Matrix.smul_apply,
    Complex.real_smul]
  ring

private theorem integral_schattenNormReal_symmetricComplexGaussianMatrix_smul_rpow_root
    (b : Matrix n n ℂ) {p c : ℝ} (hp : 0 < p) (hc : 0 ≤ c) :
    (∫ G, schattenNormReal (symmetricComplexGaussianMatrix (c • b) G) p ^ p
      ∂gaussianMatrix n n) ^ p⁻¹ =
        c * (∫ G, schattenNormReal (symmetricComplexGaussianMatrix b G) p ^ p
          ∂gaussianMatrix n n) ^ p⁻¹ := by
  simp_rw [symmetricComplexGaussianMatrix_profile_real_smul,
    schattenNormReal_real_smul_complex _ _ hp, abs_of_nonneg hc,
    Real.mul_rpow hc (schattenNormReal_nonneg _ _)]
  rw [integral_const_mul, Real.mul_rpow (Real.rpow_nonneg hc _)
    (integral_nonneg fun G => Real.rpow_nonneg (schattenNormReal_nonneg _ _) _),
    Real.rpow_rpow_inv hc hp.ne']

/-- For every real exponent greater than two, the actual complex symmetric
Gaussian multiplier is bounded by its row profile and entry profile, with
constant independent of the exponent and matrix dimension. -/
theorem integral_schattenNormReal_symmetricComplexGaussianMatrix_rpow_root_le_of_two_lt
    (b : Matrix n n ℂ) (hb : b.IsSymm) {p : ℝ} (hp : 2 < p) :
    (∫ G, schattenNormReal (symmetricComplexGaussianMatrix b G) p ^ p
      ∂gaussianMatrix n n) ^ p⁻¹ ≤
      96 * ((∑ i, (∑ j, ‖b i j‖ ^ 2) ^ (p / 2)) ^ p⁻¹ +
        2 * Real.sqrt p * (∑ i, ∑ j, ‖b i j‖ ^ p) ^ p⁻¹) := by
  classical
  have hp0 : 0 < p := by linarith
  have hD : 0 ≤ ∑ i, (∑ j, ‖b i j‖ ^ 2) ^ (p / 2) :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _) _
  have hE : 0 ≤ ∑ i, ∑ j, ‖b i j‖ ^ p :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) _
  by_cases hbzero : b = 0
  · have hz (G : Matrix n n ℝ) : symmetricComplexGaussianMatrix b G = 0 := by
      ext i j
      simp [symmetricComplexGaussianMatrix, hbzero]
    simp_rw [hz, schattenNormReal_zero hp0, Real.zero_rpow hp0.ne', integral_zero,
      Real.zero_rpow (inv_ne_zero hp0.ne')]
    positivity
  obtain ⟨k, θ, hk, hkp, hqhi, hθ, hexp⟩ := exists_even_reciprocal_interpolation hp
  let q : ℝ := ((2 * k : ℕ) : ℝ)
  let c : ℝ := Real.sqrt q
  let A : ℝ := (∑ i, (∑ j, ‖b i j‖ ^ 2) ^ (p / 2)) ^ p⁻¹
  let E : ℝ := (∑ i, ∑ j, ‖b i j‖ ^ p) ^ p⁻¹
  let K : ℝ := A + c * E
  have hA : 0 ≤ A := Real.rpow_nonneg hD _
  have hEnn : 0 ≤ E := Real.rpow_nonneg hE _
  have hq0 : 0 < q := hp0.trans hkp
  have hc : 0 < c := Real.sqrt_pos.mpr hq0
  have hc1 : 1 ≤ c := by
    change 1 ≤ Real.sqrt q
    exact Real.one_le_sqrt.mpr (by linarith)
  have hEpos : 0 < E := by
    have hbn : ∃ i j, b i j ≠ 0 := by
      by_contra! hh
      exact hbzero (by ext i j; exact hh i j)
    obtain ⟨i, j, hij⟩ := hbn
    have hh : 0 < ∑ i, ∑ j, ‖b i j‖ ^ p :=
      (Real.rpow_pos_of_pos (norm_pos_iff.mpr hij) p).trans_le
        ((Finset.single_le_sum (fun j _ => Real.rpow_nonneg (norm_nonneg _) p) (Finset.mem_univ j)).trans
          (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ =>
            Real.rpow_nonneg (norm_nonneg _) p) (Finset.mem_univ i)))
    exact Real.rpow_pos_of_pos hh _
  have hK : 0 < K := add_pos_of_nonneg_of_pos hA (mul_pos hc hEpos)
  have hApow : A ^ p = ∑ i, (∑ j, ‖b i j‖ ^ 2) ^ (p / 2) := Real.rpow_inv_rpow hD hp0.ne'
  have hEpow : E ^ p = ∑ i, ∑ j, ‖b i j‖ ^ p := Real.rpow_inv_rpow hE hp0.ne'
  have hAK : A ≤ K := le_add_of_nonneg_right (mul_nonneg hc.le hEnn)
  have hcθ : c ^ θ ≤ c := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hc1 hθ.2.le
  have hcEK : c ^ θ * E ≤ K :=
    (mul_le_mul_of_nonneg_right hcθ hEnn).trans (le_add_of_nonneg_left hA)
  let bn : Matrix n n ℂ := K⁻¹ • b
  have hbn : bn.IsSymm := hb.smul _
  have hnorm (i j : n) : ‖bn i j‖ = K⁻¹ * ‖b i j‖ := by
    simp only [bn, Matrix.smul_apply, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hK)]
  have hrowbn : (∑ i, (∑ j, ‖bn i j‖ ^ 2) ^ (p / 2)) =
      K⁻¹ ^ p * ∑ i, (∑ j, ‖b i j‖ ^ 2) ^ (p / 2) := by
    simp_rw [hnorm, mul_pow, ← Finset.mul_sum,
      Real.mul_rpow (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _)]
    have he : (K⁻¹ ^ 2) ^ (p / 2) = K⁻¹ ^ p := by
      rw [← Real.rpow_natCast K⁻¹ 2, ← Real.rpow_mul (inv_nonneg.mpr hK.le)]
      congr 1
      norm_num
      ring
    rw [he, ← Finset.mul_sum]
  have hentrybn : (∑ i, ∑ j, ‖bn i j‖ ^ p) = K⁻¹ ^ p * ∑ i, ∑ j, ‖b i j‖ ^ p := by
    simp_rw [hnorm, Real.mul_rpow (inv_nonneg.mpr hK.le) (norm_nonneg _), ← Finset.mul_sum]
  have hcancel : K⁻¹ ^ p * K ^ p = 1 := by
    rw [← Real.mul_rpow (inv_nonneg.mpr hK.le) hK.le, inv_mul_cancel₀ hK.ne', Real.one_rpow]
  have hrow1 : (∑ i, (∑ j, ‖bn i j‖ ^ 2) ^ (p / 2)) ≤ 1 := by
    rw [hrowbn, ← hApow]
    exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hA hAK hp0.le)
      (Real.rpow_nonneg (inv_nonneg.mpr hK.le) _)).trans_eq hcancel
  have hentry1 : c ^ (θ * p) * (∑ i, ∑ j, ‖bn i j‖ ^ p) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg (Real.rpow_nonneg hc.le _) hEnn) hcEK hp0.le)
      (Real.rpow_nonneg (inv_nonneg.mpr hK.le) p)
    rw [Real.mul_rpow (Real.rpow_nonneg hc.le _) hEnn, ← Real.rpow_mul hc.le, hEpow] at hh
    rw [hentrybn]
    calc
      _ = K⁻¹ ^ p * (c ^ (θ * p) * (∑ i, ∑ j, ‖b i j‖ ^ p)) := by ring
      _ ≤ K⁻¹ ^ p * K ^ p := hh
      _ = 1 := hcancel
  have hn := integral_schattenNormReal_symmetricComplexGaussianMatrix_rpow_root_le_of_normalized_profiles
    bn hbn k hk p hp hkp θ hθ hexp hrow1 hentry1
  have hscale : b = K • bn := by
    dsimp [bn]
    rw [smul_smul, mul_inv_cancel₀ hK.ne', one_smul]
  have hrootScale := integral_schattenNormReal_symmetricComplexGaussianMatrix_smul_rpow_root bn hp0 hK.le
  rw [← hscale] at hrootScale
  rw [hrootScale]
  have hcBound : c ≤ 2 * Real.sqrt p := by
    have hh := Real.sqrt_le_sqrt hqhi
    have hs : Real.sqrt (4 * p) = 2 * Real.sqrt p := by rw [Real.sqrt_mul (by norm_num)]; norm_num
    rwa [hs] at hh
  calc
    _ ≤ K * 96 := mul_le_mul_of_nonneg_left hn hK.le
    _ ≤ _ := by dsimp [K, A, E]; nlinarith [mul_le_mul_of_nonneg_right hcBound hEnn]

/-- The actual symmetric Gaussian matrix satisfies the source's sharp
two-profile upper moment bound at every real exponent at least two.
The explicit universal constant `512` is independent of the exponent,
matrix dimension, and nonnegative symmetric variance profile.
Source: Latała--van Handel--Youssef, arXiv:1711.00807v2, Theorem 1.1,
all-real-exponent upper half.
atlas: heterogeneous-gaussian-schatten-moments (partial) -/
theorem integral_schattenNorm_symmetricGaussianMatrix_rpow_root_le
    (b : Matrix n n ℝ) (hb : b.IsSymm) (hb0 : ∀ i j, 0 ≤ b i j)
    {p : ℝ} (hp : 2 ≤ p) :
    (∫ G, schattenNorm (symmetricGaussianMatrix b G) (ENNReal.ofReal p) ^ p
      ∂gaussianMatrix n n) ^ p⁻¹ ≤
      512 * ((∑ i, (∑ j, b i j ^ 2) ^ (p / 2)) ^ p⁻¹ +
        Real.sqrt p * (∑ i, ‖b i‖ ^ p) ^ p⁻¹) := by
  have hp0 : 0 < p := by linarith
  simp only [schattenNorm_ofReal _ hp0.le]
  by_cases hp2 : p = 2
  · subst p
    simp only [Real.rpow_two]
    have hh := integral_schattenNormReal_symmetricGaussianMatrix_pow_two_mul_root_le b hb 1 (by omega)
    norm_num only [Nat.mul_one, Nat.cast_ofNat, pow_one, Real.sqrt_one, one_mul] at hh
    simp only [one_div] at hh
    apply hh.trans
    have hA : 0 ≤ (∑ i, ∑ j, b i j ^ 2) ^ ((2 : ℝ)⁻¹) :=
      Real.rpow_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) _
    have hB : 0 ≤ (∑ i, ‖b i‖ ^ 2) ^ ((2 : ℝ)⁻¹) :=
      Real.rpow_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) _
    have hsqrt : 1 ≤ Real.sqrt (2 : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
    norm_num only [div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one]
    nlinarith [mul_nonneg (sub_nonneg.mpr hsqrt) hB]
  · have hpgt : 2 < p := lt_of_le_of_ne hp (Ne.symm hp2)
    let bc : Matrix n n ℂ := b.map Complex.ofReal
    have hbc : bc.IsSymm := by
      ext i j
      change (b j i : ℂ) = (b i j : ℂ)
      rw [hb.apply i j]
    have hX (G : Matrix n n ℝ) : symmetricComplexGaussianMatrix bc G =
        (symmetricGaussianMatrix b G).map Complex.ofReal := by
      ext i j
      simp [bc, symmetricComplexGaussianMatrix, symmetricGaussianMatrix]
    have hnorm (G : Matrix n n ℝ) :
        schattenNormReal (symmetricComplexGaussianMatrix bc G) p =
          schattenNormReal (symmetricGaussianMatrix b G) p := by
      rw [hX]
      have hs (i : ℕ) : singularValues ((symmetricGaussianMatrix b G).map Complex.ofReal) i =
          singularValues (symmetricGaussianMatrix b G) i :=
        singularValues_map_ofReal (𝕜 := ℂ) _ i
      simp only [schattenNormReal, hs]
    have hcomplex := integral_schattenNormReal_symmetricComplexGaussianMatrix_rpow_root_le_of_two_lt bc hbc hpgt
    have hh : (∫ G, schattenNormReal (symmetricGaussianMatrix b G) p ^ p
        ∂gaussianMatrix n n) ^ p⁻¹ ≤
        96 * ((∑ i, (∑ j, b i j ^ 2) ^ (p / 2)) ^ p⁻¹ +
          2 * Real.sqrt p * (∑ i, ∑ j, b i j ^ p) ^ p⁻¹) := by
      simpa only [hnorm, bc, Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hb0 _ _)] using hcomplex
    have hconvert := sqrt_mul_sum_entry_rpow_root_le_two_row_profiles b hb0 hp
    have hA : 0 ≤ (∑ i, (∑ j, b i j ^ 2) ^ (p / 2)) ^ p⁻¹ :=
      Real.rpow_nonneg (Finset.sum_nonneg fun i _ =>
        Real.rpow_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _) _) _
    have hB : 0 ≤ Real.sqrt p * (∑ i, ‖b i‖ ^ p) ^ p⁻¹ :=
      mul_nonneg (Real.sqrt_nonneg p)
        (Real.rpow_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _) _)
    nlinarith

end NLAlib
