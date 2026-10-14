import NLAlib.Matrix.Spectral.NumericalRange
import NLAlib.ForMathlib.Analysis.Convex.SphereImage
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Convexity of the two-dimensional numerical range

Complex unit vectors give the Bloch sphere in three real coordinates. The
quadratic form is an affine real-linear map on that sphere. Rank-nullity
and the sphere/ball image lemma give convexity, including degenerate ellipses.
Source: Horn–Johnson (1991), Chapter 1; operator derivations, (S10).
Atlas: `field-of-values-def` (two-dimensional convexity helper).
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

private def blochVector (x : Fin 2 → ℂ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![2 * (star (x 0) * x 1).re,
    2 * (star (x 0) * x 1).im, ‖x 0‖ ^ 2 - ‖x 1‖ ^ 2]

private def blochMap (B : Matrix (Fin 2) (Fin 2) ℂ) :
    EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℂ where
  toFun r := ∑ i : Fin 3, r i • ![(B 0 1 + B 1 0) / 2,
    Complex.I * (B 0 1 - B 1 0) / 2, (B 0 0 - B 1 1) / 2] i
  map_add' r s := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a r := by simp [Finset.smul_sum, mul_assoc]

private theorem norm_sq_complex (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

private theorem norm_blochVector_eq_one {x : Fin 2 → ℂ}
    (hx : ‖WithLp.toLp 2 x‖ = 1) : ‖blochVector x‖ = 1 := by
  have hs : ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 = 1 := by
    have h := EuclideanSpace.norm_sq_eq (WithLp.toLp 2 x)
    simpa [hx, Fin.sum_univ_two] using h.symm
  have hc := norm_sq_complex (star (x 0) * x 1)
  rw [norm_mul, norm_star, mul_pow] at hc
  have hb : ‖blochVector x‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ i : Fin 3, ‖![2 * (star (x 0) * x 1).re,
      2 * (star (x 0) * x 1).im, ‖x 0‖ ^ 2 - ‖x 1‖ ^ 2] i‖ ^ 2) = 1
    simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero, Real.norm_eq_abs, sq_abs]
    nlinarith
  nlinarith [norm_nonneg (blochVector x)]

private theorem quadForm_eq_affine_bloch {x : Fin 2 → ℂ}
    (hx : ‖WithLp.toLp 2 x‖ = 1) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    quadForm B x = (B 0 0 + B 1 1) / 2 + blochMap B (blochVector x) := by
  have hs : ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 = 1 := by
    have h := EuclideanSpace.norm_sq_eq (WithLp.toLp 2 x)
    simpa [hx, Fin.sum_univ_two] using h.symm
  have hsC : (‖x 0‖ ^ 2 : ℂ) + (‖x 1‖ ^ 2 : ℂ) = 1 := by
    exact_mod_cast hs
  have hself (z : ℂ) : star z * z = (‖z‖ ^ 2 : ℂ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  let c := star (x 0) * x 1
  have hq : quadForm B x = (‖x 0‖ ^ 2 : ℂ) * B 0 0 +
      (‖x 1‖ ^ 2 : ℂ) * B 1 1 + c * B 0 1 + star c * B 1 0 := by
    simp only [quadForm, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.star_apply,
      c, star_mul, star_star]
    linear_combination B 0 0 * hself (x 0) + B 1 1 * hself (x 1)
  have hc : c = (c.re : ℂ) + Complex.I * (c.im : ℂ) := by
    simpa [mul_comm] using (Complex.re_add_im c).symm
  have hcs : star c = (c.re : ℂ) - Complex.I * (c.im : ℂ) := by
    rw [hc]
    simp [star_mul, sub_eq_add_neg]
    ring
  rw [hq]
  change (‖x 0‖ ^ 2 : ℂ) * B 0 0 + (‖x 1‖ ^ 2 : ℂ) * B 1 1 + c * B 0 1 +
    star c * B 1 0 = (B 0 0 + B 1 1) / 2 +
      ∑ i : Fin 3, (blochVector x) i • ![(B 0 1 + B 1 0) / 2,
        Complex.I * (B 0 1 - B 1 0) / 2, (B 0 0 - B 1 1) / 2] i
  simp only [blochVector, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero, Complex.real_smul]
  change (‖x 0‖ ^ 2 : ℂ) * B 0 0 + (‖x 1‖ ^ 2 : ℂ) * B 1 1 + c * B 0 1 +
    star c * B 1 0 = (B 0 0 + B 1 1) / 2 +
      (((2 * c.re : ℝ) : ℂ) * ((B 0 1 + B 1 0) / 2) +
      (((2 * c.im : ℝ) : ℂ) * (Complex.I * (B 0 1 - B 1 0) / 2) +
      ((‖x 0‖ ^ 2 - ‖x 1‖ ^ 2 : ℝ) : ℂ) * ((B 0 0 - B 1 1) / 2)))
  push_cast
  linear_combination ((B 0 0 + B 1 1) / 2) * hsC + B 0 1 * hc + B 1 0 * hcs

private theorem exists_unit_blochVector_eq (r : EuclideanSpace ℝ (Fin 3))
    (hr : ‖r‖ = 1) :
    ∃ x : Fin 2 → ℂ, ‖WithLp.toLp 2 x‖ = 1 ∧ blochVector x = r := by
  have hs : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 = 1 := by
    have h := EuclideanSpace.norm_sq_eq r
    rw [hr] at h
    simpa [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs, add_assoc] using h.symm
  have hr2 : -1 ≤ r 2 := by nlinarith [sq_nonneg (r 0), sq_nonneg (r 1)]
  by_cases hbot : r 2 = -1
  · have hzero0 : r 0 = 0 := by nlinarith [sq_nonneg (r 1)]
    have hzero1 : r 1 = 0 := by nlinarith [sq_nonneg (r 0)]
    refine ⟨![0, 1], ?_, ?_⟩
    · have hnorm : ‖(WithLp.toLp 2 ![0, (1 : ℂ)] : EuclideanSpace ℂ (Fin 2))‖ ^ 2 = 1 := by
        simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      nlinarith [norm_nonneg (WithLp.toLp 2 ![0, (1 : ℂ)] : EuclideanSpace ℂ (Fin 2))]
    · ext i
      fin_cases i <;> simp [blochVector, hzero0, hzero1, hbot]
  · have hr2gt : -1 < r 2 := lt_of_le_of_ne hr2 (Ne.symm hbot)
    let u : ℝ := Real.sqrt ((1 + r 2) / 2)
    have hu : 0 < u := Real.sqrt_pos.mpr (by dsimp; linarith)
    have hu0 : u ≠ 0 := hu.ne'
    have huSq : u ^ 2 = (1 + r 2) / 2 := Real.sq_sqrt (by linarith)
    have hden : (2 * u) ^ 2 = 2 * (1 + r 2) := by nlinarith
    let v : ℂ := (r 0 / (2 * u) : ℝ) + Complex.I * (r 1 / (2 * u) : ℝ)
    have hv : ‖v‖ ^ 2 = (1 - r 2) / 2 := by
      rw [norm_sq_complex]
      simp only [v, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        zero_mul, mul_zero, one_mul, zero_add, add_zero, sub_zero]
      rw [div_pow, div_pow, ← add_div, hden]
      field_simp [show 1 + r 2 ≠ 0 by linarith]
      nlinarith [hs]
    have huNorm : ‖(u : ℂ)‖ ^ 2 = (1 + r 2) / 2 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using huSq
    let x : Fin 2 → ℂ := ![(u : ℂ), v]
    have hx : ‖WithLp.toLp 2 x‖ = 1 := by
      have hxSq : ‖WithLp.toLp 2 x‖ ^ 2 = 1 := by
        rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
        change ‖(u : ℂ)‖ ^ 2 + ‖v‖ ^ 2 = 1
        rw [huNorm, hv]
        ring
      nlinarith [norm_nonneg (WithLp.toLp 2 x)]
    refine ⟨x, hx, ?_⟩
    ext i
    fin_cases i
    · change 2 * (star (u : ℂ) * v).re = r 0
      simp only [v, Complex.star_def, Complex.conj_ofReal,
        Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        zero_mul, mul_zero, one_mul, zero_add, add_zero, sub_zero]
      field_simp [hu0]
    · change 2 * (star (u : ℂ) * v).im = r 1
      simp only [v, Complex.star_def, Complex.conj_ofReal,
        Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        zero_mul, mul_zero, one_mul, zero_add, add_zero, sub_zero]
      field_simp [hu0]
    · change ‖(u : ℂ)‖ ^ 2 - ‖v‖ ^ 2 = r 2
      rw [huNorm, hv]
      ring

private theorem numericalRange_eq_affine_bloch_image (B : Matrix (Fin 2) (Fin 2) ℂ) :
    numericalRange B = (fun z => (B 0 0 + B 1 1) / 2 + z) ''
      (blochMap B '' Metric.sphere 0 1) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨blochMap B (blochVector x), ⟨blochVector x, ?_, rfl⟩, ?_⟩
    · simpa only [Metric.mem_sphere, dist_zero_right] using norm_blochVector_eq_one hx
    · exact (quadForm_eq_affine_bloch hx B).symm
  · rintro ⟨w, ⟨r, hr, rfl⟩, rfl⟩
    have hnorm : ‖r‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hr
    obtain ⟨x, hx, hxr⟩ := exists_unit_blochVector_eq r hnorm
    refine ⟨x, hx, ?_⟩
    rw [quadForm_eq_affine_bloch hx B, hxr]

/-- The numerical range of every complex two-by-two matrix is convex,
including scalar matrices and degenerate ellipses. The Bloch sphere is an
affine image of a three-dimensional real unit sphere, whose linear image
equals a convex ball image because its kernel is nontrivial.
Source: Horn–Johnson (1991), Chapter 1; operator derivations, (S10).
atlas: field-of-values-def (partial) -/
theorem convex_numericalRange_two (B : Matrix (Fin 2) (Fin 2) ℂ) :
    Convex ℝ (numericalRange B) := by
  have hker : LinearMap.ker (blochMap B) ≠ ⊥ := by
    intro h
    have hdim := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp h)
    rw [finrank_euclideanSpace_fin, Complex.finrank_real_complex] at hdim
    omega
  rw [numericalRange_eq_affine_bloch_image]
  exact ((blochMap B).convex_image_sphere_of_ker_ne_bot hker).translate _

end NLAlib
