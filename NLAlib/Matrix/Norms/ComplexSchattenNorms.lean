import NLAlib.Matrix.Norms.Realification
import NLAlib.Matrix.Norms.SchattenNorms
import NLAlib.Matrix.Norms.SchattenFrames

/-!
# Complex Schatten triangle inequality and real homogeneity

Realification transfers the real Schatten norm axioms. Its exact
dimension-doubling factor cancels, so the triangle inequality has constant
one. These results equip the complex matrix space, regarded as a real
vector space, with its actual finite Schatten norm.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The native finite Schatten norm on complex square matrices satisfies the
triangle inequality at every real exponent at least one. -/
theorem schattenNormReal_add_le_complex (A B : Matrix n n ℂ) {p : ℝ} (hp : 1 ≤ p) :
    schattenNormReal (A + B) p ≤ schattenNormReal A p + schattenNormReal B p := by
  have h := schattenNormReal_add_le (matrixRealification A) (matrixRealification B) hp
  rw [← matrixRealification_add, schattenNormReal_matrixRealification,
    schattenNormReal_matrixRealification, schattenNormReal_matrixRealification,
    ← mul_add] at h
  exact (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)).mp h

/-- Real scalar multiplication is absolutely homogeneous for the native
finite Schatten norm on complex matrices, with no extra constant. -/
theorem schattenNormReal_real_smul_complex (A : Matrix n n ℂ) (c : ℝ)
    {p : ℝ} (hp : 0 < p) :
    schattenNormReal (c • A) p = |c| * schattenNormReal A p := by
  have h := schattenNormReal_smul (matrixRealification A) c hp
  rw [← matrixRealification_smul, schattenNormReal_matrixRealification,
    schattenNormReal_matrixRealification] at h
  have hc := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (1 / p)).ne'
  apply (mul_left_cancel₀ hc)
  calc
    (2 : ℝ) ^ (1 / p) * schattenNormReal (c • A) p =
        |c| * ((2 : ℝ) ^ (1 / p) * schattenNormReal A p) := h
    _ = _ := by ring

/-- Complex scalar multiplication is absolutely homogeneous for every
positive finite Schatten exponent, with its exact native normalization. -/
theorem schattenNormReal_smul_complex (A : Matrix n n ℂ) (c : ℂ)
    {p : ℝ} (hp : 0 < p) :
    schattenNormReal (c • A) p = ‖c‖ * schattenNormReal A p := by
  obtain ⟨U, V, hA⟩ := exists_isSVD A
  let d : Fin (Fintype.card n) → ℂ := fun i => (singularValues A i : ℂ)
  have hd : (rectDiag (singularValues A) :
      Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ) = Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [d, rectDiag_apply_ofReal]
    · have hval : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      simp [d, rectDiag_apply_ofReal, hij, hval]
  have hnorm : schattenNormReal A p =
      (∑ i : Fin (Fintype.card n), singularValues A i ^ p) ^ (1 / p) := by
    conv_lhs => rw [hA.eq, hd]
    rw [schattenNormReal_isometry_mul_mul_conjTranspose hA.conjTranspose_mul_left
      hA.conjTranspose_mul_right, schattenNormReal_diagonal_complex]
    simp only [d, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (singularValues_nonneg _ _)]
  have hscale : c • A = U * Matrix.diagonal (fun i => c * d i) * Vᴴ := by
    calc
      c • A = c • (U * rectDiag (singularValues A) * Vᴴ) := congrArg (c • ·) hA.eq
      _ = U * (c • rectDiag (singularValues A)) * Vᴴ := by
        rw [← Matrix.smul_mul, ← Matrix.mul_smul]
      _ = _ := by rw [hd, ← Matrix.diagonal_smul]; rfl
  rw [hscale, schattenNormReal_isometry_mul_mul_conjTranspose hA.conjTranspose_mul_left
    hA.conjTranspose_mul_right, schattenNormReal_diagonal_complex]
  simp_rw [norm_mul, d, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (singularValues_nonneg A _),
    Real.mul_rpow (norm_nonneg c) (singularValues_nonneg A _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (norm_nonneg c) p)
    (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (singularValues_nonneg A _) _),
    one_div, Real.rpow_rpow_inv (norm_nonneg c) hp.ne', hnorm, one_div]

end NLAlib
