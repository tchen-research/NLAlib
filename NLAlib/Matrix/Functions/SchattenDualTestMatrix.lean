import NLAlib.Matrix.Functions.SchattenDualTest
import NLAlib.Matrix.Norms.SchattenFrames
import NLAlib.Matrix.Norms.SchattenNormalization

/-!
# Matrix analytic dual tests

Full singular frames turn the entire scalar coefficient functions into
matrix-valued tests with exact boundary norms and full trace attainment.
Source: Sutter--Berta--Tomamichel, arXiv:1604.03023v3, Appendix D.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The analytic dual tester in fixed full singular frames. The orientation
is chosen so that the scalar analytic pairing is `trace (T(z) * G(z))`. -/
def schattenDualTestMatrix
    (U V : Matrix n (Fin (Fintype.card n)) ℂ) (r p : ℝ)
    (w : Fin (Fintype.card n) → ℝ) (z : ℂ) : Matrix n n ℂ :=
  V * Matrix.diagonal (fun i => schattenDualTestCoefficient r p (w i) z) * Uᴴ

/-- The matrix tester is entire, including identically zero singular
coefficient directions. -/
@[fun_prop] theorem differentiable_schattenDualTestMatrix
    (U V : Matrix n (Fin (Fintype.card n)) ℂ) (r p : ℝ)
    (w : Fin (Fintype.card n) → ℝ) :
    Differentiable ℂ (schattenDualTestMatrix U V r p w) := by
  let L : (Fin (Fintype.card n) → ℂ) →ₗ[ℂ] Matrix n n ℂ :=
    { toFun := fun d => V * Matrix.diagonal d * Uᴴ
      map_add' := by
        intro a b
        change V * Matrix.diagonal (fun i => a i + b i) * Uᴴ = _
        rw [← Matrix.diagonal_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := by
        intro c d
        simp only [Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul,
          RingHom.id_apply] }
  have hc : Differentiable ℂ (fun z => fun i : Fin (Fintype.card n) =>
      schattenDualTestCoefficient r p (w i) z) :=
    differentiable_pi.mpr fun i => differentiable_schattenDualTestCoefficient r p (w i)
  have hL : Differentiable ℂ (fun d : Fin (Fintype.card n) → ℂ =>
      V * Matrix.diagonal d * Uᴴ) := by
    convert! L.toContinuousLinearMap.differentiable using 1
  exact hL.comp hc

/-- The matrix tester is continuous on the entire plane. -/
@[fun_prop] theorem continuous_schattenDualTestMatrix
    (U V : Matrix n (Fin (Fintype.card n)) ℂ) (r p : ℝ)
    (w : Fin (Fintype.card n) → ℝ) :
    Continuous (schattenDualTestMatrix U V r p w) :=
  (differentiable_schattenDualTestMatrix U V r p w).continuous

open scoped Matrix.Norms.L2Operator in
/-- On the closed strip, the analytic dual tester is a spectral contraction
whenever its singular coefficients lie in the unit interval. -/
theorem specNorm_schattenDualTestMatrix_le_one
    {U V : Matrix n (Fin (Fintype.card n)) ℂ}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) {r p : ℝ}
    (hr : 0 < r) (hp : 1 ≤ p) {w : Fin (Fintype.card n) → ℝ}
    (hw : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1) {z : ℂ} (hz : z.re ≤ 1) :
    specNorm (schattenDualTestMatrix U V r p w z) ≤ 1 := by
  rw [schattenDualTestMatrix,
    specNorm_mul_conjTranspose_right_of_hasOrthonormalCols hU,
    specNorm_mul_left_of_hasOrthonormalCols hV,
    specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i =>
    norm_schattenDualTestCoefficient_le_one hr hp (hw i) hz

/-- The left boundary test has nuclear norm one for normalized source
power coefficients. -/
theorem nuclearNorm_schattenDualTestMatrix_left
    {U V : Matrix n (Fin (Fintype.card n)) ℂ}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) {r p : ℝ}
    (hr : 0 < r) (hp : 0 < p) {w : Fin (Fintype.card n) → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hpower : ∑ i, w i ^ (p / r) = 1) (t : ℝ) :
    nuclearNorm (schattenDualTestMatrix U V r p w ((t : ℂ) * Complex.I)) = 1 := by
  rw [← schattenNormReal_one, schattenDualTestMatrix,
    schattenNormReal_isometry_mul_mul_conjTranspose hV hU,
    schattenNormReal_diagonal_complex]
  simp only [Real.rpow_one, one_div_one]
  simp_rw [norm_schattenDualTestCoefficient_left hr hp (hw _) t]
  exact hpower

/-- At the right boundary, a finite conjugate test has Schatten norm one.
No singular coefficient is required to be positive. -/
theorem schattenNormReal_schattenDualTestMatrix_right
    {U V : Matrix n (Fin (Fintype.card n)) ℂ}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) {r p q : ℝ}
    (hr : 0 < r) (hpq : Real.HolderConjugate p q)
    {w : Fin (Fintype.card n) → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hpower : ∑ i, w i ^ (p / r) = 1) (t : ℝ) :
    schattenNormReal (schattenDualTestMatrix U V r p w (1 + (t : ℂ) * Complex.I)) q = 1 := by
  rw [schattenDualTestMatrix, schattenNormReal_isometry_mul_mul_conjTranspose hV hU,
    schattenNormReal_diagonal_complex]
  simp_rw [norm_schattenDualTestCoefficient_right_rpow hr hpq (hw _) t]
  rw [hpower, Real.one_rpow]

/-- The actual analytic dual tester attains the original Schatten norm at
the interpolation point in the full complex trace pairing. This includes
rank-deficient nonzero matrices. -/
theorem IsSVD.trace_schattenDualTestMatrix_center_mul
    {A : Matrix n n ℂ} {U V : Matrix n (Fin (Fintype.card n)) ℂ}
    (h : IsSVD A U V) {r p : ℝ} (hr : 0 < r) (hpr : r < p) (hA : A ≠ 0) :
    ((schattenDualTestMatrix U V r p
      (fun i => singularValues A i / schattenNormReal A (p / r)) (r : ℂ)) * A).trace =
      (schattenNormReal A (p / r) : ℂ) := by
  let b : ℕ → ℝ := fun i => (singularValues A i / schattenNormReal A (p / r)) ^ (p / r - 1)
  have hα : 1 < p / r := (one_lt_div hr).mpr hpr
  have hC := schattenNormReal_pos A (lt_trans zero_lt_one hα) hA
  have hdiag : Matrix.diagonal (fun i : Fin (Fintype.card n) =>
      schattenDualTestCoefficient r p (singularValues A i / schattenNormReal A (p / r)) (r : ℂ)) =
      (rectDiag b : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, rectDiag_apply_ofReal, ↓reduceIte]
      exact schattenDualTestCoefficient_center hr hpr
        (div_nonneg (singularValues_nonneg A i) hC.le)
    · have hval : (i : ℕ) ≠ j := fun he => hij (Fin.ext he)
      simp only [Matrix.diagonal_apply_ne _ hij, rectDiag_apply_ofReal, if_neg hval]
  have hcenter : schattenDualTestMatrix U V r p
      (fun i => singularValues A i / schattenNormReal A (p / r)) (r : ℂ) =
      (U * (rectDiag b : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ) * Vᴴ)ᴴ := by
    rw [schattenDualTestMatrix, hdiag, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, conjTranspose_rectDiag, Matrix.mul_assoc]
  rw [hcenter]
  have htr := congrArg star (h.trace_conjTranspose_mul_mul_rectDiag_mul_conjTranspose b)
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, RCLike.star_def, RCLike.conj_ofReal] at htr
  rw [htr]
  have hs := sum_singularValues_mul_normalized_rpow_eq_schattenNormReal A hα hA
  convert! congrArg Complex.ofReal hs using 1

end NLAlib
