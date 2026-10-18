import NLAlib.Matrix.Functions.MatrixDysonBounds
import Mathlib.Analysis.SpecificLimits.Basic

/-! # The exterior norm barrier for matrix Dyson solutions

The quadratic norm inequality, continuity along actual vertical lines,
and decay at imaginary infinity select the small branch. Its imaginary
part bound has the exact radius `‖A‖ + 2 * sqrt ‖S‖`.
Source: Ajanki--Erdős--Krüger, Proposition 2.1, equations (4.3)--(4.8).
-/

noncomputable section
open Matrix Filter Set
open scoped Topology Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The polynomial Dyson identity gives a quadratic inequality for the
actual operator norm; no scalar branch or spectral representation is assumed. -/
theorem mul_specNorm_le_one_add_of_matrixDyson
    (A : Matrix n n ℂ) (S : Matrix n n ℂ →L[ℂ] Matrix n n ℂ)
    {z : ℂ} (X : Matrix n n ℂ)
    (heq : (z • 1 - A + S X) * X = -1) {c : ℝ} (hc : c ≤ |z.re|) :
    (c - specNorm A) * specNorm X ≤ 1 + ‖S‖ * specNorm X ^ 2 := by
  have hsum : z • X - A * X + S X * X = -1 := by
    simpa only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] using heq
  have hzX : z • X = -1 + A * X - S X * X := by
    calc
      _ = (z • X - A * X + S X * X) + A * X - S X * X := by abel
      _ = _ := by rw [hsum]
  have hnorm : ‖z‖ * ‖X‖ ≤ 1 + ‖A‖ * ‖X‖ + ‖S‖ * ‖X‖ ^ 2 := by
    calc
      _ = ‖z • X‖ := (norm_smul z X).symm
      _ = ‖-1 + A * X - S X * X‖ := congrArg norm hzX
      _ ≤ ‖-1 + A * X‖ + ‖S X * X‖ := norm_sub_le _ _
      _ ≤ ‖(-1 : Matrix n n ℂ)‖ + ‖A * X‖ + ‖S X * X‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ ≤ 1 + ‖A‖ * ‖X‖ + (‖S‖ * ‖X‖) * ‖X‖ := by
        gcongr
        · simp
        · exact norm_mul_le _ _
        · exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (S.le_opNorm X) (norm_nonneg X))
      _ = _ := by ring
  have hc' : c ≤ ‖z‖ := hc.trans (Complex.abs_re_le_norm z)
  have hm := mul_le_mul_of_nonneg_right hc' (norm_nonneg X)
  change (c - ‖A‖) * ‖X‖ ≤ 1 + ‖S‖ * ‖X‖ ^ 2
  nlinarith

omit [Nonempty n] in
/-- Along any fixed vertical line, imaginary coercivity forces norm decay. -/
theorem tendsto_specNorm_matrixDyson_vertical
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (S : Matrix n n ℂ →L[ℂ] Matrix n n ℂ)
    (hS : ∀ X : Matrix n n ℂ, 0 ≤ X → 0 ≤ S X)
    (M : ℂ → Matrix n n ℂ)
    (hpos : ∀ z : ℂ, 0 < z.im → 0 ≤ (imaginaryPart (M z) : Matrix n n ℂ))
    (heq : ∀ z : ℂ, 0 < z.im → (z • 1 - A + S (M z)) * M z = -1)
    (x : ℝ) :
    Tendsto (fun y : ℝ => specNorm (M ((x : ℂ) + y * Complex.I))) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => specNorm_nonneg _))
    _ tendsto_inv_atTop_zero
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  have hz : 0 < ((x : ℂ) + y * Complex.I).im := by simpa using hy
  simpa using specNorm_le_inv_im_of_matrixDyson A hA S hS hz _ (hpos _ hz) (heq _ hz)

/-- Continuity and the actual Dyson equation select the small norm branch
outside every radius strictly larger than `‖A‖ + 2 sqrt ‖S‖`. -/
theorem specNorm_lt_two_div_of_matrixDyson_exterior
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (S : Matrix n n ℂ →L[ℂ] Matrix n n ℂ)
    (hS : ∀ X : Matrix n n ℂ, 0 ≤ X → 0 ≤ S X)
    (M : ℂ → Matrix n n ℂ)
    (hM : ContinuousOn M {z : ℂ | 0 < z.im})
    (hpos : ∀ z : ℂ, 0 < z.im → 0 ≤ (imaginaryPart (M z) : Matrix n n ℂ))
    (heq : ∀ z : ℂ, 0 < z.im → (z • 1 - A + S (M z)) * M z = -1)
    {c : ℝ} (hc : specNorm A + 2 * Real.sqrt ‖S‖ < c)
    {z : ℂ} (hz : 0 < z.im) (hcz : c ≤ |z.re|) :
    specNorm (M z) < 2 / (c - specNorm A) := by
  have hδ : 0 < c - specNorm A := by
    have := Real.sqrt_nonneg ‖S‖
    linarith
  have hgap : 4 * ‖S‖ < (c - specNorm A) ^ 2 := by
    have hs := Real.sq_sqrt (norm_nonneg S)
    have hs0 := Real.sqrt_nonneg ‖S‖
    nlinarith
  have hf : ContinuousOn (fun y : ℝ => specNorm (M ((z.re : ℂ) + y * Complex.I))) (Ioi 0) := by
    apply (hM.comp (by fun_prop) (fun y hy => by simpa using hy)).norm
  have hb := hf.lt_two_div_of_quadratic
    (tendsto_specNorm_matrixDyson_vertical A hA S hS M hpos heq z.re)
    hδ hgap (fun y hy => mul_specNorm_le_one_add_of_matrixDyson A S
      (M ((z.re : ℂ) + y * Complex.I)) (heq _ (by simpa using hy)) (by simpa using hcz)) hz
  simpa only [Complex.re_add_im] using hb

/-- Taking norms in the proved imaginary Dyson congruence retains the
variance-map operator norm, without replacing it by a trace estimate. -/
theorem norm_imaginaryPart_le_matrixDyson_quadratic
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (S : Matrix n n ℂ →L[ℂ] Matrix n n ℂ)
    (hS : ∀ X : Matrix n n ℂ, 0 ≤ X → 0 ≤ S X)
    {z : ℂ} (hz : 0 ≤ z.im) (X : Matrix n n ℂ)
    (heq : (z • 1 - A + S X) * X = -1) :
    ‖(imaginaryPart X : Matrix n n ℂ)‖ ≤
      specNorm X ^ 2 * (z.im + ‖S‖ * ‖(imaginaryPart X : Matrix n n ℂ)‖) := by
  have hid := imaginaryPart_eq_matrixDyson_congruence A hA S hS z X heq
  calc
    _ = ‖Xᴴ * (z.im • 1 + S (imaginaryPart X : Matrix n n ℂ)) * X‖ := congrArg norm hid
    _ ≤ (‖Xᴴ‖ * ‖z.im • 1 + S (imaginaryPart X : Matrix n n ℂ)‖) * ‖X‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg X))
    _ ≤ (‖X‖ * (z.im + ‖S‖ * ‖(imaginaryPart X : Matrix n n ℂ)‖)) * ‖X‖ := by
      rw [Matrix.l2_opNorm_conjTranspose]
      gcongr
      calc
        _ ≤ ‖z.im • (1 : Matrix n n ℂ)‖ + ‖S (imaginaryPart X : Matrix n n ℂ)‖ := norm_add_le _ _
        _ ≤ z.im + ‖S‖ * ‖(imaginaryPart X : Matrix n n ℂ)‖ := by
          simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg hz] using
            add_le_add_left (S.le_opNorm (imaginaryPart X : Matrix n n ℂ)) z.im
    _ = _ := by dsimp [specNorm]; ring

/-- The exterior imaginary-part estimate with the exact support radius.
All bounds are derived from the equation, positivity, and continuity.
atlas: matrix-dyson-stieltjes-representation (partial) -/
theorem norm_imaginaryPart_le_of_matrixDyson_exterior
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (S : Matrix n n ℂ →L[ℂ] Matrix n n ℂ)
    (hS : ∀ X : Matrix n n ℂ, 0 ≤ X → 0 ≤ S X)
    (M : ℂ → Matrix n n ℂ)
    (hM : ContinuousOn M {z : ℂ | 0 < z.im})
    (hpos : ∀ z : ℂ, 0 < z.im → 0 ≤ (imaginaryPart (M z) : Matrix n n ℂ))
    (heq : ∀ z : ℂ, 0 < z.im → (z • 1 - A + S (M z)) * M z = -1)
    {c : ℝ} (hc : specNorm A + 2 * Real.sqrt ‖S‖ < c)
    {z : ℂ} (hz : 0 < z.im) (hcz : c ≤ |z.re|) :
    ‖(imaginaryPart (M z) : Matrix n n ℂ)‖ ≤
      (4 / ((c - specNorm A) ^ 2 - 4 * ‖S‖)) * z.im := by
  have hδ : 0 < c - specNorm A := by
    have := Real.sqrt_nonneg ‖S‖
    linarith
  have hgap : 0 < (c - specNorm A) ^ 2 - 4 * ‖S‖ := by
    have hs := Real.sq_sqrt (norm_nonneg S)
    have hs0 := Real.sqrt_nonneg ‖S‖
    nlinarith
  have hr := specNorm_lt_two_div_of_matrixDyson_exterior A hA S hS M hM hpos heq hc hz hcz
  have hsq : specNorm (M z) ^ 2 ≤ 4 / (c - specNorm A) ^ 2 := by
    have h := pow_le_pow_left₀ (specNorm_nonneg (M z)) hr.le 2
    simpa only [div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using h
  have hq := norm_imaginaryPart_le_matrixDyson_quadratic A hA S hS hz.le (M z) (heq z hz)
  have hb : ‖(imaginaryPart (M z) : Matrix n n ℂ)‖ ≤
      (4 / (c - specNorm A) ^ 2) *
        (z.im + ‖S‖ * ‖(imaginaryPart (M z) : Matrix n n ℂ)‖) :=
    hq.trans (mul_le_mul_of_nonneg_right hsq (by positivity))
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg (c - specNorm A))
  have he : (c - specNorm A) ^ 2 *
      ((4 / (c - specNorm A) ^ 2) *
        (z.im + ‖S‖ * ‖(imaginaryPart (M z) : Matrix n n ℂ)‖)) =
      4 * (z.im + ‖S‖ * ‖(imaginaryPart (M z) : Matrix n n ℂ)‖) := by
    field_simp
  rw [he] at hm
  rw [div_mul_eq_mul_div, le_div_iff₀ hgap]
  nlinarith

end NLAlib
