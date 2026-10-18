import NLAlib.Matrix.Functions.MatrixDysonBounds

/-!
# Matrix Dyson normalization at imaginary infinity

The polynomial Dyson identity controls `zM(z)+I` by its linear and
quadratic norm terms. The proved upper-half-plane inverse bound then
forces the genuine matrix limit `iy M(iy) → -I`, without any analyticity
or representation hypothesis.
Source: Ajanki--Erdos--Kruger (2019), Proposition 2.1.
-/

noncomputable section
open Matrix Filter Set
open scoped Topology Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual polynomial Dyson identity bounds the normalization error
by the linear and quadratic matrix norm terms. Positivity is unnecessary
for this algebraic estimate. -/
theorem specNorm_matrixDyson_normalization_error_le
    (A : Matrix n n ℂ) (S : Matrix n n ℂ →L[ℂ] Matrix n n ℂ)
    (z : ℂ) (X : Matrix n n ℂ)
    (heq : (z • 1 - A + S X) * X = -1) :
    specNorm (z • X + 1) ≤ specNorm A * specNorm X + ‖S‖ * specNorm X ^ 2 := by
  have he : z • X + 1 = A * X - S X * X := by
    have h := heq
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] at h
    calc
      z • X + 1 = (z • X - A * X + S X * X) + A * X - S X * X + 1 := by abel
      _ = -1 + A * X - S X * X + 1 := by rw [h]
      _ = A * X - S X * X := by abel
  have hSX : ‖S X‖ ≤ ‖S‖ * ‖X‖ := S.le_opNorm X
  simp only [specNorm_eq_norm]
  rw [he]
  calc
    _ ≤ ‖A * X‖ + ‖S X * X‖ := norm_sub_le _ _
    _ ≤ ‖A‖ * ‖X‖ + ‖S X‖ * ‖X‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ ‖A‖ * ‖X‖ + (‖S‖ * ‖X‖) * ‖X‖ :=
      by gcongr
    _ = _ := by ring

/-- On the positive imaginary axis the Dyson normalization error is
bounded by `‖A‖/y + ‖S‖/y²`, derived entirely from the equation. -/
theorem specNorm_matrixDyson_normalization_error_mul_I_le
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (S : Matrix n n ℂ →L[ℂ] Matrix n n ℂ)
    (hS : ∀ X : Matrix n n ℂ, 0 ≤ X → 0 ≤ S X)
    {y : ℝ} (hy : 0 < y) (X : Matrix n n ℂ)
    (hpos : 0 ≤ (imaginaryPart X : Matrix n n ℂ))
    (heq : (((y : ℂ) * Complex.I) • 1 - A + S X) * X = -1) :
    specNorm (((y : ℂ) * Complex.I) • X + 1) ≤
      specNorm A * y⁻¹ + ‖S‖ * (y⁻¹) ^ 2 := by
  have hz : 0 < ((y : ℂ) * Complex.I).im := by simpa using hy
  have hX : specNorm X ≤ y⁻¹ := by
    simpa using specNorm_le_inv_im_of_matrixDyson A hA S hS hz X hpos heq
  apply (specNorm_matrixDyson_normalization_error_le A S _ X heq).trans
  have hnX : 0 ≤ specNorm X := by simp only [specNorm_eq_norm]; positivity
  have hsq : specNorm X ^ 2 ≤ (y⁻¹) ^ 2 := pow_le_pow_left₀ hnX hX 2
  exact add_le_add
    (mul_le_mul_of_nonneg_left hX (by simp only [specNorm_eq_norm]; positivity))
    (mul_le_mul_of_nonneg_left hsq (norm_nonneg S))

/-- A positive-imaginary matrix Dyson solution has the exact Stieltjes
normalization `iy M(iy) → -I`. No normalization, holomorphy, scalar measure,
or compact-support assumption is supplied to this theorem.
Source: Ajanki--Erdos--Kruger (2019), Proposition 2.1.
This theorem supplies the normalization component.
atlas: matrix-dyson-stieltjes-representation (partial) -/
theorem tendsto_mul_I_smul_matrixDyson
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (S : Matrix n n ℂ →L[ℂ] Matrix n n ℂ)
    (hS : ∀ X : Matrix n n ℂ, 0 ≤ X → 0 ≤ S X)
    (M : ℂ → Matrix n n ℂ)
    (hpos : ∀ z : ℂ, 0 < z.im → 0 ≤ (imaginaryPart (M z) : Matrix n n ℂ))
    (heq : ∀ z : ℂ, 0 < z.im → (z • 1 - A + S (M z)) * M z = -1) :
    Tendsto (fun y : ℝ => ((y : ℂ) * Complex.I) • M ((y : ℂ) * Complex.I))
      atTop (𝓝 (-1)) := by
  have hinv : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hbound : Tendsto (fun y : ℝ => specNorm A * y⁻¹ + ‖S‖ * (y⁻¹) ^ 2)
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using
      (hinv.const_mul (specNorm A)).add ((hinv.pow 2).const_mul ‖S‖)
  have hnorm : Tendsto (fun y : ℝ =>
      ‖((y : ℂ) * Complex.I) • M ((y : ℂ) * Complex.I) + 1‖) atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hbound
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    have hz : 0 < ((y : ℂ) * Complex.I).im := by simpa using hy
    exact specNorm_matrixDyson_normalization_error_mul_I_le A hA S hS hy _
      (hpos _ hz) (heq _ hz)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [sub_neg_eq_add] using hnorm

end NLAlib
