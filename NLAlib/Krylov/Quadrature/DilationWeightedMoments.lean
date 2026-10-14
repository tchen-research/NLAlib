import NLAlib.Krylov.Quadrature.DilationMoments

/-! # The weighted odd reduction of a rectangular dilation

The squared-variable pushforward of `x² dμ` for the actual dilation at `(u,0)` is
the right normal matrix's spectral measure at `Bᵀu`. This supplies the native measure
used by the odd orthogonal-polynomial reduction.
-/

noncomputable section
open Matrix Polynomial MeasureTheory Finset
open scoped Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Rectangular multiplication intertwines all powers of the two normal matrices. -/
theorem pow_mul_transpose_mul_eq_mul_pow (B : Matrix m n ℝ) (k : ℕ) :
    (B * Bᵀ) ^ k * B = B * (Bᵀ * B) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    calc
      ((B * Bᵀ) ^ k * (B * Bᵀ)) * B =
          ((B * Bᵀ) ^ k * B) * (Bᵀ * B) := by simp only [Matrix.mul_assoc]
      _ = B * (Bᵀ * B) ^ k * (Bᵀ * B) := by rw [ih]
      _ = _ := Matrix.mul_assoc _ _ _

/-- The next left-normal moment is the right-normal moment at the transposed seed. -/
theorem dotProduct_pow_succ_left_normal_eq (B : Matrix m n ℝ) (u : m → ℝ) (k : ℕ) :
    u ⬝ᵥ ((B * Bᵀ) ^ (k + 1) *ᵥ u) =
      (Bᵀ *ᵥ u) ⬝ᵥ ((Bᵀ * B) ^ k *ᵥ (Bᵀ *ᵥ u)) := by
  have hp : (B * Bᵀ) ^ (k + 1) = B * ((Bᵀ * B) ^ k * Bᵀ) := by
    rw [pow_succ, ← Matrix.mul_assoc, pow_mul_transpose_mul_eq_mul_pow, Matrix.mul_assoc]
  rw [hp, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    ← Matrix.mulVec_mulVec]

/-- The weighted even polynomial form of the actual dilation equals the right normal
matrix form at `Bᵀu`. Source: Gautschi (2004), Section 2.2; operator derivations (OP19).
atlas: symmetric-measure-even-odd-reduction (partial) -/
theorem polynomialIntegral_spectralMeasure_dilation_X_sq_mul_comp_X_sq
    (B : Matrix m n ℝ) (u : m → ℝ) (p : ℝ[X]) :
    polynomialIntegral (spectralMeasure (isHermitian_dilation B) (Sum.elim u 0))
      (hasPolynomialMoments_spectralMeasure _ _) (X ^ 2 * p.comp (X ^ 2)) =
    polynomialIntegral (spectralMeasure (isHermitian_conjTranspose_mul_self B) (Bᵀ *ᵥ u))
      (hasPolynomialMoments_spectralMeasure _ _) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [add_comp, mul_add, map_add] using congrArg₂ (· + ·) hp hq
  | monomial k c =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, pow_comp, X_comp]
    rw [show (X ^ 2 * (C c * (X ^ 2) ^ k) : ℝ[X]) = C c * X ^ (2 * (k + 1)) by
      rw [← pow_mul, mul_left_comm, ← pow_add, show 2 + 2 * k = 2 * (k + 1) by omega]]
    rw [C_mul', C_mul', map_smul, map_smul]
    congr 1
    simp only [polynomialIntegral_apply, eval_pow, eval_X]
    rw [integral_pow_two_mul_spectralMeasure_dilation, integral_pow_spectralMeasure,
      integral_pow_spectralMeasure, conjTranspose_eq_transpose_of_trivial]
    exact dotProduct_pow_succ_left_normal_eq B u k

/-- The native weighted squared pushforward of the actual dilation measure is exactly
the right-normal spectral measure at `Bᵀu`, including zero seeds and singular blocks.
Source: Gautschi (2004), Section 2.2; operator derivations (OP19).
atlas: symmetric-measure-even-odd-reduction (partial) -/
theorem map_sq_withDensity_sq_spectralMeasure_dilation (B : Matrix m n ℝ) (u : m → ℝ) :
    Measure.map (fun x : ℝ => x ^ 2)
      ((spectralMeasure (isHermitian_dilation B) (Sum.elim u 0)).withDensity
        (fun x : ℝ => ENNReal.ofReal (x ^ 2))) =
      spectralMeasure (isHermitian_conjTranspose_mul_self B) (Bᵀ *ᵥ u) := by
  let μ := spectralMeasure (isHermitian_dilation B) (Sum.elim u 0)
  let ν := μ.withDensity (fun x : ℝ => ENNReal.ofReal (x ^ 2))
  let hμ := hasPolynomialMoments_spectralMeasure (isHermitian_dilation B) (Sum.elim u 0)
  let hν := hasPolynomialMoments_withDensity_sq hμ
  let : IsFiniteMeasure ν := (integrable_const_iff_isFiniteMeasure (by norm_num : (1 : ℝ) ≠ 0)).mp
    (by simpa only [eval_one] using hν 1)
  let s := univ.image (isHermitian_dilation B).eigenvalues
  let t := univ.image (isHermitian_conjTranspose_mul_self B).eigenvalues
  have hsμ : ∀ᵐ x ∂μ, x ∈ s := by
    have hr : ∀ᵐ x ∂μ, x ∈ Set.range (isHermitian_dilation B).eigenvalues := by
      rw [ae_iff]
      exact spectralMeasure_compl_range_eigenvalues _ _
    filter_upwards [hr] with x hx
    obtain ⟨i, rfl⟩ := hx
    exact mem_image.mpr ⟨i, mem_univ _, rfl⟩
  have hsν : ∀ᵐ x ∂ν, x ∈ s := by
    apply (ae_withDensity_iff (by fun_prop)).mpr
    filter_upwards [hsμ] with x hx _
    exact hx
  have ht : ∀ᵐ x ∂spectralMeasure (isHermitian_conjTranspose_mul_self B) (Bᵀ *ᵥ u), x ∈ t := by
    have hr : ∀ᵐ x ∂spectralMeasure (isHermitian_conjTranspose_mul_self B) (Bᵀ *ᵥ u),
        x ∈ Set.range (isHermitian_conjTranspose_mul_self B).eigenvalues := by
      rw [ae_iff]
      exact spectralMeasure_compl_range_eigenvalues _ _
    filter_upwards [hr] with x hx
    obtain ⟨i, rfl⟩ := hx
    exact mem_image.mpr ⟨i, mem_univ _, rfl⟩
  apply measure_eq_of_integral_eval_eq_of_finite_carrier (s.image (fun x => x ^ 2) ∪ t)
  · apply (ae_map_iff (by fun_prop) ((s.image (fun x => x ^ 2) ∪ t).finite_toSet.measurableSet)).mpr
    filter_upwards [hsν] with x hx
    exact mem_union_left _ (mem_image.mpr ⟨x, hx, rfl⟩)
  · filter_upwards [ht] with x hx
    exact mem_union_right _ hx
  · intro p
    change polynomialIntegral (Measure.map (fun x : ℝ => x ^ 2) ν)
      (hasPolynomialMoments_map_sq hν) p = _
    rw [polynomialIntegral_map_sq ν hν, polynomialIntegral_withDensity_sq μ hμ]
    exact polynomialIntegral_spectralMeasure_dilation_X_sq_mul_comp_X_sq B u p

end NLAlib
