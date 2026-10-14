import NLAlib.Krylov.Quadrature.MomentOrthogonality
import NLAlib.Matrix.Functions.HermitianCalculus
import NLAlib.Polynomial.OrthogonalPolynomials.SquareMeasures
import NLAlib.ForMathlib.MeasureTheory.FinitePolynomialMoments

/-! # Even and odd moments of the rectangular symmetric dilation

The actual block matrix `[0 B;Bᵀ 0]` at `(u,0)` has the even moments of `BBᵀ` at
`u` and zero odd moments. These finite block identities connect the native squared
measure reduction to rectangular matrix problems, including empty index types.
-/

noncomputable section
open Matrix Polynomial MeasureTheory Finset
open scoped Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Every even power of the actual rectangular Hermitian dilation is block diagonal.
Source: Gautschi (2004), Section 2.2; operator derivations (OP19).
atlas: symmetric-measure-even-odd-reduction (partial) -/
theorem dilation_pow_two_mul (B : Matrix m n ℝ) (k : ℕ) :
    dilation B ^ (2 * k) = fromBlocks ((B * Bᵀ) ^ k) 0 0 ((Bᵀ * B) ^ k) := by
  rw [pow_mul, dilation_sq, fromBlocks_diagonal_pow]
  simp only [conjTranspose_eq_transpose_of_trivial]

/-- Every odd power of the actual rectangular symmetric dilation has zero diagonal
blocks. Source: Gautschi (2004), Section 2.2; operator derivations (OP19).
atlas: symmetric-measure-even-odd-reduction (partial) -/
theorem dilation_pow_two_mul_add_one (B : Matrix m n ℝ) (k : ℕ) :
    dilation B ^ (2 * k + 1) =
      fromBlocks 0 (((B * Bᵀ) ^ k) * B) (((Bᵀ * B) ^ k) * Bᵀ) 0 := by
  rw [pow_succ, dilation_pow_two_mul, dilation, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    conjTranspose_eq_transpose_of_trivial]

/-- The actual dilation at the upper-block seed has the even spectral moments of the
left normal matrix. Source: Gautschi (2004), Section 2.2; operator derivations (OP19).
atlas: symmetric-measure-even-odd-reduction (partial) -/
theorem integral_pow_two_mul_spectralMeasure_dilation (B : Matrix m n ℝ) (u : m → ℝ)
    (k : ℕ) :
    (∫ x, x ^ (2 * k) ∂spectralMeasure (isHermitian_dilation B) (Sum.elim u 0)) =
      ∫ x, x ^ k ∂spectralMeasure (isHermitian_mul_conjTranspose_self B) u := by
  rw [integral_pow_spectralMeasure, integral_pow_spectralMeasure, dilation_pow_two_mul]
  simp [fromBlocks_mulVec, Function.comp_def, conjTranspose_eq_transpose_of_trivial,
    dotProduct, Fintype.sum_sum_type]

/-- All odd spectral moments vanish at a seed in only the upper block.
Source: Gautschi (2004), Section 2.2; operator derivations (OP19).
atlas: symmetric-measure-even-odd-reduction (partial) -/
theorem integral_pow_two_mul_add_one_spectralMeasure_dilation (B : Matrix m n ℝ)
    (u : m → ℝ) (k : ℕ) :
    (∫ x, x ^ (2 * k + 1) ∂spectralMeasure (isHermitian_dilation B) (Sum.elim u 0)) = 0 := by
  rw [integral_pow_spectralMeasure, dilation_pow_two_mul_add_one]
  simp [fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]

/-- Every even upper-seed polynomial form of the actual dilation is the polynomial
form of the left normal matrix. Source: Gautschi (2004), Section 2.2; (OP19).
atlas: symmetric-measure-even-odd-reduction (partial) -/
theorem polynomialIntegral_spectralMeasure_dilation_comp_X_sq (B : Matrix m n ℝ)
    (u : m → ℝ) (p : ℝ[X]) :
    polynomialIntegral (spectralMeasure (isHermitian_dilation B) (Sum.elim u 0))
      (hasPolynomialMoments_spectralMeasure _ _) (p.comp (X ^ 2)) =
    polynomialIntegral (spectralMeasure (isHermitian_mul_conjTranspose_self B) u)
      (hasPolynomialMoments_spectralMeasure _ _) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [add_comp, map_add] using congrArg₂ (· + ·) hp hq
  | monomial k c =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, pow_comp, X_comp,
      ← pow_mul, C_mul', C_mul', map_smul, map_smul]
    congr 1
    simp only [polynomialIntegral_apply, eval_pow, eval_X]
    simpa only [Nat.mul_comm] using integral_pow_two_mul_spectralMeasure_dilation B u k

/-- The upper-seed moment functional of the dilation is invariant under reflection.
Source: Gautschi (2004), Section 2.2; operator derivations (OP17)–(OP19).
atlas: symmetric-measure-even-odd-reduction (partial) -/
theorem polynomialIntegral_spectralMeasure_dilation_comp_neg_X (B : Matrix m n ℝ)
    (u : m → ℝ) (p : ℝ[X]) :
    polynomialIntegral (spectralMeasure (isHermitian_dilation B) (Sum.elim u 0))
      (hasPolynomialMoments_spectralMeasure _ _) (p.comp (-X)) =
    polynomialIntegral (spectralMeasure (isHermitian_dilation B) (Sum.elim u 0))
      (hasPolynomialMoments_spectralMeasure _ _) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [add_comp, map_add] using congrArg₂ (· + ·) hp hq
  | monomial k c =>
    simp only [polynomialIntegral_apply, eval_comp, eval_neg, eval_X, eval_monomial]
    rw [show (fun x : ℝ => c * (-x) ^ k) =
      (fun x => (c * (-1) ^ k) * x ^ k) by funext x; rw [neg_pow]; ring,
      integral_const_mul, integral_const_mul]
    by_cases hk : Even k
    · rw [hk.neg_one_pow, mul_one]
    · obtain ⟨l, rfl⟩ := Nat.not_even_iff_odd.mp hk
      rw [integral_pow_two_mul_add_one_spectralMeasure_dilation]
      simp

private theorem ae_mem_eigenvalue_finset {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (b : ι → ℝ) :
    ∀ᵐ x ∂spectralMeasure hA b, x ∈ univ.image hA.eigenvalues := by
  have hr : ∀ᵐ x ∂spectralMeasure hA b, x ∈ Set.range hA.eigenvalues := by
    rw [ae_iff]
    exact spectralMeasure_compl_range_eigenvalues hA b
  filter_upwards [hr] with x hx
  obtain ⟨i, rfl⟩ := hx
  exact mem_image.mpr ⟨i, mem_univ _, rfl⟩

/-- The actual upper-seed spectral measure of the rectangular dilation is symmetric
under negation, including zero seeds and rectangular matrices with empty dimensions.
Source: Gautschi (2004), Section 2.2; operator derivations (OP17)–(OP19).
atlas: symmetric-measure-even-odd-reduction (partial) -/
theorem map_neg_spectralMeasure_dilation (B : Matrix m n ℝ) (u : m → ℝ) :
    Measure.map (fun x : ℝ => -x)
      (spectralMeasure (isHermitian_dilation B) (Sum.elim u 0)) =
      spectralMeasure (isHermitian_dilation B) (Sum.elim u 0) := by
  let μ := spectralMeasure (isHermitian_dilation B) (Sum.elim u 0)
  let s := univ.image (isHermitian_dilation B).eigenvalues
  have hs : ∀ᵐ x ∂μ, x ∈ s := ae_mem_eigenvalue_finset _ _
  apply measure_eq_of_integral_eval_eq_of_finite_carrier (s.image (fun x => -x) ∪ s)
  · apply (ae_map_iff (by fun_prop) ((s.image (fun x => -x) ∪ s).finite_toSet.measurableSet)).mpr
    filter_upwards [hs] with x hx
    exact mem_union_left _ (mem_image.mpr ⟨x, hx, rfl⟩)
  · filter_upwards [hs] with x hx
    exact mem_union_right _ hx
  · intro p
    rw [integral_map_of_stronglyMeasurable (by fun_prop) p.continuous.stronglyMeasurable]
    have h := polynomialIntegral_spectralMeasure_dilation_comp_neg_X B u p
    simpa only [polynomialIntegral_apply, eval_comp, eval_neg, eval_X] using h

/-- Squaring the actual dilation spectral measure gives exactly the left normal
matrix's spectral measure at the original seed, rather than only a list of matching
moments. Source: Gautschi (2004), Section 2.2; operator derivations (OP19).
atlas: symmetric-measure-even-odd-reduction (partial) -/
theorem map_sq_spectralMeasure_dilation (B : Matrix m n ℝ) (u : m → ℝ) :
    Measure.map (fun x : ℝ => x ^ 2)
      (spectralMeasure (isHermitian_dilation B) (Sum.elim u 0)) =
      spectralMeasure (isHermitian_mul_conjTranspose_self B) u := by
  let μ := spectralMeasure (isHermitian_dilation B) (Sum.elim u 0)
  let ν := spectralMeasure (isHermitian_mul_conjTranspose_self B) u
  let s := univ.image (isHermitian_dilation B).eigenvalues
  let t := univ.image (isHermitian_mul_conjTranspose_self B).eigenvalues
  have hs : ∀ᵐ x ∂μ, x ∈ s := ae_mem_eigenvalue_finset _ _
  have ht : ∀ᵐ x ∂ν, x ∈ t := ae_mem_eigenvalue_finset _ _
  apply measure_eq_of_integral_eval_eq_of_finite_carrier (s.image (fun x => x ^ 2) ∪ t)
  · apply (ae_map_iff (by fun_prop) ((s.image (fun x => x ^ 2) ∪ t).finite_toSet.measurableSet)).mpr
    filter_upwards [hs] with x hx
    exact mem_union_left _ (mem_image.mpr ⟨x, hx, rfl⟩)
  · filter_upwards [ht] with x hx
    exact mem_union_right _ hx
  · intro p
    rw [integral_map_of_stronglyMeasurable (by fun_prop) p.continuous.stronglyMeasurable]
    have h := polynomialIntegral_spectralMeasure_dilation_comp_X_sq B u p
    simpa only [polynomialIntegral_apply, eval_comp, eval_pow, eval_X] using h

end NLAlib
