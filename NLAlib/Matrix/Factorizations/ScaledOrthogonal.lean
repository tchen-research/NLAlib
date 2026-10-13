import NLAlib.Matrix.Factorizations.ProcrustesRotations
/-!
# Nearest scaled orthogonal matrices

The scalar optimum is the average singular value. The same polar orthogonal
factor attains it; negative scaling does not improve the minimum. The empty
matrix case is stated separately. Horn–Johnson 2013, §7.4.6.
-/

noncomputable section
open scoped Matrix MatrixOrder
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The one-sided scaled Procrustes error at a polar orthogonal factor is an
explicit scalar quadratic. Horn–Johnson 2013, §7.4.6.
atlas: orthogonal-procrustes (partial) -/
theorem frobSq_sub_smul_polar_eq {A U : Matrix n n ℝ}
    (hU : HasOrthonormalCols U) (hA : U * CFC.sqrt (Aᵀ * A) = A) (c : ℝ) :
    frobSq (A - c • U) = frobSq A - 2 * c * nuclearNorm A + (Fintype.card n : ℝ) * c ^ 2 := by
  rw [frobSq_sub, frobInner_smul_right, frobSq_smul,
    frobInner_eq_nuclearNorm_of_polar hU hA, frobSq_frame_eq_card hU]
  ring

/-- At positive dimension every scaled orthogonal competitor has error at
least the singular-value-average optimum, allowing every real scaling.
Horn–Johnson 2013, §7.4.6.
atlas: orthogonal-procrustes (partial) -/
theorem frobSq_sub_nuclearNorm_sq_div_card_le_sub_smul
    (A U : Matrix n n ℝ) (hU : HasOrthonormalCols U) (c : ℝ)
    (hCard : 0 < Fintype.card n) :
    frobSq A - nuclearNorm A ^ 2 / (Fintype.card n : ℝ) ≤ frobSq (A - c • U) := by
  have hPos := frobInner_le_nuclearNorm_of_specNorm_le_one A U
    (specNorm_le_one_of_orthonormal hU)
  have hNeg := frobInner_le_nuclearNorm_of_specNorm_le_one A (-U)
    (by simpa only [specNorm_neg] using specNorm_le_one_of_orthonormal hU)
  have hAbs : |frobInner A U| ≤ nuclearNorm A := by
    rw [frobInner_neg_right] at hNeg
    exact abs_le.mpr ⟨by linarith, hPos⟩
  have hBound : frobInner A U ^ 2 ≤ nuclearNorm A ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (frobInner A U)) hAbs 2
    simpa only [sq_abs] using h
  have hN : (0 : ℝ) < Fintype.card n := by exact_mod_cast hCard
  rw [frobSq_sub, frobInner_smul_right, frobSq_smul, frobSq_frame_eq_card hU]
  apply le_of_mul_le_mul_left _ hN
  have hDiv : (Fintype.card n : ℝ) * (nuclearNorm A ^ 2 / (Fintype.card n : ℝ)) =
      nuclearNorm A ^ 2 := by field_simp
  rw [mul_sub, hDiv]
  have hSq := sq_nonneg ((Fintype.card n : ℝ) * c - frobInner A U)
  nlinarith

/-- The average-singular-value multiple of any orthogonal polar factor is a
nearest scaled orthogonal matrix. The scalar has the explicit nonzero
dimension denominator. Horn–Johnson 2013, §7.4.6.
atlas: orthogonal-procrustes (partial) -/
theorem frobSq_sub_avg_smul_polar_eq {A U : Matrix n n ℝ}
    (hU : HasOrthonormalCols U) (hA : U * CFC.sqrt (Aᵀ * A) = A)
    (hCard : 0 < Fintype.card n) :
    frobSq (A - (nuclearNorm A / (Fintype.card n : ℝ)) • U) =
      frobSq A - nuclearNorm A ^ 2 / (Fintype.card n : ℝ) := by
  rw [frobSq_sub_smul_polar_eq hU hA]
  have hN : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hCard
  field_simp
  ring

/-- The scaled orthogonal Procrustes problem has its explicit attained
minimum at positive dimension, allowing positive or negative real scalars.
Horn–Johnson 2013, §7.4.6.
atlas: orthogonal-procrustes (partial) -/
theorem isLeast_frobSq_sub_scaled_orthogonal (A : Matrix n n ℝ)
    (hCard : 0 < Fintype.card n) :
    IsLeast {z : ℝ | ∃ (c : ℝ) (U : Matrix n n ℝ),
      HasOrthonormalCols U ∧ frobSq (A - c • U) = z}
      (frobSq A - nuclearNorm A ^ 2 / (Fintype.card n : ℝ)) := by
  obtain ⟨U, hU, hA⟩ := exists_isometry_mul_sqrt_gram_eq A le_rfl
  refine ⟨⟨nuclearNorm A / (Fintype.card n : ℝ), U, hU,
    frobSq_sub_avg_smul_polar_eq hU hA hCard⟩, ?_⟩
  rintro z ⟨c, V, hV, rfl⟩
  exact frobSq_sub_nuclearNorm_sq_div_card_le_sub_smul A V hV c hCard

/-- In dimension zero the unique square matrix has scaled-orthogonal error
zero; no ordinary quotient by the dimension is used. Horn–Johnson §7.4.6,
frontier derivations' endpoint convention.
atlas: orthogonal-procrustes (partial) -/
theorem isLeast_frobSq_sub_scaled_orthogonal_of_isEmpty [IsEmpty n] (A : Matrix n n ℝ) :
    IsLeast {z : ℝ | ∃ (c : ℝ) (U : Matrix n n ℝ),
      HasOrthonormalCols U ∧ frobSq (A - c • U) = z} 0 := by
  refine ⟨⟨0, 1, by simp [HasOrthonormalCols], ?_⟩, ?_⟩
  · have hA : A = 0 := by ext i; exact isEmptyElim i
    simp [hA, frobSq_zero]
  · rintro z ⟨c, U, _, rfl⟩
    exact frobSq_nonneg _

/-- In the source's left-polar convention `A = P U`, the nearest scaled
orthogonal matrix is exactly `(tr P / n) U`. Horn–Johnson 2013, §7.4.6.
atlas: orthogonal-procrustes (partial) -/
theorem frobSq_sub_trace_rowGram_avg_smul_leftPolar_eq {A U : Matrix n n ℝ}
    (hU : HasOrthonormalCols U) (hA : CFC.sqrt (A * Aᵀ) * U = A)
    (hCard : 0 < Fintype.card n) :
    frobSq (A - ((CFC.sqrt (A * Aᵀ)).trace / (Fintype.card n : ℝ)) • U) =
      frobSq A - nuclearNorm A ^ 2 / (Fintype.card n : ℝ) := by
  have hSym (M : Matrix n n ℝ) : (CFC.sqrt M)ᵀ = CFC.sqrt M := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg M).star_eq
  have hAt : Uᵀ * CFC.sqrt (Aᵀᵀ * Aᵀ) = Aᵀ := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hSym] using
      congrArg Matrix.transpose hA
  have hRight : U * CFC.sqrt (Aᵀ * A) = A := by
    have h := sqrt_rowGram_mul_eq_of_isometry_mul_sqrt_gram_eq hU.transpose hAt
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hSym] using
      congrArg Matrix.transpose h
  rw [← nuclearNorm_eq_trace_sqrt_rowGram]
  exact frobSq_sub_avg_smul_polar_eq hU hRight hCard

end NLAlib
