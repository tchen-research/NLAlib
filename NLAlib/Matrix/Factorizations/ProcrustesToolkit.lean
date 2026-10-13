import NLAlib.Matrix.Factorizations.ScaledOrthogonal
/-!
# Complete orthogonal Procrustes contract

Attained minima for one-sided, two-sided and scaled orthogonal approximation,
and every advertised equality consequence, including empty matrices.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

/-- The complete real Procrustes bundle: attained one-sided and two-sided
minima, the scalar optimum with an explicit positive-dimension denominator,
the empty endpoint, exact Mirsky/von-Neumann equality equivalence and both
PSD cross-product consequences. Horn–Johnson 2013, §§7.4.4–7.4.6 and
Corollary 7.4.1.5. The concrete polar minimizers are supplied by the component
theorems `frobSq_sub_mul_eq_of_cross_polar` and
`frobSq_sub_trace_rowGram_avg_smul_leftPolar_eq`.
atlas: orthogonal-procrustes -/
theorem orthogonal_procrustes_properties {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A B : Matrix m n ℝ) :
    IsLeast {z : ℝ | ∃ U : Matrix m m ℝ,
      HasOrthonormalCols U ∧ frobSq (A - U * B) = z}
      (frobSq A + frobSq B - 2 * nuclearNorm (A * Bᵀ)) ∧
    IsLeast {z : ℝ | ∃ (U : Matrix m m ℝ) (T : Matrix n n ℝ),
      HasOrthonormalCols U ∧ HasOrthonormalCols T ∧ frobSq (A - U * B * T) = z}
      (∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        (singularValues A i - singularValues B i) ^ 2) ∧
    (∀ C : Matrix m m ℝ, 0 < Fintype.card m →
      IsLeast {z : ℝ | ∃ (c : ℝ) (U : Matrix m m ℝ),
        HasOrthonormalCols U ∧ frobSq (C - c • U) = z}
        (frobSq C - nuclearNorm C ^ 2 / (Fintype.card m : ℝ))) ∧
    (∀ C : Matrix m m ℝ, Fintype.card m = 0 →
      IsLeast {z : ℝ | ∃ (c : ℝ) (U : Matrix m m ℝ),
        HasOrthonormalCols U ∧ frobSq (C - c • U) = z} 0) ∧
    (frobSq (A - B) = ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
      (singularValues A i - singularValues B i) ^ 2 ↔
      frobInner A B = ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        singularValues A i * singularValues B i) ∧
    (frobSq (A - B) = ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
      (singularValues A i - singularValues B i) ^ 2 →
      (A * Bᵀ).PosSemidef ∧ (Bᵀ * A).PosSemidef) := by
  refine ⟨isLeast_frobSq_sub_orthogonal_mul A B,
    isLeast_frobSq_sub_orthogonal_mul_mul A B, isLeast_frobSq_sub_scaled_orthogonal,
    ?_, frobSq_sub_eq_sum_singularValues_sub_sq_iff A B,
    posSemidef_cross_products_of_frobSq_sub_eq_sum_singularValues_sub_sq A B⟩
  intro C hCard
  have : IsEmpty m := Fintype.card_eq_zero_iff.mp hCard
  exact isLeast_frobSq_sub_scaled_orthogonal_of_isEmpty C

end NLAlib
