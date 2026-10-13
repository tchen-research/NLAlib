import NLAlib.Matrix.Factorizations.Procrustes
import NLAlib.Matrix.Subspaces.OrthogonalProducts
import NLAlib.Matrix.Norms.SchattenSingularCoefficients
/-!
# Two-sided Procrustes and equality consequences

SVD alignment attains von Neumann's pairing bound. Frobenius expansion
identifies the two-sided minimum and the exact Mirsky equality condition.
The latter forces both cross-products to be positive semidefinite.
Horn–Johnson 2013, §§7.4.4–7.4.6 and Corollary 7.4.1.5.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- Equality in Frobenius Mirsky is exactly equality in the signed von
Neumann pairing. Arbitrary finite indices and empty dimensions are included.
Horn–Johnson 2013, Corollary 7.4.1.5.
atlas: orthogonal-procrustes (partial) -/
theorem frobSq_sub_eq_sum_singularValues_sub_sq_iff (A B : Matrix m n ℝ) :
    frobSq (A - B) = ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
      (singularValues A i - singularValues B i) ^ 2 ↔
    frobInner A B = ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
      singularValues A i * singularValues B i := by
  have hExpand : (∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
      (singularValues A i - singularValues B i) ^ 2) =
      frobSq A - 2 * (∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        singularValues A i * singularValues B i) + frobSq B := by
    rw [frobSq_eq_sum_sq_singularValues,
      frobSq_eq_sum_sq_singularValues, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [frobSq_sub, hExpand]
  constructor <;> intro h <;> linarith

/-- The nuclear norm of a cross-product is bounded by the singular-value
pairing of its two factors. Horn–Johnson 2013, §7.4.4. -/
theorem nuclearNorm_mul_transpose_le_sum_singularValues_mul (A B : Matrix m n ℝ) :
    nuclearNorm (A * Bᵀ) ≤ ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
      singularValues A i * singularValues B i := by
  obtain ⟨U, hU, hPolar⟩ := exists_isometry_mul_sqrt_gram_eq (A * Bᵀ) le_rfl
  have hPair : frobInner A (U * B) = nuclearNorm (A * Bᵀ) := by
    rw [frobInner_mul_eq_frobInner_mul_transpose,
      frobInner_eq_nuclearNorm_of_polar hU hPolar]
  have h := (le_abs_self (frobInner A (U * B))).trans
    (abs_frobInner_le_sum_singularValues_mul A (U * B))
  simpa only [hPair, ← singularValues_eq_linearMap, singularValues_isometry_mul hU B] using h

/-- Equality in von Neumann's signed trace inequality forces the row
cross-product to be PSD. Horn–Johnson 2013, Corollary 7.4.1.5.
atlas: orthogonal-procrustes (partial) -/
theorem posSemidef_mul_transpose_of_frobInner_eq_sum_singularValues_mul
    (A B : Matrix m n ℝ)
    (hEq : frobInner A B = ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
      singularValues A i * singularValues B i) :
    (A * Bᵀ).PosSemidef := by
  apply (trace_eq_nuclearNorm_iff_posSemidef _).mp
  have hNuclear := nuclearNorm_mul_transpose_le_sum_singularValues_mul A B
  have hLower := frobInner_le_nuclearNorm_of_specNorm_le_one (A * Bᵀ)
    (1 : Matrix m m ℝ) (specNorm_le_one_of_orthonormal (by simp))
  have hTrace : frobInner (A * Bᵀ) (1 : Matrix m m ℝ) = (A * Bᵀ).trace := by
    rw [frobInner_eq_trace, RCLike.re_to_real,
      Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_one, Matrix.trace_transpose]
  rw [hTrace] at hLower
  rw [frobInner_eq_re_trace_mul_conjTranspose, RCLike.re_to_real,
    Matrix.conjTranspose_eq_transpose_of_trivial] at hEq
  linarith

/-- Equality in the Frobenius Mirsky bound forces both rectangular
cross-products to be positive semidefinite. These are necessary consequences;
they are not asserted to suffice for equality. Horn–Johnson 2013, Cor. 7.4.1.5.
atlas: orthogonal-procrustes (partial) -/
theorem posSemidef_cross_products_of_frobSq_sub_eq_sum_singularValues_sub_sq
    (A B : Matrix m n ℝ)
    (hEq : frobSq (A - B) = ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
      (singularValues A i - singularValues B i) ^ 2) :
    (A * Bᵀ).PosSemidef ∧ (Bᵀ * A).PosSemidef := by
  have hPair := (frobSq_sub_eq_sum_singularValues_sub_sq_iff A B).mp hEq
  refine ⟨posSemidef_mul_transpose_of_frobInner_eq_sum_singularValues_mul A B hPair, ?_⟩
  have hPairT : frobInner Bᵀ Aᵀ =
      ∑ i ∈ Finset.range (min (Fintype.card n) (Fintype.card m)),
        singularValues Bᵀ i * singularValues Aᵀ i := by
    simpa only [frobInner_transpose, frobInner_comm B A,
      ← singularValues_eq_linearMap, singularValues_transpose, min_comm, mul_comm] using hPair
  simpa only [Matrix.transpose_transpose] using
    posSemidef_mul_transpose_of_frobInner_eq_sum_singularValues_mul Bᵀ Aᵀ hPairT

/-- Genuine orthogonal rotations on both sides attain von Neumann's
singular-value pairing, on arbitrary finite rectangular indices.
Horn–Johnson 2013, §7.4.5.
atlas: orthogonal-procrustes (partial) -/
theorem exists_orthogonal_pair_attaining_singularValue_pairing (A B : Matrix m n ℝ) :
    ∃ (U : Matrix m m ℝ) (T : Matrix n n ℝ), HasOrthonormalCols U ∧ HasOrthonormalCols T ∧
      frobInner A (U * B * T) = ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        singularValues A i * singularValues B i := by
  classical
  obtain ⟨LA, RA, hA⟩ := exists_isSVD A
  obtain ⟨LB, RB, hB⟩ := exists_isSVD B
  let U := LA * LBᵀ
  let T := RB * RAᵀ
  have hLA : HasOrthonormalCols LA := hA.conjTranspose_mul_left
  have hRA : HasOrthonormalCols RA := hA.conjTranspose_mul_right
  have hLB : HasOrthonormalCols LB := hB.conjTranspose_mul_left
  have hRB : HasOrthonormalCols RB := hB.conjTranspose_mul_right
  have hLBt : HasOrthonormalCols LBᵀ := by
    change LBᵀᴴ * LBᵀ = 1
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
    exact hB.mul_conjTranspose_left
  have hRAt : HasOrthonormalCols RAᵀ := by
    change RAᵀᴴ * RAᵀ = 1
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
    exact hA.mul_conjTranspose_right
  refine ⟨U, T, hLA.mul hLBt, hRB.mul hRAt, ?_⟩
  have hAligned : U * B * T = LA *
      (rectDiag (singularValues B) :
        Matrix (Fin (Fintype.card m)) (Fin (Fintype.card n)) ℝ) * RAᵀ := by
    dsimp [U, T]
    nth_rw 1 [hB.eq]
    simp only [Matrix.mul_assoc, Matrix.conjTranspose_eq_transpose_of_trivial]
    rw [← Matrix.mul_assoc LBᵀ LB _, show LBᵀ * LB = 1 from hB.conjTranspose_mul_left,
      Matrix.one_mul, ← Matrix.mul_assoc RBᵀ RB _,
      show RBᵀ * RB = 1 from hB.conjTranspose_mul_right, Matrix.one_mul]
  rw [hAligned, hA.frobInner_mul_rectDiag_mul_transpose]

/-- Two-sided orthogonal Procrustes has the exact singular-value squared
distance as its minimum. SVD alignment supplies genuine attained rotations,
including rank-deficient and empty shapes. Horn–Johnson 2013, §7.4.5.
atlas: orthogonal-procrustes (partial) -/
theorem isLeast_frobSq_sub_orthogonal_mul_mul (A B : Matrix m n ℝ) :
    IsLeast {z : ℝ | ∃ (U : Matrix m m ℝ) (T : Matrix n n ℝ),
      HasOrthonormalCols U ∧ HasOrthonormalCols T ∧ frobSq (A - U * B * T) = z}
      (∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        (singularValues A i - singularValues B i) ^ 2) := by
  have hσ (U : Matrix m m ℝ) (T : Matrix n n ℝ)
      (hU : HasOrthonormalCols U) (hT : HasOrthonormalCols T) (i : ℕ) :
      singularValues (U * B * T) i = singularValues B i := by
    rw [singularValues_mul_orthogonal _ hT, singularValues_isometry_mul hU]
  obtain ⟨U, T, hU, hT, hPair⟩ := exists_orthogonal_pair_attaining_singularValue_pairing A B
  refine ⟨⟨U, T, hU, hT, ?_⟩, ?_⟩
  · have h := (frobSq_sub_eq_sum_singularValues_sub_sq_iff A (U * B * T)).mpr
      (by simpa only [hσ U T hU hT] using hPair)
    simpa only [hσ U T hU hT] using h
  · rintro z ⟨V, W, hV, hW, rfl⟩
    have h := sum_sq_singularValues_add_sub_le_frobSq (V * B * W) (A - V * B * W)
    rw [show V * B * W + (A - V * B * W) = A by abel] at h
    simpa only [hσ V W hV hW] using h

end NLAlib
