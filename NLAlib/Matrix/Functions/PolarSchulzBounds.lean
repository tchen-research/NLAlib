import NLAlib.Matrix.Functions.PolarSchulzDefect

/-! # Quadratic operator-norm bounds for inverse-free polar iteration

The initial defect is allowed to have norm greater than one. All bounds
start at the first iterate, exactly as required by the admissible scalar
interval. Source: Higham–Schreiber (1990), §3.
-/
noncomputable section
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace NLAlib
variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
variable [DecidableEq m] [DecidableEq n] [DecidableEq r]

/-- Every defect after the first has operator norm strictly below one. -/
theorem IsThinSVD.specNorm_polarSchulzDefect_lt_one
    {A : Matrix m n ℂ} {U : Matrix m r ℂ} {V : Matrix n r ℂ} {σ : r → ℝ}
    (h : IsThinSVD A U V σ) (hRank : A.rank = Fintype.card n)
    (hA : specNorm A < Real.sqrt 3) (k : ℕ) :
    specNorm (polarSchulzDefect (polarSchulzIterate A (k + 1))) < 1 := by
  rw [h.specNorm_polarSchulzDefect_eq hRank]
  apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr
  intro i
  have he := polarSchulzScalar_defect_mem (h.pos i)
    (h.sq_lt_three_of_specNorm_lt_sqrt_three hA i) k
  simpa only [Real.norm_eq_abs, abs_of_nonneg he.1] using he.2

/-- Quadratic contraction starts after the first step, and uses the actual
matrix orthogonality-defect norms. -/
theorem IsThinSVD.specNorm_polarSchulzDefect_step_le
    {A : Matrix m n ℂ} {U : Matrix m r ℂ} {V : Matrix n r ℂ} {σ : r → ℝ}
    (h : IsThinSVD A U V σ) (hRank : A.rank = Fintype.card n)
    (hA : specNorm A < Real.sqrt 3) (k : ℕ) :
    specNorm (polarSchulzDefect (polarSchulzIterate A (k + 2))) ≤
      specNorm (polarSchulzDefect (polarSchulzIterate A (k + 1))) ^ 2 := by
  rw [h.specNorm_polarSchulzDefect_eq hRank, h.specNorm_polarSchulzDefect_eq hRank]
  apply (pi_norm_le_iff_of_nonneg (sq_nonneg _)).mpr
  intro i
  have hi := h.sq_lt_three_of_specNorm_lt_sqrt_three hA i
  have he := polarSchulzScalar_defect_mem (h.pos i) hi (k + 1)
  rw [Real.norm_eq_abs, abs_of_nonneg he.1]
  exact (polarSchulzScalar_defect_step_le (h.pos i) hi k).trans
    (pow_le_pow_left₀ (polarSchulzScalar_defect_mem (h.pos i) hi k).1
      ((le_abs_self _).trans (norm_le_pi_norm
        (fun i => 1 - polarSchulzScalar (σ i) (k + 1) ^ 2) i)) 2)

/-- The polar-factor error is bounded by the actual orthogonality defect. -/
theorem IsThinSVD.specNorm_polarSchulzIterate_sub_polar_le_defect
    {A : Matrix m n ℂ} {U : Matrix m r ℂ} {V : Matrix n r ℂ} {σ : r → ℝ}
    (h : IsThinSVD A U V σ) (hRank : A.rank = Fintype.card n)
    (hA : specNorm A < Real.sqrt 3) (k : ℕ) :
    specNorm (polarSchulzIterate A (k + 1) - canonicalPartialPolar A) ≤
      specNorm (polarSchulzDefect (polarSchulzIterate A (k + 1))) := by
  have hQ : canonicalPartialPolar A = thinSingularMatrix U V (fun _ => 1) := by
    rw [h.canonicalPartialPolar_eq]
    simp [thinSingularMatrix]
  rw [h.specNorm_polarSchulzDefect_eq hRank, h.polarSchulzIterate_eq,
    hQ, thinSingularMatrix_sub,
    specNorm_thinSingularMatrix U V h.left_orth h.right_orth]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact (abs_polarSchulzScalar_sub_one_le_defect (h.pos i)
    (h.sq_lt_three_of_specNorm_lt_sqrt_three hA i) k).trans
      ((le_abs_self _).trans (norm_le_pi_norm
        (fun i => 1 - polarSchulzScalar (σ i) (k + 1) ^ 2) i))

/-- Double-exponential operator-norm defect decay from the actual first defect. -/
theorem IsThinSVD.specNorm_polarSchulzDefect_le
    {A : Matrix m n ℂ} {U : Matrix m r ℂ} {V : Matrix n r ℂ} {σ : r → ℝ}
    (h : IsThinSVD A U V σ) (hRank : A.rank = Fintype.card n)
    (hA : specNorm A < Real.sqrt 3) (k : ℕ) :
    specNorm (polarSchulzDefect (polarSchulzIterate A (k + 1))) ≤
      specNorm (polarSchulzDefect (polarSchulzIterate A 1)) ^ (2 ^ k) := by
  rw [h.specNorm_polarSchulzDefect_eq hRank, h.specNorm_polarSchulzDefect_eq hRank]
  apply (pi_norm_le_iff_of_nonneg (pow_nonneg (norm_nonneg _) _)).mpr
  intro i
  have hi := h.sq_lt_three_of_specNorm_lt_sqrt_three hA i
  have he := polarSchulzScalar_defect_mem (h.pos i) hi k
  rw [Real.norm_eq_abs, abs_of_nonneg he.1]
  exact (polarSchulzScalar_defect_le (h.pos i) hi k).trans
    (pow_le_pow_left₀ (polarSchulzScalar_defect_mem (h.pos i) hi 0).1
      ((le_abs_self _).trans (norm_le_pi_norm
        (fun i => 1 - polarSchulzScalar (σ i) 1 ^ 2) i)) (2 ^ k))

/-- Full source defect and error guarantees for the actual input matrix,
with the full-column-rank and strict initial norm hypotheses alone.
Source: Higham–Schreiber (1990), §3.
atlas: polar-newton-schulz-iteration -/
theorem polarSchulz_defect_and_error_bounds (A : Matrix m n ℂ)
    (hRank : A.rank = Fintype.card n) (hA : specNorm A < Real.sqrt 3) (k : ℕ) :
    (polarSchulzDefect (polarSchulzIterate A (k + 1))).PosSemidef ∧
    (1 - polarSchulzDefect (polarSchulzIterate A (k + 1))).PosDef ∧
    specNorm (polarSchulzDefect (polarSchulzIterate A (k + 1))) < 1 ∧
    specNorm (polarSchulzDefect (polarSchulzIterate A (k + 2))) ≤
      specNorm (polarSchulzDefect (polarSchulzIterate A (k + 1))) ^ 2 ∧
    specNorm (polarSchulzIterate A (k + 1) - canonicalPartialPolar A) ≤
      specNorm (polarSchulzDefect (polarSchulzIterate A (k + 1))) ∧
    specNorm (polarSchulzDefect (polarSchulzIterate A (k + 1))) ≤
      specNorm (polarSchulzDefect (polarSchulzIterate A 1)) ^ (2 ^ k) := by
  obtain ⟨U, V, h⟩ := exists_isThinSVD A
  obtain ⟨hp, hi⟩ := h.polarSchulzDefect_posSemidef_and_sub_posDef hRank hA k
  exact ⟨hp, hi, h.specNorm_polarSchulzDefect_lt_one hRank hA k,
    h.specNorm_polarSchulzDefect_step_le hRank hA k,
    h.specNorm_polarSchulzIterate_sub_polar_le_defect hRank hA k,
    h.specNorm_polarSchulzDefect_le hRank hA k⟩

end NLAlib
