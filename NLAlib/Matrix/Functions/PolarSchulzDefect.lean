import NLAlib.Matrix.Functions.PolarSchulz

/-! # Orthogonality defects of the polar Newton–Schulz recursion

The polynomial matrix identity holds for every rectangular complex matrix.
Under full column rank and the strict initial norm bound, its scalar
coordinates give positive defects below the identity and quadratic decay.
Source: Higham–Schreiber (1990), §3.
-/
noncomputable section
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace NLAlib
variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
variable [DecidableEq m] [DecidableEq n] [DecidableEq r]

omit [DecidableEq m] in
/-- The exact orthogonality-defect recurrence, with its essential factor `1/4`.
This identity requires neither full rank nor an initial norm bound.
Source: Higham–Schreiber (1990), §3.
atlas: polar-newton-schulz-iteration (partial) -/
theorem polarSchulzDefect_step (X : Matrix m n ℂ) :
    polarSchulzDefect (polarSchulzStep X) =
      (1 / 4 : ℝ) • (polarSchulzDefect X ^ 2 * ((3 : ℝ) • 1 + polarSchulzDefect X)) := by
  let S := Xᴴ * X
  let L := (3 : ℝ) • (1 : Matrix n n ℂ) - S
  have hS : Sᴴ = S := by simp [S]
  have hL : Lᴴ = L := by simp [L, hS]
  have hG : (polarSchulzStep X)ᴴ * polarSchulzStep X = (1 / 4 : ℝ) • (L * S * L) := by
    change ((1 / 2 : ℝ) • (X * L))ᴴ * ((1 / 2 : ℝ) • (X * L)) = _
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hL,
      star_trivial, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    norm_num only [show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num]
    simp only [S, Matrix.mul_assoc]
  rw [polarSchulzDefect, hG]
  calc
    _ = (1 / 4 : ℝ) • ((4 : ℝ) • (1 : Matrix n n ℂ) - L * S * L) := by module
    _ = _ := by
      congr 1
      dsimp only [L, S, polarSchulzDefect]
      noncomm_ring
      module

omit [DecidableEq m] in
/-- Defects are diagonal in the complete right singular frame. -/
theorem IsThinSVD.polarSchulzDefect_eq {A : Matrix m n ℂ} {U : Matrix m r ℂ}
    {V : Matrix n r ℂ} {σ : r → ℝ} (h : IsThinSVD A U V σ)
    (hRank : A.rank = Fintype.card n) (k : ℕ) :
    polarSchulzDefect (polarSchulzIterate A k) =
      thinSingularMatrix V V (fun i => 1 - polarSchulzScalar (σ i) k ^ 2) := by
  have hI : (1 : Matrix n n ℂ) = thinSingularMatrix V V (fun _ => 1) := by
    simp only [thinSingularMatrix, RCLike.ofReal_one, Matrix.diagonal_one, Matrix.mul_one]
    exact (h.right_mul_conjTranspose_eq_one_of_rank_eq_card hRank).symm
  rw [polarSchulzDefect, h.polarSchulzIterate_eq, thinSingularMatrix_gram U V h.left_orth,
    hI, thinSingularMatrix_sub]

omit [DecidableEq m] in
/-- The defect's norm is the exact maximum absolute scalar defect. -/
theorem IsThinSVD.specNorm_polarSchulzDefect_eq {A : Matrix m n ℂ} {U : Matrix m r ℂ}
    {V : Matrix n r ℂ} {σ : r → ℝ} (h : IsThinSVD A U V σ)
    (hRank : A.rank = Fintype.card n) (k : ℕ) :
    specNorm (polarSchulzDefect (polarSchulzIterate A k)) =
      ‖fun i => 1 - polarSchulzScalar (σ i) k ^ 2‖ := by
  rw [h.polarSchulzDefect_eq hRank, specNorm_thinSingularMatrix V V h.right_orth h.right_orth]

/-- After the first step, the defect is positive semidefinite and strictly
below the identity in the positive-definite order.
Source: Higham–Schreiber (1990), §3.
atlas: polar-newton-schulz-iteration (partial) -/
theorem IsThinSVD.polarSchulzDefect_posSemidef_and_sub_posDef
    {A : Matrix m n ℂ} {U : Matrix m r ℂ} {V : Matrix n r ℂ} {σ : r → ℝ}
    (h : IsThinSVD A U V σ) (hRank : A.rank = Fintype.card n)
    (hA : specNorm A < Real.sqrt 3) (k : ℕ) :
    (polarSchulzDefect (polarSchulzIterate A (k + 1))).PosSemidef ∧
      (1 - polarSchulzDefect (polarSchulzIterate A (k + 1))).PosDef := by
  constructor
  · rw [h.polarSchulzDefect_eq hRank]
    apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    change (0 : ℂ) ≤ ((1 - polarSchulzScalar (σ i) (k + 1) ^ 2 : ℝ) : ℂ)
    exact_mod_cast (polarSchulzScalar_defect_mem (h.pos i)
      (h.sq_lt_three_of_specNorm_lt_sqrt_three hA i) k).1
  · simp only [polarSchulzDefect, sub_sub_cancel]
    apply (Matrix.posSemidef_conjTranspose_mul_self _).posDef_iff_isUnit.mpr
    apply isUnit_gram_of_rank_eq_card
    rw [h.rank_polarSchulzIterate hA, hRank]

end NLAlib
