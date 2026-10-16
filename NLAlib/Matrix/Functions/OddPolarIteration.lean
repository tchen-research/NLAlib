import NLAlib.Matrix.Factorizations.CanonicalPolar
import NLAlib.Polynomial.BestApproximation.OddUpdates

/-! # Realizing odd polynomial updates on rectangular matrices

The actual Gram-polynomial recurrence preserves the fixed compact singular
directions, including negative intermediate coefficients and zero singular
directions. Its polar error equals the maximum scalar composition error.
Source: Polar Express, §2, equations (3)–(6); compact-SVD extension.
-/
noncomputable section
open Finset
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
variable [DecidableEq m] [DecidableEq n] [DecidableEq r]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- A finite sum acts coordinatewise between fixed singular frames. -/
theorem thinSingularMatrix_sum {ι : Type*} (U : Matrix m r ℂ) (V : Matrix n r ℂ)
    (s : Finset ι) (f : ι → r → ℝ) :
    thinSingularMatrix U V (fun j => ∑ i ∈ s, f i j) = ∑ i ∈ s, thinSingularMatrix U V (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [thinSingularMatrix]
  | @insert i s hi ih =>
    simp only [sum_insert hi]
    rw [← thinSingularMatrix_add, ih]

omit [DecidableEq m] in
/-- Multiplication by a Gram power is an odd scalar power in each fixed direction. -/
theorem thinSingularMatrix_mul_gram_pow (U : Matrix m r ℂ) (V : Matrix n r ℂ)
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) (f : r → ℝ) (j : ℕ) :
    thinSingularMatrix U V f * ((thinSingularMatrix U V f)ᴴ * thinSingularMatrix U V f) ^ j =
      thinSingularMatrix U V (fun i => f i ^ (2 * j + 1)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ← Matrix.mul_assoc, ih,
      thinSingularMatrix_gram U V hU, thinSingularMatrix_mul U V V hV]
    congr 1
    funext i
    rw [← pow_add]
    congr 1

/-- The actual matrix update from the supplied odd scalar coefficients. -/
def oddMatrixUpdate (q : ℕ) (a : ℕ → ℝ) (X : Matrix m n ℂ) : Matrix m n ℂ :=
  ∑ j ∈ range (q + 1), a j • (X * (Xᴴ * X) ^ j)

omit [DecidableEq m] in
/-- Each actual matrix polynomial update realizes its scalar polynomial,
without any assumption on the signs of the intermediate singular coefficients.
Source: Polar Express, §2, equations (3)–(6).
atlas: polar-minimax-polynomial-iteration (partial) -/
theorem oddMatrixUpdate_thinSingularMatrix (q : ℕ) (a : ℕ → ℝ)
    (U : Matrix m r ℂ) (V : Matrix n r ℂ) (hU : HasOrthonormalCols U)
    (hV : HasOrthonormalCols V) (f : r → ℝ) :
    oddMatrixUpdate q a (thinSingularMatrix U V f) =
      thinSingularMatrix U V (fun i => oddScalarUpdate q a (f i)) := by
  simp only [oddMatrixUpdate, thinSingularMatrix_mul_gram_pow U V hU hV,
    thinSingularMatrix_smul]
  exact (thinSingularMatrix_sum U V (range (q + 1))
    (fun j i => a j * f i ^ (2 * j + 1))).symm

/-- Iterate the actual matrix updates with their stage-specific coefficients. -/
def oddMatrixIterate (q : ℕ) (a : ℕ → ℕ → ℝ) (A : Matrix m n ℂ) : ℕ → Matrix m n ℂ
  | 0 => A
  | k + 1 => oddMatrixUpdate q (a k) (oddMatrixIterate q a A k)

omit [DecidableEq m] in
/-- Exact matrix realization of the scalar composition at every rank.
In particular zero singular directions remain zero, rather than acquiring
arbitrary isometric completions.
Source: Polar Express, §2, compact-SVD derivation.
atlas: polar-minimax-polynomial-iteration (partial) -/
theorem IsThinSVD.oddMatrixIterate_eq {A : Matrix m n ℂ} {U : Matrix m r ℂ}
    {V : Matrix n r ℂ} {σ : r → ℝ} (h : IsThinSVD A U V σ)
    (q : ℕ) (a : ℕ → ℕ → ℝ) (k : ℕ) :
    oddMatrixIterate q a A k =
      thinSingularMatrix U V (fun i => oddScalarComposition q a (σ i) k) := by
  induction k with
  | zero => exact h.eq
  | succ k ih =>
    rw [oddMatrixIterate, ih,
      oddMatrixUpdate_thinSingularMatrix q (a k) U V h.left_orth h.right_orth]
    rfl

/-- Exact polar error of the actual matrix algorithm. The function norm is
the finite maximum, and is zero for the empty retained singular block.
Source: Polar Express, §2 and Theorem 3.3, compact-SVD extension.
atlas: polar-minimax-polynomial-iteration (partial) -/
theorem IsThinSVD.specNorm_polar_sub_oddMatrixIterate_eq
    {A : Matrix m n ℂ} {U : Matrix m r ℂ} {V : Matrix n r ℂ} {σ : r → ℝ}
    (h : IsThinSVD A U V σ) (q : ℕ) (a : ℕ → ℕ → ℝ) (k : ℕ) :
    specNorm (canonicalPartialPolar A - oddMatrixIterate q a A k) =
      ‖fun i => 1 - oddScalarComposition q a (σ i) k‖ := by
  have hQ : canonicalPartialPolar A = thinSingularMatrix U V (fun _ => 1) := by
    rw [h.canonicalPartialPolar_eq]
    simp [thinSingularMatrix]
  rw [hQ, h.oddMatrixIterate_eq, thinSingularMatrix_sub,
    specNorm_thinSingularMatrix U V h.left_orth h.right_orth]

/-- A scalar interval error transfers to every matrix in the corresponding
positive-singular-value class; rank zero is included. -/
theorem IsThinSVD.specNorm_polar_sub_oddMatrixIterate_le
    {A : Matrix m n ℂ} {U : Matrix m r ℂ} {V : Matrix n r ℂ} {σ : r → ℝ}
    (h : IsThinSVD A U V σ) (q : ℕ) (a : ℕ → ℕ → ℝ) (k : ℕ)
    {l u ε : ℝ} (hσ : ∀ i, σ i ∈ Set.Icc l u) (hε : 0 ≤ ε)
    (hscalar : ∀ x ∈ Set.Icc l u, |1 - oddScalarComposition q a x k| ≤ ε) :
    specNorm (canonicalPartialPolar A - oddMatrixIterate q a A k) ≤ ε := by
  rw [h.specNorm_polar_sub_oddMatrixIterate_eq]
  apply (pi_norm_le_iff_of_nonneg hε).mpr
  exact fun i => hscalar (σ i) (hσ i)

end NLAlib
