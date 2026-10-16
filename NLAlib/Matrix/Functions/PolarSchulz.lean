import NLAlib.Matrix.Factorizations.CanonicalPolar
import NLAlib.ForMathlib.Analysis.PolarSchulzScalar

/-! # Inverse-free rectangular polar iteration

The actual matrix recursion preserves fixed thin singular directions. Its
initial scalar interval is `(0,sqrt 3)`, and it enters `(0,1]` after one step.
Source: Higham–Schreiber (1990), §3, equation (3.3).
-/
noncomputable section
open Filter
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
namespace NLAlib
variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
variable [DecidableEq m] [DecidableEq n] [DecidableEq r]

/-- One actual inverse-free polar step, using the column Gram matrix. -/
def polarSchulzStep (X : Matrix m n ℂ) : Matrix m n ℂ :=
  (1 / 2 : ℝ) • (X * ((3 : ℝ) • 1 - Xᴴ * X))

/-- The actual Newton–Schulz polar recursion. -/
def polarSchulzIterate (A : Matrix m n ℂ) : ℕ → Matrix m n ℂ
  | 0 => A
  | k + 1 => polarSchulzStep (polarSchulzIterate A k)

/-- The column orthogonality defect. -/
def polarSchulzDefect (X : Matrix m n ℂ) : Matrix n n ℂ := 1 - Xᴴ * X

omit [DecidableEq m] in
/-- An inverse-free step acts on each fixed real singular coefficient by
the scalar cubic, even for negative intermediate values. -/
theorem polarSchulzStep_thinSingularMatrix (U : Matrix m r ℂ) (V : Matrix n r ℂ)
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) (f : r → ℝ) :
    polarSchulzStep (thinSingularMatrix U V f) =
      thinSingularMatrix U V (fun i => f i * (3 - f i ^ 2) / 2) := by
  rw [polarSchulzStep, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    thinSingularMatrix_gram U V hU, thinSingularMatrix_mul U V V hV,
    thinSingularMatrix_smul, thinSingularMatrix_sub, thinSingularMatrix_smul]
  congr 1
  funext i
  ring

omit [DecidableEq m] in
/-- Exact fixed-direction representation of the actual inverse-free recurrence.
Source: Higham–Schreiber (1990), §3, equation (3.3).
atlas: polar-newton-schulz-iteration (partial) -/
theorem IsThinSVD.polarSchulzIterate_eq {A : Matrix m n ℂ} {U : Matrix m r ℂ}
    {V : Matrix n r ℂ} {σ : r → ℝ} (h : IsThinSVD A U V σ) (k : ℕ) :
    polarSchulzIterate A k = thinSingularMatrix U V (fun i => polarSchulzScalar (σ i) k) := by
  induction k with
  | zero => exact h.eq
  | succ k ih =>
    rw [polarSchulzIterate, ih, polarSchulzStep_thinSingularMatrix U V h.left_orth h.right_orth]
    rfl

/-- The operator-norm hypothesis implies the strict scalar admissibility
interval for each actual retained singular direction. -/
theorem IsThinSVD.sq_lt_three_of_specNorm_lt_sqrt_three
    {A : Matrix m n ℂ} {U : Matrix m r ℂ} {V : Matrix n r ℂ} {σ : r → ℝ}
    (h : IsThinSVD A U V σ) (hA : specNorm A < Real.sqrt 3) (i : r) : σ i ^ 2 < 3 := by
  have hn : ‖σ‖ < Real.sqrt 3 := by
    rwa [h.eq, ← thinSingularMatrix, specNorm_thinSingularMatrix U V h.left_orth h.right_orth] at hA
  have hs : σ i < Real.sqrt 3 :=
    lt_of_le_of_lt ((le_abs_self _).trans (norm_le_pi_norm σ i)) hn
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), h.pos i]

/-- Under the strict initial norm bound, every iterate preserves rank. -/
theorem IsThinSVD.rank_polarSchulzIterate {A : Matrix m n ℂ} {U : Matrix m r ℂ}
    {V : Matrix n r ℂ} {σ : r → ℝ} (h : IsThinSVD A U V σ)
    (hA : specNorm A < Real.sqrt 3) (k : ℕ) : (polarSchulzIterate A k).rank = A.rank := by
  have hp : ∀ i, 0 < polarSchulzScalar (σ i) k := by
    intro i
    cases k with
    | zero => exact h.pos i
    | succ k => exact (polarSchulzScalar_mem (h.pos i)
        (h.sq_lt_three_of_specNorm_lt_sqrt_three hA i) k).1
  exact (IsThinSVD.rank_eq_card
    ⟨h.left_orth, h.right_orth, hp, h.polarSchulzIterate_eq k⟩).trans h.rank_eq_card.symm

/-- Convergence of the actual inverse-free recurrence under its strict initial
operator-norm hypothesis, including deficient-rank inputs.
Source: Higham–Schreiber (1990), §3; the rectangular thin-SVD extension.
atlas: polar-newton-schulz-iteration (partial) -/
theorem IsThinSVD.tendsto_polarSchulzIterate {A : Matrix m n ℂ} {U : Matrix m r ℂ}
    {V : Matrix n r ℂ} {σ : r → ℝ} (h : IsThinSVD A U V σ)
    (hA : specNorm A < Real.sqrt 3) :
    Tendsto (polarSchulzIterate A) atTop (𝓝 (canonicalPartialPolar A)) := by
  have hs : Tendsto (fun k i => polarSchulzScalar (σ i) k) atTop (𝓝 (fun _ : r => (1 : ℝ))) :=
    tendsto_pi_nhds.mpr (fun i => tendsto_polarSchulzScalar (h.pos i)
      (h.sq_lt_three_of_specNorm_lt_sqrt_three hA i))
  have hc : Continuous (fun f : r → ℝ => thinSingularMatrix U V f) := by
    unfold thinSingularMatrix
    fun_prop
  have ht := hc.continuousAt.tendsto.comp hs
  have he : (fun k => thinSingularMatrix U V (fun i => polarSchulzScalar (σ i) k)) =
      polarSchulzIterate A := funext (fun k => (h.polarSchulzIterate_eq k).symm)
  change Tendsto (fun k => thinSingularMatrix U V (fun i => polarSchulzScalar (σ i) k))
    atTop (𝓝 (thinSingularMatrix U V (fun _ => 1))) at ht
  rw [he] at ht
  simpa only [thinSingularMatrix, RCLike.ofReal_one, Matrix.diagonal_one, Matrix.mul_one,
    ← h.canonicalPartialPolar_eq] using ht

/-- Convergence stated directly for the input matrix, with no SVD premise. -/
theorem tendsto_polarSchulzIterate (A : Matrix m n ℂ) (hA : specNorm A < Real.sqrt 3) :
    Tendsto (polarSchulzIterate A) atTop (𝓝 (canonicalPartialPolar A)) := by
  obtain ⟨U, V, h⟩ := exists_isThinSVD A
  exact h.tendsto_polarSchulzIterate hA

end NLAlib
