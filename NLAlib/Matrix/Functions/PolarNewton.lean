import NLAlib.Matrix.Factorizations.CanonicalPolar
import NLAlib.ForMathlib.Analysis.PolarNewtonScalar

/-! # Rectangular polar Newton iteration

The actual pseudoinverse recursion preserves each fixed singular direction.
The scalar Cayley coordinate gives the closed form, rank preservation,
convergence to the canonical partial polar factor, and the explicit rate.
Full-column-rank inputs therefore converge to the polar isometry.
Source: Higham (1986), §3.2, Theorem 3.1 and equations (3.4)–(3.7).
-/
noncomputable section
open Filter
open scoped Matrix Matrix.Norms.L2Operator Topology
namespace NLAlib
variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
variable [DecidableEq m] [DecidableEq n] [DecidableEq r]

/-- The actual rectangular polar Newton recursion. -/
def polarNewtonIterate (A : Matrix m n ℂ) : ℕ → Matrix m n ℂ
  | 0 => A
  | k + 1 => (1 / 2 : ℝ) • (polarNewtonIterate A k + (moorePenroseInverse (polarNewtonIterate A k))ᴴ)

omit [DecidableEq m] [DecidableEq n] in
/-- The fixed-direction scalar representation of the actual matrix recurrence.
No sorting assumption is imposed on intermediate coefficient functions.
Source: Higham (1986), §3.2; rectangular extension via the Moore–Penrose inverse.
atlas: polar-newton-iteration (partial) -/
theorem IsThinSVD.polarNewtonIterate_eq {A : Matrix m n ℂ} {U : Matrix m r ℂ}
    {V : Matrix n r ℂ} {σ : r → ℝ} (h : IsThinSVD A U V σ) (k : ℕ) :
    polarNewtonIterate A k = thinSingularMatrix U V (fun i => polarNewtonScalar (σ i) k) := by
  induction k with
  | zero => exact h.eq
  | succ k ih =>
    let f : r → ℝ := fun i => polarNewtonScalar (σ i) k
    have ht : IsThinSVD (thinSingularMatrix U V f) U V f :=
      ⟨h.left_orth, h.right_orth, fun i => polarNewtonScalar_pos (h.pos i) k, rfl⟩
    rw [polarNewtonIterate, ih, ht.moorePenroseInverse_eq]
    simp only [← RCLike.ofReal_inv]
    change (1 / 2 : ℝ) • (thinSingularMatrix U V f +
      (thinSingularMatrix V U (fun i => (f i)⁻¹))ᴴ) = _
    rw [thinSingularMatrix_conjTranspose, thinSingularMatrix_add, thinSingularMatrix_smul]
    congr 1
    funext i
    dsimp only [f, polarNewtonScalar]
    ring

omit [DecidableEq m] [DecidableEq n] in
/-- Every Newton iterate retains the full original rank, including arbitrary
rank-deficient matrices and the empty singular block. -/
theorem IsThinSVD.rank_polarNewtonIterate {A : Matrix m n ℂ} {U : Matrix m r ℂ}
    {V : Matrix n r ℂ} {σ : r → ℝ} (h : IsThinSVD A U V σ) (k : ℕ) :
    (polarNewtonIterate A k).rank = A.rank := by
  have ht : IsThinSVD (polarNewtonIterate A k) U V (fun i => polarNewtonScalar (σ i) k) :=
    ⟨h.left_orth, h.right_orth, fun i => polarNewtonScalar_pos (h.pos i) k,
      h.polarNewtonIterate_eq k⟩
  exact ht.rank_eq_card.trans h.rank_eq_card.symm

omit [DecidableEq m] [DecidableEq n] in
/-- Exact closed formula in each fixed positive singular direction.
Source: Higham (1986), equations (3.4)–(3.7).
atlas: polar-newton-iteration (partial) -/
theorem IsThinSVD.polarNewtonIterate_closed_form {A : Matrix m n ℂ} {U : Matrix m r ℂ}
    {V : Matrix n r ℂ} {σ : r → ℝ} (h : IsThinSVD A U V σ) (k : ℕ) :
    polarNewtonIterate A k = thinSingularMatrix U V (fun i =>
      (1 + ((σ i - 1) / (σ i + 1)) ^ (2 ^ k)) /
        (1 - ((σ i - 1) / (σ i + 1)) ^ (2 ^ k))) := by
  rw [h.polarNewtonIterate_eq]
  congr 1
  funext i
  exact polarNewtonScalar_eq (h.pos i) k

/-- The finite maximum of the absolute initial Cayley coordinates. -/
def polarNewtonRadius (σ : r → ℝ) : ℝ := ‖fun i => (σ i - 1) / (σ i + 1)‖

omit [DecidableEq r] in
/-- Positivity of the singular values forces the Newton radius below one,
also when the retained singular block is empty. -/
theorem polarNewtonRadius_lt_one {σ : r → ℝ} (hσ : ∀ i, 0 < σ i) :
    polarNewtonRadius σ < 1 := by
  apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr
  intro i
  exact abs_cayley_lt_one (hσ i)

/-- Explicit double-exponential spectral-norm error for the actual rectangular
Newton iteration. The empty singular block also satisfies this bound.
Source: Higham (1986), §3.2.
atlas: polar-newton-iteration (partial) -/
theorem IsThinSVD.specNorm_polarNewtonIterate_sub_polar_le
    {A : Matrix m n ℂ} {U : Matrix m r ℂ} {V : Matrix n r ℂ} {σ : r → ℝ}
    (h : IsThinSVD A U V σ) (k : ℕ) :
    specNorm (polarNewtonIterate A k - canonicalPartialPolar A) ≤
      2 * polarNewtonRadius σ ^ (2 ^ k) / (1 - polarNewtonRadius σ ^ (2 ^ k)) := by
  have hr : 0 ≤ polarNewtonRadius σ := norm_nonneg _
  have hr1 := polarNewtonRadius_lt_one h.pos
  have hp : polarNewtonRadius σ ^ (2 ^ k) < 1 := pow_lt_one₀ hr hr1 (by positivity)
  have hQ : canonicalPartialPolar A = thinSingularMatrix U V (fun _ => 1) := by
    rw [h.canonicalPartialPolar_eq]
    simp [thinSingularMatrix]
  rw [h.polarNewtonIterate_eq, hQ, thinSingularMatrix_sub,
    specNorm_thinSingularMatrix U V h.left_orth h.right_orth]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  apply abs_polarNewtonScalar_sub_one_le (h.pos i) hr hr1
  exact norm_le_pi_norm (fun i => (σ i - 1) / (σ i + 1)) i

omit [DecidableEq m] in
/-- Every rectangular complex input converges to its canonical partial polar
factor under the actual pseudoinverse Newton recurrence.
Source: Higham (1986), §3.2, with the fixed-rank SVD extension.
atlas: polar-newton-iteration (partial) -/
theorem IsThinSVD.tendsto_polarNewtonIterate {A : Matrix m n ℂ} {U : Matrix m r ℂ}
    {V : Matrix n r ℂ} {σ : r → ℝ} (h : IsThinSVD A U V σ) :
    Tendsto (polarNewtonIterate A) atTop (𝓝 (canonicalPartialPolar A)) := by
  have hs : Tendsto (fun k i => polarNewtonScalar (σ i) k) atTop (𝓝 (fun _ : r => (1 : ℝ))) :=
    tendsto_pi_nhds.mpr (fun i => tendsto_polarNewtonScalar (h.pos i))
  have hc : Continuous (fun f : r → ℝ => thinSingularMatrix U V f) := by
    unfold thinSingularMatrix
    fun_prop
  have ht := hc.continuousAt.tendsto.comp hs
  have he : (fun k => thinSingularMatrix U V (fun i => polarNewtonScalar (σ i) k)) =
      polarNewtonIterate A := funext (fun k => (h.polarNewtonIterate_eq k).symm)
  change Tendsto (fun k => thinSingularMatrix U V (fun i => polarNewtonScalar (σ i) k))
    atTop (𝓝 (thinSingularMatrix U V (fun _ => 1))) at ht
  rw [he] at ht
  simpa only [thinSingularMatrix, RCLike.ofReal_one, Matrix.diagonal_one, Matrix.mul_one,
    ← h.canonicalPartialPolar_eq] using ht

omit [DecidableEq m] in
/-- Rank preservation for the actual matrix recursion, without an SVD premise.
Source: Higham (1986), §3.2.
atlas: polar-newton-iteration (partial) -/
theorem rank_polarNewtonIterate (A : Matrix m n ℂ) (k : ℕ) :
    (polarNewtonIterate A k).rank = A.rank := by
  obtain ⟨U, V, h⟩ := exists_isThinSVD A
  exact h.rank_polarNewtonIterate k

omit [DecidableEq m] in
/-- Convergence for every matrix to its canonical partial polar factor.
For full column rank this target is the unique polar isometry and has the
inverse-square-root formula in `canonicalPartialPolar_eq_mul_inv_sqrt`.
Source: Higham (1986), §3.2, rectangular fixed-rank extension.
atlas: polar-newton-iteration -/
theorem tendsto_polarNewtonIterate (A : Matrix m n ℂ) :
    Tendsto (polarNewtonIterate A) atTop (𝓝 (canonicalPartialPolar A)) := by
  obtain ⟨U, V, h⟩ := exists_isThinSVD A
  exact h.tendsto_polarNewtonIterate

/-- The explicit Newton rate uses the actual positive singular values of the
input matrix. No spectral or convergence certificate is required as input.
Source: Higham (1986), equations (3.4)–(3.7).
atlas: polar-newton-iteration (partial) -/
theorem specNorm_polarNewtonIterate_sub_polar_le (A : Matrix m n ℂ) (k : ℕ) :
    specNorm (polarNewtonIterate A k - canonicalPartialPolar A) ≤
      2 * polarNewtonRadius (fun i : Fin A.rank => singularValues A i) ^ (2 ^ k) /
        (1 - polarNewtonRadius (fun i : Fin A.rank => singularValues A i) ^ (2 ^ k)) := by
  obtain ⟨U, V, h⟩ := exists_isThinSVD A
  exact h.specNorm_polarNewtonIterate_sub_polar_le k

end NLAlib
