import NLAlib.Matrix.Functions.LyapunovADI
import NLAlib.Matrix.Basic.RankBounds
import NLAlib.Matrix.Norms.GramSymmetry

/-! # Factors, ranks and residual norms of the actual Lyapunov ADI iterates -/
noncomputable section
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {K n s : Type*} [RCLike K] [Fintype n] [Fintype s] [DecidableEq n]

/-- The solved factor at step `j` of the actual ADI process. -/
def lyapunovADIUpdateFactor (A : Matrix n n K) (B : Matrix n s K) (p : ℕ → ℝ)
    (j : ℕ) : Matrix n s K := lyapunovADISolve A (p j) (lyapunovADI A B p j).1

/-- The actual accumulated low-rank factor, with `j * s` columns. -/
def lyapunovADIFactor (A : Matrix n n K) (B : Matrix n s K) (p : ℕ → ℝ)
    (j : ℕ) : Matrix n (Fin j × s) K := fun a i =>
  (Real.sqrt (2 * p i.1) : K) * lyapunovADIUpdateFactor A B p i.1 a i.2

private theorem lyapunovADI_snd_sum (A : Matrix n n K) (B : Matrix n s K)
    (p : ℕ → ℝ) (j : ℕ) :
    (lyapunovADI A B p j).2 = ∑ i ∈ Finset.range j,
      (2 * p i : K) • (lyapunovADIUpdateFactor A B p i * (lyapunovADIUpdateFactor A B p i)ᴴ) := by
  induction j with
  | zero => simp [lyapunovADI]
  | succ j hj => rw [Finset.sum_range_succ, ← hj]; rfl

/-- The accumulated factor represents the actual computed iterate exactly.
Source: user derivations, low-rank ADI factor update.
atlas: lyapunov-adi-residual-factor (partial) -/
theorem lyapunovADIFactor_mul_conjTranspose (A : Matrix n n K) (B : Matrix n s K)
    (p : ℕ → ℝ) (hp : ∀ j, 0 < p j) (j : ℕ) :
    lyapunovADIFactor A B p j * (lyapunovADIFactor A B p j)ᴴ = (lyapunovADI A B p j).2 := by
  rw [lyapunovADI_snd_sum, ← Fin.sum_univ_eq_sum_range]
  ext a b
  rw [Matrix.sum_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, lyapunovADIFactor,
    Matrix.smul_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp only [star_mul, RCLike.star_def, RCLike.conj_ofReal]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  have hs : (Real.sqrt (2 * p i) : K) ^ 2 = (2 * p i : K) := by
    exact_mod_cast Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hp i).le)
  calc
    _ = (Real.sqrt (2 * p i) : K) ^ 2 *
        (lyapunovADIUpdateFactor A B p i a c * (starRingEnd K) (lyapunovADIUpdateFactor A B p i b c)) := by ring
    _ = _ := by rw [hs]

/-- Every solved update factor has rank at most that of the original forcing factor. -/
theorem rank_lyapunovADIUpdateFactor_le (A : Matrix n n K) (B : Matrix n s K)
    (p : ℕ → ℝ) (hP : ∀ j, IsUnit (A - (p j : K) • 1).det) (j : ℕ) :
    (lyapunovADIUpdateFactor A B p j).rank ≤ B.rank := by
  unfold lyapunovADIUpdateFactor lyapunovADISolve
  exact (Matrix.rank_mul_le_right _ _).trans
    ((congrArg Matrix.rank (lyapunovADI_fst A B p hP j)).le.trans (Matrix.rank_mul_le_right _ _))

/-- The actual iterate has the sharp uncompressed rank bound `j * rank B`,
which in turn is at most `j * s`. -/
theorem rank_lyapunovADI_snd_le (A : Matrix n n K) (B : Matrix n s K)
    (p : ℕ → ℝ) (hP : ∀ j, IsUnit (A - (p j : K) • 1).det) (j : ℕ) :
    (lyapunovADI A B p j).2.rank ≤ j * B.rank := by
  induction j with
  | zero => simp [lyapunovADI]
  | succ j hj =>
    let V := lyapunovADIUpdateFactor A B p j
    change ((lyapunovADI A B p j).2 + (2 * p j : K) • (V * Vᴴ)).rank ≤ _
    have hinc : ((2 * p j : K) • (V * Vᴴ)).rank ≤ B.rank := by
      have he : (2 * p j : K) • (V * Vᴴ) = ((2 * p j : K) • (1 : Matrix n n K)) * (V * Vᴴ) := by simp
      rw [he]
      exact (Matrix.rank_mul_le_right _ _).trans ((Matrix.rank_mul_le_left _ _).trans
        (rank_lyapunovADIUpdateFactor_le A B p hP j))
    exact (rank_add_le _ _).trans (by nlinarith)

/-- The residual spectral norm is the square of the residual-factor norm. -/
theorem specNorm_lyapunovADI_residual [DecidableEq s] (A : Matrix n n K)
    (B : Matrix n s K) (p : ℕ → ℝ) (hP : ∀ j, IsUnit (A - (p j : K) • 1).det) (j : ℕ) :
    specNorm (A * (lyapunovADI A B p j).2 + (lyapunovADI A B p j).2 * Aᴴ + B * Bᴴ) =
      specNorm (lyapunovADI A B p j).1 ^ 2 := by
  rw [lyapunovADI_residual A B p hP, specNorm_mul_conjTranspose_self]

/-- The residual Frobenius norm can be computed from its smaller column Gram. -/
theorem frobNorm_lyapunovADI_residual (A : Matrix n n K) (B : Matrix n s K)
    (p : ℕ → ℝ) (hP : ∀ j, IsUnit (A - (p j : K) • 1).det) (j : ℕ) :
    frobNorm (A * (lyapunovADI A B p j).2 + (lyapunovADI A B p j).2 * Aᴴ + B * Bᴴ) =
      frobNorm ((lyapunovADI A B p j).1ᴴ * (lyapunovADI A B p j).1) := by
  rw [lyapunovADI_residual A B p hP, frobNorm_mul_conjTranspose_eq_conjTranspose_mul]

end NLAlib
