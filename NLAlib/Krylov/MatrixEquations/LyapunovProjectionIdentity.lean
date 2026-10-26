import NLAlib.Matrix.Norms.OrthogonalOffDiagonal

/-!
# Exact residual certificates for projected Lyapunov equations

The Arnoldi relation and the reduced equation expose the residual as an
off-diagonal coupling. Its two norms and rank are computed on the small block `TY`.
Source: Simoncini, *Computational methods for linear matrix equations*, §5.2.1;
the exact rank and spectral-norm formulas follow from the orthogonal block identity.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
variable {𝕜 n k l s : Type*} [RCLike 𝕜]
  [Fintype n] [Fintype k] [Fintype l] [Fintype s]
  [DecidableEq n] [DecidableEq k] [DecidableEq l]

omit [Fintype s] [DecidableEq n] [DecidableEq l] in
/-- The small operator in an orthogonal Arnoldi relation is the actual compression. -/
theorem compression_eq_of_arnoldi_relation {A : Matrix n n 𝕜}
    {V : Matrix n k 𝕜} {U : Matrix n l 𝕜} {H : Matrix k k 𝕜} {T : Matrix l k 𝕜}
    (hV : HasOrthonormalCols V) (hVU : Vᴴ * U = 0)
    (hAV : A * V = V * H + U * T) : Vᴴ * A * V = H := by
  rw [Matrix.mul_assoc, hAV, Matrix.mul_add, ← Matrix.mul_assoc Vᴴ V,
    ← Matrix.mul_assoc Vᴴ U, hV.conjTranspose_mul_self, hVU,
    Matrix.one_mul, Matrix.zero_mul, add_zero]

omit [DecidableEq n] [DecidableEq k] [DecidableEq l] in
/-- Exact projected Lyapunov residual, without any stability assumption.
atlas: lyapunov-projection-residual-certificate (partial) -/
theorem projectedLyapunov_residual_eq {A : Matrix n n 𝕜}
    {V : Matrix n k 𝕜} {U : Matrix n l 𝕜} {H Y : Matrix k k 𝕜}
    {T : Matrix l k 𝕜} {B : Matrix n s 𝕜} {Bk : Matrix k s 𝕜}
    (hAV : A * V = V * H + U * T) (hB : B = V * Bk)
    (hY : H * Y + Y * Hᴴ + Bk * Bkᴴ = 0) :
    A * (V * Y * Vᴴ) + (V * Y * Vᴴ) * Aᴴ + B * Bᴴ =
      U * T * Y * Vᴴ + V * Y * Tᴴ * Uᴴ := by
  have hadj : Vᴴ * Aᴴ = Hᴴ * Vᴴ + Tᴴ * Uᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_add] using
      congrArg Matrix.conjTranspose hAV
  have hl : A * (V * Y * Vᴴ) = (V * H + U * T) * Y * Vᴴ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hAV]
  have hr : V * Y * Vᴴ * Aᴴ = V * Y * (Hᴴ * Vᴴ + Tᴴ * Uᴴ) := by
    rw [Matrix.mul_assoc (V * Y), hadj]
  calc
    _ = V * (H * Y + Y * Hᴴ + Bk * Bkᴴ) * Vᴴ +
        (U * T * Y * Vᴴ + V * Y * Tᴴ * Uᴴ) := by
      rw [hl, hr, hB]
      simp only [Matrix.conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
      abel
    _ = _ := by rw [hY, Matrix.mul_zero, Matrix.zero_mul, zero_add]

/-- Both residual norms and the exact rank are computed on the small coupling.
Zero-width and zero-rank couplings are included.
atlas: lyapunov-projection-residual-certificate (partial) -/
theorem projectedLyapunov_residual_norms_and_rank {A : Matrix n n 𝕜}
    {V : Matrix n k 𝕜} {U : Matrix n l 𝕜} {H Y : Matrix k k 𝕜}
    {T : Matrix l k 𝕜} {B : Matrix n s 𝕜} {Bk : Matrix k s 𝕜}
    (hV : HasOrthonormalCols V) (hU : HasOrthonormalCols U) (hVU : Vᴴ * U = 0)
    (hAV : A * V = V * H + U * T) (hB : B = V * Bk)
    (hYH : Y.IsHermitian) (hY : H * Y + Y * Hᴴ + Bk * Bkᴴ = 0) :
    let R := A * (V * Y * Vᴴ) + (V * Y * Vᴴ) * Aᴴ + B * Bᴴ
    frobNorm R = Real.sqrt 2 * frobNorm (T * Y) ∧
      specNorm R = specNorm (T * Y) ∧ R.rank = 2 * (T * Y).rank := by
  dsimp only
  rw [projectedLyapunov_residual_eq hAV hB hY]
  have he : U * T * Y * Vᴴ + V * Y * Tᴴ * Uᴴ =
      U * (T * Y) * Vᴴ + V * (T * Y)ᴴ * Uᴴ := by
    simp only [Matrix.conjTranspose_mul, hYH.eq, Matrix.mul_assoc]
  rw [he]
  have h := norms_and_rank_orthogonalCoupling hV hU hVU (T * Y)
  refine ⟨?_, h.2⟩
  rw [frobNorm, h.1, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), frobNorm]

end NLAlib
