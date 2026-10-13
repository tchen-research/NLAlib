import NLAlib.Matrix.Functions.PolynomialCalculus
/-!
# Diagonal polynomial filter envelopes

Spectral-norm envelopes for polynomial filters of rectangular diagonal matrices over `[RCLike 𝕜]`:
a real polynomial `p` applied to the Gram matrix `Σᴴ Σ` of `Σ = rectDiag s` acts on the diagonal
by `s i ↦ s i · p(s i²)` (`rectDiag_mul_aeval_gram`), so entrywise bounds on the scalar filter
give exact spectral-norm bounds (`specNorm_rectDiag_le`), and the leading block of the filter is
invertible with an explicit diagonal inverse whose norm is controlled by a lower envelope
(`aeval_gram_diagonal_mul_diagonal_inv_eq_one`, `specNorm_diagonal_inv_le`). These convert the
block polynomial-filter bound of the randomized range finder to its scalar form.

Halko–Martinsson–Tropp 2011, §2.1 and §10; Gu 2015, §4. Helpers for
`polynomial-filter-range-finder`.
-/

noncomputable section
open Polynomial
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜]

/-- A real polynomial of a real diagonal matrix cast to `𝕜` is the diagonal of the values:
`p(diag (d : 𝕜)) = diag (p(d) : 𝕜)`. -/
theorem aeval_diagonal_ofReal {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) (p : ℝ[X]) :
    aeval (Matrix.diagonal fun i => (d i : 𝕜)) p =
      Matrix.diagonal fun i => ((p.eval (d i) : ℝ) : 𝕜) := by
  have h₁ : (Matrix.diagonal fun i => (d i : 𝕜)) =
      (Algebra.ofId ℝ 𝕜).mapMatrix (Matrix.diagonal d) := by
    ext i j
    by_cases hij : i = j <;> simp [hij, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one]
  rw [h₁, Polynomial.aeval_algHom_apply, aeval_diagonal]
  ext i j
  by_cases hij : i = j <;> simp [hij, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one]

/-- **Spectral norm of a rectangular diagonal matrix** is at most any bound on the absolute
values of its diagonal entries (empty blocks included). Halko–Martinsson–Tropp 2011, §2.1. -/
theorem specNorm_rectDiag_le {m n : ℕ} {s : ℕ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hs : ∀ i, i < min m n → |s i| ≤ b) :
    specNorm (rectDiag s : Matrix (Fin m) (Fin n) 𝕜) ≤ b := by
  apply (sq_le_sq₀ (specNorm_nonneg _) hb).mp
  rw [specNorm_sq_eq_specNorm_conjTranspose_mul_self, conjTranspose_rectDiag_mul_rectDiag,
    specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (sq_nonneg b)).2
  intro j
  split_ifs with hj
  · rw [RCLike.norm_ofReal, abs_of_nonneg (sq_nonneg _)]
    have h := hs j (lt_min hj j.isLt)
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb).2 h
  · simpa using sq_nonneg b

/-- **Filtering a rectangular diagonal by a polynomial of its Gram matrix** acts on the diagonal:
`Σ p(Σᴴ Σ) = rectDiag (s i · p(s i²))`. Halko–Martinsson–Tropp 2011, §10 (the power scheme). -/
theorem rectDiag_mul_aeval_gram (s : ℕ → ℝ) (p : ℝ[X]) {m n : ℕ} :
    (rectDiag s : Matrix (Fin m) (Fin n) 𝕜) *
      aeval ((rectDiag s : Matrix (Fin m) (Fin n) 𝕜)ᴴ *
        (rectDiag s : Matrix (Fin m) (Fin n) 𝕜)) p =
      rectDiag (fun i => s i * p.eval (s i ^ 2)) := by
  rw [conjTranspose_rectDiag_mul_rectDiag,
    show (Matrix.diagonal fun j : Fin n => if (j : ℕ) < m then ((s j ^ 2 : ℝ) : 𝕜) else 0) =
      Matrix.diagonal fun j : Fin n => ((if (j : ℕ) < m then s j ^ 2 else 0 : ℝ) : 𝕜) by
      congr 1; funext j; split_ifs <;> simp,
    aeval_diagonal_ofReal]
  ext i j
  rw [Matrix.mul_diagonal]
  simp only [rectDiag_apply_ofReal]
  by_cases hij : (i : ℕ) = j
  · simp [← hij, i.isLt]
  · simp only [if_neg hij, zero_mul]

/-- The polynomial filter of the Gram matrix of a square diagonal is invertible by the diagonal
of reciprocals: `p(Sᴴ S) · diag (p(s i²)⁻¹) = 1` when `p` does not vanish on the squared
entries. Halko–Martinsson–Tropp 2011, §10. -/
theorem aeval_gram_diagonal_mul_diagonal_inv_eq_one {k : Type*} [Fintype k] [DecidableEq k]
    (s : k → ℝ) (p : ℝ[X]) (hne : ∀ i, p.eval (s i ^ 2) ≠ 0) :
    aeval ((Matrix.diagonal fun i => (s i : 𝕜))ᴴ * Matrix.diagonal fun i => (s i : 𝕜)) p *
      Matrix.diagonal (fun i => (((p.eval (s i ^ 2))⁻¹ : ℝ) : 𝕜)) = 1 := by
  rw [Matrix.diagonal_conjTranspose,
    show star (fun i => (s i : 𝕜)) = fun i => (s i : 𝕜) by
      funext i; simp [Pi.star_apply, RCLike.conj_ofReal],
    Matrix.diagonal_mul_diagonal,
    show (fun i => (s i : 𝕜) * (s i : 𝕜)) = fun i => ((s i ^ 2 : ℝ) : 𝕜) by
      funext i; simp [sq],
    aeval_diagonal_ofReal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [← RCLike.ofReal_mul, mul_inv_cancel₀ (hne i), RCLike.ofReal_one]

/-- The diagonal of reciprocals of a filter has spectral norm at most the reciprocal of a positive
lower envelope on the filter values: `c ≤ |p(s i²)|` for all `i` gives
`‖diag (p(s i²)⁻¹)‖₂ ≤ 1 / c`. Halko–Martinsson–Tropp 2011, §10. -/
theorem specNorm_diagonal_inv_le {k : Type*} [Fintype k] [DecidableEq k]
    (s : k → ℝ) (p : ℝ[X]) {c : ℝ} (hc : 0 < c) (hmin : ∀ i, c ≤ |p.eval (s i ^ 2)|) :
    specNorm (Matrix.diagonal fun i => (((p.eval (s i ^ 2))⁻¹ : ℝ) : 𝕜)) ≤ 1 / c := by
  rw [specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  rw [RCLike.norm_ofReal, abs_inv, ← one_div]
  exact one_div_le_one_div_of_le hc (hmin i)

end NLAlib
