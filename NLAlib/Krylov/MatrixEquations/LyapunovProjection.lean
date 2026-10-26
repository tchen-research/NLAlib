import NLAlib.Krylov.MatrixEquations.LyapunovProjectionIdentity
import NLAlib.Matrix.Equations.LyapunovDissipative

/-!
# Solvability and forward error for projected Lyapunov equations

Strict dissipativity gives unique positive semidefinite full and compressed solutions.
Finite-dimensional coercivity and Hermitian eigenvector tests turn the exact small
residual into Frobenius and spectral forward-error bounds, both with constant `1/(2a)`.
Source: the supplied derivations, K17–K19; residual setting from Simoncini, §5.2.1.
-/

noncomputable section
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib
variable {𝕜 n k l s : Type*} [RCLike 𝕜]
  [Fintype n] [Fintype k] [Fintype l] [Fintype s]
  [DecidableEq n] [DecidableEq k] [DecidableEq l]

omit [Fintype k] [Fintype l] [Fintype s] [DecidableEq k] [DecidableEq l] in
/-- The half-Hermitian-part convention is equivalent to the doubled dissipativity bound. -/
theorem add_conjTranspose_le_of_half_le {A : Matrix n n 𝕜} {a : ℝ}
    (hA : (1 / 2 : ℝ) • (A + Aᴴ) ≤ (-a) • (1 : Matrix n n 𝕜)) :
    A + Aᴴ ≤ (-2 * a) • (1 : Matrix n n 𝕜) := by
  have h := smul_le_smul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul,
    show (2 : ℝ) * -a = -2 * a by ring] using h

omit [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] in
/-- Strict dissipativity supplies a unique full Lyapunov solution, which is PSD.
atlas: lyapunov-projection-residual-certificate (partial) -/
theorem existsUnique_posSemidef_lyapunov {A : Matrix n n 𝕜} {a : ℝ} (ha : 0 < a)
    (hA : (1 / 2 : ℝ) • (A + Aᴴ) ≤ (-a) • (1 : Matrix n n 𝕜))
    (B : Matrix n s 𝕜) :
    (∃! X : Matrix n n 𝕜, A * X + X * Aᴴ + B * Bᴴ = 0) ∧
      ∀ X : Matrix n n 𝕜, A * X + X * Aᴴ + B * Bᴴ = 0 → X.PosSemidef := by
  have hq := re_quadForm_le_of_add_conjTranspose_le (add_conjTranspose_le_of_half_le hA)
  exact ⟨existsUnique_lyapunov_of_quadratic_bound ha hq _, fun X hX =>
    posSemidef_lyapunov_solution_of_quadratic_bound ha hq
      (Matrix.posSemidef_self_mul_conjTranspose B) hX⟩

omit [Fintype l] [DecidableEq l] in
/-- Orthonormal compression preserves unique PSD solvability, with no separate
stability hypothesis on the reduced matrix.
atlas: lyapunov-projection-residual-certificate (partial) -/
theorem existsUnique_posSemidef_compressedLyapunov {A : Matrix n n 𝕜}
    {V : Matrix n k 𝕜} {a : ℝ} (ha : 0 < a)
    (hA : (1 / 2 : ℝ) • (A + Aᴴ) ≤ (-a) • (1 : Matrix n n 𝕜))
    (hV : HasOrthonormalCols V) (Bk : Matrix k s 𝕜) :
    let H := Vᴴ * A * V
    (∃! Y : Matrix k k 𝕜, H * Y + Y * Hᴴ + Bk * Bkᴴ = 0) ∧
      ∀ Y : Matrix k k 𝕜, H * Y + Y * Hᴴ + Bk * Bkᴴ = 0 → Y.PosSemidef := by
  dsimp only
  have hq := re_quadForm_le_of_add_conjTranspose_le (add_conjTranspose_le_of_half_le hA)
  have hc := re_quadForm_compression_le hq hV
  exact ⟨existsUnique_lyapunov_of_quadratic_bound ha hc _, fun Y hY =>
    posSemidef_lyapunov_solution_of_quadratic_bound ha hc
      (Matrix.posSemidef_self_mul_conjTranspose Bk) hY⟩

/-- Both forward-error bounds for the actual full and projected Lyapunov solutions.
The reduced solution's Hermitian property follows from dissipativity and its equation.
atlas: lyapunov-projection-residual-certificate (partial) -/
theorem projectedLyapunov_forward_error {A X : Matrix n n 𝕜}
    {V : Matrix n k 𝕜} {U : Matrix n l 𝕜} {H Y : Matrix k k 𝕜}
    {T : Matrix l k 𝕜} {B : Matrix n s 𝕜} {Bk : Matrix k s 𝕜} {a : ℝ}
    (ha : 0 < a)
    (hA : (1 / 2 : ℝ) • (A + Aᴴ) ≤ (-a) • (1 : Matrix n n 𝕜))
    (hV : HasOrthonormalCols V) (hU : HasOrthonormalCols U) (hVU : Vᴴ * U = 0)
    (hAV : A * V = V * H + U * T) (hB : B = V * Bk)
    (hX : A * X + X * Aᴴ + B * Bᴴ = 0)
    (hY : H * Y + Y * Hᴴ + Bk * Bkᴴ = 0) :
    frobNorm (X - V * Y * Vᴴ) ≤ Real.sqrt 2 * frobNorm (T * Y) / (2 * a) ∧
      specNorm (X - V * Y * Vᴴ) ≤ specNorm (T * Y) / (2 * a) := by
  have hq := re_quadForm_le_of_add_conjTranspose_le (add_conjTranspose_le_of_half_le hA)
  have hH := compression_eq_of_arnoldi_relation hV hVU hAV
  have hc := re_quadForm_compression_le hq hV
  rw [hH] at hc
  have hXH := isHermitian_lyapunov_solution ha hq
    (Matrix.isHermitian_mul_conjTranspose_self B) hX
  have hYH := isHermitian_lyapunov_solution ha hc
    (Matrix.isHermitian_mul_conjTranspose_self Bk) hY
  have hEH := hXH.sub (Matrix.isHermitian_mul_mul_conjTranspose V hYH)
  have hR := projectedLyapunov_residual_norms_and_rank hV hU hVU hAV hB hYH hY
  have he : A * (X - V * Y * Vᴴ) + (X - V * Y * Vᴴ) * Aᴴ =
      -(A * (V * Y * Vᴴ) + (V * Y * Vᴴ) * Aᴴ + B * Bᴴ) := by
    have hx := eq_neg_of_add_eq_zero_left hX
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    calc
      _ = (A * X + X * Aᴴ) - (A * (V * Y * Vᴴ) + (V * Y * Vᴴ) * Aᴴ) := by abel
      _ = _ := by rw [hx]; abel
  have hf := frobNorm_le_lyapunov_div ha hq (X - V * Y * Vᴴ)
  have hs := specNorm_le_lyapunov_div ha hq hEH
  rw [he, frobNorm_neg, hR.1] at hf
  rw [he, specNorm_neg, hR.2.1] at hs
  exact ⟨hf, hs⟩

end NLAlib
