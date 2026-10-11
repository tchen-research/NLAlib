import NLAlib.Matrix.DiagonalFilter
import NLAlib.Matrix.PolynomialIntertwining
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Complex diagonal polynomial filter envelopes

Real-coefficient polynomial calculus commutes with the real-to-complex
embedding. Rectangular diagonal filters and inverse leading filters retain
their explicit scalar envelopes, including empty head or tail blocks.
Source: operator manuscript `sa:filter`; supports `polynomial-filter-range-finder`.
-/

noncomputable section
set_option autoImplicit false
open Polynomial
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

/-- Real-coefficient matrix polynomial evaluation commutes with the canonical
complex embedding. Source: manuscript `sa:filter`, polynomial intertwining. -/
theorem aeval_map_ofReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (p : ℝ[X]) :
    (aeval A p).map Complex.ofReal = aeval (A.map Complex.ofReal) p := by
  exact (Polynomial.aeval_algHom_apply Complex.ofRealAm.mapMatrix A p).symm

/-- Complexifying rectangular real matrices preserves multiplication.
Source: the scalar algebra embedding; supports `polynomial-filter-range-finder`. -/
theorem map_ofReal_mul {ι κ ρ : Type*} [Fintype κ]
    (A : Matrix ι κ ℝ) (B : Matrix κ ρ ℝ) :
    (A * B).map Complex.ofReal = A.map Complex.ofReal * B.map Complex.ofReal := by
  exact Matrix.map_mul (f := Complex.ofRealHom)

/-- The adjoint of a complexified real matrix is its complexified transpose.
Source: conjugation fixes real scalars; supports `polynomial-filter-range-finder`. -/
theorem conjTranspose_map_ofReal {ι κ : Type*} (A : Matrix ι κ ℝ) :
    (A.map Complex.ofReal)ᴴ = A.transpose.map Complex.ofReal := by
  ext i j
  simp

/-- A complexified real rectangular diagonal has operator norm bounded by
any nonnegative absolute envelope, also for empty blocks.
Source: manuscript `sa:filter`, scalar filter envelope. -/
theorem norm_rectDiag_map_ofReal_le {m n : ℕ} {s : ℕ → ℝ} {b : ℝ}
    (hb : 0 ≤ b) (hs : ∀ i, i < min m n → |s i| ≤ b) :
    ‖(rectDiag s : Matrix (Fin m) (Fin n) ℝ).map Complex.ofReal‖ ≤ b := by
  apply (sq_le_sq₀ (norm_nonneg _) hb).mp
  rw [pow_two, ← Matrix.l2_opNorm_conjTranspose_mul_self,
    conjTranspose_map_ofReal, ← map_ofReal_mul, transpose_rectDiag_mul_rectDiag]
  rw [Matrix.diagonal_map (by simp : Complex.ofReal 0 = 0), Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (sq_nonneg b)).2
  intro j
  simp only [Complex.norm_real, Real.norm_eq_abs]
  split_ifs with hj
  · rw [abs_of_nonneg (sq_nonneg _)]
    have h := hs j (lt_min hj j.isLt)
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb).2 h
  · simpa using sq_nonneg b

/-- Filtering a complexified rectangular diagonal evaluates the real filter
at squared diagonal entries. Source: manuscript `sa:filter`, definition of D. -/
theorem rectDiag_map_ofReal_mul_aeval_conjGram
    (s : ℕ → ℝ) (p : ℝ[X]) {m n : ℕ} :
    let S := (rectDiag s : Matrix (Fin m) (Fin n) ℝ).map Complex.ofReal
    S * aeval (Sᴴ * S) p =
      (rectDiag (fun i => s i * p.eval (s i ^ 2)) :
        Matrix (Fin m) (Fin n) ℝ).map Complex.ofReal := by
  dsimp only
  rw [conjTranspose_map_ofReal, ← map_ofReal_mul, ← aeval_map_ofReal,
    ← map_ofReal_mul, rectDiag_mul_aeval_gram]

/-- A scalar envelope controls the actual complex rectangular filtered tail.
Source: manuscript `sa:filter`, scalar maximum/minimum bound. -/
theorem norm_rectDiag_map_ofReal_mul_aeval_conjGram_le
    {m n : ℕ} (s : ℕ → ℝ) (p : ℝ[X]) {τ : ℝ} (hτ : 0 ≤ τ)
    (hmax : ∀ i, i < min m n → |s i * p.eval (s i ^ 2)| ≤ τ) :
    let S := (rectDiag s : Matrix (Fin m) (Fin n) ℝ).map Complex.ofReal
    ‖S * aeval (Sᴴ * S) p‖ ≤ τ := by
  dsimp only
  rw [rectDiag_map_ofReal_mul_aeval_conjGram]
  exact norm_rectDiag_map_ofReal_le hτ hmax

/-- The leading complex polynomial filter has its actual diagonal right
inverse with norm at most the reciprocal of a positive lower envelope.
Source: manuscript `sa:filter`, c-phi; includes the empty leading block. -/
theorem diagonal_complex_filter_right_inverse_and_norm_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → ℝ) (p : ℝ[X])
    {c : ℝ} (hc : 0 < c) (hmin : ∀ i, c ≤ |p.eval (s i ^ 2)|) :
    let S := Matrix.diagonal (fun i => (s i : ℂ))
    let R := Matrix.diagonal (fun i => Complex.ofReal ((p.eval (s i ^ 2))⁻¹))
    aeval (Sᴴ * S) p * R = 1 ∧ ‖R‖ ≤ 1 / c := by
  dsimp only
  have hne : ∀ i, p.eval (s i ^ 2) ≠ 0 := by
    intro i hi
    have h := hmin i
    rw [hi, abs_zero] at h
    linarith
  constructor
  · have hreal : aeval ((Matrix.diagonal s).transpose * Matrix.diagonal s) p *
        Matrix.diagonal (fun i => (p.eval (s i ^ 2))⁻¹) = 1 := by
      rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, aeval_diagonal,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      simpa only [pow_two] using mul_inv_cancel₀ (hne i)
    have hS : Matrix.diagonal (fun i => (s i : ℂ)) =
        (Matrix.diagonal s).map Complex.ofReal := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    have hR : Matrix.diagonal (fun i => Complex.ofReal ((p.eval (s i ^ 2))⁻¹)) =
        (Matrix.diagonal (fun i => (p.eval (s i ^ 2))⁻¹)).map Complex.ofReal := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [hS, hR, conjTranspose_map_ofReal, ← map_ofReal_mul, ← aeval_map_ofReal,
      ← map_ofReal_mul, hreal]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  · rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs, abs_inv, ← one_div]
    exact one_div_le_one_div_of_le hc (hmin i)

end NLAlib
