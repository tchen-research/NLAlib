import NLAlib.Matrix.PolynomialCalculus
import NLAlib.Matrix.QuadraticProbe
import NLAlib.ForMathlib.Analysis.LogPowerMean
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Power-method Rayleigh error and logarithmic overlap

Mathlib's Rayleigh quotient is bridged to the matrix quadratic quotient. Finite
spectral power means then give the exact deterministic logarithmic-overlap bound.
Source: manuscript `rt:power`.
-/

noncomputable section
open Polynomial
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Mathlib's Rayleigh quotient of a real matrix is its ordinary quadratic quotient.
Source: Mathlib's `ContinuousLinearMap.rayleighQuotient`; manuscript `rt:power`.
The zero-vector convention is totalized division by zero. -/
theorem rayleighQuotient_toEuclideanCLM_eq (A : Matrix n n ℝ) (b : n → ℝ) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) A).rayleighQuotient (WithLp.toLp 2 b) =
      (b ⬝ᵥ (A *ᵥ b)) / (b ⬝ᵥ b) := by
  have hn : ‖WithLp.toLp 2 b‖ ^ 2 = b ⬝ᵥ b := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [dotProduct, pow_two]
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    real_inner_comm, Matrix.inner_toEuclideanCLM, hn]
  rfl

/-- A PSD matrix's totalized Rayleigh quotient lies between zero and its spectral
norm, even at a zero vector. Source: the spectral theorem; manuscript `rt:power`. -/
theorem rayleighQuotient_toEuclideanCLM_bounds {A : Matrix n n ℝ} (hA : A.PosSemidef)
    (b : n → ℝ) :
    0 ≤ (Matrix.toEuclideanCLM (𝕜 := ℝ) A).rayleighQuotient (WithLp.toLp 2 b) ∧
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A).rayleighQuotient (WithLp.toLp 2 b) ≤ specNorm A := by
  constructor
  · rw [rayleighQuotient_toEuclideanCLM_eq]
    apply div_nonneg _ (dotProduct_self_nonneg _)
    simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg b
  · have h := (Matrix.toEuclideanCLM (𝕜 := ℝ) A).rayleighQuotient_le_norm (WithLp.toLp 2 b)
    exact (le_abs_self _).trans (by simpa only [Matrix.l2_opNorm_toEuclideanCLM, specNorm_eq_norm] using h)

/-- The relative power-method Rayleigh error is bounded by logarithmic inverse top
overlap divided by `2q+1`. Source: manuscript `rt:power`; finite concave-power Jensen.
The chosen eigenvector is deterministic; no eigenvalue gap is assumed.
atlas: random-start-power (partial) -/
theorem sub_rayleighQuotient_pow_div_specNorm_le_log_overlap_div
    {A : Matrix n n ℝ} (hA : A.PosSemidef) (hL : 0 < specNorm A)
    (i₀ : n) (h₀ : hA.isHermitian.eigenvalues i₀ = specNorm A) (b : n → ℝ)
    (hb : (hA.isHermitian.eigenvectorBasis i₀ : n → ℝ) ⬝ᵥ b ≠ 0) (q : ℕ) :
    (specNorm A - (Matrix.toEuclideanCLM (𝕜 := ℝ) A).rayleighQuotient
      (WithLp.toLp 2 ((A ^ q) *ᵥ b))) / specNorm A ≤
      Real.log ((b ⬝ᵥ b) / ((hA.isHermitian.eigenvectorBasis i₀ : n → ℝ) ⬝ᵥ b) ^ 2) /
        ((2 * q + 1 : ℕ) : ℝ) := by
  let L := specNorm A
  have hLp : 0 < L := hL
  let c := fun i => (hA.isHermitian.eigenvectorBasis i : n → ℝ) ⬝ᵥ b
  let d := fun i => hA.isHermitian.eigenvalues i / L
  let M := fun s : ℕ => ∑ i, c i ^ 2 * d i ^ s
  have hd : ∀ i, 0 ≤ d i := fun i => div_nonneg (hA.eigenvalues_nonneg i) hL.le
  have hd0 : d i₀ = 1 := by dsimp only [d, L]; rw [h₀, div_self hL.ne']
  have hc0 : 0 < c i₀ ^ 2 := sq_pos_of_ne_zero hb
  have hMe : 0 < M (2 * q) := by
    have h := Finset.single_le_sum (f := fun i => c i ^ 2 * d i ^ (2 * q))
      (fun i _ => mul_nonneg (sq_nonneg _) (pow_nonneg (hd i) _)) (Finset.mem_univ i₀)
    rw [hd0, one_pow, mul_one] at h
    exact hc0.trans_le h
  have hEigen : ∀ i, hA.isHermitian.eigenvalues i = L * d i := by
    intro i
    dsimp only [d]
    field_simp [hLp.ne']
  have hD : ((A ^ q) *ᵥ b) ⬝ᵥ ((A ^ q) *ᵥ b) =
      L ^ (2 * q) * M (2 * q) := by
    have h := dotProduct_aeval_mulVec_self_eq_sum hA.isHermitian (X ^ q) b
    simp only [map_pow, aeval_X, eval_pow, eval_X, ← pow_mul, Nat.mul_comm q 2] at h
    rw [h]
    dsimp only [M, c]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hEigen i, mul_pow]
    ring
  have hN : ((A ^ q) *ᵥ b) ⬝ᵥ (A *ᵥ ((A ^ q) *ᵥ b)) =
      L ^ (2 * q + 1) * M (2 * q + 1) := by
    have h := quadForm_aeval_mulVec_eq_sum hA.isHermitian (X ^ q) b
    simp only [map_pow, aeval_X, eval_pow, eval_X, ← pow_mul, Nat.mul_comm q 2] at h
    rw [show ((A ^ q) *ᵥ b) ⬝ᵥ (A *ᵥ ((A ^ q) *ᵥ b)) = quadForm A ((A ^ q) *ᵥ b) from rfl, h]
    dsimp only [M, c]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← pow_succ', hEigen i, mul_pow]
    ring
  have hR : (Matrix.toEuclideanCLM (𝕜 := ℝ) A).rayleighQuotient (WithLp.toLp 2 ((A ^ q) *ᵥ b)) =
      L * (M (2 * q + 1) / M (2 * q)) := by
    rw [rayleighQuotient_toEuclideanCLM_eq, hN, hD, pow_succ]
    field_simp [hLp.ne', pow_ne_zero _ hLp.ne', hMe.ne']
  have hScalar := one_sub_sum_pow_div_sum_pow_le_log_div d c hd i₀ hd0 hb q
  have hEq : (L - L * (M (2 * q + 1) / M (2 * q))) / L =
      1 - M (2 * q + 1) / M (2 * q) := by field_simp [hLp.ne', hMe.ne']
  rw [hR, hEq]
  have hParseval : (∑ i, c i ^ 2) = b ⬝ᵥ b := sum_sq_eigenvectorBasis_dotProduct hA.isHermitian b
  rw [hParseval] at hScalar
  exact hScalar

end NLAlib
