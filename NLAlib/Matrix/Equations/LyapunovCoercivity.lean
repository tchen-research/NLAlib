import NLAlib.Matrix.Norms.FrobeniusProducts
import NLAlib.Matrix.Norms.Core
import NLAlib.Matrix.Basic.QuadForm
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite-dimensional coercivity of the continuous Lyapunov operator

A strict upper bound on the real quadratic form of `A` yields coercivity of
`E ↦ AE+EAᴴ` in the real Frobenius pairing. Injectivity then gives existence and
uniqueness on the finite-dimensional matrix space, with an explicit Frobenius bound.
This route needs no improper integral. Source: the supplied Krylov derivations, §K17–K19.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The continuous Lyapunov linear map, over either scalar field. -/
def lyapunovLinearMap (A : Matrix n n 𝕜) : Matrix n n 𝕜 →ₗ[𝕜] Matrix n n 𝕜 where
  toFun E := A * E + E * Aᴴ
  map_add' E F := by simp only [Matrix.mul_add, Matrix.add_mul]; abel
  map_smul' c E := by simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add, RingHom.id_apply]

omit [DecidableEq n] in
/-- Left multiplication pairs column by column with the matrix quadratic form. -/
theorem frobInner_mul_eq_sum_re_quadForm {p : Type*} [Fintype p]
    (A : Matrix n n 𝕜) (E : Matrix n p 𝕜) :
    frobInner E (A * E) = ∑ j, RCLike.re (quadForm A (E.col j)) := by
  simp only [frobInner_eq_trace, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, map_sum, quadForm, Matrix.mulVec, dotProduct,
    Matrix.col_apply, Pi.star_apply]

private theorem frobInner_mul_le {p : Type*} [Fintype p]
    {A : Matrix n n 𝕜} {a : ℝ}
    (hA : ∀ v : n → 𝕜, RCLike.re (quadForm A v) ≤ -a * ‖WithLp.toLp 2 v‖ ^ 2)
    (E : Matrix n p 𝕜) : frobInner E (A * E) ≤ -a * frobSq E := by
  have hid : frobSq E = ∑ j, RCLike.re (star (E.col j) ⬝ᵥ E.col j) := by
    have h := frobInner_mul_eq_sum_re_quadForm (1 : Matrix n n 𝕜) E
    simpa only [Matrix.one_mul, quadForm, Matrix.one_mulVec, frobSq] using h
  rw [frobInner_mul_eq_sum_re_quadForm, hid, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => by
    simpa only [norm_toLp_sq_eq_re_star_dotProduct] using hA (E.col j)

/-- Strict dissipativity controls the complete Lyapunov operator in Frobenius energy. -/
theorem frobInner_lyapunov_le {A : Matrix n n 𝕜} {a : ℝ}
    (hA : ∀ v : n → 𝕜, RCLike.re (quadForm A v) ≤ -a * ‖WithLp.toLp 2 v‖ ^ 2)
    (E : Matrix n n 𝕜) : frobInner E (A * E + E * Aᴴ) ≤ -2 * a * frobSq E := by
  have hleft := frobInner_mul_le hA E
  have hright := frobInner_mul_le hA Eᴴ
  have he : frobInner E (E * Aᴴ) = frobInner Eᴴ (A * Eᴴ) := by
    rw [← frobInner_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [frobSq_conjTranspose] at hright
  rw [frobInner_add_right, he]
  linarith

/-- The inverse Lyapunov estimate for arbitrary matrix errors in Frobenius norm. -/
theorem frobNorm_le_lyapunov_div {A : Matrix n n 𝕜} {a : ℝ} (ha : 0 < a)
    (hA : ∀ v : n → 𝕜, RCLike.re (quadForm A v) ≤ -a * ‖WithLp.toLp 2 v‖ ^ 2)
    (E : Matrix n n 𝕜) : frobNorm E ≤ frobNorm (A * E + E * Aᴴ) / (2 * a) := by
  have he := frobInner_lyapunov_le hA E
  have hc := neg_le_abs (frobInner E (A * E + E * Aᴴ))
  have hcs := abs_frobInner_le_frobNorm_mul_frobNorm E (A * E + E * Aᴴ)
  have hsq := frobNorm_sq E
  by_cases hz : frobNorm E = 0
  · rw [hz]
    exact div_nonneg (frobNorm_nonneg _) (by positivity)
  · have hp : 0 < frobNorm E := lt_of_le_of_ne (frobNorm_nonneg E) (Ne.symm hz)
    apply (le_div_iff₀ (by positivity : 0 < 2 * a)).2
    nlinarith

/-- A strictly dissipative Lyapunov map is injective. -/
theorem lyapunovLinearMap_injective {A : Matrix n n 𝕜} {a : ℝ} (ha : 0 < a)
    (hA : ∀ v : n → 𝕜, RCLike.re (quadForm A v) ≤ -a * ‖WithLp.toLp 2 v‖ ^ 2) :
    Function.Injective (lyapunovLinearMap A) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro E hE
  have h := frobInner_lyapunov_le hA E
  change A * E + E * Aᴴ = 0 at hE
  rw [hE, frobInner_zero_right] at h
  have hz : frobSq E = 0 := by nlinarith [frobSq_nonneg E]
  exact (frobSq_eq_zero_iff E).mp hz

/-- Every forcing has a unique continuous Lyapunov solution for strictly dissipative `A`.
The existence argument is finite-dimensional surjectivity of an injective linear map. -/
theorem existsUnique_lyapunov_of_quadratic_bound {A : Matrix n n 𝕜} {a : ℝ}
    (ha : 0 < a)
    (hA : ∀ v : n → 𝕜, RCLike.re (quadForm A v) ≤ -a * ‖WithLp.toLp 2 v‖ ^ 2)
    (Q : Matrix n n 𝕜) : ∃! X : Matrix n n 𝕜, A * X + X * Aᴴ + Q = 0 := by
  have hi := lyapunovLinearMap_injective ha hA
  have hs : Function.Surjective (lyapunovLinearMap A) := LinearMap.injective_iff_surjective.mp hi
  obtain ⟨X, hX⟩ := hs (-Q)
  refine ⟨X, ?_, ?_⟩
  · change A * X + X * Aᴴ = -Q at hX
    rw [hX, neg_add_cancel]
  · intro Y hY
    apply hi
    change A * Y + Y * Aᴴ = _
    rw [eq_neg_of_add_eq_zero_left hY]
    exact hX.symm

/-- Hermitian forcing has a Hermitian solution, by uniqueness and adjoint symmetry. -/
theorem isHermitian_lyapunov_solution {A Q X : Matrix n n 𝕜} {a : ℝ}
    (ha : 0 < a)
    (hA : ∀ v : n → 𝕜, RCLike.re (quadForm A v) ≤ -a * ‖WithLp.toLp 2 v‖ ^ 2)
    (hQ : Q.IsHermitian) (hX : A * X + X * Aᴴ + Q = 0) : X.IsHermitian := by
  have hstar := congrArg Matrix.conjTranspose hX
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hQ.eq, Matrix.conjTranspose_zero] at hstar
  have he : A * Xᴴ + Xᴴ * Aᴴ + Q = 0 := by rw [add_comm (A * Xᴴ)]; exact hstar
  have hi := lyapunovLinearMap_injective ha hA
  exact hi ((eq_neg_of_add_eq_zero_left he).trans (eq_neg_of_add_eq_zero_left hX).symm)

end NLAlib
