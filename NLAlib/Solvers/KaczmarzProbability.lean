import NLAlib.Solvers.Kaczmarz
import NLAlib.Matrix.MoorePenrose
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Randomized Kaczmarz as an actual probability expectation

Rows are sampled independently with squared-row-norm weights. Nonzero input
ensures that these weights define a probability law. Full column rank is
expressed by invertibility of the column Gram matrix; it gives the sharp
Moore–Penrose condition-number contraction bound.

Source: Strohmer–Vershynin 2009, Theorem 2. Atlas: `randomized-kaczmarz`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators ENNReal
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n]

/-- An invertible column Gram matrix gives the lower singular bound required
by the Kaczmarz recurrence, using the actual norm of the full-rank left inverse.
Source: Strohmer–Vershynin 2009, Theorem 2. Atlas: `randomized-kaczmarz`. -/
theorem inv_specNorm_pinvL_sq_mul_dotProduct_le [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (hA : IsUnit (Aᵀ * A)) (v : n → ℝ) :
    (specNorm (pinvL A))⁻¹ ^ 2 * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v) := by
  classical
  by_cases hB : specNorm (pinvL A) = 0
  · simp only [hB, inv_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul]
    exact dotProduct_self_nonneg _
  have hBound := sum_sq_mulVec_le_specNorm_sq (pinvL A) (A *ᵥ v)
  have hId : pinvL A *ᵥ (A *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, pinvL_mul hA, Matrix.one_mulVec]
  rw [hId] at hBound
  have hScale := mul_le_mul_of_nonneg_left hBound (sq_nonneg (specNorm (pinvL A))⁻¹)
  have hCancel : (specNorm (pinvL A))⁻¹ ^ 2 * specNorm (pinvL A) ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hB, one_pow]
  rw [← mul_assoc, hCancel, one_mul] at hScale
  simpa only [dotProduct, pow_two] using hScale

/-- The Frobenius condition number formed with the general Moore–Penrose
inverse. The zero matrix has value zero under this total definition.
Source: Strohmer–Vershynin 2009, Theorem 2. Atlas: `randomized-kaczmarz`.
atlas: kaczmarz-def -/
def frobConditionNumber [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) : ℝ :=
  frobNorm A * specNorm (moorePenroseInverse A)

/-- The Kaczmarz recurrence has the advertised condition-number contraction
under the necessary full-column-rank hypothesis.
Source: Strohmer–Vershynin 2009, Theorem 2. Atlas: `randomized-kaczmarz`. -/
theorem expErr_le_frobConditionNumber [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (hA : IsUnit (Aᵀ * A)) (b : m → ℝ) (xs x : n → ℝ)
    (hxs : A *ᵥ xs = b) (k : ℕ) :
    Kaczmarz.expErr A b xs x k ≤
      (1 - 1 / frobConditionNumber A ^ 2) ^ k * ((x - xs) ⬝ᵥ (x - xs)) := by
  have h := Kaczmarz.expErr_le A b xs hxs (specNorm (pinvL A))⁻¹
    (inv_specNorm_pinvL_sq_mul_dotProduct_le A hA) x k
  have hRate : 1 - (specNorm (pinvL A))⁻¹ ^ 2 / frobSq A =
      1 - 1 / frobConditionNumber A ^ 2 := by
    rw [frobConditionNumber, moorePenroseInverse_eq_pinvL A hA, mul_pow, frobNorm_sq]
    simp only [div_eq_mul_inv, one_mul, mul_inv_rev, inv_pow]
  simpa only [hRate] using h

/-- The exact distribution of an independent sequence of row choices.
Nonzero input is essential: otherwise the squared-row weights all vanish.
Source: Strohmer–Vershynin 2009, Theorem 2. Atlas: `randomized-kaczmarz`.
atlas: kaczmarz-def -/
def kaczmarzRowPathPMF (A : Matrix m n ℝ) (hA : A ≠ 0) (k : ℕ) : PMF (Fin k → m) := by
  classical
  refine PMF.ofFintype (fun ω => ENNReal.ofReal (∏ j, Kaczmarz.prob A (ω j))) ?_
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun ω _ => Finset.prod_nonneg fun j _ => Kaczmarz.prob_nonneg A (ω j))]
  have hSum : (∑ ω : Fin k → m, ∏ j, Kaczmarz.prob A (ω j)) = 1 := by
    rw [← Fintype.prod_sum]
    simp only [Kaczmarz.sum_prob A hA, Finset.prod_const_one]
  rw [hSum]
  simp

/-- The real weighted recurrence is the probability expectation of the
actual row-by-row iterates, including zero steps.
Source: Strohmer–Vershynin 2009, Theorem 2. Atlas: `randomized-kaczmarz`.
atlas: randomized-kaczmarz -/
theorem integral_sqErr_kaczmarzRowPathPMF [MeasurableSpace m] [MeasurableSingletonClass m]
    (A : Matrix m n ℝ) (hA : A ≠ 0) (b : m → ℝ) (xs x : n → ℝ) (k : ℕ) :
    (∫ ω : Fin k → m,
      (Kaczmarz.run A b k ω x - xs) ⬝ᵥ (Kaczmarz.run A b k ω x - xs)
      ∂(kaczmarzRowPathPMF A hA k).toMeasure) = Kaczmarz.expErr A b xs x k := by
  classical
  rw [PMF.integral_eq_sum, Kaczmarz.expErr_eq_sum_paths]
  apply Finset.sum_congr rfl
  intro ω _
  change (ENNReal.ofReal (∏ j, Kaczmarz.prob A (ω j))).toReal • _ = _
  rw [ENNReal.toReal_ofReal
    (Finset.prod_nonneg fun j _ => Kaczmarz.prob_nonneg A (ω j))]
  rfl

/-- Full-column-rank randomized Kaczmarz converges in the actual probability
expectation with rate `1-κ_F⁻²`, using the general Moore–Penrose inverse.
All probability and lower-singular-bound assumptions are discharged.
Source: Strohmer–Vershynin 2009, Theorem 2. Atlas: `randomized-kaczmarz`.
atlas: randomized-kaczmarz -/
theorem integral_sqErr_kaczmarz_le_frobConditionNumber
    [DecidableEq m] [DecidableEq n] [MeasurableSpace m] [MeasurableSingletonClass m]
    (A : Matrix m n ℝ) (hA0 : A ≠ 0) (hA : IsUnit (Aᵀ * A))
    (b : m → ℝ) (xs x : n → ℝ) (hxs : A *ᵥ xs = b) (k : ℕ) :
    (∫ ω : Fin k → m,
      (Kaczmarz.run A b k ω x - xs) ⬝ᵥ (Kaczmarz.run A b k ω x - xs)
      ∂(kaczmarzRowPathPMF A hA0 k).toMeasure) ≤
      (1 - 1 / frobConditionNumber A ^ 2) ^ k * ((x - xs) ⬝ᵥ (x - xs)) := by
  rw [integral_sqErr_kaczmarzRowPathPMF A hA0 b xs x k]
  exact expErr_le_frobConditionNumber A hA b xs x hxs k

end NLAlib
