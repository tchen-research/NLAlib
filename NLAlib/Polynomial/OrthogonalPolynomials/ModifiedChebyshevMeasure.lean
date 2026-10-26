import NLAlib.Polynomial.OrthogonalPolynomials.ModifiedChebyshev
import NLAlib.Polynomial.OrthogonalPolynomials.FiniteMeasureMoments

/-!
# Modified Chebyshev coefficients of a measure

The actual finite algorithm takes `2n` modified moments and recovers the monic
coefficients through order `n-1`. The measure assumptions are only finite absolute
moments through degree `2n-1` and enough support points. The finite moment functional
has the actual measure orthogonality proved in `FiniteMeasureMoments`.
Source: Gautschi (2004), Algorithm 2.1.
-/

noncomputable section
open Polynomial MeasureTheory
namespace NLAlib

/-- Included canonical norms from the finite measure functional are actual
squared polynomial integrals. -/
theorem orthogonalPolynomialNorm_finiteMeasureMomentFunctional_eq
    {μ : Measure ℝ} {n k : ℕ}
    (hμ : ∀ j < 2 * n, Integrable (fun x : ℝ => |x| ^ j) μ) (hk : k < n) :
    orthogonalPolynomialNorm (finiteMeasureMomentFunctional μ n) k =
      ∫ x, (monicOrthogonalPolynomial (finiteMeasureMomentFunctional μ n) k).eval x ^ 2 ∂μ := by
  unfold orthogonalPolynomialNorm
  rw [finiteMeasureMomentFunctional_apply hμ]
  · simp only [eval_pow]
  · rw [degree_pow, degree_eq_natDegree (monic_monicOrthogonalPolynomial _ k).ne_zero,
      natDegree_monicOrthogonalPolynomial, nsmul_eq_mul]
    exact_mod_cast (show 2 * k < 2 * n by omega)

/-- Included canonical diagonals from the finite measure functional are the
usual monic measure coefficients, with exactly the required integrals. -/
theorem orthogonalRecurrenceAlpha_finiteMeasureMomentFunctional_eq
    {μ : Measure ℝ} {n k : ℕ}
    (hμ : ∀ j < 2 * n, Integrable (fun x : ℝ => |x| ^ j) μ) (hk : k < n) :
    orthogonalRecurrenceAlpha (finiteMeasureMomentFunctional μ n) k =
      (∫ x, x * (monicOrthogonalPolynomial (finiteMeasureMomentFunctional μ n) k).eval x ^ 2 ∂μ) /
      (∫ x, (monicOrthogonalPolynomial (finiteMeasureMomentFunctional μ n) k).eval x ^ 2 ∂μ) := by
  unfold orthogonalRecurrenceAlpha
  rw [orthogonalPolynomialNorm_finiteMeasureMomentFunctional_eq hμ hk,
    finiteMeasureMomentFunctional_apply hμ]
  · simp only [eval_mul, eval_X, eval_pow]
  · rw [degree_mul, degree_X, degree_pow,
      degree_eq_natDegree (monic_monicOrthogonalPolynomial _ k).ne_zero,
      natDegree_monicOrthogonalPolynomial, nsmul_eq_mul]
    exact_mod_cast (show 1 + 2 * k < 2 * n by omega)

/-- From the actual measure's `2n` modified moments, the finite algorithm returns
its canonical monic coefficients at every requested order. No higher moments or
precomputed target coefficients are inputs. The source's stronger condition
`n < support.encard` implies the displayed support bound.
atlas: modified-chebyshev-algorithm (partial) -/
theorem modifiedChebyshevCoefficients_integral_eq {μ : Measure ℝ} {n : ℕ}
    (hμ : ∀ j < 2 * n, Integrable (fun x : ℝ => |x| ^ j) μ)
    (hs : (n : ℕ∞) ≤ μ.support.encard) (p : ℕ → ℝ[X]) (a b : ℕ → ℝ)
    (hp : ∀ j, (p j).Monic) (hdeg : ∀ j, (p j).natDegree = j)
    (hrec : ∀ j, X * p j = p (j + 1) + C (a j) * p j +
      if j = 0 then 0 else C (b j) * p (j - 1)) (k : Fin n) :
    modifiedChebyshevCoefficients a b (fun i : Fin (2 * n) => ∫ x, (p i).eval x ∂μ) k =
      (orthogonalRecurrenceAlpha (finiteMeasureMomentFunctional μ n) k,
        if (k : ℕ) = 0 then ∫ _, (1 : ℝ) ∂μ
        else orthogonalRecurrenceBeta (finiteMeasureMomentFunctional μ n) k) := by
  have hm : (fun i : Fin (2 * n) => ∫ x, (p i).eval x ∂μ) =
      fun i : Fin (2 * n) => finiteMeasureMomentFunctional μ n (p i) := by
    funext i
    symm
    apply finiteMeasureMomentFunctional_apply hμ
    rw [degree_eq_natDegree (hp i).ne_zero, hdeg]
    exact_mod_cast i.isLt
  rw [hm, modifiedChebyshevCoefficients_eq _ p a b n
    (posDef_hankelMomentMatrix_finiteMeasureMomentFunctional hμ hs) hp hdeg hrec]
  congr 2
  rw [eq_one_of_monic_natDegree_zero (hp 0) (hdeg 0), finiteMeasureMomentFunctional_apply hμ]
  · simp only [eval_one]
  · rw [degree_one]
    exact_mod_cast (show 0 < 2 * n by have := k.isLt; omega)

/-- The finite algorithm recovers the measure coefficients in their integral
form. Its `beta₀` is the mass; all later `beta` values are ratios of successive
squared norms. The polynomials here satisfy actual measure orthogonality by
`integral_monicOrthogonalPolynomial_finiteMeasure_mul_eq_zero`.
atlas: modified-chebyshev-algorithm (partial) -/
theorem modifiedChebyshevCoefficients_integral_formula {μ : Measure ℝ} {n : ℕ}
    (hμ : ∀ j < 2 * n, Integrable (fun x : ℝ => |x| ^ j) μ)
    (hs : (n : ℕ∞) ≤ μ.support.encard) (p : ℕ → ℝ[X]) (a b : ℕ → ℝ)
    (hp : ∀ j, (p j).Monic) (hdeg : ∀ j, (p j).natDegree = j)
    (hrec : ∀ j, X * p j = p (j + 1) + C (a j) * p j +
      if j = 0 then 0 else C (b j) * p (j - 1)) (k : Fin n) :
    let π := monicOrthogonalPolynomial (finiteMeasureMomentFunctional μ n)
    modifiedChebyshevCoefficients a b (fun i : Fin (2 * n) => ∫ x, (p i).eval x ∂μ) k =
      ((∫ x, x * (π k).eval x ^ 2 ∂μ) / (∫ x, (π k).eval x ^ 2 ∂μ),
        if (k : ℕ) = 0 then ∫ _, (1 : ℝ) ∂μ else
          (∫ x, (π k).eval x ^ 2 ∂μ) / (∫ x, (π (k - 1)).eval x ^ 2 ∂μ)) := by
  dsimp only
  rw [modifiedChebyshevCoefficients_integral_eq hμ hs p a b hp hdeg hrec,
    orthogonalRecurrenceAlpha_finiteMeasureMomentFunctional_eq hμ k.isLt]
  congr 1
  split_ifs with hk0
  · rfl
  · rw [orthogonalRecurrenceBeta, if_neg hk0,
      orthogonalPolynomialNorm_finiteMeasureMomentFunctional_eq hμ k.isLt,
      orthogonalPolynomialNorm_finiteMeasureMomentFunctional_eq hμ (by have := k.isLt; omega)]

end NLAlib
