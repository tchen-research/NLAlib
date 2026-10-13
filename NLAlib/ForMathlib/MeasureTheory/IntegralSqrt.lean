import Mathlib.Probability.Moments.Variance

/-!
# First moment bounded by the root second moment

On a probability space, `E X ≤ √(E X²)` for every square-integrable real `X`
(`integral_le_sqrt_integral_sq`, from `0 ≤ Var X = E X² − (E X)²`), and its threshold form
`E X² ≤ c²`, `c ≥ 0` ⟹ `E X ≤ c` (`integral_le_of_integral_sq_le`). A candidate for upstreaming
next to `ProbabilityTheory.variance_nonneg`; `exact?` finds no Mathlib lemma of this shape.
Used by the Gaussian first-moment bounds (Gordon, Chevet, linear forms) and the range-finder
assemblies (atlas `rsvd-expected-error`, `rsvd-spectral-expected`, `gordon`, `chevet`).
-/

open MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Jensen for the square root**: on a probability space, a square-integrable real random
variable satisfies `E Y ≤ √(E Y²)`. Proved from `0 ≤ Var Y = E Y² − (E Y)²`; no sign condition
on `Y`. Ported from the LRA project (`expectation_jensen_sqrt`, there for `Y ≥ 0`). -/
theorem integral_le_sqrt_integral_sq {Y : Ω → ℝ} (hYi : Integrable Y μ)
    (hY2 : Integrable (fun ω => Y ω ^ 2) μ) :
    ∫ ω, Y ω ∂μ ≤ Real.sqrt (∫ ω, Y ω ^ 2 ∂μ) := by
  have hL2 : MemLp Y 2 μ := (memLp_two_iff_integrable_sq hYi.aestronglyMeasurable).mpr hY2
  have hvar := variance_nonneg Y μ
  rw [variance_eq_sub hL2] at hvar
  have h2 : (∫ ω, Y ω ∂μ) ^ 2 ≤ ∫ ω, Y ω ^ 2 ∂μ := by
    have : μ[Y ^ 2] = ∫ ω, Y ω ^ 2 ∂μ := rfl
    linarith
  calc ∫ ω, Y ω ∂μ ≤ |∫ ω, Y ω ∂μ| := le_abs_self _
    _ = Real.sqrt ((∫ ω, Y ω ∂μ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∫ ω, Y ω ^ 2 ∂μ) := Real.sqrt_le_sqrt h2

/-- Jensen (Cauchy–Schwarz) in the form used for first moments: if `𝔼 X² ≤ c²` with `c ≥ 0`,
then `𝔼 X ≤ c`. Corollary of `integral_le_sqrt_integral_sq`. Atlas: helper of
`gordon`, `chevet`. -/
theorem integral_le_of_integral_sq_le (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : Integrable X μ) (hX2 : Integrable (fun ω => X ω ^ 2) μ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∫ ω, X ω ^ 2 ∂μ ≤ c ^ 2) : ∫ ω, X ω ∂μ ≤ c :=
  (integral_le_sqrt_integral_sq hX hX2).trans
    ((Real.sqrt_le_sqrt h).trans_eq (Real.sqrt_sq hc))

end MeasureTheory
