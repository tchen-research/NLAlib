import NLAlib.RandomMatrix.Gaussian.Moments.FourthMoment
import NLAlib.Probability.Concentration.QuadraticForms.RademacherQuadraticMoments
/-!
# Hutchinson identities for Gaussian and Rademacher test vectors

The mean and variance of the quadratic form `zᵀ A z` for a standard Gaussian vector
(`HasLaw z (gaussianVector n) μ`) and a Rademacher vector (`HasLaw z (rademacherVector n) μ`),
derived from the laws of the coordinates (`NLAlib.Probability.Gaussian.Basic.StandardGaussian`,
`NLAlib.Probability.Rademacher.Core`) and the moment identities of
`NLAlib.Probability.Concentration.QuadraticForms.QuadraticMoments`. The primary forms integrate
against the product laws themselves (`integral_quadForm_gaussianVector`, …); the `_of_hasLaw_…`
forms are for a random vector with that law, and the `_gaussianMatrix_col` forms for a column of
a standard Gaussian matrix.

Source: Hutchinson (1989) [`hutch89`]; Avron–Toledo (2011) [`at11`], Lem. 5–6.
Atlas: `hutchinson-unbiased`, `hutchinson-variance`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

section AbstractLaws

variable {n Ω : Type*} [Fintype n] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Hutchinson is unbiased for a standard Gaussian vector**: `𝔼[zᵀ A z] = tr A`.
Source: Avron–Toledo (2011) [`at11`], Lem. 5.
atlas: hutchinson-unbiased -/
theorem integral_quadForm_eq_trace_of_hasLaw_gaussianVector (A : Matrix n n ℝ)
    {z : Ω → n → ℝ} (hz : HasLaw z (gaussianVector n) μ) :
    ∫ ω, quadForm A (z ω) ∂μ = A.trace :=
  integral_quadForm_eq_trace A (fun i => memLp_two_of_hasLaw_gaussianReal (hz.hasLaw_eval_gaussianReal i))
    (fun _ _ hij => hz.iIndepFun_eval_of_gaussianVector.indepFun hij)
    (fun i => integral_eq_zero_of_hasLaw_gaussianReal (hz.hasLaw_eval_gaussianReal i))
    (fun i => integral_sq_eq_one_of_hasLaw_gaussianReal (hz.hasLaw_eval_gaussianReal i))

/-- **Hutchinson is unbiased for a Rademacher vector**: `𝔼[zᵀ A z] = tr A`.
Source: Hutchinson (1989) [`hutch89`]; Avron–Toledo (2011) [`at11`], Lem. 6.
atlas: hutchinson-unbiased -/
theorem integral_quadForm_eq_trace_of_hasLaw_rademacherVector (A : Matrix n n ℝ)
    {z : Ω → n → ℝ} (hz : HasLaw z (rademacherVector n) μ) :
    ∫ ω, quadForm A (z ω) ∂μ = A.trace :=
  integral_quadForm_eq_trace A
    (fun i => memLp_two_of_hasLaw_rademacherMeasure (hz.hasLaw_eval_rademacherMeasure i))
    (fun _ _ hij => hz.iIndepFun_eval_of_rademacherVector.indepFun hij)
    (fun i => integral_eq_zero_of_hasLaw_rademacherMeasure (hz.hasLaw_eval_rademacherMeasure i))
    (fun i => integral_sq_eq_one_of_hasLaw_rademacherMeasure (hz.hasLaw_eval_rademacherMeasure i))

/-- **Gaussian Hutchinson variance for an arbitrary real matrix**:
`Var(zᵀ A z) = ∑ Aᵢⱼ² + ∑ Aᵢⱼ Aⱼᵢ` for a standard Gaussian `z`.
Source: Avron–Toledo (2011) [`at11`], Lem. 5.
atlas: hutchinson-variance -/
theorem variance_quadForm_of_hasLaw_gaussianVector [DecidableEq n] (A : Matrix n n ℝ)
    {z : Ω → n → ℝ} (hz : HasLaw z (gaussianVector n) μ) :
    Var[fun ω => quadForm A (z ω); μ] =
      ∑ i, ∑ j, A i j ^ 2 + ∑ i, ∑ j, A i j * A j i := by
  have hl := fun i => hz.hasLaw_eval_gaussianReal i
  simpa using variance_quadForm A (fun i => (hl i).aemeasurable)
    hz.iIndepFun_eval_of_gaussianVector
    (fun i => integral_eq_zero_of_hasLaw_gaussianReal (hl i))
    (fun i => integral_sq_eq_one_of_hasLaw_gaussianReal (hl i))
    (fun i => integrable_pow_four_of_hasLaw_gaussianReal (hl i))
    (fun i => integral_pow_four_eq_three_of_hasLaw_gaussianReal (hl i))

/-- **Gaussian Hutchinson variance, symmetric `A`**: `Var(zᵀ A z) = 2 ‖A‖_F²` for a standard
Gaussian `z`. Source: Avron–Toledo (2011) [`at11`], Lem. 5.
atlas: hutchinson-variance -/
theorem variance_quadForm_of_isHermitian_of_hasLaw_gaussianVector [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {z : Ω → n → ℝ}
    (hz : HasLaw z (gaussianVector n) μ) :
    Var[fun ω => quadForm A (z ω); μ] = 2 * frobSq A := by
  have hl := fun i => hz.hasLaw_eval_gaussianReal i
  exact variance_quadForm_of_isHermitian_of_fourth_moment_eq_three
    hA (fun i => (hl i).aemeasurable)
    hz.iIndepFun_eval_of_gaussianVector
    (fun i => integral_eq_zero_of_hasLaw_gaussianReal (hl i))
    (fun i => integral_sq_eq_one_of_hasLaw_gaussianReal (hl i))
    (fun i => integrable_pow_four_of_hasLaw_gaussianReal (hl i))
    (fun i => integral_pow_four_eq_three_of_hasLaw_gaussianReal (hl i))

/-- **Rademacher Hutchinson variance, symmetric `A`**: `Var(zᵀ A z) = 2 (‖A‖_F² − ∑ Aᵢᵢ²)` for
a Rademacher `z`. Source: Hutchinson (1989) [`hutch89`]; Avron–Toledo (2011) [`at11`], Lem. 6.
atlas: hutchinson-variance -/
theorem variance_quadForm_of_isHermitian_of_hasLaw_rademacherVector [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {z : Ω → n → ℝ}
    (hz : HasLaw z (rademacherVector n) μ) :
    Var[fun ω => quadForm A (z ω); μ] = 2 * (frobSq A - ∑ i, A i i ^ 2) := by
  have hl := fun i => hz.hasLaw_eval_rademacherMeasure i
  exact variance_quadForm_of_isHermitian_of_fourth_moment_eq_one
    hA (fun i => (hl i).aemeasurable)
    hz.iIndepFun_eval_of_rademacherVector
    (fun i => integral_eq_zero_of_hasLaw_rademacherMeasure (hl i))
    (fun i => integral_sq_eq_one_of_hasLaw_rademacherMeasure (hl i))
    (fun i => integrable_pow_four_of_hasLaw_rademacherMeasure (hl i))
    (fun i => integral_pow_four_eq_one_of_hasLaw_rademacherMeasure (hl i))

end AbstractLaws

section ProductLaws

variable {n : Type*} [Fintype n]

/-- The identity has the law of the measure it is integrated against. -/
private lemma hasLaw_id {α : Type*} [MeasurableSpace α] (ν : Measure α) : HasLaw id ν ν :=
  ⟨aemeasurable_id, Measure.map_id⟩

/-- **Hutchinson is unbiased under the standard Gaussian product law**:
`∫ zᵀ A z d(gaussianVector n) = tr A`. Source: Avron–Toledo (2011) [`at11`], Lem. 5.
atlas: hutchinson-unbiased -/
theorem integral_quadForm_gaussianVector (A : Matrix n n ℝ) :
    ∫ z, quadForm A z ∂(gaussianVector n) = A.trace :=
  integral_quadForm_eq_trace_of_hasLaw_gaussianVector A (hasLaw_id _)

/-- **Gaussian Hutchinson variance under the product law**, symmetric `A`:
`Var(zᵀ A z) = 2 ‖A‖_F²`. Source: Avron–Toledo (2011) [`at11`], Lem. 5.
atlas: hutchinson-variance -/
theorem variance_quadForm_gaussianVector [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) :
    Var[fun z => quadForm A z; gaussianVector n] = 2 * frobSq A :=
  variance_quadForm_of_isHermitian_of_hasLaw_gaussianVector hA (hasLaw_id _)

/-- **Rademacher Hutchinson variance under the product law**, symmetric `A`:
`Var(zᵀ A z) = 2 (‖A‖_F² − ∑ Aᵢᵢ²)`. Source: Hutchinson (1989) [`hutch89`]; Avron–Toledo (2011)
[`at11`], Lem. 6.
atlas: hutchinson-variance -/
theorem variance_quadForm_rademacherVector [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) :
    Var[fun z => quadForm A z; rademacherVector n] = 2 * (frobSq A - ∑ i, A i i ^ 2) :=
  variance_quadForm_of_isHermitian_of_hasLaw_rademacherVector hA (hasLaw_id _)

end ProductLaws

section GaussianMatrix

variable {n κ : Type*} [Fintype n] [Fintype κ]

/-- A column of a standard Gaussian matrix is a standard Gaussian vector. Helper for
`hutchinson-unbiased`. -/
theorem hasLaw_col_gaussianMatrix (k : κ) :
    HasLaw (fun G : Matrix n κ ℝ => fun i => G i k) (gaussianVector n) (gaussianMatrix n κ) := by
  have hl : ∀ i, HasLaw (fun G : Matrix n κ ℝ => G i k) (gaussianReal 0 1) (gaussianMatrix n κ) :=
    fun i => (measurePreserving_gaussianMatrix_entry i k).hasLaw
  exact (iIndepFun_iff_hasLaw_pi_pi hl).1
    (iIndepFun_gaussianMatrix_entry.precomp (g := fun i : n => (i, k))
      (fun i j h => (Prod.mk.inj h).1))

/-- **Hutchinson is unbiased for a column of a standard Gaussian matrix**. Source: Avron–Toledo
(2011) [`at11`], Lem. 5.
atlas: hutchinson-unbiased -/
theorem integral_quadForm_gaussianMatrix_col (A : Matrix n n ℝ) (k : κ) :
    ∫ G, quadForm A (fun i => G i k) ∂(gaussianMatrix n κ) = A.trace :=
  integral_quadForm_eq_trace_of_hasLaw_gaussianVector A (hasLaw_col_gaussianMatrix k)

/-- **Gaussian Hutchinson variance for a column of a standard Gaussian matrix**, symmetric `A`:
`Var(zᵀ A z) = 2 ‖A‖_F²`. Source: Avron–Toledo (2011) [`at11`], Lem. 5.
atlas: hutchinson-variance -/
theorem variance_quadForm_gaussianMatrix_col [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (k : κ) :
    Var[fun G => quadForm A (fun i => G i k); gaussianMatrix n κ] = 2 * frobSq A :=
  variance_quadForm_of_isHermitian_of_hasLaw_gaussianVector hA (hasLaw_col_gaussianMatrix k)

end GaussianMatrix

end NLAlib
