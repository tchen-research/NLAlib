import NLAlib.RandomMatrix.Gaussian.Moments.FourthMoment
import NLAlib.Probability.Concentration.QuadraticForms.RademacherQuadraticMoments
/-!
# Hutchinson identities for concrete Gaussian and Rademacher laws

These endpoints derive the coordinate moments and integrability from the actual scalar laws.
No second- or fourth-moment assumptions are needed by the law-based trace and variance
theorems. The canonical product Gaussian and one-column Gaussian-matrix corollaries also
discharge independence. The concrete law `rademacherMeasure` is
`NLAlib.Probability.Rademacher.Core`. Atlas: `hutchinson-unbiased`, `hutchinson-variance`.

The general isotropic endpoint uses only measurable coordinates and the identity of
their second cross moments. Its diagonal moments derive square and product integrability;
neither independence nor zero means are required.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

section ScalarLaws

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

end ScalarLaws

section AbstractLaws

variable {n Ω : Type*} [Fintype n] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Hutchinson unbiasedness for mutually independent standard Gaussian coordinates.
All moment conditions follow from the laws. Avron–Toledo 2011, Lemma 5;
atlas `hutchinson-unbiased`.
atlas: hutchinson-unbiased -/
theorem integral_quadForm_eq_trace_of_standardGaussian (A : Matrix n n ℝ)
    {z : Ω → n → ℝ} (hmeas : ∀ i, AEMeasurable (fun ω => z ω i) μ)
    (hindep : iIndepFun (fun i ω => z ω i) μ)
    (hlaw : ∀ i, IsStandardGaussian μ (fun ω => z ω i)) :
    ∫ ω, quadForm A (z ω) ∂μ = A.trace := by
  have hf := fun i => memLp_two_and_moments_of_isStandardGaussian (hlaw i)
  exact integral_quadForm_eq_trace A (fun i => (hf i).1)
    (fun _ _ hij => hindep.indepFun hij) (fun i => (hf i).2.1)
    (fun i => (hf i).2.2.1)

/-- Hutchinson unbiasedness for mutually independent Rademacher coordinates.
All moment conditions follow from the laws. Hutchinson 1989; Avron–Toledo 2011, Lemma 6;
atlas `hutchinson-unbiased`.
atlas: hutchinson-unbiased -/
theorem integral_quadForm_eq_trace_of_rademacher (A : Matrix n n ℝ)
    {z : Ω → n → ℝ} (hmeas : ∀ i, AEMeasurable (fun ω => z ω i) μ)
    (hindep : iIndepFun (fun i ω => z ω i) μ)
    (hlaw : ∀ i, IsRademacher μ (fun ω => z ω i)) :
    ∫ ω, quadForm A (z ω) ∂μ = A.trace := by
  have hf := fun i => memLp_two_and_moments_of_isRademacher (hlaw i)
  exact integral_quadForm_eq_trace A (fun i => (hf i).1)
    (fun _ _ hij => hindep.indepFun hij) (fun i => (hf i).2.1)
    (fun i => (hf i).2.2.1)

/-- Gaussian Hutchinson variance for an arbitrary real matrix:
`Var(zᵀAz) = ∑ Aᵢⱼ² + ∑ AᵢⱼAⱼᵢ`. Moment and integrability assumptions are derived from
the standard Gaussian laws. Avron–Toledo 2011, Lemma 5; atlas `hutchinson-variance`. -/
theorem variance_quadForm_of_standardGaussian [DecidableEq n] (A : Matrix n n ℝ)
    {z : Ω → n → ℝ} (hmeas : ∀ i, AEMeasurable (fun ω => z ω i) μ)
    (hindep : iIndepFun (fun i ω => z ω i) μ)
    (hlaw : ∀ i, IsStandardGaussian μ (fun ω => z ω i)) :
    Var[fun ω => quadForm A (z ω); μ] =
      ∑ i, ∑ j, A i j ^ 2 + ∑ i, ∑ j, A i j * A j i := by
  have hf := fun i => memLp_two_and_moments_of_isStandardGaussian (hlaw i)
  simpa using variance_quadForm A hmeas hindep (fun i => (hf i).2.1)
    (fun i => (hf i).2.2.1) (fun i => (hf i).2.2.2.1) (fun i => (hf i).2.2.2.2)

/-- Symmetric Gaussian Hutchinson variance from actual coordinate laws:
`Var(zᵀAz) = 2‖A‖F²`. Avron–Toledo 2011, Lemma 5; atlas `hutchinson-variance`.
atlas: hutchinson-variance -/
theorem variance_quadForm_of_isSymm_of_standardGaussian [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsSymm) {z : Ω → n → ℝ}
    (hmeas : ∀ i, AEMeasurable (fun ω => z ω i) μ)
    (hindep : iIndepFun (fun i ω => z ω i) μ)
    (hlaw : ∀ i, IsStandardGaussian μ (fun ω => z ω i)) :
    Var[fun ω => quadForm A (z ω); μ] = 2 * frobSq A := by
  have hf := fun i => memLp_two_and_moments_of_isStandardGaussian (hlaw i)
  exact variance_quadForm_of_isSymm_of_fourth_moment_eq_three hA hmeas hindep
    (fun i => (hf i).2.1) (fun i => (hf i).2.2.1)
    (fun i => (hf i).2.2.2.1) (fun i => (hf i).2.2.2.2)

/-- Symmetric Rademacher Hutchinson variance from actual coordinate laws:
`Var(zᵀAz) = 2(‖A‖F² − ∑ Aᵢᵢ²)`. Hutchinson 1989; Avron–Toledo 2011, Lemma 6;
atlas `hutchinson-variance`.
atlas: hutchinson-variance -/
theorem variance_quadForm_of_isSymm_of_rademacher [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsSymm) {z : Ω → n → ℝ}
    (hmeas : ∀ i, AEMeasurable (fun ω => z ω i) μ)
    (hindep : iIndepFun (fun i ω => z ω i) μ)
    (hlaw : ∀ i, IsRademacher μ (fun ω => z ω i)) :
    Var[fun ω => quadForm A (z ω); μ] = 2 * (frobSq A - ∑ i, A i i ^ 2) := by
  have hf := fun i => memLp_two_and_moments_of_isRademacher (hlaw i)
  exact variance_quadForm_of_isSymm_of_fourth_moment_eq_one hA hmeas hindep
    (fun i => (hf i).2.1) (fun i => (hf i).2.2.1)
    (fun i => (hf i).2.2.2.1) (fun i => (hf i).2.2.2.2)

/-- Complete symmetric Gaussian Hutchinson specialization: independence and the actual
coordinate laws imply unbiasedness and variance `2‖A‖F²`, with no measurability, moment or
integrability side assumptions. Avron–Toledo 2011, Lemma 5;
atlas `hutchinson-unbiased`, `hutchinson-variance`.
atlas: hutchinson-unbiased, hutchinson-variance -/
theorem hutchinson_of_standardGaussian [DecidableEq n] {A : Matrix n n ℝ} (hA : A.IsSymm)
    {z : Ω → n → ℝ} (hindep : iIndepFun (fun i ω => z ω i) μ)
    (hlaw : ∀ i, IsStandardGaussian μ (fun ω => z ω i)) :
    (∫ ω, quadForm A (z ω) ∂μ) = A.trace ∧
      Var[fun ω => quadForm A (z ω); μ] = 2 * frobSq A := by
  have hmeas := fun i => aemeasurable_of_isStandardGaussian (hlaw i)
  exact ⟨integral_quadForm_eq_trace_of_standardGaussian A hmeas hindep hlaw,
    variance_quadForm_of_isSymm_of_standardGaussian hA hmeas hindep hlaw⟩

/-- Complete symmetric Rademacher Hutchinson specialization: independence and the actual
coordinate laws imply unbiasedness and variance `2(‖A‖F²−∑ Aᵢᵢ²)`, with no measurability,
moment or integrability side assumptions. Hutchinson 1989; Avron–Toledo 2011, Lemma 6;
atlas `hutchinson-unbiased`, `hutchinson-variance`.
atlas: hutchinson-unbiased, hutchinson-variance -/
theorem hutchinson_of_rademacher [DecidableEq n] {A : Matrix n n ℝ} (hA : A.IsSymm)
    {z : Ω → n → ℝ} (hindep : iIndepFun (fun i ω => z ω i) μ)
    (hlaw : ∀ i, IsRademacher μ (fun ω => z ω i)) :
    (∫ ω, quadForm A (z ω) ∂μ) = A.trace ∧
      Var[fun ω => quadForm A (z ω); μ] = 2 * (frobSq A - ∑ i, A i i ^ 2) := by
  have hmeas := fun i => aemeasurable_of_isRademacher (hlaw i)
  exact ⟨integral_quadForm_eq_trace_of_rademacher A hmeas hindep hlaw,
    variance_quadForm_of_isSymm_of_rademacher hA hmeas hindep hlaw⟩

end AbstractLaws

section ProductGaussian

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The Hutchinson estimator is unbiased under the canonical product standard Gaussian law.
The law, moments and mutual independence are all discharged. Avron–Toledo 2011, Lemma 5;
atlas `hutchinson-unbiased`. -/
theorem integral_quadForm_pi_gaussianReal (A : Matrix n n ℝ) :
    ∫ z, quadForm A z ∂(Measure.pi fun _ : n => gaussianReal 0 1) = A.trace := by
  apply integral_quadForm_eq_trace_of_standardGaussian A
    (fun i => (measurable_pi_apply i).aemeasurable)
    (iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id))
  intro i
  exact (measurePreserving_eval (fun _ : n => gaussianReal 0 1) i).hasLaw

/-- Symmetric Gaussian Hutchinson variance under the canonical product law, without
coordinate assumptions. Avron–Toledo 2011, Lemma 5; atlas `hutchinson-variance`. -/
theorem variance_quadForm_pi_gaussianReal {A : Matrix n n ℝ} (hA : A.IsSymm) :
    Var[fun z => quadForm A z; Measure.pi fun _ : n => gaussianReal 0 1] = 2 * frobSq A := by
  apply variance_quadForm_of_isSymm_of_standardGaussian hA
    (fun i => (measurable_pi_apply i).aemeasurable)
    (iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id))
  intro i
  exact (measurePreserving_eval (fun _ : n => gaussianReal 0 1) i).hasLaw

end ProductGaussian

section ProductRademacher

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Symmetric Hutchinson variance under the concrete product Rademacher law.
Hutchinson 1989; Avron–Toledo 2011, Lemma 6; atlas `hutchinson-variance`. -/
theorem variance_quadForm_pi_rademacherMeasure {A : Matrix n n ℝ} (hA : A.IsSymm) :
    Var[fun z => quadForm A z; Measure.pi fun _ : n => rademacherMeasure] =
      2 * (frobSq A - ∑ i, A i i ^ 2) := by
  apply variance_quadForm_of_isSymm_of_rademacher hA
    (fun i => (measurable_pi_apply i).aemeasurable)
    (iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id))
  intro i
  exact (measurePreserving_eval (fun _ : n => rademacherMeasure) i).hasLaw

end ProductRademacher

section GaussianMatrix

variable {n : ℕ}

private theorem gaussianMatrix_column_iIndepFun :
    iIndepFun (fun i (G : Matrix (Fin n) (Fin 1) ℝ) => G i 0) (gaussianMatrix (Fin n) (Fin 1)) := by
  have hrows : iIndepFun (fun i (G : Matrix (Fin n) (Fin 1) ℝ) => G i)
      (gaussianMatrix (Fin n) (Fin 1)) :=
    iIndepFun_gaussianMatrix_row
  exact hrows.comp (fun _ row => row 0) (fun _ => measurable_pi_apply 0)

/-- Hutchinson unbiasedness for the column of an actual standard Gaussian matrix.
Avron–Toledo 2011, Lemma 5; atlas `hutchinson-unbiased`. -/
theorem integral_quadForm_gaussianMatrix_column (A : Matrix (Fin n) (Fin n) ℝ) :
    ∫ G, quadForm A (fun i => G i 0) ∂(gaussianMatrix (Fin n) (Fin 1)) = A.trace := by
  apply integral_quadForm_eq_trace_of_standardGaussian A
    (fun i => (measurePreserving_gaussianMatrix_entry i 0).measurable.aemeasurable)
    gaussianMatrix_column_iIndepFun
  intro i
  exact (measurePreserving_gaussianMatrix_entry i 0).hasLaw

/-- Symmetric Hutchinson variance for the column of an actual standard Gaussian matrix.
Avron–Toledo 2011, Lemma 5; atlas `hutchinson-variance`.
atlas: hutchinson-variance -/
theorem variance_quadForm_gaussianMatrix_column {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsSymm) :
    Var[fun G => quadForm A (fun i => G i 0); gaussianMatrix (Fin n) (Fin 1)] = 2 * frobSq A := by
  apply variance_quadForm_of_isSymm_of_standardGaussian hA
    (fun i => (measurePreserving_gaussianMatrix_entry i 0).measurable.aemeasurable)
    gaussianMatrix_column_iIndepFun
  intro i
  exact (measurePreserving_gaussianMatrix_entry i 0).hasLaw

end GaussianMatrix

end NLAlib
