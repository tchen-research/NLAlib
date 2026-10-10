import NLAlib.Estimation.Hutchinson
import NLAlib.Gaussian.Moments.FourthMoment
import NLAlib.Concentration.Matrix.Defs.ScalarLaws
import NLAlib.Concentration.Scalar.Rademacher

/-!
# Hutchinson identities for concrete Gaussian and Rademacher laws

These endpoints derive the coordinate moments and integrability from the actual scalar laws.
No second- or fourth-moment assumptions are needed by the law-based trace and variance
theorems. The canonical product Gaussian and one-column Gaussian-matrix corollaries also
discharge independence. The concrete law `rademacherMeasure` is
`NLAlib.Concentration.Scalar.Rademacher`. Atlas: `hutchinson-unbiased`, `hutchinson-variance`.

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

omit [IsProbabilityMeasure μ] in
/-- A standard Gaussian law already forces a.e. measurability, since the law is nonzero.
Atlas `hutchinson-variance` (law-to-measurability bridge). -/
theorem aemeasurable_of_isStandardGaussian {g : Ω → ℝ}
    (hlaw : IsStandardGaussian μ g) : AEMeasurable g μ := by
  apply AEMeasurable.of_map_ne_zero
  rw [IsStandardGaussian] at hlaw
  rw [hlaw]
  exact IsProbabilityMeasure.ne_zero _

omit [IsProbabilityMeasure μ] in
/-- A Rademacher law already forces a.e. measurability, since its total mass is one.
Atlas `hutchinson-variance` (law-to-measurability bridge). -/
theorem aemeasurable_of_isRademacher {g : Ω → ℝ}
    (hlaw : IsRademacher μ g) : AEMeasurable g μ := by
  apply AEMeasurable.of_map_ne_zero
  intro hz
  have h := congrArg (fun ν : Measure ℝ => ν Set.univ) hz
  rw [IsRademacher] at hlaw
  rw [hlaw] at h
  norm_num at h

omit [IsProbabilityMeasure μ] in
/-- A variable with the standard Gaussian law has finite second and fourth moments,
mean zero, second moment one and fourth moment three. Avron–Toledo 2011, Lemma 5;
atlas `hutchinson-variance` (law-to-moments bridge). -/
theorem standardGaussian_hutchinson_moments {g : Ω → ℝ}
    (hg : AEMeasurable g μ) (hlaw : IsStandardGaussian μ g) :
    MemLp g 2 μ ∧ (∫ ω, g ω ∂μ) = 0 ∧ (∫ ω, g ω ^ 2 ∂μ) = 1 ∧
      Integrable (fun ω => g ω ^ 4) μ ∧ (∫ ω, g ω ^ 4 ∂μ) = 3 := by
  unfold IsStandardGaussian at hlaw
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp)
    rw [← hlaw] at h
    exact (memLp_map_measure_iff aestronglyMeasurable_id hg).1 h
  · have h := integral_id_gaussianReal (μ := 0) (v := 1)
    rw [← hlaw, integral_map hg (f := fun x : ℝ => x) (by fun_prop)] at h
    simpa using h
  · have h := variance_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_eq_integral measurable_id.aemeasurable] at h
    simp only [id, integral_id_gaussianReal, sub_zero] at h
    rw [← hlaw, integral_map hg (by fun_prop)] at h
    simpa using h
  · have h := integrable_pow_gaussianReal 4
    rw [← hlaw] at h
    exact (integrable_map_measure (by fun_prop) hg).1 h
  · have h := integral_pow_four_gaussianReal
    rw [← hlaw, integral_map hg (by fun_prop)] at h
    exact h

/-- A Rademacher variable has finite second and fourth moments, mean zero, and both
even moments equal to one. Hutchinson 1989; Avron–Toledo 2011, Lemma 6;
atlas `hutchinson-variance` (law-to-moments bridge). -/
theorem rademacher_hutchinson_moments {g : Ω → ℝ}
    (hg : AEMeasurable g μ) (hlaw : IsRademacher μ g) :
    MemLp g 2 μ ∧ (∫ ω, g ω ∂μ) = 0 ∧ (∫ ω, g ω ^ 2 ∂μ) = 1 ∧
      Integrable (fun ω => g ω ^ 4) μ ∧ (∫ ω, g ω ^ 4 ∂μ) = 1 := by
  unfold IsRademacher at hlaw
  have hS : MeasurableSet {x : ℝ | x = 1 ∨ x = -1} :=
    (measurableSet_singleton 1).union (measurableSet_singleton (-1))
  have hpm : ∀ᵐ ω ∂μ, g ω = 1 ∨ g ω = -1 := by
    rw [← ae_map_iff hg hS, hlaw, ae_add_measure_iff]
    constructor
    · exact Measure.ae_smul_measure ((ae_dirac_iff hS).2 (Or.inl rfl)) _
    · exact Measure.ae_smul_measure ((ae_dirac_iff hS).2 (Or.inr rfl)) _
  have hbd : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ 1 := hpm.mono fun ω h => by
    rcases h with h | h <;> simp [h]
  have hsq : ∀ᵐ ω ∂μ, g ω ^ 2 = 1 := hpm.mono fun ω h => by
    rcases h with h | h <;> simp [h]
  have hfour : ∀ᵐ ω ∂μ, g ω ^ 4 = 1 := hpm.mono fun ω h => by
    rcases h with h | h <;> norm_num [h]
  refine ⟨MemLp.of_bound hg.aestronglyMeasurable 1 hbd, ?_, ?_, ?_, ?_⟩
  · have h : ∫ x, x ∂(μ.map g) = ∫ ω, g ω ∂μ :=
      integral_map hg aestronglyMeasurable_id
    have hi1 : Integrable (fun x : ℝ => x) ((1 / 2 : ENNReal) • Measure.dirac (1 : ℝ)) :=
      (integrable_dirac (by simp)).smul_measure (by simp)
    have hi2 : Integrable (fun x : ℝ => x) ((1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ)) :=
      (integrable_dirac (by simp)).smul_measure (by simp)
    rw [← h, hlaw, integral_add_measure hi1 hi2, integral_smul_measure,
      integral_smul_measure, integral_dirac, integral_dirac]
    simp
  · rw [integral_congr_ae hsq]
    simp
  · exact (integrable_const (1 : ℝ)).congr (hfour.mono fun _ h => h.symm)
  · rw [integral_congr_ae hfour]
    simp

end ScalarLaws

section AbstractLaws

variable {n Ω : Type*} [Fintype n] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- An isotropic second-moment matrix implies integrable quadratic forms and
Hutchinson unbiasedness for every real square matrix. The diagonal second moments
force square integrability, so the cross moments and quadratic form are genuine
integrals. Independence and zero means are unnecessary; arbitrary measures and empty
index types are included. Source: Hutchinson 1989; Avron–Toledo 2011, §2;
atlas `hutchinson-unbiased` (general second-moment form).
atlas: hutchinson-unbiased -/
theorem integrable_and_integral_quadForm_eq_trace_of_second_moments [DecidableEq n]
    (A : Matrix n n ℝ) {z : Ω → n → ℝ}
    (hmeas : ∀ i, AEMeasurable (fun ω => z ω i) μ)
    (hsecond : ∀ i j, ∫ ω, z ω i * z ω j ∂μ = if i = j then 1 else 0) :
    Integrable (fun ω => quadForm A (z ω)) μ ∧
      (∫ ω, quadForm A (z ω) ∂μ) = A.trace := by
  have hL2 (i : n) : MemLp (fun ω => z ω i) 2 μ := by
    apply (memLp_two_iff_integrable_sq (hmeas i).aestronglyMeasurable).2
    apply integrable_of_integral_eq_one
    simpa [pow_two] using hsecond i i
  have hprod (i j : n) : Integrable (fun ω => z ω i * z ω j) μ :=
    (hL2 i).integrable_mul (hL2 j)
  constructor
  · simp_rw [quadForm_eq_sum]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hprod i j).const_mul (A i j)
  · simp_rw [quadForm_eq_sum]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hprod i j).const_mul (A i j)]
    rw [Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hprod i j).const_mul (A i j)]
    simp_rw [integral_const_mul, hsecond]
    simp

/-- Hutchinson unbiasedness for mutually independent standard Gaussian coordinates.
All moment conditions follow from the laws. Avron–Toledo 2011, Lemma 5;
atlas `hutchinson-unbiased`.
atlas: hutchinson-unbiased -/
theorem integral_quadForm_eq_trace_of_standardGaussian (A : Matrix n n ℝ)
    {z : Ω → n → ℝ} (hmeas : ∀ i, AEMeasurable (fun ω => z ω i) μ)
    (hindep : iIndepFun (fun i ω => z ω i) μ)
    (hlaw : ∀ i, IsStandardGaussian μ (fun ω => z ω i)) :
    ∫ ω, quadForm A (z ω) ∂μ = A.trace := by
  have hf := fun i => standardGaussian_hutchinson_moments (hmeas i) (hlaw i)
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
  have hf := fun i => rademacher_hutchinson_moments (hmeas i) (hlaw i)
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
  have hf := fun i => standardGaussian_hutchinson_moments (hmeas i) (hlaw i)
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
  have hf := fun i => standardGaussian_hutchinson_moments (hmeas i) (hlaw i)
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
  have hf := fun i => rademacher_hutchinson_moments (hmeas i) (hlaw i)
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
  exact (measurePreserving_eval (fun _ : n => gaussianReal 0 1) i).map_eq

/-- Symmetric Gaussian Hutchinson variance under the canonical product law, without
coordinate assumptions. Avron–Toledo 2011, Lemma 5; atlas `hutchinson-variance`. -/
theorem variance_quadForm_pi_gaussianReal {A : Matrix n n ℝ} (hA : A.IsSymm) :
    Var[fun z => quadForm A z; Measure.pi fun _ : n => gaussianReal 0 1] = 2 * frobSq A := by
  apply variance_quadForm_of_isSymm_of_standardGaussian hA
    (fun i => (measurable_pi_apply i).aemeasurable)
    (iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id))
  intro i
  exact (measurePreserving_eval (fun _ : n => gaussianReal 0 1) i).map_eq

end ProductGaussian

section ProductRademacher

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The canonical product of Rademacher laws gives an unbiased Hutchinson estimator.
All coordinate laws and independence hypotheses are discharged. Hutchinson 1989;
atlas `hutchinson-unbiased`. -/
theorem integral_quadForm_pi_rademacherMeasure (A : Matrix n n ℝ) :
    ∫ z, quadForm A z ∂(Measure.pi fun _ : n => rademacherMeasure) = A.trace := by
  apply integral_quadForm_eq_trace_of_rademacher A
    (fun i => (measurable_pi_apply i).aemeasurable)
    (iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id))
  intro i
  exact (measurePreserving_eval (fun _ : n => rademacherMeasure) i).map_eq

/-- Symmetric Hutchinson variance under the concrete product Rademacher law.
Hutchinson 1989; Avron–Toledo 2011, Lemma 6; atlas `hutchinson-variance`. -/
theorem variance_quadForm_pi_rademacherMeasure {A : Matrix n n ℝ} (hA : A.IsSymm) :
    Var[fun z => quadForm A z; Measure.pi fun _ : n => rademacherMeasure] =
      2 * (frobSq A - ∑ i, A i i ^ 2) := by
  apply variance_quadForm_of_isSymm_of_rademacher hA
    (fun i => (measurable_pi_apply i).aemeasurable)
    (iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id))
  intro i
  exact (measurePreserving_eval (fun _ : n => rademacherMeasure) i).map_eq

end ProductRademacher

section GaussianMatrix

variable {n : ℕ}

private theorem gaussianMatrix_column_iIndepFun :
    iIndepFun (fun i (G : Fin n → Fin 1 → ℝ) => G i 0) (gaussianMatrix n 1) := by
  have hrows : iIndepFun (fun i (G : Fin n → Fin 1 → ℝ) => G i)
      (gaussianMatrix n 1) :=
    iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id)
  exact hrows.comp (fun _ row => row 0) (fun _ => measurable_pi_apply 0)

/-- Hutchinson unbiasedness for the column of an actual standard Gaussian matrix.
Avron–Toledo 2011, Lemma 5; atlas `hutchinson-unbiased`. -/
theorem integral_quadForm_gaussianMatrix_column (A : Matrix (Fin n) (Fin n) ℝ) :
    ∫ G, quadForm A (fun i => G i 0) ∂(gaussianMatrix n 1) = A.trace := by
  apply integral_quadForm_eq_trace_of_standardGaussian A
    (fun i => (measurePreserving_gaussianMatrix_entry i 0).measurable.aemeasurable)
    gaussianMatrix_column_iIndepFun
  intro i
  exact (measurePreserving_gaussianMatrix_entry i 0).map_eq

/-- Symmetric Hutchinson variance for the column of an actual standard Gaussian matrix.
Avron–Toledo 2011, Lemma 5; atlas `hutchinson-variance`.
atlas: hutchinson-variance -/
theorem variance_quadForm_gaussianMatrix_column {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsSymm) :
    Var[fun G => quadForm A (fun i => G i 0); gaussianMatrix n 1] = 2 * frobSq A := by
  apply variance_quadForm_of_isSymm_of_standardGaussian hA
    (fun i => (measurePreserving_gaussianMatrix_entry i 0).measurable.aemeasurable)
    gaussianMatrix_column_iIndepFun
  intro i
  exact (measurePreserving_gaussianMatrix_entry i 0).map_eq

end GaussianMatrix

end NLAlib
