import NLAlib.Estimation.HutchinsonLaws

/-!
# The stochastic diagonal estimator

For a random vector `z` with isotropic coordinates, the `i`-th entry of `z ⊙ (A z)` is an
unbiased estimator of the diagonal entry `A_ii` (Bekas–Kokiopoulou–Saad 2007). It is the
quadratic form of the row selector `rowSelector A i` (row `i` of `A`, zero elsewhere), so the
Hutchinson identities give its mean and variance:

* `NLAlib.integral_mul_mulVec_apply_eq`: `𝔼[zᵢ (Az)ᵢ] = A_ii`;
* `NLAlib.variance_mul_mulVec_apply`: `Var[zᵢ (Az)ᵢ] = ∑ⱼ A_ij² + (m₄ − 2) A_ii²`;
* Gaussian (`m₄ = 3`): `∑ⱼ A_ij² + A_ii²`; Rademacher (`m₄ = 1`): `∑_{j ≠ i} A_ij²`
  (written `∑ⱼ A_ij² − A_ii²`).

Source: Bekas–Kokiopoulou–Saad (2007) [`bks07`], §2; Epperly–Tropp–Webber (2024) [`etw24`], §6.
Atlas: `diagonal-estimator`; uses `hutchinson-unbiased`, `hutchinson-variance`.
-/

noncomputable section

open scoped Matrix
open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The row selector: row `i` of `A`, all other rows zero. Its quadratic form is
`zᵢ (A z)ᵢ`. Atlas: `diagonal-estimator` (helper).
atlas: trace-estimators-def -/
def rowSelector (A : Matrix n n ℝ) (i : n) : Matrix n n ℝ :=
  Matrix.of fun k j => if k = i then A i j else 0

/-- `zᵀ (rowSelector A i) z = zᵢ (A z)ᵢ`. Atlas: `diagonal-estimator` (helper). -/
theorem quadForm_rowSelector (A : Matrix n n ℝ) (i : n) (z : n → ℝ) :
    quadForm (rowSelector A i) z = z i * (A *ᵥ z) i := by
  simp only [quadForm, rowSelector, dotProduct, Matrix.mulVec, Matrix.of_apply, ite_mul,
    zero_mul]
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
  simp

/-- `tr (rowSelector A i) = A_ii`. Atlas: `diagonal-estimator` (helper). -/
theorem trace_rowSelector (A : Matrix n n ℝ) (i : n) : (rowSelector A i).trace = A i i := by
  simp [rowSelector, Matrix.trace]

/-- The variance contraction for the row selector:
`∑ B_kj² + ∑ B_kj B_jk + (m₄ − 3) ∑ B_kk² = ∑ⱼ A_ij² + (m₄ − 2) A_ii²`. -/
private lemma variance_contraction_rowSelector (A : Matrix n n ℝ) (i : n) (m₄ : ℝ) :
    ∑ k, ∑ j, rowSelector A i k j ^ 2 + ∑ k, ∑ j, rowSelector A i k j * rowSelector A i j k +
        (m₄ - 3) * ∑ k, rowSelector A i k k ^ 2 =
      ∑ j, A i j ^ 2 + (m₄ - 2) * A i i ^ 2 := by
  have h1 : ∑ k, ∑ j, rowSelector A i k j ^ 2 = ∑ j, A i j ^ 2 := by
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [rowSelector, hk]) (by simp)]
    simp [rowSelector]
  have h2 : ∑ k, ∑ j, rowSelector A i k j * rowSelector A i j k = A i i ^ 2 := by
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [rowSelector, hk]) (by simp)]
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [rowSelector, hj]) (by simp)]
    simp [rowSelector, sq]
  have h3 : ∑ k, rowSelector A i k k ^ 2 = A i i ^ 2 := by
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [rowSelector, hk]) (by simp)]
    simp [rowSelector]
  rw [h1, h2, h3]
  ring

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The diagonal estimator is unbiased.** If the coordinates of `z` are square-integrable,
pairwise independent, centred and of unit second moment, then `𝔼[zᵢ (A z)ᵢ] = A_ii`.
Source: Bekas–Kokiopoulou–Saad (2007) [`bks07`], §2 (eq. (2.1)). Atlas: `diagonal-estimator`;
uses `hutchinson-unbiased`. Deviation: any isotropic vector with pairwise independent
coordinates (the source uses Rademacher or Gaussian vectors).
atlas: diagonal-estimator -/
theorem integral_mul_mulVec_apply_eq (A : Matrix n n ℝ) {z : Ω → n → ℝ}
    (hz : ∀ i, MemLp (fun ω => z ω i) 2 μ)
    (hind : ∀ i j, i ≠ j → IndepFun (fun ω => z ω i) (fun ω => z ω j) μ)
    (hmean : ∀ i, ∫ ω, z ω i ∂μ = 0) (hsq : ∀ i, ∫ ω, z ω i ^ 2 ∂μ = 1) (i : n) :
    ∫ ω, z ω i * (A *ᵥ z ω) i ∂μ = A i i := by
  simp_rw [← quadForm_rowSelector]
  rw [integral_quadForm_eq_trace _ hz hind hmean hsq, trace_rowSelector]

/-- **Variance of the diagonal estimator.** If the coordinates of `z` are independent,
centred, of unit variance and common fourth moment `m₄`, then
`Var[zᵢ (A z)ᵢ] = ∑ⱼ A_ij² + (m₄ − 2) A_ii²`.
Source: Bekas–Kokiopoulou–Saad (2007) [`bks07`], §2; derived from the Hutchinson variance
identity (Avron–Toledo 2011 [`at11`], Lem. 5–6) for the row selector. Atlas:
`diagonal-estimator`; uses `hutchinson-variance`.
atlas: diagonal-estimator -/
theorem variance_mul_mulVec_apply (A : Matrix n n ℝ) {z : Ω → n → ℝ}
    (hmeas : ∀ i, AEMeasurable (fun ω => z ω i) μ)
    (hindep : iIndepFun (fun i ω => z ω i) μ)
    (hmean : ∀ i, ∫ ω, z ω i ∂μ = 0) (hsq : ∀ i, ∫ ω, z ω i ^ 2 ∂μ = 1)
    (h4 : ∀ i, Integrable (fun ω => z ω i ^ 4) μ) {m₄ : ℝ}
    (hm4 : ∀ i, ∫ ω, z ω i ^ 4 ∂μ = m₄) (i : n) :
    Var[fun ω => z ω i * (A *ᵥ z ω) i; μ] = ∑ j, A i j ^ 2 + (m₄ - 2) * A i i ^ 2 := by
  simp_rw [← quadForm_rowSelector]
  rw [variance_quadForm _ hmeas hindep hmean hsq h4 hm4, variance_contraction_rowSelector]

/-- Diagonal estimator with independent standard Gaussian coordinates: unbiased, with
variance `∑ⱼ A_ij² + A_ii²`. Source: Bekas–Kokiopoulou–Saad (2007) [`bks07`], §2.
Atlas: `diagonal-estimator`.
atlas: diagonal-estimator -/
theorem integral_and_variance_mul_mulVec_apply_of_standardGaussian (A : Matrix n n ℝ) {z : Ω → n → ℝ}
    (hindep : iIndepFun (fun i ω => z ω i) μ)
    (hlaw : ∀ i, IsStandardGaussian μ (fun ω => z ω i)) (i : n) :
    (∫ ω, z ω i * (A *ᵥ z ω) i ∂μ) = A i i ∧
      Var[fun ω => z ω i * (A *ᵥ z ω) i; μ] = ∑ j, A i j ^ 2 + A i i ^ 2 := by
  have hmeas := fun i => aemeasurable_of_isStandardGaussian (hlaw i)
  have hf := fun i => standardGaussian_hutchinson_moments (hmeas i) (hlaw i)
  refine ⟨integral_mul_mulVec_apply_eq A (fun i => (hf i).1)
    (fun _ _ hij => hindep.indepFun hij) (fun i => (hf i).2.1) (fun i => (hf i).2.2.1) i, ?_⟩
  rw [variance_mul_mulVec_apply A hmeas hindep (fun i => (hf i).2.1) (fun i => (hf i).2.2.1)
    (fun i => (hf i).2.2.2.1) (fun i => (hf i).2.2.2.2) i]
  ring

/-- Diagonal estimator with independent Rademacher coordinates: unbiased, with variance
`∑ⱼ A_ij² − A_ii² = ∑_{j ≠ i} A_ij²`. Source: Bekas–Kokiopoulou–Saad (2007) [`bks07`], §2.
Atlas: `diagonal-estimator`.
atlas: diagonal-estimator -/
theorem integral_and_variance_mul_mulVec_apply_of_rademacher (A : Matrix n n ℝ) {z : Ω → n → ℝ}
    (hindep : iIndepFun (fun i ω => z ω i) μ)
    (hlaw : ∀ i, IsRademacher μ (fun ω => z ω i)) (i : n) :
    (∫ ω, z ω i * (A *ᵥ z ω) i ∂μ) = A i i ∧
      Var[fun ω => z ω i * (A *ᵥ z ω) i; μ] = ∑ j, A i j ^ 2 - A i i ^ 2 := by
  have hmeas := fun i => aemeasurable_of_isRademacher (hlaw i)
  have hf := fun i => rademacher_hutchinson_moments (hmeas i) (hlaw i)
  refine ⟨integral_mul_mulVec_apply_eq A (fun i => (hf i).1)
    (fun _ _ hij => hindep.indepFun hij) (fun i => (hf i).2.1) (fun i => (hf i).2.2.1) i, ?_⟩
  rw [variance_mul_mulVec_apply A hmeas hindep (fun i => (hf i).2.1) (fun i => (hf i).2.2.1)
    (fun i => (hf i).2.2.2.1) (fun i => (hf i).2.2.2.2) i]
  ring

end Probability

end NLAlib
