import NLAlib.Polynomial.FunctionApproximation.JacksonApproximation

/-!
# Positive tensor Jackson kernels

Finite products preserve the exact mass-one property, the explicit coefficient
damping, and the coordinate displacement bound of the scalar Jackson kernel.
Source: Musco--Musco--Shah--Urschel--West, arXiv:2605.31430v2, Theorem 2.5.
Atlas: `tensor-chebyshev-kernel-measure` (partial).
-/

noncomputable section

open Real MeasureTheory Set Finset Polynomial.Chebyshev

namespace NLAlib

/-- Every continuous real function is integrable for the finite product
Chebyshev measure, whose support is compact. -/
theorem integrable_pi_measureT_of_continuous {ι : Type*} [Fintype ι]
    {F : (ι → ℝ) → ℝ} (hF : Continuous F) :
    Integrable F (Measure.pi (fun _ => measureT)) := by
  apply (measurePreserving_pi_cos_chebyshev.integrable_comp hF.aestronglyMeasurable).mp
  exact integrable_pi_chebyshevAngleMeasure_of_continuous
    (hF.comp (continuous_pi (fun i => continuous_cos.comp (continuous_apply i))))

/-- The exact tensor Jackson multiplier, the product of the displayed scalar ones. -/
def tensorChebyshevJacksonDamping {ι : Type*} [Fintype ι] (M : ℕ) (α : ι → ℕ) : ℝ :=
  ∏ i, chebyshevJacksonDamping M (α i)

/-- The actual normalized tensor basis evaluated at a coordinate vector. -/
def tensorNormalizedChebyshev {ι : Type*} [Fintype ι] (α : ι → ℕ) (x : ι → ℝ) : ℝ :=
  ∏ i, normalizedChebyshev (α i) (x i)

/-- The finite positive tensor Jackson kernel is the product of its scalar kernels. -/
def tensorChebyshevJacksonKernel {ι : Type*} [Fintype ι]
    (M : ℕ) (x r : ι → ℝ) : ℝ := ∏ i, chebyshevJacksonKernel M (x i) (r i)

/-- All retained tensor multipliers are coefficient contractions. -/
theorem tensorChebyshevJacksonDamping_mem_Icc {ι : Type*} [Fintype ι]
    {M : ℕ} {α : ι → ℕ} (hα : ∀ i, α i ≤ M + 1) :
    tensorChebyshevJacksonDamping M α ∈ Icc (0 : ℝ) 1 := by
  exact ⟨prod_nonneg (fun i _ => (chebyshevJacksonDamping_mem_Icc (hα i)).1),
    prod_le_one (fun i _ => (chebyshevJacksonDamping_mem_Icc (hα i)).1)
      (fun i _ => (chebyshevJacksonDamping_mem_Icc (hα i)).2)⟩

/-- The actual tensor kernel is nonnegative on the closed cube. -/
theorem tensorChebyshevJacksonKernel_nonneg {ι : Type*} [Fintype ι]
    (M : ℕ) {x r : ι → ℝ} (hx : ∀ i, x i ∈ Icc (-1 : ℝ) 1)
    (hr : ∀ i, r i ∈ Icc (-1 : ℝ) 1) :
    0 ≤ tensorChebyshevJacksonKernel M x r :=
  prod_nonneg (fun i _ => chebyshevJacksonKernel_nonneg M (hx i) (hr i))

/-- The tensor Jackson kernel has mass one, also for the empty coordinate family. -/
theorem integral_tensorChebyshevJacksonKernel {ι : Type*} [Fintype ι]
    (M : ℕ) (r : ι → ℝ) :
    (∫ x, tensorChebyshevJacksonKernel M x r ∂Measure.pi (fun _ => measureT)) = 1 := by
  unfold tensorChebyshevJacksonKernel
  rw [integral_fintype_prod_eq_prod (fun i x => chebyshevJacksonKernel M x (r i))]
  simp only [integral_chebyshevJacksonKernel, prod_const_one]

/-- The tensor kernel is continuous in both coordinate vectors. -/
@[fun_prop] theorem continuous_tensorChebyshevJacksonKernel {ι : Type*} [Fintype ι]
    (M : ℕ) : Continuous (fun p : (ι → ℝ) × (ι → ℝ) =>
      tensorChebyshevJacksonKernel M p.1 p.2) := by
  unfold tensorChebyshevJacksonKernel chebyshevJacksonKernel normalizedChebyshev
  fun_prop

/-- The tensor kernel is exactly the finite diagonal expansion with the
explicit product damping, rather than an assumed positive kernel. -/
theorem tensorChebyshevJacksonKernel_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℕ) (x r : ι → ℝ) :
    tensorChebyshevJacksonKernel M x r =
      ∑ α ∈ Fintype.piFinset (fun _ : ι => range (M + 1)), tensorChebyshevJacksonDamping M α *
        tensorNormalizedChebyshev α x * tensorNormalizedChebyshev α r := by
  classical
  unfold tensorChebyshevJacksonKernel chebyshevJacksonKernel
  rw [prod_univ_sum]
  apply sum_congr rfl
  intro α _
  simp only [tensorChebyshevJacksonDamping, tensorNormalizedChebyshev, prod_mul_distrib]

/-- A single-coordinate displacement integrates to its scalar counterpart. -/
theorem integral_tensorChebyshevJacksonKernel_mul_abs_sub {ι : Type*} [Fintype ι]
    (M : ℕ) (r : ι → ℝ) (i : ι) :
    (∫ x, tensorChebyshevJacksonKernel M x r * |x i - r i|
      ∂Measure.pi (fun _ => measureT)) =
      ∫ x, chebyshevJacksonKernel M x (r i) * |x - r i| ∂measureT := by
  classical
  have hfun (x : ι → ℝ) : tensorChebyshevJacksonKernel M x r * |x i - r i| =
      ∏ j, chebyshevJacksonKernel M (x j) (r j) * (if j = i then |x j - r j| else 1) := by
    rw [prod_mul_distrib]
    simp [tensorChebyshevJacksonKernel]
  simp_rw [hfun]
  rw [integral_fintype_prod_eq_prod (fun j (x : ℝ) =>
    chebyshevJacksonKernel M x (r j) * (if j = i then |x - r j| else 1))]
  have hint (j : ι) : (∫ x, chebyshevJacksonKernel M x (r j) *
      (if j = i then |x - r j| else 1) ∂measureT) =
      if j = i then (∫ x, chebyshevJacksonKernel M x (r i) * |x - r i| ∂measureT) else 1 := by
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji, integral_chebyshevJacksonKernel]
  simp_rw [hint]
  simp

/-- The actual product kernel has total coordinate displacement at most `6d/M`. -/
theorem integral_tensorChebyshevJacksonKernel_mul_sum_abs_sub_le {ι : Type*} [Fintype ι]
    {M : ℕ} (hM : 1 ≤ M) {r : ι → ℝ} (hr : ∀ i, r i ∈ Icc (-1 : ℝ) 1) :
    (∫ x, tensorChebyshevJacksonKernel M x r * ∑ i, |x i - r i|
      ∂Measure.pi (fun _ => measureT)) ≤ 6 * Fintype.card ι / M := by
  simp_rw [mul_sum]
  rw [integral_finsetSum (f := fun i x => tensorChebyshevJacksonKernel M x r * |x i - r i|)
    _ (fun i _ => integrable_pi_measureT_of_continuous (by fun_prop))]
  simp_rw [integral_tensorChebyshevJacksonKernel_mul_abs_sub]
  calc
    _ ≤ ∑ i : ι, (6 / M : ℝ) :=
      sum_le_sum (fun i _ => integral_chebyshevJacksonKernel_mul_abs_sub_le hM (hr i))
    _ = _ := by simp; ring

end NLAlib
