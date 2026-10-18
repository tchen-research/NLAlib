import NLAlib.Polynomial.FunctionApproximation.JacksonTensorApproximation
import NLAlib.ForMathlib.Analysis.CoordinateModulus

/-!
# Coordinate bounds for the tensor Jackson operator

The actual positive tensor kernel gives the source's sum of coordinate
Lipschitz constants, without requiring a global extension hypothesis.
Source: Musco--Musco--Shah--Urschel--West, arXiv:2605.31430v2, Theorem 2.5.
Atlas: `tensor-chebyshev-kernel-measure` (partial).
-/

noncomputable section

open Real MeasureTheory Set Finset Polynomial.Chebyshev

namespace NLAlib

/-- The tensor kernel has the weighted coordinate displacement bound. -/
theorem integral_tensorChebyshevJacksonKernel_mul_sum_weighted_abs_sub_le
    {ι : Type*} [Fintype ι] {M : ℕ} (hM : 1 ≤ M) (L : ι → NNReal)
    {r : ι → ℝ} (hr : ∀ i, r i ∈ Icc (-1 : ℝ) 1) :
    (∫ x, tensorChebyshevJacksonKernel M x r * ∑ i, (L i : ℝ) * |x i - r i|
      ∂Measure.pi (fun _ => measureT)) ≤ (6 / M) * ∑ i, (L i : ℝ) := by
  have hfun (x : ι → ℝ) : tensorChebyshevJacksonKernel M x r *
      (∑ i, (L i : ℝ) * |x i - r i|) =
      ∑ i, (L i : ℝ) * (tensorChebyshevJacksonKernel M x r * |x i - r i|) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  simp_rw [hfun]
  rw [integral_finsetSum (f := fun i x => (L i : ℝ) *
    (tensorChebyshevJacksonKernel M x r * |x i - r i|)) _
    (fun i _ => integrable_pi_measureT_of_continuous (by fun_prop))]
  simp_rw [integral_const_mul, integral_tensorChebyshevJacksonKernel_mul_abs_sub]
  calc
    _ ≤ ∑ i, (L i : ℝ) * (6 / M) := sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (integral_chebyshevJacksonKernel_mul_abs_sub_le hM (hr i)) (L i).coe_nonneg
    _ = _ := by rw [← sum_mul]; ring

/-- An actual summed coordinate modulus controls the tensor Jackson error. -/
theorem abs_tensorChebyshevJacksonApprox_sub_le_of_modulus
    {ι : Type*} [Fintype ι] [DecidableEq ι] {f : EuclideanSpace ℝ ι → ℝ}
    (hf : Continuous f) (L : ι → NNReal)
    (hmod : ∀ x ∈ chebyshevCube ι, ∀ y ∈ chebyshevCube ι,
      |f x - f y| ≤ ∑ i, (L i : ℝ) * |x i - y i|)
    {M : ℕ} (hM : 1 ≤ M) {r : EuclideanSpace ℝ ι} (hr : r ∈ chebyshevCube ι) :
    |tensorChebyshevJacksonApprox f M r - f r| ≤ (6 / M) * ∑ i, (L i : ℝ) := by
  have hK : Continuous (fun x : ι → ℝ => tensorChebyshevJacksonKernel M x (WithLp.ofLp r)) := by
    fun_prop
  have hif : Integrable (fun x : ι → ℝ => tensorChebyshevJacksonKernel M x (WithLp.ofLp r) *
      f (WithLp.toLp 2 x)) (Measure.pi (fun _ => measureT)) :=
    integrable_pi_measureT_of_continuous (hK.mul (hf.comp (PiLp.continuous_toLp 2 _)))
  have heq : tensorChebyshevJacksonApprox f M r - f r =
      ∫ x, tensorChebyshevJacksonKernel M x (WithLp.ofLp r) * (f (WithLp.toLp 2 x) - f r)
        ∂Measure.pi (fun _ => measureT) := by
    rw [tensorChebyshevJacksonApprox_eq_integral hf]
    simp_rw [mul_sub]
    rw [integral_sub hif ((integrable_pi_measureT_of_continuous hK).mul_const _),
      integral_mul_const, integral_tensorChebyshevJacksonKernel, one_mul]
  rw [heq, ← Real.norm_eq_abs]
  have hdom : Integrable (fun x : ι → ℝ => tensorChebyshevJacksonKernel M x (WithLp.ofLp r) *
      ∑ i, (L i : ℝ) * |x i - r i|) (Measure.pi (fun _ => measureT)) :=
    integrable_pi_measureT_of_continuous (by fun_prop)
  have hbound := norm_integral_le_of_norm_le hdom (show ∀ᵐ x ∂Measure.pi (fun _ => measureT),
      ‖tensorChebyshevJacksonKernel M x (WithLp.ofLp r) * (f (WithLp.toLp 2 x) - f r)‖ ≤
        tensorChebyshevJacksonKernel M x (WithLp.ofLp r) * ∑ i, (L i : ℝ) * |x i - r i| from by
    filter_upwards [ae_mem_chebyshevCube (ι := ι)] with x hx
    have hpos := tensorChebyshevJacksonKernel_nonneg M hx hr
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpos]
    exact mul_le_mul_of_nonneg_left (hmod _ hx _ hr) hpos)
  exact hbound.trans (integral_tensorChebyshevJacksonKernel_mul_sum_weighted_abs_sub_le hM L hr)

/-- Coordinate Lipschitz hypotheses telescope on the actual closed cube. -/
theorem abs_sub_le_sum_of_coordinate_chebyshevCube
    {ι : Type*} [Fintype ι] [DecidableEq ι] {f : EuclideanSpace ℝ ι → ℝ} (L : ι → NNReal)
    (hf : ∀ i, ∀ x ∈ chebyshevCube ι, ∀ y ∈ chebyshevCube ι,
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ (L i : ℝ) * |x i - y i|)
    {x y : EuclideanSpace ℝ ι} (hx : x ∈ chebyshevCube ι) (hy : y ∈ chebyshevCube ι) :
    |f x - f y| ≤ ∑ i, (L i : ℝ) * |x i - y i| :=
  Function.abs_sub_le_sum_of_coordinate_bound (fun _ : ι => Icc (-1 : ℝ) 1)
    (fun z => f (WithLp.toLp 2 z)) (fun i => (L i : ℝ))
    (fun i z hz w hw hzw => hf i (WithLp.toLp 2 z) hz (WithLp.toLp 2 w) hw hzw) hx hy

/-- Separate coordinate Lipschitz control implies Euclidean Lipschitz
continuity on the cube, so real Lipschitz extension is available. -/
theorem lipschitzOnWith_sum_of_coordinate_chebyshevCube
    {ι : Type*} [Fintype ι] [DecidableEq ι] {f : EuclideanSpace ℝ ι → ℝ} (L : ι → NNReal)
    (hf : ∀ i, ∀ x ∈ chebyshevCube ι, ∀ y ∈ chebyshevCube ι,
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ (L i : ℝ) * |x i - y i|) :
    LipschitzOnWith (∑ i, L i) f (chebyshevCube ι) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.dist_eq, dist_eq_norm]
  refine (abs_sub_le_sum_of_coordinate_chebyshevCube L hf hx hy).trans ?_
  calc
    _ ≤ ∑ i, (L i : ℝ) * ‖x - y‖ := sum_le_sum fun i _ => by
      apply mul_le_mul_of_nonneg_left _ (L i).coe_nonneg
      simpa only [PiLp.sub_apply, Real.norm_eq_abs] using (PiLp.norm_apply_le (x - y) i)
    _ = _ := by rw [← sum_mul]; simp

/-- The source's coordinate Lipschitz hypotheses imply the exact `6/M` times
the sum of the coordinate constants on the closed cube. -/
theorem abs_tensorChebyshevJacksonApprox_sub_le_of_coordinate_lipschitz
    {ι : Type*} [Fintype ι] [DecidableEq ι] {f : EuclideanSpace ℝ ι → ℝ} (L : ι → NNReal)
    (hf : ∀ i, ∀ x ∈ chebyshevCube ι, ∀ y ∈ chebyshevCube ι,
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ (L i : ℝ) * |x i - y i|)
    {M : ℕ} (hM : 1 ≤ M) {r : EuclideanSpace ℝ ι} (hr : r ∈ chebyshevCube ι) :
    |tensorChebyshevJacksonApprox f M r - f r| ≤ (6 / M) * ∑ i, (L i : ℝ) := by
  have hLip := lipschitzOnWith_sum_of_coordinate_chebyshevCube L hf
  obtain ⟨g, hg, hfg⟩ := hLip.extend_real
  rw [tensorChebyshevJacksonApprox_congr hfg, hfg hr]
  apply abs_tensorChebyshevJacksonApprox_sub_le_of_modulus hg.continuous L ?_ hM hr
  intro x hx y hy
  rw [← hfg hx, ← hfg hy]
  exact abs_sub_le_sum_of_coordinate_chebyshevCube L hf hx hy

end NLAlib
