import NLAlib.Polynomial.FunctionApproximation.JacksonTensorKernel

/-!
# Coefficient-controlled tensor Jackson approximation

The finite tensor polynomial uses actual normalized Chebyshev coefficients and
the explicit product Jackson damping. The positive kernel controls the error.
Source: Musco--Musco--Shah--Urschel--West, arXiv:2605.31430v2, Theorem 2.5;
MMRS arXiv:2408.12385v3, Appendix A.1.
Atlas: `tensor-chebyshev-kernel-measure`, `chebyshev-moment-wasserstein` (partial).
-/

noncomputable section

open Real MeasureTheory Set Finset Polynomial.Chebyshev

namespace NLAlib

/-- The tensor basis is continuous in the coordinate vector. -/
@[fun_prop] theorem continuous_tensorNormalizedChebyshev {ι : Type*} [Fintype ι]
    (α : ι → ℕ) : Continuous (tensorNormalizedChebyshev α) := by
  unfold tensorNormalizedChebyshev
  fun_prop

/-- The actual finite tensor Jackson polynomial with coefficient contractions. -/
def tensorChebyshevJacksonApprox {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : EuclideanSpace ℝ ι → ℝ) (M : ℕ) (r : EuclideanSpace ℝ ι) : ℝ :=
  ∑ α ∈ Fintype.piFinset (fun _ : ι => range (M + 1)), tensorChebyshevJacksonDamping M α *
    tensorChebyshevCoeff f α * tensorNormalizedChebyshev α (WithLp.ofLp r)

/-- Every finite tensor Jackson approximant is a continuous polynomial function. -/
@[fun_prop] theorem continuous_tensorChebyshevJacksonApprox {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : EuclideanSpace ℝ ι → ℝ) (M : ℕ) : Continuous (tensorChebyshevJacksonApprox f M) := by
  unfold tensorChebyshevJacksonApprox
  exact continuous_finsetSum _ (fun α _ => continuous_const.mul
    ((continuous_tensorNormalizedChebyshev α).comp (PiLp.continuous_ofLp 2 _)))

/-- Tensor approximation depends only on values on the closed cube. -/
theorem tensorChebyshevJacksonApprox_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f g : EuclideanSpace ℝ ι → ℝ} (hfg : EqOn f g (chebyshevCube ι)) (M : ℕ)
    (r : EuclideanSpace ℝ ι) : tensorChebyshevJacksonApprox f M r = tensorChebyshevJacksonApprox g M r := by
  simp_rw [tensorChebyshevJacksonApprox, tensorChebyshevCoeff_congr hfg]

/-- The finite tensor polynomial is the actual product-kernel integral. -/
theorem tensorChebyshevJacksonApprox_eq_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : EuclideanSpace ℝ ι → ℝ} (hf : Continuous f) (M : ℕ) (r : EuclideanSpace ℝ ι) :
    tensorChebyshevJacksonApprox f M r =
      ∫ x, tensorChebyshevJacksonKernel M x (WithLp.ofLp r) * f (WithLp.toLp 2 x)
        ∂Measure.pi (fun _ => measureT) := by
  have hterm (α : ι → ℕ) (x : ι → ℝ) : tensorChebyshevJacksonDamping M α *
      tensorNormalizedChebyshev α x * tensorNormalizedChebyshev α (WithLp.ofLp r) *
        f (WithLp.toLp 2 x) =
      (tensorChebyshevJacksonDamping M α * tensorNormalizedChebyshev α (WithLp.ofLp r)) *
        (f (WithLp.toLp 2 x) * tensorNormalizedChebyshev α x) := by ring
  simp_rw [tensorChebyshevJacksonKernel_eq_sum, sum_mul, hterm]
  rw [integral_finsetSum (f := fun α x =>
    (tensorChebyshevJacksonDamping M α * tensorNormalizedChebyshev α (WithLp.ofLp r)) *
      (f (WithLp.toLp 2 x) * tensorNormalizedChebyshev α x)) _ (fun α _ =>
    (integrable_pi_measureT_of_continuous ((hf.comp (PiLp.continuous_toLp 2 _)).mul
      (continuous_tensorNormalizedChebyshev α))).const_mul _)]
  simp_rw [integral_const_mul]
  unfold tensorChebyshevJacksonApprox tensorChebyshevCoeff tensorNormalizedChebyshev
  apply sum_congr rfl
  intro α _
  ring

/-- In finite Euclidean space, the Euclidean norm is bounded by the sum of
absolute coordinate values. -/
theorem euclidean_norm_le_sum_abs {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    ‖x‖ ≤ ∑ i, |x i| := by
  classical
  have hx : x = ∑ i, PiLp.single 2 i (x i) := by
    ext j
    simp
  calc
    ‖x‖ = ‖∑ i, PiLp.single 2 i (x i)‖ := congrArg norm hx
    _ ≤ ∑ i, ‖(PiLp.single 2 i (x i) : EuclideanSpace ℝ ι)‖ := norm_sum_le _ _
    _ = _ := by simp only [PiLp.norm_single, Real.norm_eq_abs]

/-- Euclidean Lipschitz functions have the explicit tensor Jackson uniform
error `6dL/M`. This global form is the intermediate extension theorem. -/
theorem abs_tensorChebyshevJacksonApprox_sub_le_of_lipschitzWith
    {ι : Type*} [Fintype ι] [DecidableEq ι] {f : EuclideanSpace ℝ ι → ℝ}
    {L : NNReal} (hf : LipschitzWith L f) {M : ℕ} (hM : 1 ≤ M)
    {r : EuclideanSpace ℝ ι} (hr : r ∈ chebyshevCube ι) :
    |tensorChebyshevJacksonApprox f M r - f r| ≤ 6 * Fintype.card ι * (L : ℝ) / M := by
  have hK : Continuous (fun x : ι → ℝ => tensorChebyshevJacksonKernel M x (WithLp.ofLp r)) := by
    fun_prop
  have hif : Integrable (fun x : ι → ℝ => tensorChebyshevJacksonKernel M x (WithLp.ofLp r) *
      f (WithLp.toLp 2 x)) (Measure.pi (fun _ => measureT)) :=
    integrable_pi_measureT_of_continuous (hK.mul (hf.continuous.comp (PiLp.continuous_toLp 2 _)))
  have heq : tensorChebyshevJacksonApprox f M r - f r =
      ∫ x, tensorChebyshevJacksonKernel M x (WithLp.ofLp r) * (f (WithLp.toLp 2 x) - f r)
        ∂Measure.pi (fun _ => measureT) := by
    rw [tensorChebyshevJacksonApprox_eq_integral hf.continuous]
    simp_rw [mul_sub]
    rw [integral_sub hif ((integrable_pi_measureT_of_continuous hK).mul_const _),
      integral_mul_const, integral_tensorChebyshevJacksonKernel, one_mul]
  rw [heq, ← Real.norm_eq_abs]
  have hdom : Integrable (fun x : ι → ℝ => (L : ℝ) *
      (tensorChebyshevJacksonKernel M x (WithLp.ofLp r) * ∑ i, |x i - r i|))
      (Measure.pi (fun _ => measureT)) := integrable_pi_measureT_of_continuous (by fun_prop)
  have hbound := norm_integral_le_of_norm_le hdom (show ∀ᵐ x ∂Measure.pi (fun _ => measureT),
      ‖tensorChebyshevJacksonKernel M x (WithLp.ofLp r) * (f (WithLp.toLp 2 x) - f r)‖ ≤
        (L : ℝ) * (tensorChebyshevJacksonKernel M x (WithLp.ofLp r) * ∑ i, |x i - r i|) from by
    filter_upwards [ae_mem_chebyshevCube (ι := ι)] with x hx
    have hpos := tensorChebyshevJacksonKernel_nonneg M hx hr
    have hLip := hf.dist_le_mul (WithLp.toLp 2 x) r
    rw [Real.dist_eq, dist_eq_norm] at hLip
    have hnorm := euclidean_norm_le_sum_abs (WithLp.toLp 2 x - r)
    have hL : |f (WithLp.toLp 2 x) - f r| ≤ (L : ℝ) * ∑ i, |x i - r i| :=
      hLip.trans (mul_le_mul_of_nonneg_left hnorm L.coe_nonneg)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpos]
    exact (mul_le_mul_of_nonneg_left hL hpos).trans_eq (by ring))
  rw [integral_const_mul] at hbound
  exact hbound.trans ((mul_le_mul_of_nonneg_left
    (integral_tensorChebyshevJacksonKernel_mul_sum_abs_sub_le hM hr) L.coe_nonneg).trans_eq (by ring))

/-- The full tensor Jackson error requires Lipschitz continuity only on the
closed Euclidean cube, as in the informal approximation theorem. -/
theorem abs_tensorChebyshevJacksonApprox_sub_le_of_lipschitzOnWith
    {ι : Type*} [Fintype ι] [DecidableEq ι] {f : EuclideanSpace ℝ ι → ℝ}
    {L : NNReal} (hf : LipschitzOnWith L f (chebyshevCube ι)) {M : ℕ} (hM : 1 ≤ M)
    {r : EuclideanSpace ℝ ι} (hr : r ∈ chebyshevCube ι) :
    |tensorChebyshevJacksonApprox f M r - f r| ≤ 6 * Fintype.card ι * (L : ℝ) / M := by
  obtain ⟨g, hg, hfg⟩ := hf.extend_real
  rw [tensorChebyshevJacksonApprox_congr hfg, hfg hr]
  exact abs_tensorChebyshevJacksonApprox_sub_le_of_lipschitzWith hg hM hr

end NLAlib
