import NLAlib.Matrix.Norms.BilinearProbes
import NLAlib.ForMathlib.Analysis.Matrix.BilinearFunctional
import NLAlib.ForMathlib.MeasureTheory.MatrixIntegral
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Actual centered bilinear weak variance of a matrix law

The squared sigma-star parameter is the supremum of the actual centered
complex bilinear second moments. Closed unit balls retain all degenerate
shapes and supply the natural interface to the resolvent concentration API.
It is distinct from the single-vector quadratic weak variance.
Source: arXiv:2201.05142v3, Section 2.1 and Theorem 2.6.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "E" => EuclideanSpace ℂ n

open scoped Matrix.Norms.L2Operator in
/-- The actual centered bilinear second-moment supremum over two closed
Euclidean unit balls. It is finite for square-integrable matrix laws.
Source: arXiv:2201.05142v3, the sigma-star parameter. -/
def bilinearWeakVariance (μ : Measure M) : ℝ :=
  sSup ((fun q : E × E => ∫ A : M,
    ‖star q.1.ofLp ⬝ᵥ ((A-∫ B : M, B ∂μ) *ᵥ q.2.ofLp)‖^2 ∂μ) ''
      {q | ‖q.1‖ ≤ 1 ∧ ‖q.2‖ ≤ 1})

open scoped Matrix.Norms.L2Operator in
/-- The actual bilinear weak variance is nonnegative in every dimension. -/
theorem bilinearWeakVariance_nonneg (μ : Measure M) : 0 ≤ bilinearWeakVariance μ := by
  apply Real.sSup_nonneg
  rintro _ ⟨q, _, rfl⟩
  exact integral_nonneg fun _ => sq_nonneg _

open scoped Matrix.Norms.L2Operator in
/-- Every actual centered unit-ball bilinear moment is bounded by the
actual centered operator-norm second moment. Hermitian support is unnecessary. -/
theorem integral_norm_sq_centered_bilinear_le_centered_specNorm_sq
    (μ : Measure M) [IsProbabilityMeasure μ] (hμ : MemLp (id : M → M) 2 μ)
    (v w : E) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    (∫ A : M, ‖star v.ofLp ⬝ᵥ ((A-∫ B : M, B ∂μ) *ᵥ w.ofLp)‖^2 ∂μ) ≤
      ∫ A : M, specNorm (A-∫ B : M, B ∂μ)^2 ∂μ := by
  have hc : MemLp (fun A : M => A-∫ B : M, B ∂μ) 2 μ := hμ.sub (memLp_const _)
  have hb := ((Matrix.bilinearCLM v.ofLp w.ofLp).restrictScalars ℝ).comp_memLp' hc
  change MemLp (fun A : M => star v.ofLp ⬝ᵥ ((A-∫ B : M, B ∂μ) *ᵥ w.ofLp)) 2 μ at hb
  have hi := hb.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hn : Integrable (fun A : M => specNorm (A-∫ B : M, B ∂μ)^2) μ := by
    simpa only [specNorm_eq_norm] using hc.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  apply integral_mono hi hn
  intro A
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_star_dotProduct_mulVec_le_specNorm _ v w hv hw) 2

open scoped Matrix.Norms.L2Operator in
/-- The actual centered bilinear moments on the two unit balls form a
bounded set for every square-integrable matrix probability law. -/
theorem bddAbove_centered_bilinear_moments
    (μ : Measure M) [IsProbabilityMeasure μ] (hμ : MemLp (id : M → M) 2 μ) :
    BddAbove ((fun q : E × E => ∫ A : M,
      ‖star q.1.ofLp ⬝ᵥ ((A-∫ B : M, B ∂μ) *ᵥ q.2.ofLp)‖^2 ∂μ) ''
        {q | ‖q.1‖ ≤ 1 ∧ ‖q.2‖ ≤ 1}) := by
  refine ⟨∫ A : M, specNorm (A-∫ B : M, B ∂μ)^2 ∂μ, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  exact integral_norm_sq_centered_bilinear_le_centered_specNorm_sq μ hμ q.1 q.2 hq.1 hq.2

open scoped Matrix.Norms.L2Operator in
/-- The defined weak variance bounds each actual centered unit-ball
bilinear moment. The bound is on the literal modulus-squared expectation. -/
theorem integral_norm_sq_centered_bilinear_le_bilinearWeakVariance
    (μ : Measure M) [IsProbabilityMeasure μ] (hμ : MemLp (id : M → M) 2 μ)
    (v w : E) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    (∫ A : M, ‖star v.ofLp ⬝ᵥ ((A-∫ B : M, B ∂μ) *ᵥ w.ofLp)‖^2 ∂μ) ≤
      bilinearWeakVariance μ :=
  le_csSup (bddAbove_centered_bilinear_moments μ hμ) ⟨(v,w), ⟨hv,hw⟩, rfl⟩

open scoped Matrix.Norms.L2Operator in
/-- A uniform actual bilinear second-moment budget bounds the defined
weak variance, including empty matrix dimensions. -/
theorem bilinearWeakVariance_le (μ : Measure M) {b : ℝ}
    (h : ∀ v w : E, ‖v‖ ≤ 1 → ‖w‖ ≤ 1 →
      (∫ A : M, ‖star v.ofLp ⬝ᵥ ((A-∫ B : M, B ∂μ) *ᵥ w.ofLp)‖^2 ∂μ) ≤ b) :
    bilinearWeakVariance μ ≤ b := by
  apply csSup_le
  · exact ⟨0, ⟨(0,0), by simp, by simp⟩⟩
  · rintro _ ⟨q,hq,rfl⟩
    exact h q.1 q.2 hq.1 hq.2

open scoped Matrix.Norms.L2Operator in
/-- The native bilinear weak variance is finite and bounded by the actual
centered operator-norm second moment. -/
theorem bilinearWeakVariance_le_centered_specNorm_sq
    (μ : Measure M) [IsProbabilityMeasure μ] (hμ : MemLp (id : M → M) 2 μ) :
    bilinearWeakVariance μ ≤ ∫ A : M, specNorm (A-∫ B : M, B ∂μ)^2 ∂μ :=
  bilinearWeakVariance_le μ (integral_norm_sq_centered_bilinear_le_centered_specNorm_sq μ hμ)

end NLAlib
