import NLAlib.Polynomial.Quadrature.GaussFilledContour
import NLAlib.ForMathlib.Analysis.Complex.CubicalPathChainWinding
import NLAlib.ForMathlib.Analysis.Complex.CubicalPathChainBounds

/-! # General piecewise C1 Gauss remainder from geometric contour data

The contour is an actual closed finite concatenation of C1 native paths.
Its closed filled region is represented explicitly as its trace together
with all bounded complementary components. This is the usual closed
interior for a Jordan contour; the theorem in fact applies to arbitrary
finite cycles with this geometric neighborhood property. It neither uses
nor asserts a separate Jordan separation or classification theorem.

One normalized native inverse integral at one point of the avoided support
interval specifies positive orientation. All support-wise winding values,
support containment in the filled region, an actual finite filling, Cauchy's
formula, and the required integration interchanges are then derived.
Source: Gautschi (2004), Theorem 2.48.
-/

noncomputable section
open Polynomial MeasureTheory Set Complex
open scoped unitInterval
namespace NLAlib

/-- The actual native general-contour Gauss formula from a closed filled
region and one positive-orientation normalization. Only the individual
pieces are C1; arbitrary corners and zero velocities are allowed. The
canonical rule includes order zero and exact support termination.
Source: Gautschi (2004), Theorem 2.48.
atlas: gauss-remainder-contour-kernel (partial) -/
theorem integral_sub_gauss_eq_curveIntegral_concat_of_positive_orientation
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn : (n : ℕ∞) ≤ μ.support.encard)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω)
    {k : ℕ} (p : Fin (k + 1) → Ω)
    (γ : (i : Fin k) → Path (p i.castSucc) (p i.succ))
    (hp : p (Fin.last k) = p 0)
    (hγ : ∀ i, ContDiffOn ℝ 1 ((γ i).map continuous_subtype_val).extend I)
    (hoff : ∀ i r, ∀ x ∈ Icc a b, ((γ i) r : ℂ) ≠ (x : ℂ))
    (hfill : boundedComplementFill (cubicalTrace (Cubical.pathChain p γ)) ⊆ Ω)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Icc a b)
    (hpos : (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      curveIntegral (fun z => (z - (x₀ : ℂ))⁻¹ • ContinuousLinearMap.id ℂ ℂ)
        ((Path.concat p γ).map continuous_subtype_val) = 1) :
    let hμ := hasPolynomialMoments_of_ae_mem_Icc hs
    (∫ x : ℝ, f (x : ℂ) ∂μ) - ∑ i : Fin n, (gaussWeights μ hμ n i : ℂ) *
        f (gaussNodes μ hμ n i : ℂ) =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        curveIntegral (fun z => (f z * gaussRemainderKernel μ hμ n z) •
          ContinuousLinearMap.id ℂ ℂ) ((Path.concat p γ).map continuous_subtype_val) := by
  have hw := cubicalWindingIntegral_pathChain_eq_one_of_curveIntegral_eq p γ hp hγ hx₀ hoff hpos
  have hI (x : ℝ) (hx : x ∈ Icc a b) : (x : ℂ) ∈ Ω := by
    apply hfill
    apply mem_boundedComplementFill_cubicalTrace_of_winding_ne_zero (Cubical.pathChain p γ)
      (Cubical.boundaryOne_pathChain_eq_zero p γ hp)
      (contDiffOn_cubicalPath_of_mem_support_pathChain p γ hγ)
    rw [hw x hx]
    exact one_ne_zero
  exact integral_sub_gauss_eq_curveIntegral_concat_of_boundedComplementFill_subset hs hn hΩ hf hI
    p γ hp hγ hoff hfill hw

/-- The exact two-maximum general-contour Gauss error estimate, under the
same geometric filled-region and one-point orientation data as the native
formula. The length is the actual sum of piece-speed integrals through the
native finite path chain.
Source: Gautschi (2004), Theorem 2.48.
atlas: gauss-remainder-contour-kernel (partial) -/
theorem norm_integral_sub_gauss_le_length_mul_maxNorm_of_positive_orientation
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn : (n : ℕ∞) ≤ μ.support.encard)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω)
    {k : ℕ} (p : Fin (k + 1) → Ω)
    (γ : (i : Fin k) → Path (p i.castSucc) (p i.succ))
    (hp : p (Fin.last k) = p 0)
    (hγ : ∀ i, ContDiffOn ℝ 1 ((γ i).map continuous_subtype_val).extend I)
    (hoff : ∀ i r, ∀ x ∈ Icc a b, ((γ i) r : ℂ) ≠ (x : ℂ))
    (hfill : boundedComplementFill (cubicalTrace (Cubical.pathChain p γ)) ⊆ Ω)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Icc a b)
    (hpos : (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      curveIntegral (fun z => (z - (x₀ : ℂ))⁻¹ • ContinuousLinearMap.id ℂ ℂ)
        ((Path.concat p γ).map continuous_subtype_val) = 1) :
    let hμ := hasPolynomialMoments_of_ae_mem_Icc hs
    ‖(∫ x : ℝ, f (x : ℂ) ∂μ) - ∑ i : Fin n, (gaussWeights μ hμ n i : ℂ) *
      f (gaussNodes μ hμ n i : ℂ)‖ ≤
        (∑ i : Fin k, ∫ t in (0 : ℝ)..1,
          ‖derivWithin ((γ i).map continuous_subtype_val).extend I t‖) / (2 * Real.pi) *
        cubicalMaxNorm (Cubical.pathChain p γ) (gaussRemainderKernel μ hμ n) *
          cubicalMaxNorm (Cubical.pathChain p γ) f := by
  have hw := cubicalWindingIntegral_pathChain_eq_one_of_curveIntegral_eq p γ hp hγ hx₀ hoff hpos
  have hI (x : ℝ) (hx : x ∈ Icc a b) : (x : ℂ) ∈ Ω := by
    apply hfill
    apply mem_boundedComplementFill_cubicalTrace_of_winding_ne_zero (Cubical.pathChain p γ)
      (Cubical.boundaryOne_pathChain_eq_zero p γ hp)
      (contDiffOn_cubicalPath_of_mem_support_pathChain p γ hγ)
    rw [hw x hx]
    exact one_ne_zero
  have hchainoff : ∀ q ∈ (Cubical.pathChain p γ).support, ∀ r,
      ∀ x ∈ Icc a b, (q r : ℂ) ≠ (x : ℂ) := by
    intro q hq
    obtain ⟨i, rfl⟩ := Cubical.exists_piece_of_mem_support_pathChain p γ hq
    exact hoff i
  rw [← cubicalLength_pathChain_eq_sum p γ]
  exact norm_integral_sub_gauss_le_cubicalLength_mul_maxNorm_of_boundedComplementFill_subset
    hs hn hΩ hf hI (Cubical.pathChain p γ) (Cubical.boundaryOne_pathChain_eq_zero p γ hp)
    (contDiffOn_cubicalPath_of_mem_support_pathChain p γ hγ) hchainoff hfill hw

end NLAlib
