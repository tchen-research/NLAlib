import NLAlib.Polynomial.Quadrature.GaussCubicalNorm
import NLAlib.ForMathlib.Analysis.Complex.CubicalFilledTrace
import NLAlib.ForMathlib.Analysis.Complex.CubicalPathChainIntegral

/-! # Gauss remainder on contours with a filled-trace neighborhood

The actual finite filling theorem discharges the topological premise in
the general-contour Gauss formula and exact maximum-norm estimate. The
bounded-complement fill models the trace plus all bounded complementary
components; for a Jordan contour this is the standard closed interior.
No Jordan separation theorem is assumed or proved here: the stronger
finite-cycle theorem directly uses this explicit geometric closed-fill set.

The finite native path version identifies the resulting chain integral
with the actual integral of the cornered concatenation. Only the individual
pieces are C1, and zero derivatives and degenerate pieces are allowed.
Source: Gautschi (2004), Theorem 2.48.
-/

noncomputable section
open Polynomial MeasureTheory Set Complex
open scoped unitInterval
namespace NLAlib

/-- General-contour Gauss remainder under the actual geometric neighborhood
hypothesis. The finite cubical filling and Cauchy formula are proved from
the compact filled trace, rather than supplied as assumptions.
Source: Gautschi (2004), Theorem 2.48.
atlas: gauss-remainder-contour-kernel (partial) -/
theorem integral_sub_gauss_eq_cubicalCurveIntegral_of_boundedComplementFill_subset
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn : (n : ℕ∞) ≤ μ.support.encard)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω)
    (hI : ∀ x ∈ Icc a b, (x : ℂ) ∈ Ω) (Γ : Cubical.OneChain Ω)
    (hc : Cubical.boundaryOne Γ = 0)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    (hoff : ∀ γ ∈ Γ.support, ∀ r, ∀ x ∈ Icc a b, (γ r : ℂ) ≠ (x : ℂ))
    (hfill : boundedComplementFill (cubicalTrace Γ) ⊆ Ω)
    (hw : ∀ x ∈ Icc a b, cubicalWindingIntegral Γ (x : ℂ) = 1) :
    let hμ := hasPolynomialMoments_of_ae_mem_Icc hs
    (∫ x : ℝ, f (x : ℂ) ∂μ) - ∑ i : Fin n, (gaussWeights μ hμ n i : ℂ) *
        f (gaussNodes μ hμ n i : ℂ) =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        cubicalCurveIntegral (fun z => f z * gaussRemainderKernel μ hμ n z) Γ := by
  exact integral_sub_gauss_eq_cubicalCurveIntegral_gaussRemainderKernel hs hn hΩ hf hI Γ hΓ
    hoff (isNullHomologous_of_boundedComplementFill_cubicalTrace_subset hΩ Γ hc hΓ hfill) hw

/-- The exact length-over-`2 pi` times two actual contour maxima bound,
under the geometric filled-trace hypothesis. The theorem constructs the
filling and proves compact-support kernel continuity.
Source: Gautschi (2004), Theorem 2.48.
atlas: gauss-remainder-contour-kernel (partial) -/
theorem norm_integral_sub_gauss_le_cubicalLength_mul_maxNorm_of_boundedComplementFill_subset
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn : (n : ℕ∞) ≤ μ.support.encard)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω)
    (hI : ∀ x ∈ Icc a b, (x : ℂ) ∈ Ω) (Γ : Cubical.OneChain Ω)
    (hc : Cubical.boundaryOne Γ = 0)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    (hoff : ∀ γ ∈ Γ.support, ∀ r, ∀ x ∈ Icc a b, (γ r : ℂ) ≠ (x : ℂ))
    (hfill : boundedComplementFill (cubicalTrace Γ) ⊆ Ω)
    (hw : ∀ x ∈ Icc a b, cubicalWindingIntegral Γ (x : ℂ) = 1) :
    let hμ := hasPolynomialMoments_of_ae_mem_Icc hs
    ‖(∫ x : ℝ, f (x : ℂ) ∂μ) - ∑ i : Fin n, (gaussWeights μ hμ n i : ℂ) *
      f (gaussNodes μ hμ n i : ℂ)‖ ≤ cubicalLength Γ / (2 * Real.pi) *
        cubicalMaxNorm Γ (gaussRemainderKernel μ hμ n) * cubicalMaxNorm Γ f := by
  exact norm_integral_sub_gauss_le_cubicalLength_mul_maxNorm hs hn hΩ hf hI Γ hΓ hoff
    (isNullHomologous_of_boundedComplementFill_cubicalTrace_subset hΩ Γ hc hΓ hfill) hw

/-- The source's general-contour formula with the actual native integral
of a finite concatenation of C1 pieces. Endpoint closure gives a cycle;
actual filled-trace geometry constructs its filling. Smoothness at the joins
is not required.
Source: Gautschi (2004), Theorem 2.48.
atlas: gauss-remainder-contour-kernel (partial) -/
theorem integral_sub_gauss_eq_curveIntegral_concat_of_boundedComplementFill_subset
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn : (n : ℕ∞) ≤ μ.support.encard)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω)
    (hI : ∀ x ∈ Icc a b, (x : ℂ) ∈ Ω) {k : ℕ}
    (p : Fin (k + 1) → Ω) (γ : (i : Fin k) → Path (p i.castSucc) (p i.succ))
    (hp : p (Fin.last k) = p 0)
    (hγ : ∀ i, ContDiffOn ℝ 1 ((γ i).map continuous_subtype_val).extend I)
    (hoff : ∀ i r, ∀ x ∈ Icc a b, ((γ i) r : ℂ) ≠ (x : ℂ))
    (hfill : boundedComplementFill (cubicalTrace (Cubical.pathChain p γ)) ⊆ Ω)
    (hw : ∀ x ∈ Icc a b, cubicalWindingIntegral (Cubical.pathChain p γ) (x : ℂ) = 1) :
    let hμ := hasPolynomialMoments_of_ae_mem_Icc hs
    (∫ x : ℝ, f (x : ℂ) ∂μ) - ∑ i : Fin n, (gaussWeights μ hμ n i : ℂ) *
        f (gaussNodes μ hμ n i : ℂ) =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        curveIntegral (fun z => (f z * gaussRemainderKernel μ hμ n z) •
          ContinuousLinearMap.id ℂ ℂ) ((Path.concat p γ).map continuous_subtype_val) := by
  let hμ := hasPolynomialMoments_of_ae_mem_Icc hs
  have hchainoff : ∀ q ∈ (Cubical.pathChain p γ).support, ∀ r,
      ∀ x ∈ Icc a b, (q r : ℂ) ≠ (x : ℂ) := by
    intro q hq
    obtain ⟨i, rfl⟩ := Cubical.exists_piece_of_mem_support_pathChain p γ hq
    exact hoff i
  have he := integral_sub_gauss_eq_cubicalCurveIntegral_of_boundedComplementFill_subset hs hn hΩ hf hI
    (Cubical.pathChain p γ) (Cubical.boundaryOne_pathChain_eq_zero p γ hp)
    (contDiffOn_cubicalPath_of_mem_support_pathChain p γ hγ) hchainoff hfill hw
  dsimp only at he ⊢
  rw [cubicalCurveIntegral_pathChain_eq_curveIntegral_concat] at he
  · exact he
  · intro i
    have hK := continuousOn_gaussRemainderKernel_of_compact_off_Icc hμ hs hn
      (isCompact_range ((γ i).map continuous_subtype_val).continuous) (by
        rintro z ⟨r, rfl⟩
        exact hoff i r)
    have hF := hf.continuousOn.mono (show range ((γ i).map continuous_subtype_val) ⊆ Ω from by
      rintro z ⟨r, rfl⟩
      exact ((γ i) r).property)
    exact ((hF.mul hK).smul continuousOn_const).curveIntegrable_of_contDiffOn (hγ i)
      (fun r => mem_range_self r)

end NLAlib
