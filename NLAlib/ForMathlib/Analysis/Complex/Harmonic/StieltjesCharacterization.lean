import NLAlib.ForMathlib.Analysis.Complex.Harmonic.StieltjesSupport

/-!
# The normalized scalar Stieltjes characterization

Existence, uniqueness, exact mass, and compact support are derived from
holomorphy, positivity, high-imaginary normalization, and the exterior
imaginary estimate. This is the scalar measure-theoretic input to the
matrix Dyson representation, Ajanki--Erdos--Kruger, Proposition 2.1.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

/-- A normalized positive-imaginary analytic function has exactly one
positive finite real Stieltjes measure, with its mass fixed by the
normalization. No compact-support or representation premise is needed.
This theorem supplies the scalar foundation component.
atlas: matrix-dyson-stieltjes-representation (partial) -/
theorem AnalyticOnNhd.existsUnique_finiteMeasure_stieltjes_eq {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.im})
    (hpos : ∀ z : ℂ, 0 < z.im → 0 ≤ (f z).im)
    (c : NNReal)
    (hlim : Tendsto (fun y : ℝ => (y : ℂ) * Complex.I * f ((y : ℂ) * Complex.I))
      atTop (𝓝 (-(c : ℝ) : ℂ))) :
    ∃! μ : FiniteMeasure ℝ, μ.mass = c ∧
      ∀ z : ℂ, 0 < z.im → f z = ∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂(μ : Measure ℝ) := by
  obtain ⟨μ, hm, hμ⟩ := hf.exists_finiteMeasure_stieltjes_eq hpos c hlim
  refine ⟨μ, ⟨hm, hμ⟩, ?_⟩
  intro ν hν
  apply FiniteMeasure.toMeasure_injective
  exact measure_eq_of_integral_real_cauchyKernel_eq (ν : Measure ℝ) (μ : Measure ℝ)
    (fun z hz => (hν.2 z hz).symm.trans (hμ z hz))

/-- The normalized positive Stieltjes measure is supported in the compact
spectral interval when its imaginary part is uniformly of order height
outside every strictly larger interval. The measure is constructed and
unique, rather than supplied as a hypothesis.
Source: Ajanki--Erdos--Kruger (2019), Proposition 2.1.
This theorem supplies the scalar foundation component.
atlas: matrix-dyson-stieltjes-representation (partial) -/
theorem AnalyticOnNhd.existsUnique_finiteMeasure_stieltjes_eq_of_im_le
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.im})
    (hpos : ∀ z : ℂ, 0 < z.im → 0 ≤ (f z).im)
    (c : NNReal)
    (hlim : Tendsto (fun y : ℝ => (y : ℂ) * Complex.I * f ((y : ℂ) * Complex.I))
      atTop (𝓝 (-(c : ℝ) : ℂ)))
    (κ : ℝ)
    (hb : ∀ a : ℝ, κ < a → ∃ C : ℝ, ∀ z : ℂ, 0 < z.im → a ≤ |z.re| →
      (f z).im ≤ C * z.im) :
    ∃! μ : FiniteMeasure ℝ, μ.mass = c ∧
      (∀ᵐ x : ℝ ∂(μ : Measure ℝ), x ∈ Icc (-κ) κ) ∧
      ∀ z : ℂ, 0 < z.im → f z = ∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂(μ : Measure ℝ) := by
  obtain ⟨μ, hμ, huniq⟩ := hf.existsUnique_finiteMeasure_stieltjes_eq hpos c hlim
  have hsupp : ∀ᵐ x : ℝ ∂(μ : Measure ℝ), x ∈ Icc (-κ) κ := by
    apply ae_mem_Icc_of_im_cauchyKernel_le_mul (μ : Measure ℝ) κ
    intro a ha
    obtain ⟨C, hC⟩ := hb a ha
    exact ⟨C, fun z hz hza => by rw [← hμ.2 z hz]; exact hC z hz hza⟩
  refine ⟨μ, ⟨hμ.1, hsupp, hμ.2⟩, ?_⟩
  intro ν hν
  exact huniq ν ⟨hν.1, hν.2.2⟩
