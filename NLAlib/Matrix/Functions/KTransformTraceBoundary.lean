import NLAlib.Matrix.Functions.KTransformRealBoundary
import NLAlib.Matrix.Functions.KTransformLowerRealInverse
import NLAlib.Matrix.Functions.KTransformStableInverse
import NLAlib.Matrix.Functions.KTransformPotentialFrechet
import NLAlib.ForMathlib.MeasureTheory.LogarithmicPotential

/-! # The actual real trace law and the moving K potential

The upper-plane trace characterization extends to genuine real spectral gaps
by continuity of the actual compact-support Cauchy integral. The Frechet
gradient then differentiates the potential along every genuinely solved path.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

omit [Nonempty n] in
/-- The actual compact trace Cauchy law extends by continuity to every
real gap at which a matrix extension is analytic. -/
theorem normalizedTrace_real_stieltjes_extension_eq
    (F G : ℂ → M) (α : ℝ) (μ : FiniteMeasure ℝ)
    (hcompact : IsCompact (μ : Measure ℝ).support)
    (hμ : ∀ z : ℂ, 0 < z.im → normalizedTrace (α • F z) =
      ∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂(μ : Measure ℝ))
    (u : ℝ) (hu : ∀ t ∈ (μ : Measure ℝ).support, u < t)
    (hGa : AnalyticAt ℂ G (u : ℂ))
    (hGN : ∀ z : ℂ, 0 < z.im → G z = α • F z) :
    normalizedTrace (G u) = ((∫ t : ℝ, (t - u)⁻¹ ∂(μ : Measure ℝ) : ℝ) : ℂ) := by
  let φ : ℝ → ℂ := fun y => (u : ℂ) + (y : ℂ) * Complex.I
  have hφ : Tendsto φ (𝓝[>] (0 : ℝ)) (𝓝 (u : ℂ)) := by
    have hc : Continuous φ := by fun_prop
    simpa only [φ, Complex.ofReal_zero, zero_mul, add_zero] using
      (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  let L : M →L[ℂ] ℂ := (normalizedTraceLinearMap (n := n) (𝕜 := ℂ)).toContinuousLinearMap
  have hleft : Tendsto (fun y : ℝ => normalizedTrace (G (φ y)))
      (𝓝[>] 0) (𝓝 (normalizedTrace (G u))) :=
    L.continuous.continuousAt.tendsto.comp (hGa.continuousAt.tendsto.comp hφ)
  have hca := analyticAt_integral_real_cauchyKernel_of_support
    (μ : Measure ℝ) hcompact (u : ℂ) (by
      intro t ht he
      exact (hu t ht).ne (Complex.ofReal_injective he).symm)
  have hright := hca.continuousAt.tendsto.comp hφ
  have he : (fun y : ℝ => normalizedTrace (G (φ y))) =ᶠ[𝓝[>] 0]
      (fun y : ℝ => ∫ t : ℝ, ((t : ℂ) - φ y)⁻¹ ∂(μ : Measure ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hz : 0 < (φ y).im := by simpa [φ] using (show 0 < y from hy)
    rw [hGN _ hz, hμ _ hz]
  have hlim := tendsto_nhds_unique hleft (hright.congr' (he.mono fun _ h => h.symm))
  rw [hlim]
  simp only [← Complex.ofReal_sub, ← Complex.ofReal_inv]
  exact integral_complex_ofReal

/-- Below the actual trace support, every genuine stable scalar solution
has the actual real Stieltjes trace. The native branch and true boundary
continuity establish this identity; it is not a supplied certificate.
Source: Montanari--Saeed (2026), equation (45).
atlas: block-wishart-log-potential (partial) -/
theorem normalizedTrace_stable_matrixKTransform_solution_eq_stieltjes
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0 < α) (F : ℂ → M)
    (hFa : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im})
    (hF : ∀ z : ℂ, 0 < z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z) = z • 1)
    (μ : FiniteMeasure ℝ) (hcompact : IsCompact (μ : Measure ℝ).support)
    (hμ : ∀ z : ℂ, 0 < z.im → normalizedTrace (α • F z) =
      ∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂(μ : Measure ℝ))
    (u : ℝ) (hu : ∀ t ∈ (μ : Measure ℝ).support, u < t)
    (S : M) (hS : S ∈ matrixKStableDomain ν α)
    (hK : matrixKTransform ν α S = (u : ℂ) • 1) :
    α * (normalizedTrace S).re = ∫ t : ℝ, (t - u)⁻¹ ∂(μ : Measure ℝ) := by
  obtain ⟨G, hGa, hGN, _hreal, _hGp, _hGdp⟩ :=
    exists_posDef_real_stieltjes_extension_matrixKTransform ν hν α hα F hFa hF μ hμ u hu
  have hGS := eq_real_stieltjes_extension_at_stable_matrixKTransform_solution
    ν hν α hα F hF G u hGa hGN S hS hK
  have h := normalizedTrace_real_stieltjes_extension_eq F G α μ hcompact hμ u hu hGa hGN
  rw [hGS] at h
  have hr := congrArg Complex.re h
  have hsm : normalizedTrace (α • S) = (α : ℂ) * normalizedTrace S := by
    rw [← normalizedTrace_smul]
    congr 1
  simpa only [hsm, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using hr

omit [Nonempty n] in
/-- Along any differentiable actual scalar solution path, the moving
potential has its exact envelope derivative. The actual Frechet gradient
makes the matrix-path contribution zero at the solved point.
Source: Montanari--Saeed (2026), equation (45).
atlas: block-wishart-log-potential (partial) -/
theorem hasDerivAt_matrixKPotential_solution_path
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : α ≠ 0) (S : ℝ → M) (B : M) (u : ℝ)
    (hpath : HasDerivAt S B u) (hS : (S u).PosDef)
    (hgap : ∀ T ∈ ν.support, ((S u)⁻¹ + T.val).PosDef)
    (hK : matrixKTransform ν α (S u) = (u : ℂ) • 1) :
    HasDerivAt (fun v : ℝ => matrixKPotential ν α v (S v))
      (-α * (S u).trace.re) u := by
  let L : M →L[ℝ] ℝ := Complex.reCLM.comp (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap
  have htr : HasDerivAt (fun v : ℝ => (S v).trace.re) B.trace.re u :=
    L.hasFDerivAt.comp_hasDerivAt u hpath
  have hzero : HasDerivAt (fun v : ℝ => matrixKPotential ν α u (S v)) 0 u := by
    have h := (hasFDerivAt_matrixKPotential ν hν α u hα (S u) hS hgap).comp_hasDerivAt u hpath
    change HasDerivAt (fun v : ℝ => matrixKPotential ν α u (S v))
      (α * ((matrixKTransform ν α (S u) - (u : ℂ) • 1) * B).trace.re) u at h
    simpa only [hK, sub_self, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re,
      mul_zero] using h
  have hc := (((hasDerivAt_id u).sub_const u).mul htr).const_mul α
  have hd := hzero.sub hc
  convert! hd using 1
  · ext v
    dsimp only [matrixKPotential, Pi.sub_apply, Pi.mul_apply, id_eq]
    ring
  · simp

/-- The potential of the actual stable inverse has precisely the derivative
of the characterized trace law's logarithmic potential throughout its true
lower spectral gap. Every inverse value and derivative is constructed from
the native stable domain; neither trace nor branch regularity is assumed.
Source: Montanari--Saeed (2026), equation (45).
atlas: block-wishart-log-potential (partial) -/
theorem hasDerivAt_matrixKStableInverse_potential_below_trace_support
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0 < α) (F : ℂ → M)
    (hFa : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im})
    (hF : ∀ z : ℂ, 0 < z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z) = z • 1)
    (μ : FiniteMeasure ℝ) (hmass : μ.mass = 1)
    (hcompact : IsCompact (μ : Measure ℝ).support)
    (hμ : ∀ z : ℂ, 0 < z.im → normalizedTrace (α • F z) =
      ∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂(μ : Measure ℝ))
    (u : ℝ) (hu : ∀ t ∈ (μ : Measure ℝ).support, u < t) :
    HasDerivAt (fun v : ℝ => matrixKPotential ν α v
      (matrixKStableInverse ν α ((v : ℂ) • 1)) / (Fintype.card n : ℝ))
      (-(∫ t : ℝ, (t - u)⁻¹ ∂(μ : Measure ℝ))) u := by
  have hscalar (r : ℝ) : (r : ℂ) • (1 : M) = r • (1 : M) :=
    IsScalarTower.algebraMap_smul ℂ r (1 : M)
  obtain ⟨S₀, hS₀, hK₀⟩ :=
    exists_stable_matrixKTransform_scalar_solution_below_trace_support
      ν hν α hα F hFa hF μ hmass hcompact hμ u hu
  have hU : (u : ℂ) • (1 : M) ∈ matrixKTransform ν α '' matrixKStableDomain ν α :=
    ⟨S₀, hS₀, hK₀⟩
  obtain ⟨hS, hK⟩ := matrixKStableInverse_mem_and_transform_eq ν α hU
  obtain ⟨B, _hBH, hd, _hDB⟩ := exists_hasDerivAt_matrixKStableInverse_affine
    ν hν α hα 0 1 Matrix.isHermitian_one u (by simpa only [zero_add, ← hscalar] using hU)
  have hpath : HasDerivAt (fun v : ℝ => matrixKStableInverse ν α ((v : ℂ) • 1)) B u := by
    simpa only [zero_add, ← hscalar] using hd
  have hpot := (hasDerivAt_matrixKPotential_solution_path ν hν α hα.ne'
    (fun v : ℝ => matrixKStableInverse ν α ((v : ℂ) • 1)) B u hpath hS.1 hS.2.1 hK).div_const
      (Fintype.card n : ℝ)
  have ht := normalizedTrace_stable_matrixKTransform_solution_eq_stieltjes
    ν hν α hα F hFa hF μ hcompact hμ u hu _ hS hK
  have hreal (A : M) : (normalizedTrace A).re = A.trace.re / (Fintype.card n : ℝ) := by
    have hc : (Fintype.card n : ℂ)⁻¹ = (((Fintype.card n : ℝ)⁻¹ : ℝ) : ℂ) := by simp
    rw [normalizedTrace, hc]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, div_eq_mul_inv, mul_comm]
  convert! hpot using 1
  rw [← ht, hreal]
  ring
end NLAlib
