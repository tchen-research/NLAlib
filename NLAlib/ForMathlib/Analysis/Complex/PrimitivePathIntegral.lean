import NLAlib.ForMathlib.Analysis.Complex.PrimitiveRefinement

/-! # Intrinsic integrals of continuous paths with local primitives

Uniform local-primitive subdivisions give a well-defined integral along a
continuous path. A subdivision exists for every path inside an open
holomorphy domain, and its transport agrees with the native curve integral
when the path is C¹. No assumed scalar Cauchy formula is used.
-/

noncomputable section
open Set MeasureTheory
open scoped unitInterval
namespace Complex

/-- A finite uniform subdivision with actual local complex primitives along
a parameterized path. Open chart domains and containment refer to whole
closed cells, including their endpoints. -/
structure PrimitivePathSubdivision (g : ℂ → ℂ) (γ : ℝ → ℂ) where
  size : ℕ
  size_pos : 0 < size
  chart : ℕ → Set ℂ
  primitive : ℕ → ℂ → ℂ
  isOpen_chart : ∀ i < size, IsOpen (chart i)
  hasDerivAt_primitive : ∀ i < size, ∀ z ∈ chart i, HasDerivAt (primitive i) (g z) z
  continuousOn : ∀ i < size, ContinuousOn g (chart i)
  mapsTo_chart : ∀ i < size, ∀ t ∈ Icc ((i : ℝ) / size) ((i + 1 : ℝ) / size),
    γ t ∈ chart i

namespace PrimitivePathSubdivision

/-- The finite sum of actual local primitive increments on the subdivision. -/
def transport {g : ℂ → ℂ} {γ : ℝ → ℂ} (D : PrimitivePathSubdivision g γ) : ℂ :=
  primitiveSubdivisionTransport γ (fun i => (i : ℝ) / D.size) D.primitive D.size

/-- Every admissible uniform subdivision of the same continuous path gives
the same integral. The common refinement is derived, rather than assumed. -/
theorem transport_eq {g : ℂ → ℂ} {γ : ℝ → ℂ} (hγ : Continuous γ)
    (D E : PrimitivePathSubdivision g γ) : D.transport = E.transport :=
  primitiveSubdivisionTransport_uniform_eq hγ D.size_pos E.size_pos
    D.isOpen_chart E.isOpen_chart D.hasDerivAt_primitive E.hasDerivAt_primitive
    D.mapsTo_chart E.mapsTo_chart

/-- On a C¹ native path, this subdivision integral equals the existing native
curve integral. Speed integrability and local FTC are proved by the transport
agreement theorem. -/
theorem transport_eq_curveIntegral {a b : ℂ} {g : ℂ → ℂ} (γ : Path a b)
    (D : PrimitivePathSubdivision g γ.extend) (hγ : ContDiffOn ℝ 1 γ.extend I) :
    D.transport = curveIntegral (fun z => g z • ContinuousLinearMap.id ℂ ℂ) γ := by
  have hsize : 0 < (D.size : ℝ) := by exact_mod_cast D.size_pos
  apply primitiveSubdivisionTransport_eq_curveIntegral_of_hasDerivAt γ hγ
    (fun i _ => div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ i) hsize.le)
    (by simp) (by simp [D.size_pos.ne'])
    (fun i hi => ⟨div_nonneg (Nat.cast_nonneg i) hsize.le,
      (div_le_one hsize).mpr (by exact_mod_cast hi)⟩)
    D.hasDerivAt_primitive D.continuousOn
    (by simpa only [Nat.cast_add, Nat.cast_one] using D.mapsTo_chart)

end PrimitivePathSubdivision

/-- A finite primitive subdivision is automatically available on every
continuous path in an open holomorphy domain. -/
theorem nonempty_primitivePathSubdivision_of_differentiableOn
    {a b : ℂ} (γ : Path a b) {Ω : Set ℂ} {g : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) (hγΩ : ∀ t, γ t ∈ Ω) :
    Nonempty (PrimitivePathSubdivision g γ.extend) := by
  obtain ⟨n, hn, U, G, h⟩ := exists_primitive_subdivision_of_differentiableOn γ hΩ hg hγΩ
  exact ⟨⟨n, hn, U, G, fun i hi => (h i hi).1,
    fun i hi => (h i hi).2.1, fun i hi => (h i hi).2.2.1,
    fun i hi => (h i hi).2.2.2⟩⟩

/-- The intrinsic integral of a continuous path admitting local primitive
charts. Existence is derived from holomorphy by the preceding theorem; the
value is independent of every subdivision and chart choice. -/
def primitivePathIntegral {a b : ℂ} (g : ℂ → ℂ) (γ : Path a b)
    (h : Nonempty (PrimitivePathSubdivision g γ.extend)) : ℂ :=
  (Classical.choice h).transport

/-- Any actual local primitive subdivision computes the intrinsic continuous
path integral. -/
theorem primitivePathIntegral_eq_transport {a b : ℂ} {g : ℂ → ℂ} (γ : Path a b)
    (h : Nonempty (PrimitivePathSubdivision g γ.extend))
    (D : PrimitivePathSubdivision g γ.extend) : primitivePathIntegral g γ h = D.transport :=
  PrimitivePathSubdivision.transport_eq γ.continuous_extend (Classical.choice h) D

/-- The intrinsic continuous-path integral agrees with the native curve
integral on all C¹ paths. This is a proved extension, not a Cauchy certificate. -/
theorem primitivePathIntegral_eq_curveIntegral {a b : ℂ} {g : ℂ → ℂ} (γ : Path a b)
    (h : Nonempty (PrimitivePathSubdivision g γ.extend))
    (hγ : ContDiffOn ℝ 1 γ.extend I) :
    primitivePathIntegral g γ h = curveIntegral (fun z => g z • ContinuousLinearMap.id ℂ ℂ) γ :=
  PrimitivePathSubdivision.transport_eq_curveIntegral γ (Classical.choice h) hγ

/-- A constant path has zero intrinsic local-primitive transport. This is the
degenerate one-cube relation in normalized singular cubical homology. -/
theorem primitivePathIntegral_refl {a : ℂ} {g : ℂ → ℂ}
    (h : Nonempty (PrimitivePathSubdivision g (Path.refl a).extend)) :
    primitivePathIntegral g (Path.refl a) h = 0 := by
  rw [primitivePathIntegral_eq_transport (Path.refl a) h (Classical.choice h)]
  unfold PrimitivePathSubdivision.transport primitiveSubdivisionTransport
  simp [Path.refl_extend]

end Complex
