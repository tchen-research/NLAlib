import NLAlib.ForMathlib.Analysis.Complex.PrimitiveCubicalTransport
import NLAlib.ForMathlib.Topology.CubicalChains

/-! # Cauchy cancellation on actual singular cubical boundaries

Holomorphy constructs intrinsic transport on every continuous edge. Finite
primitive-grid cancellation kills each singular square boundary and hence
every finite singular cubical boundary. On a finite chain of C1 edges this is
the actual native curve integral. This is the null-homology alternative for
general-contour Cauchy theorems, including multiply connected domains.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Finset MeasureTheory
open scoped unitInterval
namespace Complex

/-- A continuous singular edge in a planar domain, as a native ambient path. -/
def cubicalPath {Ω : Set ℂ} (γ : C(I, Ω)) : Path (γ 0 : ℂ) (γ 1 : ℂ) where
  toContinuousMap := ⟨fun t => (γ t : ℂ), continuous_subtype_val.comp γ.continuous⟩
  source' := rfl
  target' := rfl

/-- Native scalar curve integration, extended linearly to finite signed
continuous singular one-chains. Regularity is imposed by theorems using it. -/
def cubicalCurveIntegral {Ω : Set ℂ} (g : ℂ → ℂ) : Cubical.OneChain Ω →ₗ[ℤ] ℂ :=
  Finsupp.linearCombination ℤ (fun γ =>
    curveIntegral (fun z => g z • ContinuousLinearMap.id ℂ ℂ) (cubicalPath γ))

/-- The intrinsic continuous-edge integral of a holomorphic function, extended
linearly to finite signed singular one-chains. Its local primitive charts are
constructed from holomorphy on the actual open domain. -/
def cubicalPrimitiveIntegral {Ω : Set ℂ} (g : ℂ → ℂ) (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) : Cubical.OneChain Ω →ₗ[ℤ] ℂ :=
  Finsupp.linearCombination ℤ (fun γ => primitivePathIntegral g (cubicalPath γ)
    (nonempty_primitivePathSubdivision_of_differentiableOn (cubicalPath γ) hΩ hg
      (fun t => (γ t).property)))

/-- The integral of a holomorphic function around an actual continuous
singular square boundary is zero. No smoothness of that square or its faces,
convexity of the ambient domain, or Cauchy equality is supplied. -/
theorem cubicalPrimitiveIntegral_squareBoundary {Ω : Set ℂ}
    {g : ℂ → ℂ} (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) (q : C(I × I, Ω)) :
    cubicalPrimitiveIntegral g hΩ hg (Cubical.squareBoundary q) = 0 := by
  let ψ : ℝ × ℝ → ℂ := fun t =>
    (q (projIcc 0 1 zero_le_one t.1, projIcc 0 1 zero_le_one t.2) : ℂ)
  have hψ : Continuous ψ := (continuous_subtype_val.comp q.continuous).comp
    ((continuous_projIcc.comp continuous_fst).prodMk (continuous_projIcc.comp continuous_snd))
  let D := Classical.choice (nonempty_primitiveHomotopyGrid_of_differentiableOn hψ hΩ hg
    (fun _ _ => (q _).property))
  have hp (γ : C(I, Ω)) := nonempty_primitivePathSubdivision_of_differentiableOn
    (cubicalPath γ) hΩ hg (fun t => (γ t).property)
  simp only [Cubical.squareBoundary, map_add, map_sub, cubicalPrimitiveIntegral,
    Finsupp.linearCombination_single, one_smul]
  apply primitivePathIntegral_boundary_eq_zero_of_grid
    (cubicalPath (Cubical.left q)) (cubicalPath (Cubical.right q))
    (cubicalPath (Cubical.bottom q)) (cubicalPath (Cubical.top q))
    (hp _) (hp _) (hp _) (hp _) hψ D
  · intro t ht
    rw [(cubicalPath (Cubical.left q)).extend_apply ht]
    simp [cubicalPath, ψ, Cubical.left, projIcc_of_mem zero_le_one ht]
  · intro t ht
    rw [(cubicalPath (Cubical.right q)).extend_apply ht]
    simp [cubicalPath, ψ, Cubical.right, projIcc_of_mem zero_le_one ht]
  · intro t ht
    rw [(cubicalPath (Cubical.bottom q)).extend_apply ht]
    simp [cubicalPath, ψ, Cubical.bottom, projIcc_of_mem zero_le_one ht]
  · intro t ht
    rw [(cubicalPath (Cubical.top q)).extend_apply ht]
    simp [cubicalPath, ψ, Cubical.top, projIcc_of_mem zero_le_one ht]

/-- The intrinsic holomorphic integral kills every actual finite singular
cubical two-chain boundary, by linearity and proved square cancellation. -/
theorem cubicalPrimitiveIntegral_boundaryTwo {Ω : Set ℂ}
    {g : ℂ → ℂ} (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) (S : Cubical.TwoChain Ω) :
    cubicalPrimitiveIntegral g hΩ hg (Cubical.boundaryTwo S) = 0 := by
  rw [Cubical.boundaryTwo, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, map_sum, map_smul, cubicalPrimitiveIntegral_squareBoundary hΩ hg,
    smul_zero, Finset.sum_const_zero]

/-- The intrinsic holomorphic integral kills every degenerate constant edge,
so it descends to normalized cubical one-chains. -/
theorem cubicalPrimitiveIntegral_constantChain {Ω : Set ℂ}
    {g : ℂ → ℂ} (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) (D : Ω →₀ ℤ) :
    cubicalPrimitiveIntegral g hΩ hg (Cubical.constantChain D) = 0 := by
  have hz (x : Ω) : cubicalPrimitiveIntegral g hΩ hg
      (Finsupp.single (ContinuousMap.const I x) 1) = 0 := by
    rw [cubicalPrimitiveIntegral, Finsupp.linearCombination_single, one_smul]
    change primitivePathIntegral g (Path.refl (x : ℂ)) _ = 0
    exact primitivePathIntegral_refl _
  rw [Cubical.constantChain, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, map_sum, map_smul, hz, smul_zero, Finset.sum_const_zero]

/-- The intrinsic integral equals the actual native curve integral on a
finite chain whose nonzero edges are C1. -/
theorem cubicalPrimitiveIntegral_eq_cubicalCurveIntegral {Ω : Set ℂ}
    {g : ℂ → ℂ} (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) (Γ : Cubical.OneChain Ω)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I) :
    cubicalPrimitiveIntegral g hΩ hg Γ = cubicalCurveIntegral g Γ := by
  unfold cubicalPrimitiveIntegral cubicalCurveIntegral
  simp only [Finsupp.linearCombination_apply, Finsupp.sum]
  apply sum_congr rfl
  intro γ hγ
  rw [primitivePathIntegral_eq_curveIntegral _ _ (hΓ γ hγ)]

/-- A holomorphic function integrates to zero on every actual null-homologous
finite C1 cycle. Null homology is an explicit finite continuous cubical
two-chain boundary in the holomorphy domain, with no scalar Cauchy assumption.
The domain may be multiply connected.
atlas: gauss-remainder-contour-kernel (partial) -/
theorem cubicalCurveIntegral_eq_zero_of_isNullHomologous {Ω : Set ℂ}
    {g : ℂ → ℂ} (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) (Γ : Cubical.OneChain Ω)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    (hnull : Cubical.IsNullHomologous Γ) : cubicalCurveIntegral g Γ = 0 := by
  rw [← cubicalPrimitiveIntegral_eq_cubicalCurveIntegral hΩ hg Γ hΓ]
  obtain ⟨S, D, rfl⟩ := hnull
  rw [map_add, cubicalPrimitiveIntegral_boundaryTwo hΩ hg,
    cubicalPrimitiveIntegral_constantChain hΩ hg, add_zero]

end Complex
