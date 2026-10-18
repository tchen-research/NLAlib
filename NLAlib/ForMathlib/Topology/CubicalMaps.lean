import NLAlib.ForMathlib.Topology.CubicalChains

/-! # Continuous images and subtype lifts of normalized cubical chains

Continuous maps act on the actual singular cubes and commute with both
boundary maps and constant-edge normalization. A finite chain whose active
edges lie in a subset has an actual lift to that subset; no ambient
extension of a path or arbitrary base point is needed.
-/

noncomputable section
open scoped unitInterval
namespace Cubical

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Push forward a finite cubical one-chain along an actual continuous map. -/
def mapOne (f : C(X, Y)) : OneChain X →ₗ[ℤ] OneChain Y :=
  Finsupp.lmapDomain ℤ ℤ (fun γ => f.comp γ)

/-- Push forward a finite cubical two-chain along an actual continuous map. -/
def mapTwo (f : C(X, Y)) : TwoChain X →ₗ[ℤ] TwoChain Y :=
  Finsupp.lmapDomain ℤ ℤ (fun q => f.comp q)

/-- Push forward the finite endpoint chain. -/
def mapZero (f : C(X, Y)) : (X →₀ ℤ) →ₗ[ℤ] (Y →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ f

@[simp]
theorem mapOne_single (f : C(X, Y)) (γ : C(I, X)) (k : ℤ) :
    mapOne f (Finsupp.single γ k) = Finsupp.single (f.comp γ) k := by
  simp [mapOne]

@[simp]
theorem mapTwo_single (f : C(X, Y)) (q : C(I × I, X)) (k : ℤ) :
    mapTwo f (Finsupp.single q k) = Finsupp.single (f.comp q) k := by
  simp [mapTwo]

@[simp]
theorem mapZero_single (f : C(X, Y)) (x : X) (k : ℤ) :
    mapZero f (Finsupp.single x k) = Finsupp.single (f x) k := by
  simp [mapZero]

/-- Actual one-chain pushforwards respect composition of continuous maps. -/
theorem mapOne_mapOne (f : C(X, Y)) (g : C(Y, Z)) (Γ : OneChain X) :
    mapOne g (mapOne f Γ) = mapOne (g.comp f) Γ := by
  have h : (mapOne g).comp (mapOne f) = mapOne (g.comp f) := by
    apply Finsupp.lhom_ext
    intro γ k
    simp only [LinearMap.comp_apply, mapOne_single]
    rfl
  exact LinearMap.congr_fun h Γ

/-- Mapping a square maps each of its four faces. -/
theorem mapOne_squareBoundary (f : C(X, Y)) (q : C(I × I, X)) :
    mapOne f (squareBoundary q) = squareBoundary (f.comp q) := by
  have hL : f.comp (left q) = left (f.comp q) := by ext t; rfl
  have hR : f.comp (right q) = right (f.comp q) := by ext t; rfl
  have hB : f.comp (bottom q) = bottom (f.comp q) := by ext t; rfl
  have hT : f.comp (top q) = top (f.comp q) := by ext t; rfl
  simp only [squareBoundary, map_add, map_sub, mapOne_single, hL, hR, hB, hT]

/-- Continuous pushforward commutes with the endpoint boundary. -/
theorem boundaryOne_mapOne (f : C(X, Y)) (Γ : OneChain X) :
    boundaryOne (mapOne f Γ) = mapZero f (boundaryOne Γ) := by
  have h : boundaryOne.comp (mapOne f) = (mapZero f).comp boundaryOne := by
    apply Finsupp.lhom_ext
    intro γ k
    simp [boundaryOne]
  exact LinearMap.congr_fun h Γ

/-- Continuous pushforward commutes with the two-dimensional boundary. -/
theorem boundaryTwo_mapTwo (f : C(X, Y)) (S : TwoChain X) :
    boundaryTwo (mapTwo f S) = mapOne f (boundaryTwo S) := by
  have h : boundaryTwo.comp (mapTwo f) = (mapOne f).comp boundaryTwo := by
    apply Finsupp.lhom_ext
    intro q k
    simp [boundaryTwo, mapOne_squareBoundary]
  exact LinearMap.congr_fun h S

/-- Continuous pushforward commutes with degenerate constant edges. -/
theorem constantChain_mapZero (f : C(X, Y)) (D : X →₀ ℤ) :
    constantChain (mapZero f D) = mapOne f (constantChain D) := by
  have h : constantChain.comp (mapZero f) = (mapOne f).comp constantChain := by
    apply Finsupp.lhom_ext
    intro x k
    simp [constantChain, ContinuousMap.comp_const]
  exact LinearMap.congr_fun h D

/-- An actual normalized filling pushes forward continuously. -/
theorem IsNullHomologous.map {Γ : OneChain X} (hΓ : IsNullHomologous Γ) (f : C(X, Y)) :
    IsNullHomologous (mapOne f Γ) := by
  obtain ⟨S, D, rfl⟩ := hΓ
  refine ⟨mapTwo f S, mapZero f D, ?_⟩
  rw [boundaryTwo_mapTwo, constantChain_mapZero, ← map_add]

/-- An injective continuous map is injective on actual interval maps. -/
theorem comp_injective {A : Type*} [TopologicalSpace A]
    (f : C(X, Y)) (hf : Function.Injective f) :
    Function.Injective (fun γ : C(A, X) => f.comp γ) := by
  intro γ δ h
  ext t
  apply hf
  exact congrArg (fun p : C(A, Y) => p t) h

/-- An injective continuous map induces an injective one-chain map. -/
theorem mapOne_injective (f : C(X, Y)) (hf : Function.Injective f) :
    Function.Injective (mapOne f) :=
  Finsupp.mapDomain_injective (comp_injective f hf)

/-- An injective continuous map induces an injective endpoint-chain map. -/
theorem mapZero_injective (f : C(X, Y)) (hf : Function.Injective f) :
    Function.Injective (mapZero f) :=
  Finsupp.mapDomain_injective hf

/-- A finite chain whose actual active paths lie in a subset lifts to that
subset. This also covers an empty chain in an empty subset. -/
theorem exists_mapOne_subtype_val_eq (Γ : OneChain X) (S : Set X)
    (hΓ : ∀ γ ∈ Γ.support, ∀ t, γ t ∈ S) :
    ∃ Δ : OneChain S,
      mapOne (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X)) Δ = Γ := by
  let j : C(S, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hj : Function.Injective (fun γ : C(I, S) => j.comp γ) :=
    comp_injective j Subtype.val_injective
  have hs : (↑Γ.support : Set C(I, X)) ⊆ Set.range (fun γ : C(I, S) => j.comp γ) := by
    intro γ hγ
    refine ⟨⟨fun t => ⟨γ t, hΓ γ hγ t⟩, γ.continuous.subtype_mk _⟩, ?_⟩
    ext t
    rfl
  refine ⟨Finsupp.comapDomain (fun γ : C(I, S) => j.comp γ) Γ hj.injOn, ?_⟩
  exact Finsupp.mapDomain_comapDomain _ hj Γ hs

/-- A finite two-chain whose active continuous squares lie in a subset has
an actual lift to that subset, including an empty subset and empty chain. -/
theorem exists_mapTwo_subtype_val_eq (Γ : TwoChain X) (S : Set X)
    (hΓ : ∀ q ∈ Γ.support, ∀ t, q t ∈ S) :
    ∃ Δ : TwoChain S,
      mapTwo (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X)) Δ = Γ := by
  let j : C(S, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hj : Function.Injective (fun q : C(I × I, S) => j.comp q) :=
    comp_injective j Subtype.val_injective
  have hs : (↑Γ.support : Set C(I × I, X)) ⊆
      Set.range (fun q : C(I × I, S) => j.comp q) := by
    intro q hq
    refine ⟨⟨fun t => ⟨q t, hΓ q hq t⟩, q.continuous.subtype_mk _⟩, ?_⟩
    ext t
    rfl
  refine ⟨Finsupp.comapDomain (fun q : C(I × I, S) => j.comp q) Γ hj.injOn, ?_⟩
  exact Finsupp.mapDomain_comapDomain _ hj Γ hs

end Cubical
