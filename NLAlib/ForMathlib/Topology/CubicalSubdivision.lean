import NLAlib.ForMathlib.Topology.CubicalChainRelations
import Mathlib.Algebra.BigOperators.Intervals

/-! # Actual finite subdivision of a continuous cubical edge

A fan of continuous squares connects the finite subedges to the original
edge. The square images lie in the original path image. Consequently this
subdivision changes a chain only by an actual normalized cubical boundary,
with no regularity or injectivity assumption on the parameterization.
-/

noncomputable section
open scoped unitInterval
namespace Cubical
variable {X : Type*} [TopologicalSpace X]

/-- A constant edge is degenerate in the normalized cubical chain complex. -/
theorem isNullHomologous_single_const (x : X) (k : ℤ) :
    IsNullHomologous (Finsupp.single (ContinuousMap.const I x) k) := by
  refine ⟨0, Finsupp.single x k, ?_⟩
  simp [constantChain]

/-- The actual subedge between two parameter values, with its linear
parameterization in the unit interval. The values may coincide or reverse. -/
def subedge (γ : C(I, X)) (r s : I) : C(I, X) :=
  γ.comp ⟨Set.Icc.convexComb r s, Set.Icc.continuous_convexComb r s⟩

@[simp]
theorem subedge_zero (γ : C(I, X)) (r s : I) : subedge γ r s 0 = γ r := by
  simp [subedge]

@[simp]
theorem subedge_one (γ : C(I, X)) (r s : I) : subedge γ r s 1 = γ s := by
  simp [subedge]

/-- A single continuous fan square gives the difference between two initial
subpaths and their intervening actual subedge. Its image stays on `γ`. -/
theorem isNullHomologous_initialPart_sub_initialPart_sub_subedge
    (γ : C(I, X)) (r s : I) :
    IsNullHomologous (Finsupp.single (initialPart γ s) 1 -
      Finsupp.single (initialPart γ r) 1 - Finsupp.single (subedge γ r s) 1) := by
  let q : C(I × I, X) := ⟨fun p => γ (p.2 * Set.Icc.convexComb r s p.1), by
    apply γ.continuous.comp
    apply continuous_induced_rng.mpr
    change Continuous (fun p : I × I => (p.2 : ℝ) *
      ((1 - (p.1 : ℝ)) * (r : ℝ) + (p.1 : ℝ) * (s : ℝ)))
    fun_prop⟩
  have hL : left q = initialPart γ r := by ext t; simp [left, q, initialPart]
  have hR : right q = initialPart γ s := by ext t; simp [right, q, initialPart]
  have hT : top q = subedge γ r s := by ext t; simp [top, q, subedge]
  have hB : bottom q = ContinuousMap.const I (γ 0) := by ext t; simp [bottom, q]
  refine ⟨Finsupp.single q 1, Finsupp.single (γ 0) (-1), ?_⟩
  simp only [boundaryTwo, constantChain, Finsupp.linearCombination_single,
    one_smul, neg_smul, squareBoundary, hL, hR, hT, hB]
  abel

/-- The finite chain of actual linearly parameterized subedges. -/
def subdivisionChain (γ : C(I, X)) (p : ℕ → I) (n : ℕ) : OneChain X :=
  ∑ i ∈ Finset.range n, Finsupp.single (subedge γ (p i) (p (i + 1))) 1

/-- The fan-square fillings telescope for any finite sequence of parameter
values, including repeated or unordered values. -/
theorem isNullHomologous_initialPart_sub_subdivisionChain
    (γ : C(I, X)) (p : ℕ → I) (n : ℕ) :
    IsNullHomologous (Finsupp.single (initialPart γ (p n)) 1 -
      Finsupp.single (initialPart γ (p 0)) 1 - subdivisionChain γ p n) := by
  induction n with
  | zero => simpa [subdivisionChain] using (isNullHomologous_zero (X := X))
  | succ n ih =>
    have h := (isNullHomologous_initialPart_sub_initialPart_sub_subedge γ (p n) (p (n + 1))).add ih
    convert h using 1
    simp only [subdivisionChain, Finset.sum_range_succ]
    abel

/-- A subdivision beginning at zero and ending at one represents the
original edge modulo actual normalized continuous square boundaries. -/
theorem isNullHomologous_single_sub_subdivisionChain
    (γ : C(I, X)) (p : ℕ → I) (n : ℕ) (hzero : p 0 = 0) (hone : p n = 1) :
    IsNullHomologous (Finsupp.single γ 1 - subdivisionChain γ p n) := by
  have h := isNullHomologous_initialPart_sub_subdivisionChain γ p n
  have h0 : initialPart γ (p 0) = ContinuousMap.const I (γ 0) := by
    ext t
    simp [initialPart, hzero]
  have h1 : initialPart γ (p n) = γ := by
    ext t
    simp [initialPart, hone]
  rw [h0, h1] at h
  have hc := h.add (isNullHomologous_single_const (γ 0) 1)
  convert hc using 1
  abel

/-- Uniform subdivision nodes, clamped after the final node so that the
sequence is a total function into the actual unit interval. -/
def uniformNode (n i : ℕ) : I :=
  Set.projIcc 0 1 zero_le_one ((i : ℝ) / n)

/-- Uniform nodes before the final index have their actual expected value. -/
theorem coe_uniformNode_of_le {n i : ℕ} (hn : 0 < n) (hi : i ≤ n) :
    (uniformNode n i : ℝ) = (i : ℝ) / n := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one
    ⟨div_nonneg (Nat.cast_nonneg i) hn'.le,
      (div_le_one hn').mpr (by exact_mod_cast hi)⟩)

/-- The actual uniformly subdivided path has the same normalized cubical
homology class. Its constructed filling uses only points on the original edge. -/
theorem isNullHomologous_single_sub_uniform_subdivisionChain
    (γ : C(I, X)) {n : ℕ} (hn : 0 < n) :
    IsNullHomologous (Finsupp.single γ 1 - subdivisionChain γ (uniformNode n) n) := by
  apply isNullHomologous_single_sub_subdivisionChain
  · apply Subtype.ext
    rw [coe_uniformNode_of_le hn (Nat.zero_le n)]
    simp
  · apply Subtype.ext
    rw [coe_uniformNode_of_le hn le_rfl]
    simp [hn.ne']

/-- Actual uniform subdivision extended linearly to finite chains. A
different positive subdivision count can be chosen for each continuous edge. -/
def uniformSubdivision (size : C(I, X) → ℕ) : OneChain X →ₗ[ℤ] OneChain X :=
  Finsupp.linearCombination ℤ (fun γ => subdivisionChain γ (uniformNode (size γ)) (size γ))

/-- Subdividing each actual edge preserves its cubical homology class, with
an explicit finite filling supplied by the fan-square construction. -/
theorem isNullHomologous_sub_uniformSubdivision (Γ : OneChain X)
    (size : C(I, X) → ℕ) (hsize : ∀ γ, 0 < size γ) :
    IsNullHomologous (Γ - uniformSubdivision size Γ) := by
  induction Γ using Finsupp.induction_linear with
  | zero => simpa using (isNullHomologous_zero (X := X))
  | add Γ Δ hΓ hΔ =>
    have he := hΓ.add hΔ
    convert he using 1
    simp only [map_add]
    abel
  | single γ k =>
    have he := (isNullHomologous_single_sub_uniform_subdivisionChain γ (hsize γ)).smul k
    simpa only [uniformSubdivision, Finsupp.linearCombination_single, smul_sub,
      Finsupp.smul_single_one] using he

/-- Actual subdivision preserves the native finite endpoint boundary. -/
theorem boundaryOne_uniformSubdivision (Γ : OneChain X)
    (size : C(I, X) → ℕ) (hsize : ∀ γ, 0 < size γ) :
    boundaryOne (uniformSubdivision size Γ) = boundaryOne Γ := by
  have he := (isNullHomologous_sub_uniformSubdivision Γ size hsize).boundaryOne_eq_zero
  rw [map_sub, sub_eq_zero] at he
  exact he.symm

end Cubical
