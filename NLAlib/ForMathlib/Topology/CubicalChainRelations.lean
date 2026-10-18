import NLAlib.ForMathlib.Topology.CubicalChains

/-! # Additivity and subdivision of normalized cubical null homology

Splitting an actual continuous edge into its initial and final parts changes
its one-chain only by a continuous square boundary and a constant edge. This
is a genuine topological subdivision relation, with no smoothness assumption.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped unitInterval
namespace Cubical
variable {X : Type*} [TopologicalSpace X]

/-- The zero chain has an explicit normalized cubical filling. -/
theorem isNullHomologous_zero : IsNullHomologous (0 : OneChain X) :=
  ⟨0, 0, by simp⟩

/-- Actual normalized cubical null-homology witnesses add. -/
theorem IsNullHomologous.add {Γ Δ : OneChain X}
    (hΓ : IsNullHomologous Γ) (hΔ : IsNullHomologous Δ) : IsNullHomologous (Γ + Δ) := by
  obtain ⟨S, D, rfl⟩ := hΓ
  obtain ⟨T, E, rfl⟩ := hΔ
  refine ⟨S + T, D + E, ?_⟩
  simp only [map_add]
  abel

/-- Negating a finite filling negates its actual normalized boundary. -/
theorem IsNullHomologous.neg {Γ : OneChain X} (hΓ : IsNullHomologous Γ) :
    IsNullHomologous (-Γ) := by
  obtain ⟨S, D, rfl⟩ := hΓ
  refine ⟨-S, -D, ?_⟩
  simp only [map_neg]
  abel

/-- Actual normalized cubical null-homology witnesses subtract. -/
theorem IsNullHomologous.sub {Γ Δ : OneChain X}
    (hΓ : IsNullHomologous Γ) (hΔ : IsNullHomologous Δ) : IsNullHomologous (Γ - Δ) := by
  simpa only [sub_eq_add_neg] using hΓ.add hΔ.neg

/-- Integer multiples of an actual normalized cubical filling give an
actual filling of the corresponding integer multiple. -/
theorem IsNullHomologous.smul {Γ : OneChain X} (hΓ : IsNullHomologous Γ) (k : ℤ) :
    IsNullHomologous (k • Γ) := by
  obtain ⟨S, D, rfl⟩ := hΓ
  refine ⟨k • S, k • D, ?_⟩
  simp only [map_smul, smul_add]

/-- Finite sums of actual normalized cubical boundaries have an actual
finite normalized cubical filling. -/
theorem isNullHomologous_finsetSum {ι : Type*} (s : Finset ι) (f : ι → OneChain X)
    (hf : ∀ i ∈ s, IsNullHomologous (f i)) : IsNullHomologous (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isNullHomologous_zero (X := X))
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- The initial portion of an actual continuous singular edge. -/
def initialPart (γ : C(I, X)) (r : I) : C(I, X) :=
  γ.comp ⟨fun t => t * r, by
    apply continuous_induced_rng.mpr
    change Continuous (fun t : I => (t : ℝ) * (r : ℝ))
    fun_prop⟩

/-- The final portion of an actual continuous singular edge, with parameter
`r + (1-r)t`, expressed intrinsically in the unit interval. -/
def finalPart (γ : C(I, X)) (r : I) : C(I, X) :=
  γ.comp ⟨fun t => unitInterval.symm (unitInterval.symm r * unitInterval.symm t), by
    apply continuous_induced_rng.mpr
    change Continuous (fun t : I => 1 - (1 - (r : ℝ)) * (1 - (t : ℝ)))
    fun_prop⟩

/-- Splitting a continuous edge at any parameter, including either endpoint,
preserves its normalized cubical homology class. An actual continuous square
and a degenerate initial-point edge supply the filling. -/
theorem isNullHomologous_single_sub_initialPart_sub_finalPart
    (γ : C(I, X)) (r : I) :
    IsNullHomologous (Finsupp.single γ 1 - Finsupp.single (initialPart γ r) 1 -
      Finsupp.single (finalPart γ r) 1) := by
  let q : C(I × I, X) := ⟨fun p => γ (p.2 *
    unitInterval.symm (unitInterval.symm r * unitInterval.symm p.1)), by
      apply γ.continuous.comp
      apply continuous_induced_rng.mpr
      change Continuous (fun p : I × I => (p.2 : ℝ) *
        (1 - (1 - (r : ℝ)) * (1 - (p.1 : ℝ))))
      fun_prop⟩
  have hleft : left q = initialPart γ r := by ext t; simp [left, q, initialPart]
  have hright : right q = γ := by ext t; simp [right, q]
  have hbottom : bottom q = ContinuousMap.const I (γ 0) := by ext t; simp [bottom, q]
  have htop : top q = finalPart γ r := by ext t; simp [top, q, finalPart]
  refine ⟨Finsupp.single q 1, Finsupp.single (γ 0) (-1), ?_⟩
  simp only [boundaryTwo, constantChain, Finsupp.linearCombination_single, one_smul,
    neg_smul, squareBoundary, hleft, hright, hbottom, htop]
  abel

end Cubical
