import NLAlib.ForMathlib.Topology.CubicalChains
import NLAlib.ForMathlib.Topology.CubicalChainRelations
import Mathlib.Topology.Homotopy.Path
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Null-homotopic loops bound normalized singular cubical chains

The actual contracting path homotopy is a continuous singular two-cube. Its
other faces are constant, so its boundary is the loop modulo degenerate
one-cubes. This connects the explicit chain definition to native topology.
-/

noncomputable section
open scoped unitInterval
namespace Cubical

/-- Any actual continuous nullhomotopy supplies a normalized singular cubical
filling of the loop. The normalization includes the necessary constant edge. -/
theorem isNullHomologous_single_of_pathHomotopy
    {X : Type*} [TopologicalSpace X] {x : X} (γ : Path x x)
    (H : γ.Homotopy (Path.refl x)) :
    IsNullHomologous (Finsupp.single γ.toContinuousMap 1) := by
  let q : C(I × I, X) := ⟨H, H.toHomotopy.continuous⟩
  have hleft : left q = γ.toContinuousMap := by
    ext t
    simp [left, q]
  have hright : right q = ContinuousMap.const I x := by
    ext t
    simp [right, q]
  have hbottom : bottom q = ContinuousMap.const I x := by
    ext t
    simp [bottom, q]
  have htop : top q = ContinuousMap.const I x := by
    ext t
    simp [top, q]
  refine ⟨Finsupp.single q (-1), Finsupp.single x 1, ?_⟩
  simp only [boundaryTwo, constantChain, Finsupp.linearCombination_single,
    neg_smul, one_smul, squareBoundary, hleft, hright, hbottom, htop]
  abel

/-- A concatenation and the sum of its two actual path pieces represent the
same normalized cubical homology class. Corners and constant path pieces are
allowed, since this is a purely continuous subdivision argument. -/
theorem isNullHomologous_single_trans_sub
    {X : Type*} [TopologicalSpace X] {a b c : X} (γ : Path a b) (δ : Path b c) :
    IsNullHomologous (Finsupp.single (γ.trans δ).toContinuousMap 1 -
      Finsupp.single γ.toContinuousMap 1 - Finsupp.single δ.toContinuousMap 1) := by
  let r : I := ⟨1 / 2, by constructor <;> norm_num⟩
  have hi : initialPart (γ.trans δ).toContinuousMap r = γ.toContinuousMap := by
    ext t
    change (γ.trans δ) (t * r) = γ t
    have ht : ((t * r : I) : ℝ) = (t : ℝ) / 2 := by
      simp only [Set.Icc.coe_mul, r]
      ring
    rw [← (γ.trans δ).extend_apply (t * r).property]
    rw [Path.extend_trans_of_le_half _ _ (by rw [ht]; linarith [t.property.2]), ht]
    rw [show 2 * ((t : ℝ) / 2) = (t : ℝ) by ring, γ.extend_apply t.property]
  have hf : finalPart (γ.trans δ).toContinuousMap r = δ.toContinuousMap := by
    ext t
    change (γ.trans δ) (unitInterval.symm (unitInterval.symm r * unitInterval.symm t)) = δ t
    let u := unitInterval.symm (unitInterval.symm r * unitInterval.symm t)
    have ht : (u : ℝ) = (1 + (t : ℝ)) / 2 := by
      simp only [u, unitInterval.coe_symm_eq, Set.Icc.coe_mul, r]
      ring
    change (γ.trans δ) u = δ t
    rw [← (γ.trans δ).extend_apply u.property]
    rw [Path.extend_trans_of_half_le _ _ (by rw [ht]; linarith [t.property.1]), ht]
    rw [show 2 * ((1 + (t : ℝ)) / 2) - 1 = (t : ℝ) by ring, δ.extend_apply t.property]
  have h := isNullHomologous_single_sub_initialPart_sub_finalPart (γ.trans δ).toContinuousMap r
  rwa [hi, hf] at h

end Cubical
