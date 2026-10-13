import NLAlib.Matrix.Inequalities.MajorizationConvex
/-!
# Complete majorization def contract

The clauses below are the actual universally quantified public statements,
assembled so that a full atlas tag certifies the entire family. Individual
clauses remain available in the imported topic modules.
-/

noncomputable section
open scoped ENNReal
namespace NLAlib
universe u_1

/-- All clauses of the majorization-def result, with their original hypotheses,
constants, finite indices and endpoint conventions.
Components: `majorized_iff_exists_doublyStochastic`, `majorized_iff_mem_convexHull_permutations`, `majorized_iff_sum_convex_le`, `weaklyMajorized_iff_sum_monotone_convex_le`.
Source: mo11, Def 1.A.1, 1.A.2; Thm 2.B.2 (HLP); Prop 4.B.1–4.B.2; bhatia97, §II.1–II.3.
atlas: majorization-def -/
theorem majorization_toolkit_properties :
    (∀ {ι : Type u_1} [_inst : Fintype ι] [_inst_1 : DecidableEq ι] (x y : ι → ℝ),
  NLAlib.Majorized x y ↔ ∃ D ∈ doublyStochastic ℝ ι, D.mulVec y = x) ∧
    (∀ {ι : Type u_1} [_inst : Fintype ι] [DecidableEq ι] (x y : ι → ℝ),
  NLAlib.Majorized x y ↔ x ∈ (convexHull ℝ) (Set.range fun (σ : Equiv.Perm ι) => y ∘ ⇑σ)) ∧
    (∀ {ι : Type u_1} [_inst : Fintype ι] [DecidableEq ι] (x y : ι → ℝ),
  NLAlib.Majorized x y ↔ ∀ (φ : ℝ → ℝ), ConvexOn ℝ Set.univ φ → ∑ i : ι, φ (x i) ≤ ∑ i : ι, φ (y i)) ∧
    (∀ {ι : Type u_1} [_inst : Fintype ι] [DecidableEq ι] (x y : ι → ℝ),
  NLAlib.WeaklyMajorized x y ↔
    ∀ (φ : ℝ → ℝ), Monotone φ → ConvexOn ℝ Set.univ φ → ∑ i : ι, φ (x i) ≤ ∑ i : ι, φ (y i)) := by
  exact ⟨@NLAlib.majorized_iff_exists_doublyStochastic,
    @NLAlib.majorized_iff_mem_convexHull_permutations,
    @NLAlib.majorized_iff_sum_convex_le,
    @NLAlib.weaklyMajorized_iff_sum_monotone_convex_le⟩

end NLAlib
