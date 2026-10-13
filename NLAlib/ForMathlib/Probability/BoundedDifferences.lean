import Mathlib.Probability.Moments.SubGaussian

/-!
# Bounded coordinate oscillation

Finite coordinate replacement bounds imply a global diameter bound. A bounded scalar range
diameter gives Hoeffding's sharp MGF proxy `c²/4` without requiring an attained minimum
(`hasSubgaussianMGF_of_range_oscillation`, a convenience form of Mathlib's
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` (Hoeffding's lemma); upstreaming candidate).
These are general prerequisites for the operator averaging proof of McDiarmid.

Source: Boucheron–Lugosi–Massart 2013, Theorem 6.2.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

/-- Coordinate oscillations bound the diameter of a function on a finite product,
including heterogeneous coordinate types and the empty product.
Boucheron–Lugosi–Massart 2013, §6.1;
supports atlas `mcdiarmid`. -/
theorem _root_.abs_sub_le_sum_of_coordinate_oscillation
    {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (f : (∀ i, S i) → ℝ) (c : ι → ℝ)
    (h : ∀ i (x : ∀ j, S j) (y : S i), |f (Function.update x i y) - f x| ≤ c i)
    (x y : ∀ i, S i) : |f y - f x| ≤ ∑ i, c i := by
  let z (s : Finset ι) : ∀ i, S i := fun i => if i ∈ s then y i else x i
  have hs : ∀ s : Finset ι, |f (z s) - f x| ≤ ∑ i ∈ s, c i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [z]
    | @insert i s hi ih =>
      have hz : z (insert i s) = Function.update (z s) i (y i) := by
        funext j
        by_cases hij : j = i
        · subst j; simp [z]
        · simp [z, hij]
      rw [hz, Finset.sum_insert hi]
      exact (abs_sub_le _ _ _).trans (add_le_add (h i (z s) (y i)) ih)
  simpa [z] using hs Finset.univ

/-- A measurable scalar function of range diameter at most `c≥0` has centred
MGF proxy `c²/4`. The infimum of its range need not be attained.
Hoeffding's lemma (Boucheron–Lugosi–Massart 2013, Lemma 2.2); supports `mcdiarmid`. -/
theorem hasSubgaussianMGF_of_range_oscillation
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : AEMeasurable g μ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x y, |g x - g y| ≤ c) :
    HasSubgaussianMGF (fun x => g x - ∫ y, g y ∂μ) ⟨c ^ 2 / 4, by positivity⟩ μ := by
  let : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  let x₀ : Ω := Classical.choice (inferInstance : Nonempty Ω)
  have hbb : BddBelow (Set.range g) := by
    refine ⟨g x₀ - c, ?_⟩
    rintro _ ⟨x, rfl⟩
    have := (abs_le.mp (h x x₀)).1
    linarith
  let a := sInf (Set.range g)
  have hb : ∀ x, g x ∈ Set.Icc a (a + c) := by
    intro x
    refine ⟨csInf_le hbb ⟨x, rfl⟩, ?_⟩
    have hl : g x - c ≤ a := by
      refine le_csInf (Set.range_nonempty g) ?_
      rintro _ ⟨y, rfl⟩
      have := (abs_le.mp (h x y)).2
      linarith
    linarith
  have hsg := hasSubgaussianMGF_of_mem_Icc hg (Filter.Eventually.of_forall hb)
  have hproxy : ((‖a + c - a‖₊ / 2) ^ 2 : NNReal) = ⟨c ^ 2 / 4, by positivity⟩ := by
    ext
    change (‖a + c - a‖ / 2) ^ 2 = c ^ 2 / 4
    rw [add_sub_cancel_left, Real.norm_eq_abs, abs_of_nonneg hc]
    ring
  rw [hproxy] at hsg
  exact hsg

end ProbabilityTheory
