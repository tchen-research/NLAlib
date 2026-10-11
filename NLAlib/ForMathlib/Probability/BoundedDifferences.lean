import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Data.Finset.Update

/-!
# Bounded coordinate oscillation

Finite coordinate replacement bounds imply a global diameter bound, hence
integrability on product probability spaces. A bounded scalar range diameter
gives Hoeffding's sharp MGF proxy `c²/4` without requiring an attained minimum.
These are general prerequisites for the operator averaging proof of McDiarmid.

Source: `open_problems_operator_rederivations.tex`, `eq:bd` and
`eq:fiberhoeffding`; Boucheron–Lugosi–Massart 2013, Theorem 6.2.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace NLAlib

/-- Coordinate oscillations bound the diameter of a function on a finite product,
including heterogeneous coordinate types and the empty product.
Source: the coordinate replacement argument following manuscript `eq:bd`;
supports atlas `mcdiarmid`. -/
theorem abs_sub_le_sum_of_coordinate_oscillation
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

/-- Global coordinate bounds make a measurable function integrable on a finite
product probability space; integrability is derived, not an extra hypothesis.
Source: manuscript `eq:bd`, boundedness paragraph; supports atlas `mcdiarmid`. -/
theorem integrable_pi_of_coordinate_oscillation
    {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, MeasurableSpace (S i)] (μ : ∀ i, Measure (S i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : (∀ i, S i) → ℝ) (hf : Measurable f)
    (c : ι → ℝ)
    (h : ∀ i (x : ∀ j, S j) (y : S i), |f (Function.update x i y) - f x| ≤ c i) :
    Integrable f (Measure.pi μ) := by
  let : ∀ i, Nonempty (S i) := fun i => nonempty_of_isProbabilityMeasure (μ i)
  let x₀ : ∀ i, S i := fun i => Classical.choice (inferInstance : Nonempty (S i))
  refine Integrable.of_bound hf.aestronglyMeasurable (|f x₀| + ∑ i, c i)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  have hd := abs_sub_le_sum_of_coordinate_oscillation f c h x₀ x
  calc |f x| ≤ |f x - f x₀| + |f x₀| := by
          simpa only [sub_add_cancel] using abs_add_le (f x - f x₀) (f x₀)
    _ ≤ (∑ i, c i) + |f x₀| := add_le_add hd le_rfl
    _ = |f x₀| + ∑ i, c i := add_comm _ _

/-- A measurable scalar function of range diameter at most `c≥0` has centred
MGF proxy `c²/4`. The infimum of its range need not be attained.
Source: sharp fibre Hoeffding argument `eq:fiberhoeffding`; supports `mcdiarmid`. -/
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

end NLAlib
