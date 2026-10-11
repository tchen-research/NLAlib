/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.ForMathlib.Probability.FiniteLawBasics

/-!
# Independent finite product laws

Exact coordinate, product-observable and cylinder probabilities follow from
the literal product masses. Source: sparse-Fock pinned commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace NLAlib.SparseFock
namespace FiniteLaw
variable {α β ι κ : Type*}

section IndependentProduct

variable [Fintype ι] [DecidableEq ι] [Fintype α]

/-- Product law with independent coordinates.  The joint mass is definitionally
the product of the individual coordinate masses.

Source: ported from `SparseFockFormal.FiniteProbability`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def independentProduct (μ : ι → FiniteLaw α) : FiniteLaw (ι → α) where
  weight x := ∏ i, (μ i).weight (x i)
  weight_nonneg x := Finset.prod_nonneg fun i _hi => (μ i).weight_nonneg (x i)
  sum_weight := by
    rw [← Fintype.prod_sum]
    simp only [(μ _).sum_weight, Finset.prod_const_one]

/-- The mass of an independent finite product outcome is the product of its coordinate masses.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem independentProduct_weight (μ : ι → FiniteLaw α) (x : ι → α) :
    (independentProduct μ).weight x = ∏ i, (μ i).weight (x i) := rfl

/-- Exact factorization of the expectation of arbitrary separated coordinate
observables.  This is the principal independence theorem.

Source: ported from `SparseFockFormal.FiniteProbability`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem expect_independentProduct_factorizes
    (μ : ι → FiniteLaw α) (f : ι → α → ℝ) :
    (independentProduct μ).expect (fun x => ∏ i, f i (x i)) =
      ∏ i, (μ i).expect (f i) := by
  calc
    (independentProduct μ).expect (fun x => ∏ i, f i (x i)) =
        ∑ x : ι → α, ∏ i, ((μ i).weight (x i) * f i (x i)) := by
      rw [expect]
      apply Finset.sum_congr rfl
      intro x _hx
      simp only [independentProduct_weight, Finset.prod_mul_distrib]
    _ = ∏ i, ∑ a, ((μ i).weight a * f i a) := by
      exact (Fintype.prod_sum
        (fun i a => (μ i).weight a * f i a)).symm
    _ = ∏ i, (μ i).expect (f i) := by
      simp only [expect]

/-- Factorization remains exact when observables are attached only to a subset
of coordinates.

Source: ported from `SparseFockFormal.FiniteProbability`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem expect_independentProduct_factorizes_on
    (μ : ι → FiniteLaw α) (s : Finset ι) (f : ι → α → ℝ) :
    (independentProduct μ).expect (fun x => ∏ i ∈ s, f i (x i)) =
      ∏ i ∈ s, (μ i).expect (f i) := by
  let g : ι → α → ℝ := fun i a => if i ∈ s then f i a else 1
  have hgpoint (x : ι → α) :
      (∏ i, g i (x i)) = ∏ i ∈ s, f i (x i) := by
    simp [g]
  have hgexpect (i : ι) :
      (μ i).expect (g i) = if i ∈ s then (μ i).expect (f i) else 1 := by
    by_cases hi : i ∈ s
    · simp [g, hi]
    · simp [g, hi]
  calc
    (independentProduct μ).expect (fun x => ∏ i ∈ s, f i (x i)) =
        (independentProduct μ).expect (fun x => ∏ i, g i (x i)) := by
      apply (independentProduct μ).expect_congr
      intro x
      exact (hgpoint x).symm
    _ = ∏ i, (μ i).expect (g i) :=
      expect_independentProduct_factorizes μ g
    _ = ∏ i ∈ s, (μ i).expect (f i) := by
      simp_rw [hgexpect]
      simp

/-- Every coordinate of the product law has its prescribed expectation.

Source: ported from `SparseFockFormal.FiniteProbability`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem expect_independentProduct_apply
    (μ : ι → FiniteLaw α) (i : ι) (f : α → ℝ) :
    (independentProduct μ).expect (fun x => f (x i)) = (μ i).expect f := by
  have h := expect_independentProduct_factorizes_on μ {i} (fun _ => f)
  simpa using h

/-- Every coordinate event has its prescribed marginal probability.

Source: ported from `SparseFockFormal.FiniteProbability`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem prob_independentProduct_apply
    (μ : ι → FiniteLaw α) (i : ι) (s : Set α) :
    (independentProduct μ).prob {x | x i ∈ s} = (μ i).prob s := by
  classical
  calc
    (independentProduct μ).prob {x | x i ∈ s} =
        (independentProduct μ).expect (fun x => indicator s (x i)) := by
      rw [prob]
      apply (independentProduct μ).expect_congr
      intro x
      simp [indicator]
    _ = (μ i).expect (indicator s) :=
      expect_independentProduct_apply μ i (indicator s)
    _ = (μ i).prob s := rfl

/-- In particular, the one-coordinate mass of the product law is the original
coordinate mass.

Source: ported from `SparseFockFormal.FiniteProbability`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem prob_independentProduct_eq
    [DecidableEq α] (μ : ι → FiniteLaw α) (i : ι) (a : α) :
    (independentProduct μ).prob {x | x i = a} = (μ i).weight a := by
  calc
    (independentProduct μ).prob {x | x i = a} =
        (μ i).prob {a} := by
      simpa only [Set.mem_singleton_iff] using
        prob_independentProduct_apply μ i ({a} : Set α)
    _ = (μ i).weight a := prob_singleton (μ i) a

/-- The cylinder event determined by one event at each coordinate.

Source: ported from `SparseFockFormal.FiniteProbability`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def cylinder (s : ι → Set α) : Set (ι → α) :=
  {x | ∀ i, x i ∈ s i}

omit [DecidableEq ι] [Fintype α] in
/-- The indicator of a cylinder event is the product of its coordinate indicators.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem indicator_cylinder (s : ι → Set α) (x : ι → α) :
    indicator (cylinder s) x = ∏ i, indicator (s i) (x i) := by
  classical
  by_cases hall : ∀ i, x i ∈ s i
  · simp [indicator, cylinder, hall]
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    have hleft : x ∉ cylinder s := by
      intro hx
      exact hi (hx i)
    rw [indicator]
    simp only [hleft, ↓reduceIte]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [indicator, hi]

/-- Exact factorization of all finite coordinate-cylinder events.  This is the
event-level statement of mutual independence.

Source: ported from `SparseFockFormal.FiniteProbability`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem prob_independentProduct_cylinder
    (μ : ι → FiniteLaw α) (s : ι → Set α) :
    (independentProduct μ).prob (cylinder s) = ∏ i, (μ i).prob (s i) := by
  calc
    (independentProduct μ).prob (cylinder s) =
        (independentProduct μ).expect
          (fun x => ∏ i, indicator (s i) (x i)) := by
      rw [prob]
      apply (independentProduct μ).expect_congr
      intro x
      exact indicator_cylinder s x
    _ = ∏ i, (μ i).expect (indicator (s i)) :=
      expect_independentProduct_factorizes μ (fun i => indicator (s i))
    _ = ∏ i, (μ i).prob (s i) := by
      simp only [prob]

end IndependentProduct

end FiniteLaw
end NLAlib.SparseFock
