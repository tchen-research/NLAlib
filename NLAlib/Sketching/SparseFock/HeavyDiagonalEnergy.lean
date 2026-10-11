/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.HeavyPreservingGram

set_option autoImplicit false

/-!
# Heavy same-site diagonal energy

The preserving-band Gram identity and weighted diagonal-correction energy bounds.
Ported from `SparseFockFormal.HeavyBandsConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock.HeavyBandsConcrete

open ParsevalFrame LocalOperator FiniteOperator ExternalOperator GlobalBands BandInventory
  NamedBands FiniteHilbert TypedBlockCS ConcreteLadder
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

variable {d m n : ℕ}

/-- Exact concrete factorization of the named grade-preserving heavy band,
including the actual same-site correction.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hzero_gram_sub_diagonal (F : Frame n d) :
    Hzero m (frameRows F) =
      (AUpStack (m := m) F).transpose * AUpStack (m := m) F +
      (ADownStack (m := m) F).transpose * ADownStack (m := m) F -
      (DUp (m := m) F + DDown (m := m) F) := by
  rw [AUpStack_gram, ADownStack_gram]
  unfold Hzero
  abel

/-- One-site creation analysis evaluates the selected transitioned fiber's frame coefficient.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem AUpOne_mulVec (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (r : Fin m) (i : Fin n)
    (σ : Pattern m n) :
    Matrix.mulVec (AUpOne F r i) x σ =
      if σ (r, i) = .two then
        analyze F (fiber x (setSite σ (r, i) .one)) i else 0 := by
  simp only [Matrix.mulVec, dotProduct, AUpOne]
  exact one_rUp_analysis F x r i σ

/-- One-site annihilation analysis evaluates the selected transitioned fiber's frame coefficient.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem ADownOne_mulVec (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (r : Fin m) (i : Fin n)
    (σ : Pattern m n) :
    Matrix.mulVec (ADownOne F r i) x σ =
      if σ (r, i) = .one then
        analyze F (fiber x (setSite σ (r, i) .two)) i else 0 := by
  simp only [Matrix.mulVec, dotProduct, ADownOne]
  exact one_rDown_analysis F x r i σ

/-- Frame analysis restricted to a finite subset has energy bounded by its cardinality times input energy.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem subset_analysis_le_card_mul (F : Frame n d) (S : Finset (Fin n))
    (v : EVec d) :
    (∑ i ∈ S, (analyze F v i) ^ 2) ≤
      (S.card : ℝ) * ParsevalFrame.normSq v := by
  calc
    (∑ i ∈ S, (analyze F v i) ^ 2) ≤
        ∑ i ∈ S, ParsevalFrame.normSq v := by
      apply Finset.sum_le_sum
      intro i hi
      have h := subset_analysis F {i} v
      simpa using h
    _ = (S.card : ℝ) * ParsevalFrame.normSq v := by simp

/-- Exact same-site creation energy, bounded by the occupation number.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem DUp_energy_le_weighted (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ r, ∑ i, fockNormSq (Matrix.mulVec (AUpOne F r i) x)) ≤
      ∑ p, (p.grade : ℝ) * ParsevalFrame.normSq (fiber x p) := by
  classical
  calc
    (∑ r, ∑ i, fockNormSq (Matrix.mulVec (AUpOne F r i) x)) =
        ∑ r, ∑ i, ∑ σ,
          if σ (r, i) = .two then
            (analyze F (fiber x (setSite σ (r, i) .one)) i) ^ 2 else 0 := by
      simp only [fockNormSq, AUpOne_mulVec]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro σ _
      by_cases h : σ (r, i) = .two <;> simp [h]
    _ = ∑ r, ∑ σ, ∑ i,
          if σ (r, i) = .two then
            (analyze F (fiber x (setSite σ (r, i) .one)) i) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
    _ = ∑ σ, ∑ r, ∑ i,
          if σ (r, i) = .two then
            (analyze F (fiber x (setSite σ (r, i) .one)) i) ^ 2 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ σ, ∑ r, ∑ i ∈ σ.heavyInRow r,
          (analyze F (fiber x (setSite σ (r, i) .one)) i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro r _
      rw [Pattern.heavyInRow, Finset.sum_filter]
    _ = ∑ z : MarkedSite m n .two,
          (analyze F (fiber x
            (setSite z.pattern (z.row, z.col) .one)) z.col) ^ 2 := by
      simpa only [Pattern.heavyInRow] using
        sum_markedSite (m := m) (n := n) .two
          (fun p r i ↦ (analyze F (fiber x (setSite p (r, i) .one)) i) ^ 2)
    _ = ∑ z : MarkedSite m n .one,
          (analyze F (fiber x z.pattern) z.col) ^ 2 := by
      rw [sum_marked_reindex .two .one]
      apply Finset.sum_congr rfl
      intro z _
      simp only [markedTransition, Equiv.coe_fn_symm_mk]
      rw [setSite_restore z.pattern (z.row, z.col) z.state]
    _ = ∑ p, ∑ r, ∑ i ∈ p.lightInRow r,
          (analyze F (fiber x p) i) ^ 2 := by
      symm
      simpa only [Pattern.lightInRow] using
        sum_markedSite (m := m) (n := n) .one
          (fun p _ i ↦ (analyze F (fiber x p) i) ^ 2)
    _ ≤ ∑ p, ∑ r, ((p.lightInRow r).card : ℝ) *
          ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro r _
      exact subset_analysis_le_card_mul F (p.lightInRow r) (fiber x p)
    _ = ∑ p, (p.light.card : ℝ) * ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [← Finset.sum_mul, ← Nat.cast_sum,
        ← Pattern.card_light_eq_sum_card_lightInRow]
    _ ≤ ∑ p, (p.grade : ℝ) * ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_le_sum
      intro p _
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast p.card_light_le_grade)
        real_inner_self_nonneg

/-- Exact same-site demotion energy, with the same occupation bound.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem DDown_energy_le_weighted (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ r, ∑ i, fockNormSq (Matrix.mulVec (ADownOne F r i) x)) ≤
      ∑ p, (p.grade : ℝ) * ParsevalFrame.normSq (fiber x p) := by
  classical
  calc
    (∑ r, ∑ i, fockNormSq (Matrix.mulVec (ADownOne F r i) x)) =
        ∑ r, ∑ i, ∑ σ,
          if σ (r, i) = .one then
            (analyze F (fiber x (setSite σ (r, i) .two)) i) ^ 2 else 0 := by
      simp only [fockNormSq, ADownOne_mulVec]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro σ _
      by_cases h : σ (r, i) = .one <;> simp [h]
    _ = ∑ r, ∑ σ, ∑ i,
          if σ (r, i) = .one then
            (analyze F (fiber x (setSite σ (r, i) .two)) i) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
    _ = ∑ σ, ∑ r, ∑ i,
          if σ (r, i) = .one then
            (analyze F (fiber x (setSite σ (r, i) .two)) i) ^ 2 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ σ, ∑ r, ∑ i ∈ σ.lightInRow r,
          (analyze F (fiber x (setSite σ (r, i) .two)) i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro r _
      rw [Pattern.lightInRow, Finset.sum_filter]
    _ = ∑ z : MarkedSite m n .one,
          (analyze F (fiber x
            (setSite z.pattern (z.row, z.col) .two)) z.col) ^ 2 := by
      simpa only [Pattern.lightInRow] using
        sum_markedSite (m := m) (n := n) .one
          (fun p r i ↦ (analyze F (fiber x (setSite p (r, i) .two)) i) ^ 2)
    _ = ∑ z : MarkedSite m n .two,
          (analyze F (fiber x z.pattern) z.col) ^ 2 := by
      rw [sum_marked_reindex .one .two]
      apply Finset.sum_congr rfl
      intro z _
      simp only [markedTransition, Equiv.coe_fn_symm_mk]
      rw [setSite_restore z.pattern (z.row, z.col) z.state]
    _ = ∑ p, ∑ r, ∑ i ∈ p.heavyInRow r,
          (analyze F (fiber x p) i) ^ 2 := by
      symm
      simpa only [Pattern.heavyInRow] using
        sum_markedSite (m := m) (n := n) .two
          (fun p _ i ↦ (analyze F (fiber x p) i) ^ 2)
    _ ≤ ∑ p, ∑ r, ((p.heavyInRow r).card : ℝ) *
          ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro r _
      exact subset_analysis_le_card_mul F (p.heavyInRow r) (fiber x p)
    _ = ∑ p, (p.heavy.card : ℝ) * ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [← Finset.sum_mul, ← Nat.cast_sum,
        ← Pattern.card_heavy_eq_sum_card_heavyInRow]
    _ ≤ ∑ p, (p.grade : ℝ) * ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_le_sum
      intro p _
      have hcard : p.heavy.card ≤ p.grade := by
        have htwo := p.two_mul_card_heavy_le_grade
        omega
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        real_inner_self_nonneg

end

end NLAlib.SparseFock.HeavyBandsConcrete
