/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.HeavyDiagonalEnergy

set_option autoImplicit false

/-!
# Exact heavy diagonal occupation identities

Exact light/heavy occupation energies and the combined diagonal correction bound.
Ported from `SparseFockFormal.HeavyBandsConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock.HeavyBandsConcrete

open ParsevalFrame LocalOperator FiniteOperator ExternalOperator GlobalBands BandInventory
  NamedBands FiniteHilbert TypedBlockCS ConcreteLadder
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

variable {d m n : ℕ}

/-- The same-site creation correction has exactly the summed light-site frame-coefficient energy.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem DUp_energy_eq_light (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ r, ∑ i, fockNormSq (Matrix.mulVec (AUpOne F r i) x)) =
      ∑ p, ∑ r, ∑ i ∈ p.lightInRow r,
        (analyze F (fiber x p) i) ^ 2 := by
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
    _ = _ := by
      symm
      simpa only [Pattern.lightInRow] using
        sum_markedSite (m := m) (n := n) .one
          (fun p _ i ↦ (analyze F (fiber x p) i) ^ 2)

/-- The same-site annihilation correction has exactly the summed heavy-site frame-coefficient energy.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem DDown_energy_eq_heavy (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ r, ∑ i, fockNormSq (Matrix.mulVec (ADownOne F r i) x)) =
      ∑ p, ∑ r, ∑ i ∈ p.heavyInRow r,
        (analyze F (fiber x p) i) ^ 2 := by
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
    _ = _ := by
      symm
      simpa only [Pattern.heavyInRow] using
        sum_markedSite (m := m) (n := n) .two
          (fun p _ i ↦ (analyze F (fiber x p) i) ^ 2)

/-- The combined diagonal correction energy is bounded by total occupation-weighted fiber energy.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Dcombined_energy_le_weighted (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ r, ∑ i, fockNormSq (Matrix.mulVec (AUpOne F r i) x)) +
      (∑ r, ∑ i, fockNormSq (Matrix.mulVec (ADownOne F r i) x)) ≤
      ∑ p, (p.grade : ℝ) * ParsevalFrame.normSq (fiber x p) := by
  rw [DUp_energy_eq_light, DDown_energy_eq_heavy, ← Finset.sum_add_distrib]
  calc
    (∑ p, ((∑ r, ∑ i ∈ p.lightInRow r,
          (analyze F (fiber x p) i) ^ 2) +
        (∑ r, ∑ i ∈ p.heavyInRow r,
          (analyze F (fiber x p) i) ^ 2))) ≤
      ∑ p, (((p.light.card + p.heavy.card : ℕ) : ℝ) *
        ParsevalFrame.normSq (fiber x p)) := by
      apply Finset.sum_le_sum
      intro p _
      calc
        _ ≤ (∑ r, ((p.lightInRow r).card : ℝ) *
              ParsevalFrame.normSq (fiber x p)) +
            ∑ r, ((p.heavyInRow r).card : ℝ) *
              ParsevalFrame.normSq (fiber x p) := by
          exact add_le_add
            (Finset.sum_le_sum fun r _ ↦
              subset_analysis_le_card_mul F (p.lightInRow r) (fiber x p))
            (Finset.sum_le_sum fun r _ ↦
              subset_analysis_le_card_mul F (p.heavyInRow r) (fiber x p))
        _ = ((p.light.card + p.heavy.card : ℕ) : ℝ) *
            ParsevalFrame.normSq (fiber x p) := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum,
            ← Nat.cast_sum, ← Pattern.card_light_eq_sum_card_lightInRow,
            ← Pattern.card_heavy_eq_sum_card_heavyInRow]
          push_cast
          ring
    _ ≤ ∑ p, (p.grade : ℝ) * ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_le_sum
      intro p _
      have hc : p.light.card + p.heavy.card ≤ p.grade := by
        rw [Pattern.grade_eq_card_light_add_two_mul_card_heavy]
        omega
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc)
        real_inner_self_nonneg

end

end NLAlib.SparseFock.HeavyBandsConcrete
