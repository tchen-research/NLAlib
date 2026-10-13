import NLAlib.Matrix.Perturbation.EigenvalueVariation
import NLAlib.ForMathlib.Analysis.OneSidedVariation
/-!
# Indexed Lidskii–Wielandt eigenvalue inequalities

Every selected eigenvalue sum obeys Lidskii's exact top-eigenvalue bound.
The proof uses compact eigenframe subsequences and a scalar minimum argument,
without differentiability, simplicity, or integration of spectral derivatives.
Source: Bhatia 1997, Theorem III.4.1. Atlas: `lidskii`.
-/

noncomputable section
open scoped Matrix
open Filter Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Indexed Lidskii–Wielandt: every selected decreasing eigenvalue sum of `A+B`
is at most the same selected sum of `A` plus the top `|J|` sum of `B`.
Bhatia 1997, Theorem III.4.1. Real symmetric matrices on arbitrary finite indices;
empty dimensions, repeated eigenvalues, and all negative eigenvalues are included.
atlas: lidskii -/
theorem sum_eigenvalues₀_add_le_sum_add_eigenvaluePrefix {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (J : Finset (Fin (Fintype.card n))) :
    (∑ j ∈ J, (hA.add hB).eigenvalues₀ j) ≤ (∑ j ∈ J, hA.eigenvalues₀ j) +
      eigenvaluePrefix hB J.card := by
  let F : ℝ → ℝ := fun t => ∑ j ∈ J, (isHermitian_add_smul hA hB t).eigenvalues₀ j
  have hF : Continuous F := continuous_finsetSum J fun j _ => continuous_eigenvalues₀_pencil hA hB j
  have hvar (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
      ∃ c ≤ eigenvaluePrefix hB J.card,
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto
        (fun ν => (F (t + (1 - t) / ((φ ν : ℝ) + 2)) - F t) /
          ((1 - t) / ((φ ν : ℝ) + 2))) atTop (𝓝 c) := by
    let h : ℕ → ℝ := fun ν => (1 - t) / ((ν : ℝ) + 2)
    have hhpos : ∀ ν, 0 < h ν := by
      intro ν
      exact div_pos (sub_pos.mpr ht.2) (by positivity)
    have hh : Tendsto h atTop (𝓝 0) := by
      have hden : Tendsto (fun ν : ℕ => (ν : ℝ) + 2) atTop atTop :=
        by simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
          (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 2)
      exact tendsto_const_nhds.div_atTop hden
    obtain ⟨c, hc, φ, hφ, hv⟩ := exists_subseq_eigenvalues₀_sum_difference_quotient_tendsto
      (isHermitian_add_smul hA hB t) hB J h hhpos hh
    refine ⟨c, hc, φ, hφ, ?_⟩
    apply hv.congr'
    apply Filter.Eventually.of_forall
    intro ν
    simp only [F, h]
    congr 2
    apply Finset.sum_congr rfl
    intro j _
    exact eigenvalues₀_pencil_add hA hB t ((1 - t) / ((φ ν : ℝ) + 2)) j
  have hinc := sub_le_of_continuous_of_subseq_difference_quotient_le F hF.continuousOn
    (eigenvaluePrefix hB J.card) hvar
  have hF0 : F 0 = ∑ j ∈ J, hA.eigenvalues₀ j := by simp only [F, zero_smul, add_zero]
  have hF1 : F 1 = ∑ j ∈ J, (hA.add hB).eigenvalues₀ j := by simp only [F, one_smul]
  rw [hF0, hF1] at hinc
  linarith

/-- Lidskii's ordinary majorization of the coordinatewise signed eigenvalue
increment. Bhatia 1997, Theorem III.4.1; no sorting of the increment is assumed.
atlas: lidskii -/
theorem majorized_eigenvalues₀_add_sub {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Majorized (fun i => (hA.add hB).eigenvalues₀ i - hA.eigenvalues₀ i) hB.eigenvalues₀ := by
  classical
  constructor
  · rw [weaklyMajorized_iff_sum_le]
    intro J
    have hJ := sum_eigenvalues₀_add_le_sum_add_eigenvaluePrefix hA hB J
    have hprefix : eigenvaluePrefix hB J.card ≤ sumLargest hB.eigenvalues₀ J.card := le_rfl
    rw [Finset.sum_sub_distrib]
    linarith
  · have htrace (C : Matrix n n ℝ) (hC : C.IsHermitian) :
        (∑ i, hC.eigenvalues₀ i) = C.trace := by
      have h := sum_eigenvalues_eq_sum_sorted hC id
      calc
        _ = ∑ i : n, hC.eigenvalues i := by simpa only [id_eq] using h.symm
        _ = C.trace := by simpa using hC.trace_eq_sum_eigenvalues.symm
    rw [Finset.sum_sub_distrib, htrace _ (hA.add hB), htrace _ hA, htrace _ hB,
      Matrix.trace_add]
    ring

end NLAlib
