import NLAlib.Probability.Gaussian.Moments.WickPairingEdges
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Positive covariance comparisons for Wick diagrams

Pairing weights are nonnegative for nonnegative covariance arrays and are
monotone in those arrays. A covariance split into two nonnegative terms
expands into a finite sum over independent orientation choices for its pairs.
-/

noncomputable section

open scoped BigOperators

namespace NLAlib

/-- A Wick pairing weight is nonnegative when all its covariance entries are. -/
theorem gaussianPairingWeight_nonneg {m : ℕ} (C : Fin m → Fin m → ℝ)
    (hC : ∀ i j, 0 ≤ C i j) (π : GaussianPairings m) : 0 ≤ gaussianPairingWeight C π := by
  induction m using Nat.twoStepInduction with
  | zero => exact zero_le_one
  | one => exact Empty.elim π
  | more m ih _ =>
    obtain ⟨j, π⟩ := π
    exact mul_nonneg (hC _ _) (ih _ (fun _ _ => hC _ _) π)

/-- Increasing a nonnegative covariance array increases every Wick pairing
weight, including the empty diagram. -/
theorem gaussianPairingWeight_le_gaussianPairingWeight {m : ℕ}
    (C D : Fin m → Fin m → ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (hCD : ∀ i j, C i j ≤ D i j) (π : GaussianPairings m) :
    gaussianPairingWeight C π ≤ gaussianPairingWeight D π := by
  induction m using Nat.twoStepInduction with
  | zero => exact le_rfl
  | one => exact Empty.elim π
  | more m ih _ =>
    obtain ⟨j, π⟩ := π
    apply mul_le_mul (hCD _ _) (ih _ _ (fun _ _ => hC _ _) (fun _ _ => hCD _ _) π)
      (gaussianPairingWeight_nonneg _ (fun _ _ => hC _ _) π)
      ((hC _ _).trans (hCD _ _))

/-- Splitting a covariance into two terms expands its pairing weight into
the sum over all binary choices on the actual pairs. This algebraic identity
keeps every orientation, including both contributions at diagonal entries. -/
theorem gaussianPairingWeight_add_eq_sum_orientations {m : ℕ}
    (C D : Fin m → Fin m → ℝ) (π : GaussianPairings m) :
    gaussianPairingWeight (fun i j => C i j + D i j) π =
      ∑ flip : Fin (gaussianPairingEdges π).length → Bool,
        ∏ e : Fin (gaussianPairingEdges π).length,
          if flip e then D ((gaussianPairingEdges π).get e).1 ((gaussianPairingEdges π).get e).2
          else C ((gaussianPairingEdges π).get e).1 ((gaussianPairingEdges π).get e).2 := by
  classical
  rw [gaussianPairingWeight_eq_prod_gaussianPairingEdges]
  have hprod :
      ((gaussianPairingEdges π).map (fun e => C e.1 e.2 + D e.1 e.2)).prod =
        ∏ e : Fin (gaussianPairingEdges π).length,
          (C ((gaussianPairingEdges π).get e).1 ((gaussianPairingEdges π).get e).2 +
            D ((gaussianPairingEdges π).get e).1 ((gaussianPairingEdges π).get e).2) := by
    rw [← List.prod_ofFn]
    congr 1
    rw [List.ofFn_comp' (f := fun e : Fin (gaussianPairingEdges π).length => (gaussianPairingEdges π).get e)
      (g := fun e => C e.1 e.2 + D e.1 e.2), List.ofFn_get]
  rw [hprod]
  have h := Finset.prod_univ_sum
    (fun _ : Fin (gaussianPairingEdges π).length => (Finset.univ : Finset Bool))
    (fun e flip => if flip then D ((gaussianPairingEdges π).get e).1 ((gaussianPairingEdges π).get e).2
      else C ((gaussianPairingEdges π).get e).1 ((gaussianPairingEdges π).get e).2)
  rw [Fintype.piFinset_univ] at h
  simpa [add_comm] using h

end NLAlib
