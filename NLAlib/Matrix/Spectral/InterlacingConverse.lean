import NLAlib.Matrix.Spectral.InterlacingInduction
import NLAlib.Matrix.Spectral.InterlacingStrictConstruction
import NLAlib.Matrix.Spectral.InterlacingTrace
/-!
# Converse interlacing with every weak inequality and repeated root

The strict-original-spectrum residue construction extends by exact deletion
and restoration of forced repeated roots. Characteristic polynomials retain
all algebraic multiplicities; empty and singleton dimensions are included.
-/

noncomputable section
open Polynomial
open scoped Matrix
namespace NLAlib

/-- Every pair of weakly increasing real lists with positive rank-one
interlacing is realized by a real diagonal matrix plus `vvᵀ`. The target
characteristic polynomial records every multiplicity, including repeated
original and target roots and the empty list. Horn–Johnson 2013,
Theorem 4.3.26; derivations Section herm:converse.
atlas: interlacing-converse (partial) -/
theorem exists_diagonal_add_vecMulVec_charpoly {n : ℕ} (d b : Fin n → ℝ)
    (hd : Monotone d) (hb : Monotone b) (hlo : ∀ i, d i ≤ b i)
    (hhi : ∀ i j, i.val + 1 = j.val → b i ≤ d j) :
    ∃ v : Fin n → ℝ, (Matrix.diagonal d + Matrix.vecMulVec v v).charpoly =
      ∏ j, (X - C (b j)) := by
  apply rank_one_interlacing_converse_of_strict_cases
    (fun _ d b hd hb hlo hhi => exists_diagonal_add_vecMulVec_charpoly_of_strictMono d b hd hb hlo hhi)
    n d b hd hb hlo
  exact interlacing_upper_of_adjacent d b hd hhi

/-- Every weakly interlacing pair of real lists is realized by a real
symmetric border of the prescribed diagonal matrix. The exact target
characteristic polynomial retains repeated roots and all weak equalities;
the empty leading matrix gives the one-dimensional target. Horn–Johnson
2013, Theorem 4.3.21; derivations Section herm:converse.
atlas: interlacing-converse (partial) -/
theorem exists_bordered_diagonal_charpoly {n : ℕ}
    (d : Fin n → ℝ) (b : Fin (n + 1) → ℝ) (hd : Monotone d) (hb : Monotone b)
    (h : ∀ i, b i.castSucc ≤ d i ∧ d i ≤ b i.succ) :
    ∃ v : Fin n → ℝ, ∃ a : ℝ,
      (Matrix.fromBlocks (Matrix.diagonal d) (Matrix.replicateCol (Fin 1) v)
        (Matrix.replicateRow (Fin 1) v) (Matrix.of (fun _ _ : Fin 1 => a))).charpoly =
        ∏ j, (X - C (b j)) := by
  apply bordered_interlacing_converse_of_strict_cases ?_ n d b hd hb h
  intro k d b hd hb h
  obtain ⟨v, a, _, hchar⟩ := exists_bordered_diagonal_charpoly_of_strictMono d b hd hb h
  exact ⟨v, a, hchar⟩

/-- The positive rank-one converse realizes the entire weak target spectrum
with the exact squared Euclidean coupling norm equal to the target sum
minus the original sum. Horn–Johnson 2013, Theorem 4.3.26;
includes zero coupling, repeated roots and empty dimension.
atlas: interlacing-converse (partial) -/
theorem exists_diagonal_add_vecMulVec_charpoly_with_sum_sq {n : ℕ}
    (d b : Fin n → ℝ) (hd : Monotone d) (hb : Monotone b) (hlo : ∀ i, d i ≤ b i)
    (hhi : ∀ i j, i.val + 1 = j.val → b i ≤ d j) :
    ∃ v : Fin n → ℝ, (Matrix.diagonal d + Matrix.vecMulVec v v).charpoly =
      (∏ j, (X - C (b j))) ∧ (∑ i, (v i) ^ 2) = (∑ i, b i) - ∑ i, d i := by
  obtain ⟨v, hv⟩ := exists_diagonal_add_vecMulVec_charpoly d b hd hb hlo hhi
  exact ⟨v, hv, by simpa only [Matrix.trace_diagonal] using
    sum_sq_eq_sum_sub_trace_of_charpoly_add_vecMulVec (Matrix.diagonal d) v b hv⟩

/-- The bordered converse realizes the entire weak target spectrum with
the border scalar exactly the difference of the target and original sums.
Horn–Johnson 2013, Theorem 4.3.21; all repetitions and empty cases remain.
atlas: interlacing-converse (partial) -/
theorem exists_bordered_diagonal_charpoly_with_trace {n : ℕ}
    (d : Fin n → ℝ) (b : Fin (n + 1) → ℝ) (hd : Monotone d) (hb : Monotone b)
    (h : ∀ i, b i.castSucc ≤ d i ∧ d i ≤ b i.succ) :
    ∃ v : Fin n → ℝ, ∃ a : ℝ,
      (Matrix.fromBlocks (Matrix.diagonal d) (Matrix.replicateCol (Fin 1) v)
        (Matrix.replicateRow (Fin 1) v) (Matrix.of (fun _ _ : Fin 1 => a))).charpoly =
        (∏ j, (X - C (b j))) ∧ a = (∑ i, b i) - ∑ i, d i := by
  obtain ⟨v, a, hchar⟩ := exists_bordered_diagonal_charpoly d b hd hb h
  exact ⟨v, a, hchar, by simpa only [Matrix.trace_diagonal] using
    border_eq_sum_sub_trace_of_charpoly_eq_prod (Matrix.diagonal d) v a b hchar⟩

end NLAlib
