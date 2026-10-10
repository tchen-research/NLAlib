import NLAlib.Matrix.FiniteIndexTransport
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Continuity of the actual best-rank Frobenius error

The optimal Frobenius distance is 1-Lipschitz in Frobenius distance by the
triangle inequality and the proved Frobenius minimizer. The rank-norm
comparison yields a `sqrt(card n)` Lipschitz bound in the actual operator norm.
This proves continuity of the squared optimum without asserting that an
arbitrary classical SVD selector is measurable.
Atlas: `eckart-young`, `rsvd-expected-error`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator NNReal
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The actual optimal squared Frobenius error is nonnegative.
Atlas `eckart-young` (optimal-value API). -/
theorem bestRankFrobSq_nonneg (A : Matrix m n ℝ) (k : ℕ) :
    0 ≤ bestRankFrobSq k A := by
  obtain ⟨B, hB⟩ := exists_isBestRankApprox A k
  rw [← hB.frobSq_sub_eq_bestRankFrobSq]
  exact frobSq_nonneg _

private theorem sqrt_bestRankFrobSq_eq {A B : Matrix m n ℝ} {k : ℕ}
    (h : IsBestRankApprox k A B) :
    Real.sqrt (bestRankFrobSq k A) = frobNorm (A - B) := by
  rw [← h.frobSq_sub_eq_bestRankFrobSq]
  rfl

private theorem sqrt_bestRankFrobSq_le_sub
    (A B : Matrix m n ℝ) (k : ℕ) (hB : B.rank ≤ k) :
    Real.sqrt (bestRankFrobSq k A) ≤ frobNorm (A - B) := by
  obtain ⟨C, hC⟩ := exists_isBestRankApprox A k
  rw [sqrt_bestRankFrobSq_eq hC, frobNorm, frobNorm]
  exact Real.sqrt_le_sqrt (hC.2 B hB)

private theorem sqrt_bestRankFrobSq_le_add (A B : Matrix m n ℝ) (k : ℕ) :
    Real.sqrt (bestRankFrobSq k A) ≤ Real.sqrt (bestRankFrobSq k B) + frobNorm (A - B) := by
  obtain ⟨C, hC⟩ := exists_isBestRankApprox B k
  have hbest := sqrt_bestRankFrobSq_le_sub A C k hC.1
  have hsplit : A - C = (A - B) + (B - C) := by abel
  have htri := frobNorm_add_le (A - B) (B - C)
  rw [← hsplit, ← sqrt_bestRankFrobSq_eq hC] at htri
  linarith

/-- The optimal rank-constrained Frobenius distance is 1-Lipschitz in
Frobenius distance, with no restrictions on rank or matrix dimensions.
Atlas `eckart-young` (optimal-value API). -/
theorem abs_sqrt_bestRankFrobSq_sub_le_frobNorm (A B : Matrix m n ℝ) (k : ℕ) :
    |Real.sqrt (bestRankFrobSq k A) - Real.sqrt (bestRankFrobSq k B)| ≤ frobNorm (A - B) := by
  have h1 := sqrt_bestRankFrobSq_le_add A B k
  have h2 := sqrt_bestRankFrobSq_le_add B A k
  have hnorm : frobNorm (B - A) = frobNorm (A - B) := by
    unfold frobNorm
    rw [frobSq_sub_comm]
  rw [hnorm] at h2
  rw [abs_le]
  constructor <;> linarith

/-- The optimal Frobenius distance is Lipschitz for the operator-norm matrix
metric. Its constant is `sqrt(card n)`; empty index types are included.
Atlas `eckart-young` (measurability foundation). -/
theorem lipschitz_sqrt_bestRankFrobSq [DecidableEq m] [DecidableEq n] (k : ℕ) :
    LipschitzWith ⟨Real.sqrt (Fintype.card n : ℝ), Real.sqrt_nonneg _⟩
      (fun A : Matrix m n ℝ => Real.sqrt (bestRankFrobSq k A)) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  have hcompare : frobNorm (A - B) ≤ Real.sqrt (Fintype.card n : ℝ) * specNorm (A - B) := by
    have hr : ((A - B).rank : ℝ) ≤ Fintype.card n := by exact_mod_cast (A - B).rank_le_card_width
    exact (frobNorm_le_sqrt_rank_mul_specNorm_fintype (A - B)).trans
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hr) (specNorm_nonneg _))
  calc
    dist (Real.sqrt (bestRankFrobSq k A)) (Real.sqrt (bestRankFrobSq k B)) =
        |Real.sqrt (bestRankFrobSq k A) - Real.sqrt (bestRankFrobSq k B)| := Real.dist_eq _ _
    _ ≤ frobNorm (A - B) := abs_sqrt_bestRankFrobSq_sub_le_frobNorm A B k
    _ ≤ Real.sqrt (Fintype.card n : ℝ) * specNorm (A - B) := hcompare
    _ = (⟨Real.sqrt (Fintype.card n : ℝ), Real.sqrt_nonneg _⟩ : ℝ≥0) * dist A B := by
      rw [dist_eq_norm]
      rfl

/-- The actual squared best-rank Frobenius error is continuous. This uses
only its value and does not require measurability of chosen singular vectors.
Atlas `eckart-young`, `rsvd-expected-error`. -/
theorem continuous_bestRankFrobSq [DecidableEq m] [DecidableEq n] (k : ℕ) :
    Continuous (fun A : Matrix m n ℝ => bestRankFrobSq k A) := by
  have hc := (lipschitz_sqrt_bestRankFrobSq (m := m) (n := n) k).continuous.pow 2
  have he : (fun A : Matrix m n ℝ => Real.sqrt (bestRankFrobSq k A)) ^ 2 =
      (fun A : Matrix m n ℝ => bestRankFrobSq k A) := by
    funext A
    exact Real.sq_sqrt (bestRankFrobSq_nonneg A k)
  rw [he] at hc
  exact hc

/-- The actual optimal squared Frobenius error is measurable in the entries.
Atlas `rsvd-expected-error` (no SVD-selector measurability assumption). -/
theorem measurable_bestRankFrobSq [DecidableEq m] [DecidableEq n] (k : ℕ) :
    Measurable (fun G : m → n → ℝ => bestRankFrobSq k (Matrix.of G)) := by
  have hOf : Continuous (fun G : m → n → ℝ => Matrix.of G) := continuous_id
  exact ((continuous_bestRankFrobSq k).comp hOf).measurable

end NLAlib
