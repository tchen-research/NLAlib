import NLAlib.Krylov.QueryModel.Powers
import NLAlib.Krylov.Processes.ArnoldiProcess
import NLAlib.ForMathlib.Analysis.InnerProductSpace.GramSchmidtCongruence

/-!
# Finite-query realization of the canonical Arnoldi basis

The first `q` responses to successive power queries determine the `q + 1` input
vectors used by Gram--Schmidt. Orthonormalizing this finite prefix reproduces the
native Arnoldi matrix, including its zero columns after breakdown.

This is an exact-arithmetic operation-count statement: the query model charges
only access to the matrix, not the intervening Gram--Schmidt arithmetic.
Source: Saad (2003), Section 6.3; Trefethen--Bau (1997), Lecture 33.
atlas: matvec-query-model (partial)
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

private def sequenceFromTranscript (b : n → ℝ) {q : ℕ} (h : Fin q → n → ℝ) :
    ℕ → EuclideanSpace ℝ n
  | 0 => WithLp.toLp 2 b
  | i + 1 => if hi : i < q then WithLp.toLp 2 (h ⟨i, hi⟩) else 0

private theorem sequenceFromTranscript_eq (A : Matrix n n ℝ) (b : n → ℝ) (q i : ℕ)
    (hi : i ≤ q) :
    sequenceFromTranscript b ((powerQueryAlgorithm b q).transcript (A *ᵥ ·)) i =
      krylovSeq A b i := by
  cases i with
  | zero => simp [sequenceFromTranscript, krylovSeq]
  | succ i =>
    simp only [sequenceFromTranscript, show i < q by omega, dif_pos,
      transcript_powerQueryAlgorithm, krylovSeq]

/-- An oracle-independent `q`-query algorithm producing the first `q + 1` Arnoldi
vectors, including any zero columns after breakdown. -/
def arnoldiQueryAlgorithm (b : n → ℝ) (q : ℕ) :
    QueryAlgorithm (n → ℝ) (n → ℝ) q (Matrix n (Fin (q + 1)) ℝ) :=
  (powerQueryAlgorithm b q).withOutput fun h => Matrix.of fun i j =>
    (InnerProductSpace.gramSchmidtNormed ℝ (sequenceFromTranscript b h) (j : ℕ)).ofLp i

/-- The finite-query implementation returns the native Arnoldi matrix for every matrix
and vector, without a no-breakdown hypothesis.
atlas: matvec-query-model (partial) -/
theorem run_arnoldiQueryAlgorithm (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) :
    (arnoldiQueryAlgorithm b q).run (A *ᵥ ·) = arnoldiMatrix A b (q + 1) := by
  rw [arnoldiQueryAlgorithm, QueryAlgorithm.run_withOutput]
  ext i j
  have h := InnerProductSpace.gramSchmidtNormed_eq_of_eq_prefix (𝕜 := ℝ)
    (f := sequenceFromTranscript b ((powerQueryAlgorithm b q).transcript (A *ᵥ ·)))
    (g := krylovSeq A b) (j := (j : ℕ))
    (fun k hk => sequenceFromTranscript_eq A b q k (by omega))
  exact congrArg (fun v : EuclideanSpace ℝ n => v.ofLp i) h

end NLAlib
