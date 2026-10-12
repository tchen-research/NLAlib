import NLAlib.Matrix.Spectral.InterlacingDeterminants
import Mathlib.Data.Real.Basic

/-!
# Exact trace parameters in converse interlacing

A full characteristic-root factorization fixes the trace, hence the scalar
border and the squared norm of a positive or negative rank-one coupling.
All finite shapes, including empty shapes, are allowed.
Source: Horn–Johnson (2013), converse interlacing, trace identities.
-/
noncomputable section
open Polynomial
open scoped Matrix
namespace NLAlib
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Any complete real characteristic-root list sums to the matrix trace.
Source: the next coefficient of the characteristic polynomial; this form
allows a separately indexed complete list and includes empty matrices. -/
theorem trace_eq_sum_of_charpoly_eq_prod (A : Matrix n n ℝ) (b : m → ℝ)
    (hb : A.charpoly = ∏ i, (X - C (b i))) : A.trace = ∑ i, b i := by
  rw [Matrix.trace_eq_neg_charpoly_nextCoeff, hb, ← Matrix.charpoly_diagonal,
    ← Matrix.trace_eq_neg_charpoly_nextCoeff, Matrix.trace_diagonal]

/-- A prescribed bordered spectrum fixes the last diagonal scalar as its
sum minus the trace of the leading matrix. Source: Horn–Johnson (2013),
converse interlacing; no symmetry assumption is needed for this trace identity.
atlas: interlacing-converse (partial) -/
theorem border_eq_sum_sub_trace_of_charpoly_eq_prod
    (A : Matrix n n ℝ) (v : n → ℝ) (a : ℝ) (b : m → ℝ)
    (hb : (Matrix.fromBlocks A (Matrix.replicateCol (Fin 1) v)
      (Matrix.replicateRow (Fin 1) v) (Matrix.of fun _ _ : Fin 1 => a)).charpoly =
        ∏ i, (X - C (b i))) : a = (∑ i, b i) - A.trace := by
  have ht := trace_eq_sum_of_charpoly_eq_prod _ b hb
  simp only [Matrix.trace, Matrix.diag, Matrix.fromBlocks, Fintype.sum_sum_type,
    Matrix.of_apply, Fin.sum_univ_one, Sum.elim_inl, Sum.elim_inr] at ht
  change a = (∑ i, b i) - ∑ i, A i i
  linarith

/-- A prescribed positive rank-one-update spectrum fixes the squared
Euclidean coupling norm as the target sum minus the original trace.
Source: Horn–Johnson (2013), converse interlacing; the sum of coordinate
squares is explicit and includes the empty vector.
atlas: interlacing-converse (partial) -/
theorem sum_sq_eq_sum_sub_trace_of_charpoly_add_vecMulVec
    (A : Matrix n n ℝ) (v : n → ℝ) (b : m → ℝ)
    (hb : (A + Matrix.vecMulVec v v).charpoly = ∏ i, (X - C (b i))) :
    (∑ i, (v i) ^ 2) = (∑ i, b i) - A.trace := by
  have ht := trace_eq_sum_of_charpoly_eq_prod _ b hb
  rw [Matrix.trace_add, Matrix.trace_vecMulVec] at ht
  simp only [dotProduct, ← pow_two] at ht
  linarith

/-- A prescribed negative rank-one-update spectrum fixes the squared
Euclidean coupling norm as the original trace minus the target sum.
Source: Horn–Johnson (2013), converse interlacing; includes empty dimension.
atlas: interlacing-converse (partial) -/
theorem sum_sq_eq_trace_sub_sum_of_charpoly_sub_vecMulVec
    (A : Matrix n n ℝ) (v : n → ℝ) (b : m → ℝ)
    (hb : (A - Matrix.vecMulVec v v).charpoly = ∏ i, (X - C (b i))) :
    (∑ i, (v i) ^ 2) = A.trace - ∑ i, b i := by
  have ht := trace_eq_sum_of_charpoly_eq_prod _ b hb
  rw [Matrix.trace_sub, Matrix.trace_vecMulVec] at ht
  simp only [dotProduct, ← pow_two] at ht
  linarith

end NLAlib
