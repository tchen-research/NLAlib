import NLAlib.Polynomial.BestApproximation.GapDirections
import NLAlib.ForMathlib.LinearAlgebra.Matrix.ColumnLaplacianKernel

/-!
# The actual gap-evaluation Laplacian

Alternating divided-derivative evaluations and positive barycentric row weights produce
an actual strict column Laplacian. Its positive cofactor kernel is a polynomial relation.
Source: focused rederivations, `polyretry:peak-laplacian` and `polyretry:positive-q-relation`.
-/

noncomputable section

open Polynomial Matrix Finset

namespace NLAlib

/-- The finite weighted evaluation matrix of the actual divided gap derivatives.
Source: focused rederivations, the matrix `A=diag(b)B`. -/
def interpolationGapEvaluationLaplacian (n : ℕ) (t : Fin n → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun r i =>
  |Lagrange.nodalWeight univ (interpolationGapCriticalPoint n t) r| *
    ((-1 : ℝ) ^ (r.val + i.val) *
      (interpolationGapDividedDerivative n t i).eval (interpolationGapCriticalPoint n t r))

/-- The actual weighted gap-evaluation matrix has strictly positive off-diagonals.
Source: the strict nodal Wronskian certificate. -/
theorem interpolationGapEvaluationLaplacian_offdiag_pos {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (r i : Fin (n + 1)) (hri : r ≠ i) :
    0 < interpolationGapEvaluationLaplacian n t r i := by
  have hτ := strictMono_interpolationGapCriticalPoint hn ht
  apply mul_pos
  · exact abs_pos.mpr (Lagrange.nodalWeight_ne_zero hτ.injective.injOn (mem_univ r))
  · simpa only [Nat.add_comm] using eval_interpolationGapDividedDerivative_offdiag_pos hn ht i r (Ne.symm hri)

/-- Each column of the actual gap-evaluation matrix sums to zero.
Source: the vanishing top coefficient of each degree-bounded divided derivative. -/
theorem sum_interpolationGapEvaluationLaplacian_col {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) :
    (∑ r, interpolationGapEvaluationLaplacian n t r i) = 0 := by
  have hτ := strictMono_interpolationGapCriticalPoint hn ht
  have heval := sum_eval_mul_nodalWeight_eq_zero hτ.injective (degree_interpolationGapDividedDerivative_lt hn ht i)
  have hterm : ∀ r, interpolationGapEvaluationLaplacian n t r i =
      (-1 : ℝ) ^ (n + i.val) *
        ((interpolationGapDividedDerivative n t i).eval (interpolationGapCriticalPoint n t r) *
          Lagrange.nodalWeight univ (interpolationGapCriticalPoint n t) r) := by
    intro r
    dsimp [interpolationGapEvaluationLaplacian]
    rw [show |Lagrange.nodalWeight univ (interpolationGapCriticalPoint n t) r| *
        ((-1 : ℝ) ^ (r.val + i.val) *
          (interpolationGapDividedDerivative n t i).eval (interpolationGapCriticalPoint n t r)) =
        ((-1 : ℝ) ^ (r.val + i.val) * |Lagrange.nodalWeight univ (interpolationGapCriticalPoint n t) r|) *
          (interpolationGapDividedDerivative n t i).eval (interpolationGapCriticalPoint n t r) by ring,
      neg_one_pow_mul_abs_nodalWeight hτ r i.val]
    ring
  simp_rw [hterm]
  rw [← mul_sum, heval, mul_zero]

/-- Every deleted principal minor of the actual gap-evaluation matrix is nonsingular.
Source: the strict-column-Laplacian finite certificate. -/
theorem det_interpolationGapEvaluationLaplacian_minor_ne_zero {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (k : Fin (n + 1)) :
    ((interpolationGapEvaluationLaplacian n t).submatrix k.succAbove k.succAbove).det ≠ 0 :=
  strictColumnLaplacian_det_minor_ne_zero _
    (interpolationGapEvaluationLaplacian_offdiag_pos hn ht) (sum_interpolationGapEvaluationLaplacian_col hn ht) k

private theorem degree_sum_smul_gapDirection_lt {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (c : Fin (n + 1) → ℝ) :
    (∑ i, c i • interpolationGapDividedDerivative n t i).degree < n := by
  apply (degree_sum_le _ _).trans_lt
  apply (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr
  intro i hi
  exact (degree_smul_le _ _).trans_lt (degree_interpolationGapDividedDerivative_lt hn ht i)

/-- The actual divided gap derivatives have a strictly positive alternating polynomial relation.
The positive coefficients are normalized principal cofactors of the actual evaluation matrix.
Source: focused rederivations, `polyretry:positive-q-relation`.
atlas: lebesgue-constant-lower-bound (partial) -/
theorem exists_pos_sum_smul_gapDirection_eq_zero {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) :
    ∃ π : Fin (n + 1) → ℝ, (∀ i, 0 < π i) ∧ (∑ i, π i) = 1 ∧
      (∑ i, ((-1 : ℝ) ^ i.val * π i) • interpolationGapDividedDerivative n t i) = 0 := by
  obtain ⟨π, hπ, hsum, hker⟩ := strictColumnLaplacian_exists_pos_kernel_sum_one
    (interpolationGapEvaluationLaplacian n t) (interpolationGapEvaluationLaplacian_offdiag_pos hn ht)
    (sum_interpolationGapEvaluationLaplacian_col hn ht)
  refine ⟨π, hπ, hsum, ?_⟩
  let p : ℝ[X] := ∑ i, ((-1 : ℝ) ^ i.val * π i) • interpolationGapDividedDerivative n t i
  have hp := degree_sum_smul_gapDirection_lt hn ht (fun i => (-1 : ℝ) ^ i.val * π i)
  have hτ := strictMono_interpolationGapCriticalPoint hn ht
  apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero univ hτ.injective.injOn
    (hp.trans_le (by simp only [card_univ, Fintype.card_fin]; exact_mod_cast Nat.le_succ n))
  intro r hr
  have hb : |Lagrange.nodalWeight univ (interpolationGapCriticalPoint n t) r| ≠ 0 :=
    abs_ne_zero.mpr (Lagrange.nodalWeight_ne_zero hτ.injective.injOn hr)
  have hs : (-1 : ℝ) ^ r.val ≠ 0 := pow_ne_zero _ (by norm_num)
  have hrow := congrFun hker r
  have heq : (∑ i, interpolationGapEvaluationLaplacian n t r i * π i) =
      (|Lagrange.nodalWeight univ (interpolationGapCriticalPoint n t) r| * (-1 : ℝ) ^ r.val) *
        p.eval (interpolationGapCriticalPoint n t r) := by
    dsimp [p]
    rw [eval_finsetSum, mul_sum]
    apply sum_congr rfl
    intro i hi
    simp only [interpolationGapEvaluationLaplacian, eval_smul, smul_eq_mul, pow_add]
    ring
  change (∑ i, interpolationGapEvaluationLaplacian n t r i * π i) = 0 at hrow
  rw [heq] at hrow
  exact (mul_eq_zero.mp hrow).resolve_left (mul_ne_zero hb hs)

end NLAlib
