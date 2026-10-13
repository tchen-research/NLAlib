import NLAlib.Polynomial.BestApproximation.GapEvaluation
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# Full rank of the actual divided-derivative family

Every `n`-polynomial subfamily of the actual `n+1` gap directions is independent. Evaluating
at any `n` distinct points preserves this rank because all directions have degree below `n`.
Source: focused rederivations, `polyretry:peak-jacobian`.
-/

noncomputable section

open Polynomial Matrix Finset

namespace NLAlib

/-- Every actual gap-direction subfamily obtained by deleting one index is independent,
expressed as uniqueness of its finite real coefficients.
Source: the nonsingular deleted evaluation-Laplacian minor. -/
theorem eq_zero_of_sum_smul_gapDirection_eq_zero {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (k : Fin (n + 1)) (c : Fin n → ℝ)
    (hc : (∑ j, c j • interpolationGapDividedDerivative n t (k.succAbove j)) = 0) : c = 0 := by
  let d : Fin n → ℝ := fun j => (-1 : ℝ) ^ (k.succAbove j).val * c j
  let p : ℝ[X] := ∑ j, c j • interpolationGapDividedDerivative n t (k.succAbove j)
  have hdet := det_interpolationGapEvaluationLaplacian_minor_ne_zero hn ht k
  have hdker : ((interpolationGapEvaluationLaplacian n t).submatrix k.succAbove k.succAbove) *ᵥ d = 0 := by
    ext r
    let a := k.succAbove r
    have heval : p.eval (interpolationGapCriticalPoint n t a) = 0 := by rw [show p = 0 from hc, eval_zero]
    change (∑ j, interpolationGapEvaluationLaplacian n t a (k.succAbove j) * d j) = 0
    calc
      _ = (|Lagrange.nodalWeight univ (interpolationGapCriticalPoint n t) a| * (-1 : ℝ) ^ a.val) *
          p.eval (interpolationGapCriticalPoint n t a) := by
        dsimp [p]
        rw [eval_finsetSum, mul_sum]
        apply sum_congr rfl
        intro j hj
        simp only [interpolationGapEvaluationLaplacian, d, eval_smul, smul_eq_mul, pow_add]
        have hs : ((-1 : ℝ) ^ (k.succAbove j).val) ^ 2 = 1 := by
          rw [← pow_mul, Nat.mul_comm, pow_mul]
          norm_num
        calc
          _ = (|Lagrange.nodalWeight univ (interpolationGapCriticalPoint n t) a| * (-1 : ℝ) ^ a.val) *
            (((-1 : ℝ) ^ (k.succAbove j).val) ^ 2) *
            (c j * (interpolationGapDividedDerivative n t (k.succAbove j)).eval (interpolationGapCriticalPoint n t a)) := by ring
          _ = _ := by rw [hs, mul_one]
      _ = 0 := by rw [heval, mul_zero]
  have hd : d = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hdker
  ext j
  have h := congrFun hd j
  change (-1 : ℝ) ^ (k.succAbove j).val * c j = 0 at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (by norm_num))

private theorem degree_sum_smul_deleted_gapDirection_lt {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (k : Fin (n + 1)) (c : Fin n → ℝ) :
    (∑ j, c j • interpolationGapDividedDerivative n t (k.succAbove j)).degree < n := by
  apply (degree_sum_le _ _).trans_lt
  apply (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr
  intro j hj
  exact (degree_smul_le _ _).trans_lt (degree_interpolationGapDividedDerivative_lt hn ht _)

/-- Evaluating any deleted actual gap-direction family at `n` distinct points gives a
nonsingular square matrix. Source: finite polynomial interpolation and the Laplacian minor. -/
theorem det_eval_gapDirection_ne_zero {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (k : Fin (n + 1)) (v : Fin n → ℝ)
    (hv : Function.Injective v) :
    Matrix.det (fun r j : Fin n =>
      (interpolationGapDividedDerivative n t (k.succAbove j)).eval (v r)) ≠ 0 := by
  intro hdet
  obtain ⟨c, hc, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let p : ℝ[X] := ∑ j, c j • interpolationGapDividedDerivative n t (k.succAbove j)
  have hp : p = 0 := by
    apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero univ hv.injOn
      (by simpa only [card_univ, Fintype.card_fin] using degree_sum_smul_deleted_gapDirection_lt hn ht k c)
    intro r hr
    have h := congrFun hker r
    simpa only [p, eval_finsetSum, eval_smul, smul_eq_mul, mulVec, dotProduct, Pi.zero_apply, mul_comm] using h
  exact hc (eq_zero_of_sum_smul_gapDirection_eq_zero hn ht k c hp)

/-- Every maximal row minor of the actual divided-derivative evaluation Jacobian is nonzero.
Source: focused rederivations, `polyretry:peak-jacobian`.
atlas: lebesgue-constant-lower-bound (partial) -/
theorem det_gapDirection_eval_ne_zero {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (k : Fin (n + 1)) (v : Fin n → ℝ)
    (hv : Function.Injective v) :
    Matrix.det (fun i j : Fin n =>
      (interpolationGapDividedDerivative n t (k.succAbove i)).eval (v j)) ≠ 0 := by
  have h := det_eval_gapDirection_ne_zero hn ht k v hv
  let M : Matrix (Fin n) (Fin n) ℝ := fun r j =>
    (interpolationGapDividedDerivative n t (k.succAbove j)).eval (v r)
  have htrans : M.transpose.det ≠ 0 := by rw [Matrix.det_transpose]; exact h
  exact htrans

end NLAlib
