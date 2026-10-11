import NLAlib.Matrix.EigenvaluePerturbation
import NLAlib.Matrix.MajorizationWeights

/-!
# Signed eigenvalue trace inequality and Hoffman–Wielandt

Squared overlaps between two orthonormal eigenbases form a doubly stochastic
matrix. Signed rearrangement gives Richter's trace inequality and the exact
Frobenius expansion gives Hoffman–Wielandt, including zero dimensions.
Source: Horn–Johnson 2013, Corollary 6.3.8; Bhatia 1997, Theorem VI.4.1.
Atlas: `eigenvalue-perturbation-symmetric`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace pairing with a symmetric matrix is its eigenvalue-weighted sum of
quadratic forms. The real spectral theorem, supporting Richter's inequality.
-/
theorem trace_mul_eq_sum_eigenvalues_mul_quadForm {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (B : Matrix n n ℝ) :
    (A * B).trace = ∑ i, hA.eigenvalues i * quadForm B ⇑(hA.eigenvectorBasis i) := by
  let U : Matrix n n ℝ := hA.eigenvectorUnitary
  have ht : (A * B).trace = (Matrix.diagonal hA.eigenvalues * (Uᵀ * B * U)).trace := by
    conv_lhs => rw [eq_eigenvectorUnitary_mul_diagonal_mul_transpose hA]
    change ((U * Matrix.diagonal hA.eigenvalues * Uᵀ) * B).trace = _
    rw [Matrix.mul_assoc, Matrix.trace_mul_cycle]
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm
      (Uᵀ * B * U) (Matrix.diagonal hA.eigenvalues)
  rw [ht, Matrix.trace]
  simp only [Matrix.diagonal_mul, Matrix.diag]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [Matrix.mul_apply, Matrix.transpose_apply, U,
    Matrix.IsHermitian.eigenvectorUnitary_apply, quadForm, Matrix.mulVec, dotProduct,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The squared Frobenius norm of a real symmetric matrix is the sum of the
squares of its signed eigenvalues. Horn–Johnson 2013, Section 4.1.
-/
theorem frobSq_eq_sum_sq_eigenvalues {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    frobSq A = ∑ i, hA.eigenvalues i ^ 2 := by
  conv_lhs => rw [eq_eigenvectorUnitary_mul_diagonal_mul_transpose hA,
    frobSq_mul_right_of_orthonormal (transpose_eigenvectorUnitary_mul_self hA),
    frobSq_mul_left_of_orthonormal (transpose_eigenvectorUnitary_mul_self hA)]
  simp [frobSq_eq_sum_sq, Matrix.diagonal_apply]

/-- Richter's signed trace inequality for arbitrary finite real symmetric
matrices. Both lists are decreasing, and negative eigenvalues retain their signs.
Horn–Johnson 2013, Section 4.3; Bhatia 1997, Corollary III.2.6.
atlas: eigenvalue-perturbation-symmetric (partial) -/
theorem trace_mul_le_sum_eigenvalues₀_mul {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * B).trace ≤ ∑ i, hA.eigenvalues₀ i * hB.eigenvalues₀ i := by
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  let P : Matrix n n ℝ :=
    (hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ * (hB.eigenvectorUnitary : Matrix n n ℝ)
  have hP : Pᵀ * P = 1 := by
    simp only [P, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (hA.eigenvectorUnitary : Matrix n n ℝ),
      eigenvectorUnitary_mul_transpose_self hA, Matrix.one_mul,
      transpose_eigenvectorUnitary_mul_self hB]
  have hPt : P * Pᵀ = 1 := mul_eq_one_comm.mp hP
  let D : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℝ :=
    fun i j => P (e i) (e j) ^ 2
  have hD : D ∈ doublyStochastic ℝ (Fin (Fintype.card n)) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun _ _ => sq_nonneg _, ?_, ?_⟩
    · intro i
      have h := congrArg (fun M => M (e i) (e i)) hPt
      change (∑ j, P (e i) (e j) ^ 2) = 1
      exact (e.sum_comp (fun j : n => P (e i) j ^ 2)).trans (by
        simpa only [Matrix.mul_apply, Matrix.transpose_apply,
          Matrix.one_apply_eq, ← sq] using h)
    · intro j
      have h := congrArg (fun M => M (e j) (e j)) hP
      change (∑ i, P (e i) (e j) ^ 2) = 1
      exact (e.sum_comp (fun i : n => P i (e j) ^ 2)).trans (by
        simpa only [Matrix.mul_apply, Matrix.transpose_apply,
          Matrix.one_apply_eq, ← sq] using h)
  have hexp : (A * B).trace =
      ∑ i, hA.eigenvalues₀ i * (D *ᵥ hB.eigenvalues₀) i := by
    rw [trace_mul_eq_sum_eigenvalues_mul_quadForm hA B]
    simp only [quadForm_eq_sum_eigenvalues hB]
    rw [← e.sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    rw [← e.sum_comp]
    simp only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply,
      Matrix.mulVec, dotProduct, D, P, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [show (∑ k, ⇑(hB.eigenvectorBasis (e j)) k * ⇑(hA.eigenvectorBasis (e i)) k) =
        (∑ k, ⇑(hA.eigenvectorBasis (e i)) k * ⇑(hB.eigenvectorBasis (e j)) k) by
          exact Finset.sum_congr rfl fun _ _ => mul_comm _ _]
      ring
  rw [hexp]
  exact sum_mul_mulVec_le_of_doublyStochastic _ _
    hA.eigenvalues₀_antitone hB.eigenvalues₀_antitone hD

/-- Hoffman–Wielandt for signed sorted eigenvalues of two real symmetric matrices.
Horn–Johnson 2013, Corollary 6.3.8; includes the empty eigenvalue list.
atlas: eigenvalue-perturbation-symmetric (partial) -/
theorem sum_sq_eigenvalues₀_sub_le_frobSq_sub {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∑ i, (hB.eigenvalues₀ i - hA.eigenvalues₀ i) ^ 2 ≤ frobSq (B - A) := by
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  have hFA : frobSq A = ∑ i, hA.eigenvalues₀ i ^ 2 := by
    rw [frobSq_eq_sum_sq_eigenvalues hA, ← e.sum_comp]
    simp only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply]
  have hFB : frobSq B = ∑ i, hB.eigenvalues₀ i ^ 2 := by
    rw [frobSq_eq_sum_sq_eigenvalues hB, ← e.sum_comp]
    simp only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply]
  have ht := trace_mul_le_sum_eigenvalues₀_mul hB hA
  have htrans : Bᵀ = B := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hB.eq
  have hinner : frobInner B A = (B * A).trace := by rw [frobInner_eq_trace, htrans]
  rw [← hinner] at ht
  rw [frobSq_sub, hFA, hFB]
  have hexp : (∑ i, (hB.eigenvalues₀ i - hA.eigenvalues₀ i) ^ 2) =
      (∑ i, hB.eigenvalues₀ i ^ 2) - 2 * (∑ i, hB.eigenvalues₀ i * hA.eigenvalues₀ i) +
        ∑ i, hA.eigenvalues₀ i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hexp]
  linarith

/-- The Hoffman–Wielandt perturbation form with perturbation `E`.
Horn–Johnson 2013, Corollary 6.3.8; no nonemptiness, positivity, or simple eigenvalues.
atlas: eigenvalue-perturbation-symmetric (partial) -/
theorem sum_sq_eigenvalues₀_add_sub_le_frobSq {A E : Matrix n n ℝ}
    (hA : A.IsHermitian) (hE : E.IsHermitian) :
    ∑ i, ((hA.add hE).eigenvalues₀ i - hA.eigenvalues₀ i) ^ 2 ≤ frobSq E := by
  simpa only [add_sub_cancel_left] using sum_sq_eigenvalues₀_sub_le_frobSq_sub hA (hA.add hE)

end NLAlib
