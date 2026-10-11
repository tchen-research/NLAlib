import NLAlib.Matrix.SpectralFrameWeights
import NLAlib.Matrix.PrincipalAngleDefinitions

/-!
# The actual top-cluster trace deficit

Finite overlap weights and the signed boundary-gap budget give the matrix
trace deficit controlling population eigenspace perturbation. This is the
nontrivial Frobenius step in Yu–Wang–Samworth, Theorem 2.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] {A E : Matrix n n ℝ}

omit [DecidableEq n] in
/-- A trace pairing with a frame-projector difference is the corresponding
compression-trace difference. Standard cyclic trace identity. -/
theorem trace_mul_sub_frame_projector_eq_sub_compressions {k : Type*} [Fintype k]
    (A : Matrix n n ℝ) (P Q : Matrix n k ℝ) :
    (A*(P*Pᵀ-Q*Qᵀ)).trace=(Pᵀ*A*P).trace-(Qᵀ*A*Q).trace := by
  rw [Matrix.mul_sub, Matrix.trace_sub]
  congr 1 <;> rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]

/-- The positive top-cluster boundary gap times squared sine distance is
bounded by the actual compression trace deficit, for any competing frame.
Yu–Wang–Samworth, Theorem 2; no small perturbation hypothesis or principal-vector
normalization is used.
atlas: davis-kahan-sin-theta (partial) -/
theorem mul_frobSq_sinePrincipalAngles_le_trace_deficit (hA : A.IsHermitian)
    {k : ℕ} (hk0 : 0 < k) (hkN : k < Fintype.card n) {Q : Matrix n (Fin k) ℝ}
    (hQ : HasOrthonormalCols Q) :
    (hA.eigenvalues₀ ⟨k-1, by omega⟩-hA.eigenvalues₀ ⟨k, hkN⟩)*
      frobSq (sinePrincipalAngles (topEigenframe hA hkN.le) Q) ≤
      (A*(topEigenframe hA hkN.le*(topEigenframe hA hkN.le)ᵀ-Q*Qᵀ)).trace := by
  let U := sortedEigenframe hA
  let w : Fin (Fintype.card n) → ℝ := fun i => ∑ j, (Uᵀ*Q) i j^2
  have hu : HasOrthonormalCols U := hasOrthonormalCols_sortedEigenframe hA
  have huc : U*Uᵀ=1 := sortedEigenframe_mul_transpose_eq_one hA
  have hw0 : ∀ i, 0 ≤ w i := fun i => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hw1 : ∀ i, w i ≤ 1 := sum_sq_overlap_row_le_one hu hQ
  have hbudget : ∑ i, w i=(k : ℝ) := by
    simpa only [w, Fintype.card_fin] using sum_sum_sq_overlap_eq_card huc hQ
  have hgap := prefix_gap_mul_deficit_le_trace_deficit hA.eigenvalues₀ w
    hA.eigenvalues₀_antitone hw0 hw1 hk0 hkN hbudget
  have hs : frobSq (sinePrincipalAngles (topEigenframe hA hkN.le) Q) =
      (k : ℝ)-∑ i : Fin k, w (Fin.castLE hkN.le i) := by
    rw [frobSq_sinePrincipalAngles_eq_card_sub_overlap
      (hasOrthonormalCols_topEigenframe hA hkN.le) hQ, Fintype.card_fin,
      topEigenframe]
    change (k : ℝ)-frobSq ((U.submatrix id (Fin.castLE hkN.le))ᵀ*Q)=_
    rw [frobSq_prefix_transpose_mul_eq_sum_overlap_row_sq]
  have htrace : (A*(topEigenframe hA hkN.le*(topEigenframe hA hkN.le)ᵀ-Q*Qᵀ)).trace =
      (∑ i : Fin k, hA.eigenvalues₀ (Fin.castLE hkN.le i))-∑ i, hA.eigenvalues₀ i*w i := by
    rw [trace_mul_sub_frame_projector_eq_sub_compressions,
      trace_topEigenframe_compression_eq_prefix, eigenvaluePrefix,
      trace_compression_eq_sum_mul_overlap_row_sq U Q hA.eigenvalues₀
        (eq_sortedEigenframe_mul_diagonal_mul_transpose hA)]
  rw [hs, htrace]
  exact hgap

/-- Trace optimality for the perturbed matrix turns the population trace
deficit into an actual perturbation pairing. Yu–Wang–Samworth, Theorem 2.
The competing frame's exact top-trace equality allows arbitrary choices at
a repeated perturbed boundary eigenvalue.
atlas: davis-kahan-sin-theta (partial) -/
theorem mul_frobSq_sinePrincipalAngles_le_frobInner_perturbation
    (hA : A.IsHermitian) (hE : E.IsHermitian) {k : ℕ}
    (hk0 : 0 < k) (hkN : k < Fintype.card n) {Q : Matrix n (Fin k) ℝ}
    (hQ : HasOrthonormalCols Q)
    (htop : (Qᵀ*(A+E)*Q).trace=eigenvaluePrefix (hA.add hE) hkN.le) :
    (hA.eigenvalues₀ ⟨k-1, by omega⟩-hA.eigenvalues₀ ⟨k, hkN⟩)*
      frobSq (sinePrincipalAngles (topEigenframe hA hkN.le) Q) ≤
      frobInner (Q*Qᵀ-topEigenframe hA hkN.le*(topEigenframe hA hkN.le)ᵀ) E := by
  let P := topEigenframe hA hkN.le
  have hP : HasOrthonormalCols P := hasOrthonormalCols_topEigenframe hA hkN.le
  have hmax : (Pᵀ*(A+E)*P).trace ≤ (Qᵀ*(A+E)*Q).trace := by
    rw [htop]
    have hh := trace_compression_le_trace_topEigenframe (hA.add hE) hkN.le hP
    rw [trace_topEigenframe_compression_eq_prefix] at hh
    exact hh
  have hgap := mul_frobSq_sinePrincipalAngles_le_trace_deficit hA hk0 hkN hQ
  have heq : frobInner (Q*Qᵀ-P*Pᵀ) E=(E*(Q*Qᵀ-P*Pᵀ)).trace := by
    rw [frobInner_eq_trace, Matrix.transpose_sub, mul_transpose_symm, mul_transpose_symm,
      Matrix.trace_mul_comm]
  rw [heq, trace_mul_sub_frame_projector_eq_sub_compressions]
  rw [trace_mul_sub_frame_projector_eq_sub_compressions] at hgap
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add] at hmax
  change _ ≤ (Qᵀ*E*Q).trace-(Pᵀ*E*P).trace
  change _ ≤ (Pᵀ*A*P).trace-(Qᵀ*A*Q).trace at hgap
  linarith

end NLAlib
