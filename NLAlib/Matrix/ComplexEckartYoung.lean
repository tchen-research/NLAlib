import NLAlib.Matrix.ComplexVolumeProjection
import NLAlib.Matrix.ComplexVolumeSpectrum
import NLAlib.Matrix.ComplexVolumeProjectorTrace
import NLAlib.Matrix.EckartYoung

/-!
# Genuine complex Frobenius Eckart–Young tail

The actual complex Gram eigensystem and Hilbert row-space projector prove
the lower bound for arbitrary complex rank-bounded competitors. Truncating
that eigensystem supplies a genuine attaining matrix. Source: Horn–Johnson
Theorem 7.4.9; `sa:volume-theorem`; supports `volume-sampling`.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped Classical Matrix Matrix.Norms.Frobenius ComplexOrder
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- The captured Frobenius mass in a complex orthogonal row projector is
the eigenvalue-weighted diagonal budget in actual Gram eigenvectors.
Source: the complex Frobenius Eckart–Young proof, `sa:volume-theorem`. -/
theorem frobenius_norm_sq_mul_projector_eq_sum_gram_eigenvalues
    (A : Matrix m n ℂ) (P : Matrix n n ℂ)
    (hP : P.IsHermitian) (hPP : IsIdempotentElem P) :
    ‖A * P‖ ^ 2 =
      ∑ i : Fin (Fintype.card n), complexGramEigenvalues A i *
        ((((Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary : Matrix n n ℂ)ᴴ *
          P * (Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary)
          (Fintype.equivOfCardEq (Fintype.card_fin _) i)
          (Fintype.equivOfCardEq (Fintype.card_fin _) i)).re := by
  let hG := Matrix.isHermitian_conjTranspose_mul_self A
  let V : Matrix n n ℂ := hG.eigenvectorUnitary
  let R := Vᴴ * P * V
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  have hGram : (A * P)ᴴ * (A * P) = P * (Aᴴ * A) * P := by
    simp only [Matrix.conjTranspose_mul, hP.eq, Matrix.mul_assoc]
  have hspectral : Aᴴ * A = V * Matrix.diagonal (fun j => (hG.eigenvalues j : ℂ)) * Vᴴ := by
    simpa only [V, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using hG.spectral_theorem
  have hnative : ‖A * P‖ ^ 2 = ∑ j : n, hG.eigenvalues j * (R j j).re := by
    rw [frobenius_norm_sq_eq_re_trace_conjTranspose_mul, hGram,
      Matrix.trace_mul_cycle, show P * P = P from hPP,
      Matrix.trace_mul_comm P (Aᴴ * A)]
    conv_lhs => rw [hspectral]
    have ht : (V * Matrix.diagonal (fun j => (hG.eigenvalues j : ℂ)) * Vᴴ * P).trace =
        (Matrix.diagonal (fun j => (hG.eigenvalues j : ℂ)) * R).trace := by
      calc
        _ = (V * (Matrix.diagonal (fun j => (hG.eigenvalues j : ℂ)) * (Vᴴ * P))).trace := by
          congr 1
          simp only [Matrix.mul_assoc]
        _ = ((Matrix.diagonal (fun j => (hG.eigenvalues j : ℂ)) * (Vᴴ * P)) * V).trace :=
          Matrix.trace_mul_comm _ _
        _ = _ := by congr 1; simp only [R, Matrix.mul_assoc]
    rw [ht]
    simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Complex.re_sum,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  change ‖A * P‖ ^ 2 = ∑ i : Fin (Fintype.card n), complexGramEigenvalues A i * (R (e i) (e i)).re
  rw [hnative, ← e.sum_comp (fun j => hG.eigenvalues j * (R j j).re)]
  simp only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply, complexGramEigenvalues]

/-- Every actual complex rank-at-most-`k` competitor has squared Frobenius
error at least the genuine sorted Gram spectral tail.
Source: Horn–Johnson Theorem 7.4.9; `sa:volume-theorem`.
atlas: volume-sampling (partial) -/
theorem complexGramTail_le_frobenius_norm_sq_sub_of_rank_le
    (A B : Matrix m n ℂ) (k : ℕ) (hB : B.rank ≤ k) :
    complexGramTail A k ≤ ‖A - B‖ ^ 2 := by
  let P := complexColumnProjector Bᴴ
  have hs : P.IsHermitian := complexColumnProjector_isHermitian Bᴴ
  have hp : IsIdempotentElem P := complexColumnProjector_mul_self Bᴴ
  have hBP : B * P = B := mul_complexColumnProjector_conjTranspose B
  have hrankP : P.rank ≤ k := by
    rw [rank_complexColumnProjector, Matrix.rank_conjTranspose]
    exact hB
  let hG := Matrix.isHermitian_conjTranspose_mul_self A
  let V : Matrix n n ℂ := hG.eigenvectorUnitary
  let R := Vᴴ * P * V
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  have hV : Vᴴ * V = 1 := Unitary.coe_star_mul_self hG.eigenvectorUnitary
  have hV' : V * Vᴴ = 1 := Unitary.coe_mul_star_self hG.eigenvectorUnitary
  have hsR : R.IsHermitian := by
    simpa only [R, Matrix.conjTranspose_conjTranspose] using
      Matrix.isHermitian_conjTranspose_mul_mul V hs
  have hpR : IsIdempotentElem R := by
    change (Vᴴ * P * V) * (Vᴴ * P * V) = Vᴴ * P * V
    calc
      _ = Vᴴ * (P * (V * Vᴴ) * P) * V := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV', Matrix.mul_one, show P * P = P from hp]
  have hrankR : R.rank ≤ k :=
    ((Matrix.rank_mul_le_left (Vᴴ * P) V).trans (Matrix.rank_mul_le_right Vᴴ P)).trans hrankP
  have hbudget : (∑ i : Fin (Fintype.card n), (R (e i) (e i)).re) ≤ (k : ℝ) := by
    rw [e.sum_comp (fun j => (R j j).re)]
    rw [← Complex.re_sum]
    change R.trace.re ≤ (k : ℝ)
    rw [re_trace_eq_rank_of_isIdempotentElem R hpR]
    exact_mod_cast hrankR
  have hcaptured_le : ‖A * P‖ ^ 2 ≤
      ∑ i : Fin (Fintype.card n), if (i : ℕ) < k then complexGramEigenvalues A i else 0 := by
    rw [frobenius_norm_sq_mul_projector_eq_sum_gram_eigenvalues A P hs hp]
    apply sum_mul_le_sum_ite_lt_of_antitone
    · exact complexGramEigenvalues_nonneg A
    · exact complexGramEigenvalues_antitone A
    · intro i; exact (re_diag_mem_Icc_of_isHermitian_of_isIdempotentElem R hsR hpR (e i)).1
    · intro i; exact (re_diag_mem_Icc_of_isHermitian_of_isIdempotentElem R hsR hpR (e i)).2
    · exact hbudget
  have htotal : ‖A‖ ^ 2 = ∑ i : Fin (Fintype.card n), complexGramEigenvalues A i := by
    rw [frobenius_norm_sq_eq_re_trace_conjTranspose_mul, hG.trace_eq_sum_eigenvalues,
      Complex.re_sum]
    change (∑ j : n, hG.eigenvalues j) = _
    rw [← e.sum_comp hG.eigenvalues]
    simp only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply, complexGramEigenvalues]
  have hsplit : ‖A‖ ^ 2 =
      (∑ i : Fin (Fintype.card n), if (i : ℕ) < k then complexGramEigenvalues A i else 0) +
        complexGramTail A k := by
    rw [htotal, complexGramTail, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (i : ℕ) < k
    · simp only [if_pos hi, if_neg (not_le.mpr hi), add_zero]
    · simp only [if_neg hi, if_pos (not_lt.mp hi), zero_add]
  have hpyth := frobenius_norm_sq_eq_right_projection_add_residual P hs hp A
  have herr := frobenius_norm_sq_eq_right_projection_add_residual P hs hp (A - B)
  have hres : A * (1 - P) = (A - B) * (1 - P) := by
    rw [Matrix.sub_mul, Matrix.mul_sub B, Matrix.mul_one, hBP, sub_self, sub_zero]
  rw [← hres] at herr
  have hnonneg := sq_nonneg ‖(A - B) * P‖
  linarith

end NLAlib
