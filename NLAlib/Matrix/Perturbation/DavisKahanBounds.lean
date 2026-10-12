import NLAlib.Matrix.Perturbation.DavisKahanTop
import NLAlib.Matrix.Perturbation.DavisKahanPopulation
/-!
# Complete Davis–Kahan perturbation toolkit

Mixed interval/complement bounds retain all compressed residual contractions.
The sorted top-eigenspace corollary has the actual mixed eigenvalue denominator;
the population theorem retains both Frobenius branches without a smallness
condition. Empty and full subspace endpoints are explicit.
Source: Davis–Kahan §6; Yu–Wang–Samworth (2015), Theorems 1–2.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Matrix
namespace NLAlib

variable {n k r : Type*} [Fintype n] [Fintype k] [Fintype r]
  [DecidableEq n] [DecidableEq k] [DecidableEq r]

/-- Equal-width complete orthonormal frames have zero sine angles.
Stewart–Sun §I.5; the ambient space may itself be empty. -/
theorem sinePrincipalAngles_eq_zero_of_full_width {P Q : Matrix n k ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q)
    (hcard : Fintype.card k=Fintype.card n) : sinePrincipalAngles P Q=0 := by
  have hfull : P*Pᵀ=1 :=
    (Matrix.mul_eq_one_comm_of_card_eq (m := k) (n := n) (R := ℝ)
      (A := Pᵀ) (B := P) (eq := hcard)).mp hP
  apply (frobNorm_eq_zero_iff _).mp
  rw [frobNorm_sinePrincipalAngles_eq_residual hP hQ, residual_eq_one_sub_mul,
    hfull, sub_self, Matrix.zero_mul, frobNorm_zero]

/-- All requested Davis–Kahan bounds for actual invariant frames and actual
sorted spectral subspaces. Davis–Kahan §6 and Yu–Wang–Samworth (2015),
Theorems 1–2. The generic interval theorem includes empty selected or
complementary frames and needs no endpoint-order assumption. The population
Frobenius minimum is unconditional and is proved by the finite trace deficit;
zero and full top-frame widths have zero sine matrices.
atlas: davis-kahan-sin-theta (partial) -/
theorem davis_kahan_bounds {A E : Matrix n n ℝ}
    (hA : A.IsHermitian) (hE : E.IsHermitian)
    {Q Qhat : Matrix n k ℝ} {R : Matrix n r ℝ}
    (hQ : HasOrthonormalCols Q) (hQhat : HasOrthonormalCols Qhat)
    (hR : HasOrthonormalCols R) (hcomp : Qhat*Qhatᵀ+R*Rᵀ=1)
    {L : Matrix k k ℝ} {M : Matrix r r ℝ}
    (hAQ : A*Q=Q*L) (hAR : (A+E)*R=R*M) :
    (∀ a b δ : ℝ, 0 < δ →
      (∀ j, a ≤ (isHermitian_of_invariant_orthonormal_frame hA hQ hAQ).eigenvalues j ∧
        (isHermitian_of_invariant_orthonormal_frame hA hQ hAQ).eigenvalues j ≤ b) →
      (∀ i, (isHermitian_of_invariant_orthonormal_frame (hA.add hE) hR hAR).eigenvalues i ≤ a-δ ∨
        b+δ ≤ (isHermitian_of_invariant_orthonormal_frame (hA.add hE) hR hAR).eigenvalues i) →
      specNorm (sinePrincipalAngles Q Qhat) ≤ specNorm (Rᵀ*E*Q)/δ ∧
      specNorm (Rᵀ*E*Q)/δ ≤ specNorm (E*Q)/δ ∧ specNorm (E*Q)/δ ≤ specNorm E/δ ∧
      frobNorm (sinePrincipalAngles Q Qhat) ≤ frobNorm (Rᵀ*E*Q)/δ ∧
      frobNorm (Rᵀ*E*Q)/δ ≤ frobNorm (E*Q)/δ ∧ frobNorm (E*Q)/δ ≤ frobNorm E/δ ∧
      frobNorm (E*Q)/δ ≤ Real.sqrt (Fintype.card k)*specNorm E/δ) ∧
    (∀ j : ℕ, ∀ hj0 : 0 < j, ∀ hjN : j < Fintype.card n,
      0 < hA.eigenvalues₀ ⟨j-1, by omega⟩-(hA.add hE).eigenvalues₀ ⟨j, hjN⟩ →
      let S := sinePrincipalAngles (topEigenframe hA hjN.le) (topEigenframe (hA.add hE) hjN.le)
      let δ := hA.eigenvalues₀ ⟨j-1, by omega⟩-(hA.add hE).eigenvalues₀ ⟨j, hjN⟩
      specNorm S ≤ specNorm E/δ ∧ frobNorm S ≤ min (Real.sqrt j*specNorm E) (frobNorm E)/δ) ∧
    (∀ j : ℕ, ∀ hj0 : 0 < j, ∀ hjN : j < Fintype.card n,
      0 < hA.eigenvalues₀ ⟨j-1, by omega⟩-hA.eigenvalues₀ ⟨j, hjN⟩ →
      let S := sinePrincipalAngles (topEigenframe hA hjN.le) (topEigenframe (hA.add hE) hjN.le)
      let g := hA.eigenvalues₀ ⟨j-1, by omega⟩-hA.eigenvalues₀ ⟨j, hjN⟩
      specNorm S ≤ 2*specNorm E/g ∧ frobNorm S ≤ 2*min (Real.sqrt j*specNorm E) (frobNorm E)/g) ∧
    (∀ j : ℕ, ∀ hj : j ≤ Fintype.card n, j=0 ∨ j=Fintype.card n →
      sinePrincipalAngles (topEigenframe hA hj) (topEigenframe (hA.add hE) hj)=0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b δ hδ hint hout
    have hh := sinePrincipalAngles_le_compressed_residual_div_of_interval hA hE
      hQ hQhat hR hcomp hAQ hAR hδ hint hout
    have hSc := specNorm_transpose_frame_mul_le hR (E*Q)
    have hFc := frobNorm_transpose_frame_mul_le hR (E*Q)
    rw [← Matrix.mul_assoc] at hSc hFc
    exact ⟨hh.1,
      div_le_div_of_nonneg_right hSc hδ.le,
      div_le_div_of_nonneg_right (specNorm_mul_frame_le hQ E) hδ.le, hh.2,
      div_le_div_of_nonneg_right hFc hδ.le,
      div_le_div_of_nonneg_right (frobNorm_mul_frame_le hQ E) hδ.le,
      div_le_div_of_nonneg_right (frobNorm_mul_frame_le_sqrt_card_mul_specNorm hQ E) hδ.le⟩
  · intro j hj0 hjN hgap
    exact sinePrincipalAngles_le_perturbation_div_top_gap hA hE hj0 hjN hgap
  · intro j hj0 hjN hg
    exact ⟨specNorm_sinePrincipalAngles_le_two_mul_specNorm_div_population_gap hA hE hj0 hjN hg,
      frobNorm_sinePrincipalAngles_le_two_mul_min_div_population_gap hA hE hj0 hjN hg
        (hasOrthonormalCols_topEigenframe (hA.add hE) hjN.le)
        (trace_topEigenframe_compression_eq_prefix (hA.add hE) hjN.le)⟩
  · intro j hj hend
    rcases hend with hzero | hfull
    · ext i l
      have hi := i.isLt
      simp only [Fintype.card_fin] at hi
      omega
    · exact sinePrincipalAngles_eq_zero_of_full_width
        (hasOrthonormalCols_topEigenframe hA hj)
        (hasOrthonormalCols_topEigenframe (hA.add hE) hj) (by simpa only [Fintype.card_fin] using hfull)

end NLAlib
