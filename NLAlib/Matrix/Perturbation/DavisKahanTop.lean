import NLAlib.Matrix.Perturbation.DavisKahan
import NLAlib.Matrix.Spectral.EigenframeDecomposition
import NLAlib.Matrix.Subspaces.FrameContractions
import NLAlib.Matrix.Perturbation.EigenvaluePerturbation
/-!
# Sorted top-eigenspace Davis–Kahan bounds

The sorted top and complementary spectral frames give the advertised
mixed denominator. Weyl and the unit sine bound give the unconditional
constant-two population spectral bound. Source: Davis–Kahan §6 and
Yu–Wang–Samworth (2015), Theorems 1–2; atlas `davis-kahan-sin-theta`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Matrix
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] {A E : Matrix n n ℝ}

/-- The concrete sorted top-eigenspace mixed-gap theorem in both norms,
retaining the compressed perturbation residual. Davis–Kahan §6;
the denominator is exactly the population last selected eigenvalue minus
the perturbed first complementary eigenvalue.
atlas: davis-kahan-sin-theta (partial) -/
theorem sinePrincipalAngles_le_compressed_residual_div_top_gap
    (hA : A.IsHermitian) (hE : E.IsHermitian) {k : ℕ}
    (hk0 : 0 < k) (hkN : k < Fintype.card n)
    (hgap : 0 < hA.eigenvalues₀ ⟨k-1, by omega⟩-(hA.add hE).eigenvalues₀ ⟨k, hkN⟩) :
    let Q := topEigenframe hA hkN.le
    let Qhat := topEigenframe (hA.add hE) hkN.le
    let R := complementaryEigenframe (hA.add hE) hkN.le
    let δ := hA.eigenvalues₀ ⟨k-1, by omega⟩-(hA.add hE).eigenvalues₀ ⟨k, hkN⟩
    specNorm (sinePrincipalAngles Q Qhat) ≤ specNorm (Rᵀ*E*Q)/δ ∧
      frobNorm (sinePrincipalAngles Q Qhat) ≤ frobNorm (Rᵀ*E*Q)/δ := by
  dsimp only
  let Q := topEigenframe hA hkN.le
  let Qhat := topEigenframe (hA.add hE) hkN.le
  let R := complementaryEigenframe (hA.add hE) hkN.le
  let a := hA.eigenvalues₀ ⟨k-1, by omega⟩
  let b := (hA.add hE).eigenvalues₀ ⟨k, hkN⟩
  let d : Fin k → ℝ := fun i => hA.eigenvalues₀ (Fin.castLE hkN.le i)
  let e : Fin (Fintype.card n-k) → ℝ := fun i => (hA.add hE).eigenvalues₀ ⟨i.val+k, by omega⟩
  have hQ := hasOrthonormalCols_topEigenframe hA hkN.le
  have hQhat := hasOrthonormalCols_topEigenframe (hA.add hE) hkN.le
  have hR := hasOrthonormalCols_complementaryEigenframe (hA.add hE) hkN.le
  have hcomp := topEigenframe_projector_add_complementary_eq_one (hA.add hE) hkN.le
  have hmin : ∀ j, a ≤ (Matrix.isHermitian_diagonal d).eigenvalues j := by
    intro j
    obtain ⟨i, hi⟩ := exists_eq_eigenvalues_diagonal d j
    rw [← hi]
    apply hA.eigenvalues₀_antitone
    change i.val ≤ k-1
    omega
  have hmax : ∀ i, (Matrix.isHermitian_diagonal e).eigenvalues i ≤ b := by
    intro i
    obtain ⟨j, hj⟩ := exists_eq_eigenvalues_diagonal e i
    rw [← hj]
    apply (hA.add hE).eigenvalues₀_antitone
    change k ≤ j.val+k
    omega
  have heq := sylvester_complement_overlap_eq hA hE
    (mul_topEigenframe_eq_mul_diagonal hA hkN.le)
    (mul_complementaryEigenframe_eq_mul_diagonal (hA.add hE) hkN.le)
    (Matrix.isHermitian_diagonal e)
  have hS := mul_specNorm_le_specNorm_sylvester_of_one_sided
    (Matrix.isHermitian_diagonal e) (Matrix.isHermitian_diagonal d) hgap
    (by intro i; change _ ≤ a-(a-b); have hh := hmax i; linarith) hmin (Rᵀ*Q)
  have hF := mul_frobNorm_le_frobNorm_sylvester
    (Matrix.isHermitian_diagonal e) (Matrix.isHermitian_diagonal d) hgap
    (by intro i j; have hi := hmax i; have hj := hmin j; rw [le_abs]; right; linarith) (Rᵀ*Q)
  rw [heq] at hS hF
  have hswap : sinePrincipalAngles Q Qhat=sinePrincipalAngles Qhat Q := by
    unfold sinePrincipalAngles
    rw [principalAngles_comm]
  rw [← specNorm_sinePrincipalAngles_eq_complement_overlap hQhat hQ hR hcomp, ← hswap] at hS
  rw [← frobNorm_sinePrincipalAngles_eq_complement_overlap hQhat hQ hR hcomp, ← hswap] at hF
  exact ⟨(le_div_iff₀ hgap).2 (by simpa only [mul_comm] using hS),
    (le_div_iff₀ hgap).2 (by simpa only [mul_comm] using hF)⟩

/-- The sorted top-eigenspace mixed-gap corollary gives spectral perturbation
control and the Frobenius minimum of `sqrt k` times the spectral norm and
the Frobenius norm. Davis–Kahan §6, Yu–Wang–Samworth (2015), Theorem 1.
atlas: davis-kahan-sin-theta (partial) -/
theorem sinePrincipalAngles_le_perturbation_div_top_gap
    (hA : A.IsHermitian) (hE : E.IsHermitian) {k : ℕ}
    (hk0 : 0 < k) (hkN : k < Fintype.card n)
    (hgap : 0 < hA.eigenvalues₀ ⟨k-1, by omega⟩-(hA.add hE).eigenvalues₀ ⟨k, hkN⟩) :
    let S := sinePrincipalAngles (topEigenframe hA hkN.le) (topEigenframe (hA.add hE) hkN.le)
    let δ := hA.eigenvalues₀ ⟨k-1, by omega⟩-(hA.add hE).eigenvalues₀ ⟨k, hkN⟩
    specNorm S ≤ specNorm E/δ ∧
      frobNorm S ≤ min (Real.sqrt k*specNorm E) (frobNorm E)/δ := by
  dsimp only
  have hh := sinePrincipalAngles_le_compressed_residual_div_top_gap hA hE hk0 hkN hgap
  have hQ := hasOrthonormalCols_topEigenframe hA hkN.le
  have hR := hasOrthonormalCols_complementaryEigenframe (hA.add hE) hkN.le
  have hSc := specNorm_transpose_frame_mul_le hR (E*topEigenframe hA hkN.le)
  have hFc := frobNorm_transpose_frame_mul_le hR (E*topEigenframe hA hkN.le)
  rw [← Matrix.mul_assoc] at hSc hFc
  refine ⟨hh.1.trans (div_le_div_of_nonneg_right ?_ hgap.le),
    hh.2.trans (div_le_div_of_nonneg_right ?_ hgap.le)⟩
  · exact hSc.trans (specNorm_mul_frame_le hQ E)
  · apply le_min
    · exact hFc.trans
        (by simpa only [Fintype.card_fin] using frobNorm_mul_frame_le_sqrt_card_mul_specNorm hQ E)
    · exact hFc.trans (frobNorm_mul_frame_le hQ E)

/-- The unconditional population-gap spectral bound has constant two for
the sorted top eigenspaces. Yu–Wang–Samworth (2015), Theorem 2;
small perturbations use Weyl and large perturbations use the unit sine bound.
atlas: davis-kahan-sin-theta (partial) -/
theorem specNorm_sinePrincipalAngles_le_two_mul_specNorm_div_population_gap
    (hA : A.IsHermitian) (hE : E.IsHermitian) {k : ℕ}
    (hk0 : 0 < k) (hkN : k < Fintype.card n)
    (hg : 0 < hA.eigenvalues₀ ⟨k-1, by omega⟩-hA.eigenvalues₀ ⟨k, hkN⟩) :
    specNorm (sinePrincipalAngles (topEigenframe hA hkN.le) (topEigenframe (hA.add hE) hkN.le)) ≤
      2*specNorm E/(hA.eigenvalues₀ ⟨k-1, by omega⟩-hA.eigenvalues₀ ⟨k, hkN⟩) := by
  let S := specNorm (sinePrincipalAngles (topEigenframe hA hkN.le) (topEigenframe (hA.add hE) hkN.le))
  let g := hA.eigenvalues₀ ⟨k-1, by omega⟩-hA.eigenvalues₀ ⟨k, hkN⟩
  let δ := hA.eigenvalues₀ ⟨k-1, by omega⟩-(hA.add hE).eigenvalues₀ ⟨k, hkN⟩
  have hS0 : 0 ≤ S := specNorm_nonneg _
  apply (le_div_iff₀ hg).2
  change S*g ≤ 2*specNorm E
  by_cases hsmall : specNorm E < g/2
  · have hweyl := abs_eigenvalues₀_add_sub_le_specNorm hA hE ⟨k, hkN⟩
    rw [abs_le] at hweyl
    have hδ : 0 < δ := by dsimp only [δ]; change _ < g/2 at hsmall; dsimp only [g] at hsmall; linarith [hweyl.2]
    have hδg : g/2 ≤ δ := by dsimp only [δ, g] at *; linarith [hweyl.2]
    have hh := (sinePrincipalAngles_le_perturbation_div_top_gap hA hE hk0 hkN hδ).1
    have hmul := (le_div_iff₀ hδ).mp hh
    change S*δ ≤ specNorm E at hmul
    nlinarith [mul_le_mul_of_nonneg_left hδg hS0]
  · have hS : S ≤ 1 := specNorm_sinePrincipalAngles_le_one
      (hasOrthonormalCols_topEigenframe hA hkN.le)
      (hasOrthonormalCols_topEigenframe (hA.add hE) hkN.le)
    nlinarith [mul_le_mul_of_nonneg_right hS hg.le]

end NLAlib
