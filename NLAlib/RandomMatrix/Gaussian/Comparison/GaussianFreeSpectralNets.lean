import NLAlib.Matrix.Spectral.SpectralIntervalNet
import NLAlib.ForMathlib.Topology.MetricSpace.FiniteInternalNet
import NLAlib.Probability.Free.WordMatrixSpectrum
import NLAlib.Probability.Free.WordNativeMatrixLinearCombination
import NLAlib.Matrix.Structured.CoefficientBilinearParameters

/-! # Two actual spectral grids near the deterministic mean -/

noncomputable section
set_option autoImplicit false
open scoped Matrix
namespace NLAlib
variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]

open scoped Matrix.Norms.L2Operator in
/-- A deterministic grid covers the actual localized Gaussian matrices,
while a second grid lies in and covers the actual native free spectrum. Both
have at most nine times the squared matrix dimension many points. -/
theorem exists_finset_gaussian_free_spectral_nets
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    {ε : ℝ} (hε : 0 < ε)
    (hscale : Real.sqrt (specNorm (coefficientVariance A)) ≤ 2*(Fintype.card d : ℝ)*ε) :
    ∃ N M : Finset ℝ,
      N.card ≤ 9*(Fintype.card d)^2 ∧ M.card ≤ 9*(Fintype.card d)^2 ∧
      (M : Set ℝ) ⊆ spectrum ℝ (wordNativeMatrixLinearCombination A₀ A) ∧
      (∀ X : Matrix d d ℂ, specNorm (X-A₀) ≤ 4*(Fintype.card d : ℝ)*ε →
        ∀ ξ ∈ spectrum ℝ X, ∃ u ∈ N, |ξ-u| ≤ ε) ∧
      (∀ ξ ∈ spectrum ℝ (wordNativeMatrixLinearCombination A₀ A),
        ∃ u ∈ M, |ξ-u| ≤ 2*ε) := by
  classical
  obtain ⟨N, hcard, hcover⟩ := Real.exists_finset_union_intervals_net hA₀.eigenvalues
    (L := 4*(Fintype.card d : ℝ)*ε) (by positivity) hε
  have hw : 2*(4*(Fintype.card d : ℝ)*ε)/ε = ((8*Fintype.card d : ℕ) : ℝ) := by
    push_cast
    field_simp [hε.ne']
    ring
  rw [hw, Nat.ceil_natCast] at hcard
  have hcard' : N.card ≤ 9*(Fintype.card d)^2 := by
    nlinarith [Nat.le_mul_self (Fintype.card d)]
  have hvar : coefficientVariance A = ∑ i, A i^2 := by
    simp only [coefficientVariance, pow_two]
  have hfreecover : ∀ ξ ∈ spectrum ℝ (wordNativeMatrixLinearCombination A₀ A),
      ∃ u ∈ N, dist ξ u ≤ ε := by
    intro ξ hξ
    have hs : spectrum ℝ (wordMatrixLinearCombination A₀ A) =
        spectrum ℝ (wordNativeMatrixLinearCombination A₀ A) := by
      simpa only [toPiLp_wordNativeMatrixLinearCombination] using!
        CStarMatrix.spectrum_real_toPiLpStarAlgHom
          (D := d) (H := WordHilbertSpace ι)
          (isSelfAdjoint_wordNativeMatrixLinearCombination hA₀ hA)
    have hξ' : ξ ∈ spectrum ℝ (wordMatrixLinearCombination A₀ A) := hs.symm ▸ hξ
    obtain ⟨β, hβ, hd⟩ := exists_mem_mean_spectrum_dist_le_wordMatrixLinearCombination
      hA₀ A hA hξ'
    rw [hA₀.spectrum_real_eq_range_eigenvalues] at hβ
    obtain ⟨i, rfl⟩ := hβ
    have hb : |ξ-hA₀.eigenvalues i| ≤ 4*(Fintype.card d : ℝ)*ε := by
      rw [← Real.dist_eq]
      rw [← hvar] at hd
      exact hd.trans (by linarith)
    obtain ⟨u, hu, hdu⟩ := hcover ξ ⟨i, hb⟩
    exact ⟨u, hu, by simpa only [Real.dist_eq] using hdu⟩
  obtain ⟨M, hM, hMcard, hMcover⟩ := Metric.exists_finset_subset_card_le_of_cover
    (spectrum ℝ (wordNativeMatrixLinearCombination A₀ A)) N hε.le hfreecover
  refine ⟨N, M, hcard', hMcard.trans hcard', hM, ?_, ?_⟩
  · intro X hX ξ hξ
    obtain ⟨β, hβ, hd⟩ := hA₀.isSelfAdjoint.exists_mem_spectrum_real_dist_le_norm_sub hξ
    rw [hA₀.spectrum_real_eq_range_eigenvalues] at hβ
    obtain ⟨i, rfl⟩ := hβ
    apply hcover ξ
    refine ⟨i, ?_⟩
    have hh : ‖A₀-X‖ ≤ 4*(Fintype.card d : ℝ)*ε := by
      simpa only [norm_sub_rev, specNorm_eq_norm] using hX
    simpa only [Real.dist_eq] using hd.trans hh
  · intro ξ hξ
    simpa only [Real.dist_eq] using hMcover ξ hξ

end NLAlib
