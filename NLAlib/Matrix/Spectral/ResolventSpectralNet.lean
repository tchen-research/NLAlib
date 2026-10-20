import NLAlib.Matrix.Spectral.ResolventSpectralInclusion
import NLAlib.ForMathlib.Analysis.CStarAlgebra.ResolventParameter

/-!
# Spectral inclusion from resolvent comparisons on a deterministic net

The actual parameter Lipschitz estimate lifts a comparison from a net of
the source spectrum to its every spectral point. This is the deterministic
grid step of arXiv:2201.05142v3, Propositions 7.4 and 7.7.
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- A comparison of actual Hermitian resolvents on a covering set gives
directed inclusion of the native spectra. Its discretization error is exactly
`(C+1)*mesh/height²`; no eigenvector basis is chosen in the statement. -/
theorem forall_exists_mem_spectrum_dist_le_of_resolvent_net
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (N : Set ℝ) {η C δ ε : ℝ} (hη : 0 < η) (hC : 0 ≤ C)
    (hcover : ∀ ξ ∈ spectrum ℝ A, ∃ u ∈ N, |ξ-u| ≤ ε)
    (hcmp : ∀ u ∈ N,
      specNorm (resolvent A ((u : ℂ)+(η : ℂ)*Complex.I)) ≤
        C*specNorm (resolvent B ((u : ℂ)+(η : ℂ)*Complex.I))+δ)
    (herror : δ+(C+1)*ε/η^2 ≤ (2*η)⁻¹) :
    ∀ ξ ∈ spectrum ℝ A, ∃ β ∈ spectrum ℝ B, dist ξ β ≤ 2*C*η := by
  intro ξ hξ
  have hn : Nonempty n := by
    obtain ⟨i, _⟩ := hA.spectrum_real_eq_range_eigenvalues ▸ hξ
    exact ⟨i⟩
  let := hn
  obtain ⟨u, hu, hdist⟩ := hcover ξ hξ
  have hleft := hA.isSelfAdjoint.abs_norm_resolvent_real_sub_le ξ u hη.ne'
  have hright := hB.isSelfAdjoint.abs_norm_resolvent_real_sub_le u ξ hη.ne'
  simp only [← specNorm_eq_norm, abs_sub_comm u ξ] at hleft hright
  have hdist' := div_le_div_of_nonneg_right hdist (sq_nonneg η)
  have hleft' := (le_abs_self _).trans (hleft.trans hdist')
  have hright' := (le_abs_self _).trans (hright.trans hdist')
  have hgrid := hcmp u hu
  have hmul := mul_le_mul_of_nonneg_left hright' hC
  apply exists_mem_spectrum_dist_le_of_resolvent_comparison hA hB hξ hη herror
  rw [show δ+(C+1)*ε/η^2 = δ+ε/η^2+C*(ε/η^2) by ring]
  linear_combination hleft' + hgrid + hmul

end NLAlib
