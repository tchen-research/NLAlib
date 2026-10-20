import NLAlib.ForMathlib.Topology.RealIntervalNet
import NLAlib.ForMathlib.Analysis.CStarAlgebra.SpectrumPerturbation
import NLAlib.Matrix.Spectral.HermitianExtremaNorm

/-!
# Small deterministic nets for neighborhoods of Hermitian spectra

A norm neighborhood of a deterministic Hermitian matrix's spectrum is
covered by finitely many real interval grids. This is the localization grid
used in arXiv:2201.05142v3, Propositions 7.4 and 7.7.
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- One deterministic real grid covers the actual spectrum of every
matrix in a norm ball about a fixed Hermitian matrix. Its size scales with
the number of eigenvalues and the radius-to-mesh ratio. -/
theorem exists_finset_spectral_neighborhood_net {D : Matrix n n ℂ}
    (hD : D.IsHermitian) {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ N : Finset ℝ, N.card ≤ Fintype.card n*(⌈2*L/ε⌉₊+1) ∧
      ∀ A : Matrix n n ℂ, specNorm (A-D) ≤ L →
        ∀ ξ ∈ spectrum ℝ A, ∃ u ∈ N, |ξ-u| ≤ ε := by
  obtain ⟨N, hcard, hcover⟩ := Real.exists_finset_union_intervals_net hD.eigenvalues hL hε
  refine ⟨N, hcard, fun A hA ξ hξ => ?_⟩
  obtain ⟨β, hβ, hclose⟩ := hD.isSelfAdjoint.exists_mem_spectrum_real_dist_le_norm_sub hξ
  rw [hD.spectrum_real_eq_range_eigenvalues] at hβ
  obtain ⟨i, rfl⟩ := hβ
  apply hcover ξ
  refine ⟨i, ?_⟩
  have hh : ‖D-A‖ ≤ L := by simpa only [norm_sub_rev, specNorm_eq_norm] using hA
  simpa only [Real.dist_eq] using hclose.trans hh

open scoped Matrix.Norms.L2Operator in
/-- A neighborhood of radius `4*d*ε` of a deterministic Hermitian matrix
has a deterministic ε-grid with at most `9*d²` points, including dimension
zero. The grid covers native spectra directly. -/
theorem exists_finset_spectral_neighborhood_net_card_sq {D : Matrix n n ℂ}
    (hD : D.IsHermitian) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : Finset ℝ, N.card ≤ 9*(Fintype.card n)^2 ∧
      ∀ A : Matrix n n ℂ, specNorm (A-D) ≤ 4*Fintype.card n*ε →
        ∀ ξ ∈ spectrum ℝ A, ∃ u ∈ N, |ξ-u| ≤ ε := by
  obtain ⟨N, hcard, hcover⟩ := exists_finset_spectral_neighborhood_net hD
    (L := 4*Fintype.card n*ε) (by positivity) hε
  have hwidth : 2*(4*(Fintype.card n : ℝ)*ε)/ε = ((8*Fintype.card n : ℕ) : ℝ) := by
    push_cast
    field_simp [hε.ne']
    ring
  rw [hwidth, Nat.ceil_natCast] at hcard
  refine ⟨N, hcard.trans ?_, hcover⟩
  nlinarith [Nat.le_mul_self (Fintype.card n)]

end NLAlib
