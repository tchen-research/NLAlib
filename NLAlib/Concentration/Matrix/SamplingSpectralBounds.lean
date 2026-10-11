import NLAlib.Concentration.Matrix.Sampling

/-!
# Spectral bridges for matrix sampling

Positive matrices have nonnegative minimum eigenvalue and maximum eigenvalue
bounded by the trace. A Hermitian Gram norm failure is covered by the two
extreme eigenvalue failure events. Sources: operator re-derivation `sa:leverage`.
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
namespace NLAlib

/-- A positive semidefinite matrix has nonnegative minimum eigenvalue.
Source: the finite spectral theorem; supports `leverage-sampling-ose`. -/
theorem lambdaMin_nonneg_of_posSemidef {d : Type*} [Fintype d] [DecidableEq d]
    [Nonempty d] {P : Matrix d d ℂ} (hP : P.PosSemidef) : 0 ≤ lambdaMin P := by
  rw [lambdaMin, hP.isHermitian.spectrum_real_eq_range_eigenvalues]
  exact le_csInf (Set.range_nonempty _) (by rintro _ ⟨i, rfl⟩; exact hP.eigenvalues_nonneg i)

/-- A positive semidefinite matrix has maximum eigenvalue at most its real trace.
Source: the finite spectral theorem; supports `leverage-sampling-ose`. -/
theorem lambdaMax_le_trace_of_posSemidef {d : Type*} [Fintype d] [DecidableEq d]
    [Nonempty d] {P : Matrix d d ℂ} (hP : P.PosSemidef) :
    lambdaMax P ≤ P.trace.re := by
  have htrace : P.trace.re = ∑ i, hP.isHermitian.eigenvalues i := by
    rw [hP.isHermitian.trace_eq_sum_eigenvalues]
    simp
  rw [lambdaMax, hP.isHermitian.spectrum_real_eq_range_eigenvalues, htrace]
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨i, rfl⟩
  exact Finset.single_le_sum (fun j _ => hP.eigenvalues_nonneg j) (Finset.mem_univ i)

/-- A Hermitian norm deviation from identity is covered by its minimum and
maximum eigenvalue deviations. Source: operator re-derivation `sa:leverage`;
the C-star norm-attaining spectrum theorem includes equality endpoints. -/
theorem lambdaMin_le_or_le_lambdaMax_of_le_spectralNorm_sub_one
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    {H : Matrix d d ℂ} (hH : H.IsHermitian) {ε : ℝ}
    (h : ε ≤ spectralNorm (H - 1)) :
    lambdaMin H ≤ 1 - ε ∨ 1 + ε ≤ lambdaMax H := by
  have hshift : ∀ q : ℝ, q ∈ spectrum ℝ (H - 1) → q + 1 ∈ spectrum ℝ H := by
    intro q hq
    rw [spectrum.mem_iff] at hq ⊢
    have heq : algebraMap ℝ (Matrix d d ℂ) (q + 1) - H =
        algebraMap ℝ (Matrix d d ℂ) q - (H - 1) := by
      rw [map_add, map_one]
      abel
    rwa [heq]
  have hfin : (spectrum ℝ H).Finite := by
    rw [hH.spectrum_real_eq_range_eigenvalues]
    exact Set.finite_range _
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum (hH.sub Matrix.isHermitian_one).isSelfAdjoint
      with hp | hm
  · right
    have hh := le_csSup hfin.bddAbove (hshift _ hp)
    change ε ≤ ‖H - 1‖ at h
    change ‖H - 1‖ + 1 ≤ lambdaMax H at hh
    linarith
  · left
    have hh := csInf_le hfin.bddBelow (hshift _ hm)
    change ε ≤ ‖H - 1‖ at h
    change lambdaMin H ≤ -‖H - 1‖ + 1 at hh
    linarith

end NLAlib
