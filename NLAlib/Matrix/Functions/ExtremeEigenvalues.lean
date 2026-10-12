import NLAlib.Matrix.Functions.ExpLog
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Data.Real.Pointwise

/-!
# Extreme eigenvalues: scaling, identity, positivity and norm deviations

Elementary API for `lambdaMax` and `lambdaMin` on complex matrices over any finite index type:

* positive scaling and the identity: `lambdaMax_smul_of_pos`, `lambdaMin_smul_of_pos`,
  `lambdaMax_one`, `lambdaMin_one`;
* positive semidefinite matrices: `lambdaMin_nonneg_of_posSemidef`,
  `lambdaMax_le_trace_of_posSemidef`;
* a norm deviation from the identity is an extreme-eigenvalue deviation:
  `lambdaMin_le_or_le_lambdaMax_of_le_norm_sub_one`.

Atlas: helpers for `matrix-chernoff-sampling`, `leverage-sampling-ose`.

Moved from `NLAlib.Probability.Concentration.Matrix.Sampling` (spectral section) and
`NLAlib.Probability.Concentration.Matrix.SamplingSpectralBounds` (dedup round 2026-10-12).
-/

open scoped Pointwise
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

noncomputable section
set_option autoImplicit false

namespace NLAlib

section Spectral

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- `λmax(c A) = c λmax(A)` for `c > 0`. Tropp 2015, §2.1; atlas `matrix-chernoff-sampling`
(helper). -/
theorem lambdaMax_smul_of_pos (A : Matrix d d ℂ) {c : ℝ} (hc : 0 < c) :
    lambdaMax (c • A) = c * lambdaMax A := by
  have h := spectrum.unit_smul_eq_smul (R := ℝ) A (Units.mk0 c hc.ne')
  rw [Units.smul_def, Units.val_mk0] at h
  rw [lambdaMax, h, Units.smul_def, Units.val_mk0, Real.sSup_smul_of_nonneg hc.le, smul_eq_mul,
    lambdaMax]

/-- `λmin(c A) = c λmin(A)` for `c > 0`. Tropp 2015, §2.1; atlas `matrix-chernoff-sampling`
(helper). -/
theorem lambdaMin_smul_of_pos (A : Matrix d d ℂ) {c : ℝ} (hc : 0 < c) :
    lambdaMin (c • A) = c * lambdaMin A := by
  have h := spectrum.unit_smul_eq_smul (R := ℝ) A (Units.mk0 c hc.ne')
  rw [Units.smul_def, Units.val_mk0] at h
  rw [lambdaMin, h, Units.smul_def, Units.val_mk0, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul,
    lambdaMin]

/-- `λmax(I) = 1` for a nonempty index type. Tropp 2015, §2.1; atlas
`matrix-chernoff-sampling` (helper). -/
@[simp] theorem lambdaMax_one [Nonempty d] : lambdaMax (1 : Matrix d d ℂ) = 1 := by
  rw [lambdaMax, spectrum.one_eq, csSup_singleton]

/-- `λmin(I) = 1` for a nonempty index type. Tropp 2015, §2.1; atlas
`matrix-chernoff-sampling` (helper). -/
@[simp] theorem lambdaMin_one [Nonempty d] : lambdaMin (1 : Matrix d d ℂ) = 1 := by
  rw [lambdaMin, spectrum.one_eq, csInf_singleton]

end Spectral

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
theorem lambdaMin_le_or_le_lambdaMax_of_le_norm_sub_one
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    {H : Matrix d d ℂ} (hH : H.IsHermitian) {ε : ℝ}
    (h : ε ≤ ‖H - 1‖) :
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
