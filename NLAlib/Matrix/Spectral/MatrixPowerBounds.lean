import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Quantitative matrix-power bounds from Gelfand's formula

An explicit finite-prefix constant extends the eventual geometric power
bound to every exponent. No Schur or Jordan basis is required for this part.
Source: Horn–Johnson (2013), Lemmas 5.6.10–5.6.11 and Theorem 5.6.12;
atlas `matrix-power-convergence`.
-/

noncomputable section
open Filter
open scoped Matrix Matrix.Norms.L2Operator Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The complex matrix spectral radius is finite, including for empty
matrices. Source: Gelfand's spectral-radius bound, Horn–Johnson (2013),
§5.6; the bound retains the norm of the identity for a zero-dimensional ring. -/
theorem matrix_spectralRadius_ne_top (A : Matrix n n ℂ) : spectralRadius ℂ A ≠ ⊤ := by
  have h := spectrum.spectralRadius_le_pow_nnnorm_pow_one_div ℂ A 0
  simp only [Nat.cast_zero, zero_add, one_div_one, ENNReal.rpow_one, pow_one] at h
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top) h

/-- The real-valued root norms of matrix powers converge to the real spectral
radius. Source: Gelfand's formula, Horn–Johnson (2013), §5.6; empty matrices
are included, and the zero exponent is interpreted by total real division. -/
theorem tendsto_norm_matrix_pow_rpow_spectralRadius (A : Matrix n n ℂ) :
    Tendsto (fun k : ℕ => ‖A ^ k‖ ^ (1 / k : ℝ)) atTop
      (𝓝 (spectralRadius ℂ A).toReal) := by
  have h := (ENNReal.tendsto_toReal (matrix_spectralRadius_ne_top A)).comp
    (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius A)
  convert h using 1
  ext k
  exact (ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)).symm

/-- An explicit constant absorbing the powers before a geometric bound
starts. Source: Horn–Johnson (2013), Lemma 5.6.10; for positive `r`, every
term is nonnegative and the constant is at least one. -/
def matrixPowerBoundConstant (A : Matrix n n ℂ) (r : ℝ) (N : ℕ) : ℝ :=
  1 + ∑ k ∈ Finset.range N, ‖A ^ k‖ / r ^ k

/-- A positive growth rate gives a finite-prefix constant at least one.
Source: Horn–Johnson (2013), Lemma 5.6.10, explicit constant construction. -/
theorem one_le_matrixPowerBoundConstant (A : Matrix n n ℂ) {r : ℝ}
    (hr : 0 < r) (N : ℕ) : 1 ≤ matrixPowerBoundConstant A r N := by
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg fun k _ => div_nonneg (norm_nonneg _) (pow_nonneg hr.le k)

/-- An eventual geometric power bound extends to all exponents with the
defined finite-prefix constant. Source: Horn–Johnson (2013), Lemma 5.6.10. -/
theorem norm_matrix_pow_le_matrixPowerBoundConstant_mul_pow (A : Matrix n n ℂ)
    {r : ℝ} (hr : 0 < r) (N : ℕ) (hN : ∀ k, N ≤ k → ‖A ^ k‖ ≤ r ^ k) (k : ℕ) :
    ‖A ^ k‖ ≤ matrixPowerBoundConstant A r N * r ^ k := by
  by_cases hk : k < N
  · have hsum : ‖A ^ k‖ / r ^ k ≤ ∑ j ∈ Finset.range N, ‖A ^ j‖ / r ^ j :=
      Finset.single_le_sum (fun j _ => div_nonneg (norm_nonneg _) (pow_nonneg hr.le j))
        (Finset.mem_range.mpr hk)
    apply (div_le_iff₀ (pow_pos hr k)).mp
    exact hsum.trans (le_add_of_nonneg_left zero_le_one)
  · exact (hN k (le_of_not_gt hk)).trans
      (le_mul_of_one_le_left (pow_nonneg hr.le k) (one_le_matrixPowerBoundConstant A hr N))

/-- Every growth rate strictly greater than the spectral radius controls
all matrix powers with an explicit finite-prefix constant. Source:
Horn–Johnson (2013), Lemma 5.6.10 and Theorem 5.6.12; Gelfand's formula
supplies the prefix length, and the constant is a defined finite sum.
atlas: matrix-power-convergence (partial) -/
theorem exists_prefix_norm_matrix_pow_le_growth (A : Matrix n n ℂ) {r : ℝ}
    (hr : 0 < r) (hρr : (spectralRadius ℂ A).toReal < r) :
    ∃ N : ℕ, ∀ k : ℕ, ‖A ^ k‖ ≤ matrixPowerBoundConstant A r N * r ^ k := by
  have hevent := (tendsto_norm_matrix_pow_rpow_spectralRadius A).eventually
    (gt_mem_nhds hρr)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  have hbound (k : ℕ) (hk : N + 1 ≤ k) : ‖A ^ k‖ ≤ r ^ k := by
    have hkpos : 0 < k := by omega
    have hroot : ‖A ^ k‖ ^ (1 / k : ℝ) ≤ r := (hN k (by omega)).le
    have hp := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) hroot
      (Nat.cast_nonneg k : 0 ≤ (k : ℝ))
    rw [← Real.rpow_mul (norm_nonneg _), one_div_mul_cancel (Nat.cast_ne_zero.mpr hkpos.ne'),
      Real.rpow_one, Real.rpow_natCast] at hp
    exact hp
  exact ⟨N + 1, norm_matrix_pow_le_matrixPowerBoundConstant_mul_pow A hr (N + 1) hbound⟩

/-- The source's spectral-radius-plus-epsilon estimate, with an explicit
finite-prefix constant and no omitted finite exponents. Source: Horn–Johnson
(2013), Lemma 5.6.10; any positive epsilon is admitted.
atlas: matrix-power-convergence (partial) -/
theorem exists_prefix_norm_matrix_pow_le_spectralRadius_add (A : Matrix n n ℂ)
    {ε : ℝ} (hε : 0 < ε) : ∃ N : ℕ, ∀ k : ℕ,
      ‖A ^ k‖ ≤ matrixPowerBoundConstant A ((spectralRadius ℂ A).toReal + ε) N *
        ((spectralRadius ℂ A).toReal + ε) ^ k :=
  exists_prefix_norm_matrix_pow_le_growth A
    (add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hε) (lt_add_of_pos_right _ hε)

/-- Powers decay to zero whenever the complex spectral radius is below one.
Source: Horn–Johnson (2013), Theorem 5.6.12; the proof uses the explicit
geometric growth bound and includes empty matrix spaces.
atlas: matrix-power-convergence (partial) -/
theorem tendsto_matrix_pow_zero_of_spectralRadius_lt_one {A : Matrix n n ℂ}
    (hA : spectralRadius ℂ A < 1) : Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0) := by
  have hρ : (spectralRadius ℂ A).toReal < 1 := by
    exact (ENNReal.toReal_lt_toReal (matrix_spectralRadius_ne_top A) ENNReal.one_ne_top).mpr hA
  let r : ℝ := ((spectralRadius ℂ A).toReal + 1) / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hρr : (spectralRadius ℂ A).toReal < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  obtain ⟨N, hN⟩ := exists_prefix_norm_matrix_pow_le_growth A hr hρr
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun k => norm_nonneg _) hN
    (by simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1).const_mul
      (matrixPowerBoundConstant A r N)))

/-- Powers are summable when the spectral radius is below one. Source:
Horn–Johnson (2013), Corollary 5.6.13; the same explicit geometric majorant
establishes absolute convergence.
atlas: matrix-power-convergence (partial) -/
theorem summable_matrix_pow_of_spectralRadius_lt_one {A : Matrix n n ℂ}
    (hA : spectralRadius ℂ A < 1) : Summable (fun k : ℕ => A ^ k) := by
  have hρ : (spectralRadius ℂ A).toReal < 1 :=
    (ENNReal.toReal_lt_toReal (matrix_spectralRadius_ne_top A) ENNReal.one_ne_top).mpr hA
  let r : ℝ := ((spectralRadius ℂ A).toReal + 1) / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hρr : (spectralRadius ℂ A).toReal < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  obtain ⟨N, hN⟩ := exists_prefix_norm_matrix_pow_le_growth A hr hρr
  exact Summable.of_norm_bounded ((summable_geometric_of_lt_one hr.le hr1).mul_left
    (matrixPowerBoundConstant A r N)) hN

end NLAlib
