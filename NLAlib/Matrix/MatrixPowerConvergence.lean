import NLAlib.Matrix.MatrixPowerBounds

/-!
# Matrix-power convergence and the Neumann series

Decay is equivalent to a spectral radius below one, and the convergent
geometric series is the nonsingular inverse of `1-A`.
Source: Horn–Johnson (2013), Theorem 5.6.12 and Corollary 5.6.13;
atlas `matrix-power-convergence`.
-/

noncomputable section
open Filter
open scoped Matrix Matrix.Norms.L2Operator Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Decaying powers force spectral radius below one. Source: Horn–Johnson
(2013), Theorem 5.6.12; one sufficiently small positive power controls the
spectral radius by the spectral-mapping norm bound.
atlas: matrix-power-convergence (partial) -/
theorem spectralRadius_lt_one_of_tendsto_matrix_pow_zero {A : Matrix n n ℂ}
    (hA : Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0)) : spectralRadius ℂ A < 1 := by
  cases isEmpty_or_nonempty n with
  | inl hn =>
    have hAz : A = 0 := Subsingleton.elim _ _
    rw [hAz, spectrum.spectralRadius_zero]
    exact zero_lt_one
  | inr hn =>
    have hnorm := tendsto_zero_iff_norm_tendsto_zero.mp hA
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hnorm.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
    have hsmall : ‖A ^ (N + 1)‖ < 1 := hN (N + 1) (by omega)
    have hbound := spectrum.spectralRadius_le_pow_nnnorm_pow_one_div ℂ A N
    simp only [nnnorm_one, ENNReal.coe_one, ENNReal.one_rpow, mul_one] at hbound
    apply hbound.trans_lt
    apply ENNReal.rpow_lt_one
    · exact_mod_cast hsmall
    · positivity

/-- Matrix powers decay exactly for spectral radius below one. Source:
Horn–Johnson (2013), Theorem 5.6.12; arbitrary finite indices may be empty.
atlas: matrix-power-convergence (partial) -/
theorem tendsto_matrix_pow_zero_iff_spectralRadius_lt_one (A : Matrix n n ℂ) :
    Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0) ↔ spectralRadius ℂ A < 1 :=
  ⟨spectralRadius_lt_one_of_tendsto_matrix_pow_zero,
    tendsto_matrix_pow_zero_of_spectralRadius_lt_one⟩

/-- The sum of the convergent matrix geometric series is the inverse of
`1-A`. Source: Horn–Johnson (2013), Corollary 5.6.13; finite geometric sums
give the inverse identity, with no norm-below-one assumption on `A` itself.
atlas: matrix-power-convergence (partial) -/
theorem tsum_matrix_pow_eq_inv_of_spectralRadius_lt_one {A : Matrix n n ℂ}
    (hA : spectralRadius ℂ A < 1) : (∑' k : ℕ, A ^ k) = (1 - A)⁻¹ := by
  have hs := summable_matrix_pow_of_spectralRadius_lt_one hA
  have hp := tendsto_matrix_pow_zero_of_spectralRadius_lt_one hA
  have hleft : Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, A ^ k) * (1 - A))
      atTop (𝓝 ((∑' k : ℕ, A ^ k) * (1 - A))) :=
    hs.hasSum.tendsto_sum_nat.mul_const (1 - A)
  have hright : Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, A ^ k) * (1 - A))
      atTop (𝓝 1) := by
    simp only [geom_sum_mul_neg]
    simpa only [sub_zero] using tendsto_const_nhds.sub hp
  have hInv : (∑' k : ℕ, A ^ k) * (1 - A) = 1 := tendsto_nhds_unique hleft hright
  exact (Matrix.inv_eq_left_inv hInv).symm

/-- The matrix geometric series has the stated inverse as its actual sum.
Source: Horn–Johnson (2013), Corollary 5.6.13; combines absolute convergence
and the telescoping inverse identity.
atlas: matrix-power-convergence (partial) -/
theorem hasSum_matrix_pow_inv_of_spectralRadius_lt_one {A : Matrix n n ℂ}
    (hA : spectralRadius ℂ A < 1) : HasSum (fun k : ℕ => A ^ k) (1 - A)⁻¹ := by
  rw [← tsum_matrix_pow_eq_inv_of_spectralRadius_lt_one hA]
  exact (summable_matrix_pow_of_spectralRadius_lt_one hA).hasSum

/-- The denominator of the Neumann series is nonsingular whenever the
spectral radius is below one. Source: Horn–Johnson (2013), Corollary 5.6.13.
atlas: matrix-power-convergence (partial) -/
theorem isUnit_one_sub_of_matrix_spectralRadius_lt_one {A : Matrix n n ℂ}
    (hA : spectralRadius ℂ A < 1) : IsUnit (1 - A) := by
  have hs := summable_matrix_pow_of_spectralRadius_lt_one hA
  have hp := tendsto_matrix_pow_zero_of_spectralRadius_lt_one hA
  have hleft : Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, A ^ k) * (1 - A))
      atTop (𝓝 ((∑' k : ℕ, A ^ k) * (1 - A))) :=
    hs.hasSum.tendsto_sum_nat.mul_const (1 - A)
  have hright : Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, A ^ k) * (1 - A))
      atTop (𝓝 1) := by
    simp only [geom_sum_mul_neg]
    simpa only [sub_zero] using tendsto_const_nhds.sub hp
  have hInv : (∑' k : ℕ, A ^ k) * (1 - A) = 1 := tendsto_nhds_unique hleft hright
  have hdet := congrArg Matrix.det hInv
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  apply (1 - A).isUnit_iff_isUnit_det.mpr
  apply isUnit_iff_ne_zero.mpr
  intro hz
  rw [hz, mul_zero] at hdet
  exact zero_ne_one hdet

end NLAlib
