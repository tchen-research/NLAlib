import NLAlib.Matrix.Spectral.MatrixPowerConvergence
import NLAlib.Matrix.Norms.RealComplexNorm
/-!
# Real matrix powers with complex spectral radius

Complexification commutes with powers; its real-part map transports decay
back to real matrices. The complex geometric majorant bounds real spectral
norms and proves the real Neumann series. Source: Horn–Johnson (2013),
Theorem 5.6.12 and Corollary 5.6.13; atlas `matrix-power-convergence`.
-/

noncomputable section
open Filter
open scoped Matrix Matrix.Norms.L2Operator Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Complexification commutes with matrix powers. Source: Horn–Johnson
(2013), §5.6; this is the matrix ring-homomorphism power identity. -/
theorem map_ofReal_matrix_pow (A : Matrix n n ℝ) (k : ℕ) :
    (A ^ k).map Complex.ofReal = (A.map Complex.ofReal) ^ k :=
  map_pow Complex.ofRealHom.mapMatrix A k

/-- Real matrix power decay is equivalent to the complexified spectral
radius being below one. Source: Horn–Johnson (2013), Theorem 5.6.12; the
spectrum is explicitly taken over the complex field.
atlas: matrix-power-convergence (partial) -/
theorem tendsto_real_matrix_pow_zero_iff_complex_spectralRadius_lt_one
    (A : Matrix n n ℝ) : Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0) ↔
      spectralRadius ℂ (A.map Complex.ofReal) < 1 := by
  have hcont : Continuous (fun M : Matrix n n ℝ => M.map Complex.ofReal) := by fun_prop
  have hre : Continuous (fun M : Matrix n n ℂ => M.map Complex.re) := by fun_prop
  have hback (k : ℕ) : ((A.map Complex.ofReal) ^ k).map Complex.re = A ^ k := by
    rw [← map_ofReal_matrix_pow]
    rfl
  constructor
  · intro hA
    apply spectralRadius_lt_one_of_tendsto_matrix_pow_zero
    have h := hcont.continuousAt.tendsto.comp hA
    simpa only [Function.comp_def, map_ofReal_matrix_pow, Matrix.map_zero _ Complex.ofReal_zero] using h
  · intro hA
    have h := hre.continuousAt.tendsto.comp (tendsto_matrix_pow_zero_of_spectralRadius_lt_one hA)
    simpa only [Function.comp_def, hback, Matrix.map_zero _ Complex.zero_re] using h

/-- Every real matrix power satisfies the spectral-radius-plus-epsilon
estimate with the defined complex finite-prefix constant. Source:
Horn–Johnson (2013), Lemma 5.6.10; complexification uses the same spectral
radius and bounds the real Euclidean operator norm.
atlas: matrix-power-convergence (partial) -/
theorem exists_prefix_specNorm_real_matrix_pow_le_complex_spectralRadius_add
    (A : Matrix n n ℝ) {ε : ℝ} (hε : 0 < ε) : ∃ N : ℕ, ∀ k : ℕ,
      specNorm (A ^ k) ≤
        matrixPowerBoundConstant (A.map Complex.ofReal)
          ((spectralRadius ℂ (A.map Complex.ofReal)).toReal + ε) N *
            ((spectralRadius ℂ (A.map Complex.ofReal)).toReal + ε) ^ k := by
  obtain ⟨N, hN⟩ := exists_prefix_norm_matrix_pow_le_spectralRadius_add (A.map Complex.ofReal) hε
  refine ⟨N, fun k => ?_⟩
  have hh := specNorm_le_norm_map_ofReal (A ^ k)
  rw [map_ofReal_matrix_pow] at hh
  exact hh.trans (hN k)

/-- Real matrix powers are absolutely summable when their complex spectral
radius is below one. Source: Horn–Johnson (2013), Corollary 5.6.13.
atlas: matrix-power-convergence (partial) -/
theorem summable_real_matrix_pow_of_complex_spectralRadius_lt_one {A : Matrix n n ℝ}
    (hA : spectralRadius ℂ (A.map Complex.ofReal) < 1) : Summable (fun k : ℕ => A ^ k) := by
  let C := A.map Complex.ofReal
  have hρ : (spectralRadius ℂ C).toReal < 1 :=
    (ENNReal.toReal_lt_toReal (matrix_spectralRadius_ne_top C) ENNReal.one_ne_top).mpr hA
  let r : ℝ := ((spectralRadius ℂ C).toReal + 1) / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hρr : (spectralRadius ℂ C).toReal < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  obtain ⟨N, hN⟩ := exists_prefix_norm_matrix_pow_le_growth C hr hρr
  apply Summable.of_norm_bounded ((summable_geometric_of_lt_one hr.le hr1).mul_left
    (matrixPowerBoundConstant C r N))
  intro k
  rw [← specNorm_eq_norm]
  have hh := specNorm_le_norm_map_ofReal (A ^ k)
  rw [map_ofReal_matrix_pow] at hh
  exact hh.trans (hN k)

/-- The real Neumann series has the exact real inverse as its sum when the
complex spectral radius is below one. Source: Horn–Johnson (2013),
Corollary 5.6.13; no real norm-below-one assumption is imposed.
atlas: matrix-power-convergence (partial) -/
theorem hasSum_real_matrix_pow_inv_of_complex_spectralRadius_lt_one {A : Matrix n n ℝ}
    (hA : spectralRadius ℂ (A.map Complex.ofReal) < 1) : HasSum (fun k : ℕ => A ^ k) (1 - A)⁻¹ := by
  have hs := summable_real_matrix_pow_of_complex_spectralRadius_lt_one hA
  have hp := (tendsto_real_matrix_pow_zero_iff_complex_spectralRadius_lt_one A).mpr hA
  have hleft : Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, A ^ k) * (1 - A))
      atTop (𝓝 ((∑' k : ℕ, A ^ k) * (1 - A))) :=
    hs.hasSum.tendsto_sum_nat.mul_const (1 - A)
  have hright : Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, A ^ k) * (1 - A))
      atTop (𝓝 1) := by
    simp only [geom_sum_mul_neg]
    simpa only [sub_zero] using tendsto_const_nhds.sub hp
  have hInv : (∑' k : ℕ, A ^ k) * (1 - A) = 1 := tendsto_nhds_unique hleft hright
  have hsum : (∑' k : ℕ, A ^ k) = (1 - A)⁻¹ := (Matrix.inv_eq_left_inv hInv).symm
  rw [← hsum]
  exact hs.hasSum

end NLAlib
