import NLAlib.Gaussian.SimpleSpectrum
import NLAlib.Matrix.InversePowerLimit
import NLAlib.Matrix.GramSoftMinSpectral
import NLAlib.Matrix.SpectralMinimum

/-!
# Gaussian regularized soft minimum and derivative aggregate limits

Inverse-power spectral weights concentrate at the unique minimum Gram
eigenvector. Their scalar trace pairings give the exact gradient energy
and Euler contraction limits used in the Gaussian Stein argument.

Source: operator hard-edge derivation; atlas `wishart-lambda-min-tail`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology Matrix Matrix.Norms.L2Operator

namespace NLAlib

/-- The value and both first-derivative aggregates of a regularized Gram
soft minimum converge at a unique maximal inverse eigenvalue.
Source: operator hard-edge proof and normalized inverse-power weights;
atlas `wishart-lambda-min-tail` (fixed-matrix approximation helper). -/
theorem tendsto_regularizedGram_softMin_aggregates_of_unique_max
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (ε : ℝ) (G : Matrix ι κ ℝ) (hpd : (regularizedGram ε G).PosDef) (i₀ : ι)
    (hmax : ∀ i, i ≠ i₀ → hpd.inv.isHermitian.eigenvalues i <
      hpd.inv.isHermitian.eigenvalues i₀) :
    Tendsto (fun n : ℕ => inversePowerSoftMin n (regularizedGram ε G)) atTop
        (𝓝 (hpd.inv.isHermitian.eigenvalues i₀)⁻¹) ∧
      Tendsto (fun n : ℕ => frobSq (gramSoftMinGradient n ε G)) atTop
        (𝓝 (4 * ((hpd.inv.isHermitian.eigenvalues i₀)⁻¹ - ε))) ∧
      Tendsto (fun n : ℕ => frobInner G (gramSoftMinGradient n ε G)) atTop
        (𝓝 (2 * ((hpd.inv.isHermitian.eigenvalues i₀)⁻¹ - ε))) := by
  let b := hpd.inv.isHermitian.eigenvalues
  let l := fun i => (b i)⁻¹ - ε
  have hPi (i : ι) : Tendsto (fun n : ℕ =>
      (∑ j, b j ^ n) ^ (-(n : ℝ)⁻¹ - 1) * b i ^ (n + 1)) atTop
      (𝓝 (if i = i₀ then 1 else 0)) :=
    tendsto_sum_pow_rpow_mul_pow_succ_of_unique_max b i₀ (hpd.inv.eigenvalues_pos i₀)
      (fun i => (hpd.inv.eigenvalues_pos i).le) hmax i
  have hE := (tendsto_finsetSum Finset.univ (fun i _ =>
    (hPi i).const_mul (l i))).const_mul 2
  have hA := (tendsto_finsetSum Finset.univ (fun i _ =>
    ((hPi i).pow 2).const_mul (l i))).const_mul 4
  refine ⟨tendsto_inversePowerSoftMin_of_unique_max hpd i₀ hmax, ?_, ?_⟩
  · simp_rw [frobSq_gramSoftMinGradient_eq_spectral _ _ _ hpd]
    simpa only [ite_pow, one_pow, zero_pow (by omega : (2 : ℕ) ≠ 0), mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hA
  · simp_rw [frobInner_gramSoftMinGradient_eq_spectral _ _ _ hpd]
    simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] using hE

/-- The Gaussian regularized soft minimum converges to the true squared
smallest singular value plus the regularizer, while its gradient energy
and Euler contraction converge to four and two times the unregularized
value. Source: operator hard-edge proof; atlas `wishart-lambda-min-tail`.
All simple-spectrum and unique-max conditions are discharged almost surely. -/
theorem ae_tendsto_regularizedGram_softMin_aggregates_gaussianMatrix
    {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ G ∂(gaussianMatrix r k),
      Tendsto (fun n : ℕ => inversePowerSoftMin n (regularizedGram ε (Matrix.of G)))
        atTop (𝓝 (sigmaMin (Matrix.of G)ᵀ ^ 2 + ε)) ∧
      Tendsto (fun n : ℕ => frobSq (gramSoftMinGradient n ε (Matrix.of G)))
        atTop (𝓝 (4 * sigmaMin (Matrix.of G)ᵀ ^ 2)) ∧
      Tendsto (fun n : ℕ => frobInner (Matrix.of G) (gramSoftMinGradient n ε (Matrix.of G)))
        atTop (𝓝 (2 * sigmaMin (Matrix.of G)ᵀ ^ 2)) := by
  filter_upwards [ae_exists_unique_max_eigenvalues_inv_regularizedGram_gaussianMatrix
    hr hrk ε hε] with G hG
  obtain ⟨i₀, hmax⟩ := hG
  let hpd := regularizedGram_posDef hε (Matrix.of G)
  have hle (i : Fin r) : hpd.inv.isHermitian.eigenvalues i ≤
      hpd.inv.isHermitian.eigenvalues i₀ := by
    by_cases hi : i = i₀
    · simpa only [hi] using le_rfl
    · exact (hmax i hi).le
  have hX := sigmaMin_transpose_sq_eq_inv_inverse_eigenvalue_sub ε (Matrix.of G) hpd i₀ hle
  obtain ⟨hF, hA, hB⟩ :=
    tendsto_regularizedGram_softMin_aggregates_of_unique_max ε (Matrix.of G) hpd i₀ hmax
  have hXadd : (hpd.inv.isHermitian.eigenvalues i₀)⁻¹ = sigmaMin (Matrix.of G)ᵀ ^ 2 + ε := by
    linarith
  rw [hXadd] at hF
  rw [← hX] at hA hB
  exact ⟨hF, hA, hB⟩

end NLAlib
