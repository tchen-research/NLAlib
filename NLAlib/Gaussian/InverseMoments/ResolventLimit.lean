import NLAlib.Gaussian.SimpleSpectrum
import NLAlib.Matrix.InversePowerLaplacianLimit
import NLAlib.Matrix.GramSoftMinSpectral

/-!
# Sharp almost-sure resolvent Laplacian limit

Almost-sure simple Gaussian Gram spectrum discharges the unique top
inverse-eigenvalue conditions in the scalar soft minimum limit. The exact
limiting Laplacian is bounded by `2(k-r+1)`.

Source: resolvent operator hard-edge proof; atlas `wishart-lambda-min-tail`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology Matrix Matrix.Norms.L2Operator

namespace NLAlib

/-- The regularized Gaussian Gram soft minimum has an almost-sure finite
Laplacian limit bounded by the exact hard-edge coefficient.
Source: operator hard-edge proof, scalar inverse-power cancellation;
atlas `wishart-lambda-min-tail`. All simplicity and unique-max conditions
are discharged by the Gaussian polynomial zero-set argument. -/
theorem ae_exists_tendsto_gramSoftMinLaplacian_le_gaussianMatrix
    {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ G ∂(gaussianMatrix r k), ∃ L : ℝ, L ≤ 2 * ((k : ℝ) - r + 1) ∧
      Tendsto (fun n : ℕ => gramSoftMinLaplacian n ε (Matrix.of G)) atTop (𝓝 L) := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  filter_upwards [ae_injective_eigenvalues_inv_regularizedGram_gaussianMatrix hrk ε hε,
    ae_exists_unique_max_eigenvalues_inv_regularizedGram_gaussianMatrix hr hrk ε hε]
    with G hbinj hmaxex
  obtain ⟨i₀, hmax⟩ := hmaxex
  let hpd := regularizedGram_posDef hε (Matrix.of G)
  let b : Fin r → ℝ := hpd.inv.isHermitian.eigenvalues
  let b₀ : ℝ := b i₀
  let ρ : Fin r → ℝ := fun i => b i / b₀
  let w : Fin r → ℝ := fun i => (b i)⁻¹ - ε
  have hb (i : Fin r) : 0 < b i := hpd.inv.eigenvalues_pos i
  have hb₀ : 0 < b₀ := hb i₀
  have hρ₀ : ρ i₀ = 1 := div_self hb₀.ne'
  have hρ : ∀ i, i ≠ i₀ → 0 ≤ ρ i ∧ ρ i < 1 := fun i hi =>
    ⟨(div_pos (hb i) hb₀).le, (div_lt_one hb₀).2 (hmax i hi)⟩
  have hρinj : Function.Injective ρ := by
    intro i j hij
    apply hbinj
    have h := congrArg (fun x : ℝ => x * b₀) hij
    simpa only [ρ, div_mul_cancel₀ _ hb₀.ne'] using h
  have hw : ∀ i, 0 ≤ w i := by
    let U := hpd.inv.isHermitian.eigenvectorUnitary
    let φ := Unitary.conjStarAlgAut ℝ (Matrix (Fin r) (Fin r) ℝ) (star U)
    have hW : (Matrix.of G * (Matrix.of G)ᵀ).PosSemidef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.posSemidef_self_mul_conjTranspose (Matrix.of G)
    have hconj : (φ (Matrix.of G * (Matrix.of G)ᵀ)).PosSemidef := by
      simpa only [φ, Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using
        hW.conjTranspose_mul_mul_same (U : Matrix (Fin r) (Fin r) ℝ)
    have hdiag : φ (Matrix.of G * (Matrix.of G)ᵀ) = Matrix.diagonal w :=
      regularizedGram_inv_basis_conj_eq ε (Matrix.of G) hpd
    rw [hdiag, Matrix.posSemidef_diagonal_iff] at hconj
    exact hconj
  have hrel : ∀ j, j ≠ i₀ → b₀ * ρ j * (w j - w i₀) = 1 - ρ j := by
    intro j _
    dsimp only [ρ, w, b₀]
    field_simp [(hb j).ne', (hb i₀).ne']
    ring
  let L : ℝ := 2 * k - b₀ *
    ∑ i, ∑ j ∈ Finset.univ.erase i, (w i + w j) * ρ i * ρ j *
      (((if j = i₀ then 1 else 0) - (if i = i₀ then 1 else 0)) / (ρ j - ρ i))
  have hL : L ≤ 2 * ((k : ℝ) - r + 1) := by
    simpa only [Fintype.card_fin] using
      normalized_inverse_power_laplacian_symmetric_limit_le ρ w i₀ hρ₀ hρ b₀ k
        hb₀.le (hw i₀) hrel
  have ht := tendsto_normalized_inverse_power_laplacian_symmetric
    ρ w i₀ hρ₀ hρ hρinj b₀ k
  refine ⟨L, hL, ?_⟩
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  simpa only [Fintype.card_fin] using
    (gramSoftMinLaplacian_eq_normalized n hn ε (Matrix.of G) hpd b₀ hb₀).symm

end NLAlib
