import NLAlib.LowRank.RandomStartPower
import NLAlib.LowRank.RandomStartLanczos

/-!
# Exact random-start endpoints

Both actual methods are exact almost surely in dimension one. Both relative
errors are zero for the zero matrix by the manuscript's totalized convention.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

/-- Every power iterate has zero relative error for the zero matrix.
Source: manuscript `rt:random-start`, zero-matrix convention. -/
@[simp] theorem powerRayleighRelativeError_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) (q : ℕ) : powerRayleighRelativeError (0 : Matrix ι ι ℝ) b q = 0 := by
  simp only [powerRayleighRelativeError, specNorm_zero, div_zero]

/-- Every Lanczos step has zero relative error for the zero matrix.
Source: manuscript `rt:random-start`, zero-matrix convention. -/
@[simp] theorem lanczosRayleighRelativeError_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) (q : ℕ) : lanczosRayleighRelativeError (0 : Matrix ι ι ℝ) b q = 0 := by
  simp only [lanczosRayleighRelativeError, specNorm_zero, div_zero]

private theorem singleton_top_eigenvalue {A : Matrix (Fin 1) (Fin 1) ℝ} (hA : A.PosSemidef) :
    hA.isHermitian.eigenvalues 0 = specNorm A := by
  obtain ⟨i, hi⟩ := (IsGreatest.pi_norm hA.isHermitian.eigenvalues).1
  have hi0 : i = 0 := Fin.eq_zero i
  subst i
  dsimp only at hi
  rw [specNorm_eq_norm_eigenvalues hA.isHermitian, ← hi,
    Real.norm_of_nonneg (hA.eigenvalues_nonneg 0)]

/-- A nonzero top-coordinate start gives exact power iteration in dimension one,
including the initial Rayleigh quotient `q=0`. Source: manuscript `rt:random-start`.
atlas: random-start-power -/
theorem powerRayleighRelativeError_singleton_eq_zero {A : Matrix (Fin 1) (Fin 1) ℝ}
    (hA : A.PosSemidef) (b : Fin 1 → ℝ)
    (hb : (hA.isHermitian.eigenvectorBasis 0 : Fin 1 → ℝ) ⬝ᵥ b ≠ 0) (q : ℕ) :
    powerRayleighRelativeError A b q = 0 := by
  by_cases hL : specNorm A = 0
  · simp only [powerRayleighRelativeError, hL, div_zero]
  · have hLp : 0 < specNorm A := (specNorm_nonneg A).lt_of_ne (Ne.symm hL)
    have he := sub_rayleighQuotient_pow_div_specNorm_le_log_overlap_div hA hLp 0
      (singleton_top_eigenvalue hA) b hb q
    have hp : b ⬝ᵥ b = ((hA.isHermitian.eigenvectorBasis 0 : Fin 1 → ℝ) ⬝ᵥ b) ^ 2 := by
      have hs := sum_sq_eigenvectorBasis_dotProduct hA.isHermitian b
      simpa only [Fin.sum_univ_one] using hs.symm
    rw [hp, div_self (pow_ne_zero 2 hb), Real.log_one, zero_div] at he
    exact le_antisymm he (powerRayleighRelativeError_bounds hA b q).1

/-- A nonzero top-coordinate start gives exact Lanczos in dimension one at every
positive step count. Source: manuscript `rt:random-start`.
atlas: random-start-power -/
theorem lanczosRayleighRelativeError_singleton_eq_zero {A : Matrix (Fin 1) (Fin 1) ℝ}
    (hA : A.PosSemidef) (b : Fin 1 → ℝ)
    (hb : (hA.isHermitian.eigenvectorBasis 0 : Fin 1 → ℝ) ⬝ᵥ b ≠ 0)
    {q : ℕ} (hq : 1 ≤ q) : lanczosRayleighRelativeError A b q = 0 := by
  have hp : b ⬝ᵥ b = ((hA.isHermitian.eigenvectorBasis 0 : Fin 1 → ℝ) ⬝ᵥ b) ^ 2 := by
    have hs := sum_sq_eigenvectorBasis_dotProduct hA.isHermitian b
    simpa only [Fin.sum_univ_one] using hs.symm
  have hbb : b ⬝ᵥ b ≠ 0 := by rw [hp]; exact pow_ne_zero 2 hb
  have hRQ : (Matrix.toEuclideanCLM (𝕜 := ℝ) A).rayleighQuotient (WithLp.toLp 2 b) = specNorm A := by
    rw [rayleighQuotient_toEuclideanCLM_eq]
    have hs := quadForm_eq_sum_eigenvalues hA.isHermitian b
    simp only [Fin.sum_univ_one, singleton_top_eigenvalue hA] at hs
    change b ⬝ᵥ (A *ᵥ b) = specNorm A *
      ((hA.isHermitian.eigenvectorBasis 0 : Fin 1 → ℝ) ⬝ᵥ b) ^ 2 at hs
    rw [hs, ← hp, mul_div_cancel_right₀ _ hbb]
  have hbK : b ∈ krylovSpace A b q := by
    have he : q = (q - 1) + 1 := by omega
    rw [he]
    exact self_mem_krylovSpace_succ A b (q - 1)
  have hComp := rayleighQuotient_le_lanczosRitzValue_of_mem hA b q hbK
  rw [hRQ] at hComp
  have hEq := le_antisymm (lanczosRitzValue_bounds hA b q).2 hComp
  simp only [lanczosRayleighRelativeError, hEq, sub_self, zero_div]

/-- Both random-start algorithms are exact almost surely in dimension one.
Source: manuscript `rt:random-start`, scalar Gaussian atomlessness.
atlas: random-start-power -/
theorem ae_power_and_lanczos_singleton_eq_zero_pi_gaussianReal
    (A : Matrix (Fin 1) (Fin 1) ℝ) (hA : A.PosSemidef) (p : ℕ) {q : ℕ} (hq : 1 ≤ q) :
    ∀ᵐ b ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1),
      powerRayleighRelativeError A b p = 0 ∧ lanczosRayleighRelativeError A b q = 0 := by
  filter_upwards [ae_eigenvectorBasis_dotProduct_ne_zero_pi_gaussianReal hA.isHermitian 0]
    with b hb
  exact ⟨powerRayleighRelativeError_singleton_eq_zero hA b hb p,
    lanczosRayleighRelativeError_singleton_eq_zero hA b hb hq⟩

end NLAlib
