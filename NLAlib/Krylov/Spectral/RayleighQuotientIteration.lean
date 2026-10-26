import NLAlib.Matrix.Spectral.EigenvectorCoordinates
import NLAlib.Krylov.Spectral.RayleighQuotientWeights

/-!
# Hermitian Rayleigh quotient iteration

The actual normalized shifted inverse step over both `ℝ` and `ℂ`. The local estimates are
for the line of a simple eigenvector. A singular shift at a noneigenvector is a breakdown,
not a successful iteration or a kernel-projection continuation.

Source: Trefethen–Bau (1997), Lecture 27; Parlett (1998), §4.6.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib.RayleighQuotientIteration

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
variable {A : Matrix n n 𝕜}

/-- Squared tangent to the line of the selected eigenbasis vector, computed in orthonormal
coordinates. The meaningful domain has a nonzero selected coordinate. -/
def tangentSq (hA : A.IsHermitian) (i : n) (x : n → 𝕜) : ℝ :=
  (∑ j ∈ Finset.univ.erase i, ‖hA.eigenvectorCoordinates x j‖ ^ 2) /
    ‖hA.eigenvectorCoordinates x i‖ ^ 2

/-- The tangent to the selected eigenvector line, on the nonzero-overlap domain. -/
def tangent (hA : A.IsHermitian) (i : n) (x : n → 𝕜) : ℝ :=
  Real.sqrt (tangentSq hA i x)

/-- The normalized Rayleigh quotient inverse step. It is used only for invertible shifts;
the totalized value at a singular shift does not constitute an iteration step. -/
def step (A : Matrix n n 𝕜) (x : n → 𝕜) : n → 𝕜 :=
  let y := (A - rayleighQuotient A x • (1 : Matrix n n 𝕜))⁻¹ *ᵥ x
  ((‖WithLp.toLp 2 y‖⁻¹ : ℝ) : 𝕜) • y

/-- Squared tangents are nonnegative. -/
theorem tangentSq_nonneg (hA : A.IsHermitian) (i : n) (x : n → 𝕜) :
    0 ≤ tangentSq hA i x := by unfold tangentSq; positivity

/-- The squared tangent is the square of the nonnegative tangent. -/
theorem tangent_sq (hA : A.IsHermitian) (i : n) (x : n → 𝕜) :
    tangent hA i x ^ 2 = tangentSq hA i x :=
  Real.sq_sqrt (tangentSq_nonneg hA i x)

/-- Nonzero scalar multiplication preserves the eigenvector line angle. -/
theorem tangentSq_smul (hA : A.IsHermitian) (i : n) (x : n → 𝕜)
    {c : 𝕜} (hc : c ≠ 0) : tangentSq hA i (c • x) = tangentSq hA i x := by
  simp only [tangentSq, hA.eigenvectorCoordinates_smul, Pi.smul_apply, norm_smul,
    mul_pow, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hc))

/-- The exact quadratic Rayleigh error bound, with denominator `1 + tan² θ`, for real
symmetric or complex Hermitian matrices. The selected spectral coordinate must be nonzero.
atlas: rayleigh-quotient-iteration (partial) -/
theorem abs_rayleighQuotient_sub_le (hA : A.IsHermitian) {i : n} {M : ℝ}
    (hM : ∀ j, j ≠ i → |hA.eigenvalues j - hA.eigenvalues i| ≤ M)
    {x : n → 𝕜} (hx : hA.eigenvectorCoordinates x i ≠ 0) :
    |rayleighQuotient A x - hA.eigenvalues i| ≤
      M * tangentSq hA i x / (1 + tangentSq hA i x) := by
  rw [hA.rayleighQuotient_eq_sum_eigenvectorCoordinates]
  exact abs_weighted_average_sub_le (fun _ => sq_nonneg _)
    (sq_pos_of_pos (norm_pos_iff.mpr hx)) hM

/-- A nonzero selected coordinate stays nonzero under a nonsingular shifted inverse. -/
theorem eigenvectorCoordinates_inverse_ne_zero (hA : A.IsHermitian) {i : n} {μ : ℝ}
    (hμ : ∀ j, hA.eigenvalues j ≠ μ) {x : n → 𝕜}
    (hx : hA.eigenvectorCoordinates x i ≠ 0) :
    hA.eigenvectorCoordinates ((A - μ • (1 : Matrix n n 𝕜))⁻¹ *ᵥ x) i ≠ 0 := by
  rw [hA.eigenvectorCoordinates_inv_sub_smul_mulVec hμ]
  exact mul_ne_zero (inv_ne_zero (RCLike.ofReal_ne_zero.mpr (sub_ne_zero.mpr (hμ i)))) hx

/-- The finite spectral estimate for the squared tangent under an actual shifted inverse.
The lower separation `d` may be chosen as the spectral gap minus the shift error. -/
theorem tangentSq_inverse_le (hA : A.IsHermitian) {i : n} {μ d : ℝ}
    (hμ : ∀ j, hA.eigenvalues j ≠ μ) (hd : 0 < d)
    (hsep : ∀ j, j ≠ i → d ≤ |hA.eigenvalues j - μ|)
    {x : n → 𝕜} (hx : hA.eigenvectorCoordinates x i ≠ 0) :
    tangentSq hA i ((A - μ • (1 : Matrix n n 𝕜))⁻¹ *ᵥ x) ≤
      (|hA.eigenvalues i - μ| / d) ^ 2 * tangentSq hA i x := by
  have hw (j : n) : ‖hA.eigenvectorCoordinates
      ((A - μ • (1 : Matrix n n 𝕜))⁻¹ *ᵥ x) j‖ ^ 2 =
        ‖hA.eigenvectorCoordinates x j‖ ^ 2 / (hA.eigenvalues j - μ) ^ 2 := by
    rw [hA.eigenvectorCoordinates_inv_sub_smul_mulVec hμ, norm_mul, norm_inv,
      RCLike.norm_ofReal, mul_pow, inv_pow, sq_abs]
    exact (div_eq_inv_mul _ _).symm
  simp only [tangentSq, hw]
  exact inverse_weight_ratio_le (fun _ => sq_nonneg _)
    (sq_pos_of_pos (norm_pos_iff.mpr hx)) (sub_ne_zero.mpr (hμ i)) hd hsep

/-- Normalizing a valid inverse step gives a unit vector with nonzero target overlap and
does not change the tangent. This establishes that the actual RQI step is well-defined.
atlas: rayleigh-quotient-iteration (partial) -/
theorem step_norm_and_coordinates_ne_zero (hA : A.IsHermitian) {i : n} {x : n → 𝕜}
    (hx : hA.eigenvectorCoordinates x i ≠ 0)
    (hμ : ∀ j, hA.eigenvalues j ≠ rayleighQuotient A x) :
    ‖WithLp.toLp 2 (step A x)‖ = 1 ∧
      hA.eigenvectorCoordinates (step A x) i ≠ 0 ∧
      tangentSq hA i (step A x) =
        tangentSq hA i ((A - rayleighQuotient A x • (1 : Matrix n n 𝕜))⁻¹ *ᵥ x) := by
  let y := (A - rayleighQuotient A x • (1 : Matrix n n 𝕜))⁻¹ *ᵥ x
  have hy := eigenvectorCoordinates_inverse_ne_zero hA hμ hx
  have hy0 : y ≠ 0 := by
    intro hz
    apply hy
    change hA.eigenvectorCoordinates y i = 0
    rw [hz]
    simp [Matrix.IsHermitian.eigenvectorCoordinates]
  have hn : ‖WithLp.toLp 2 y‖ ≠ 0 := norm_ne_zero_iff.mpr (by
    intro hz
    apply hy0
    exact congrArg WithLp.ofLp hz)
  have hc : ((‖WithLp.toLp 2 y‖⁻¹ : ℝ) : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (inv_ne_zero hn)
  change ‖WithLp.toLp 2 (((‖WithLp.toLp 2 y‖⁻¹ : ℝ) : 𝕜) • y)‖ = 1 ∧ _
  refine ⟨?_, ?_, tangentSq_smul hA i y hc⟩
  · rw [WithLp.toLp_smul, norm_smul, RCLike.norm_ofReal,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hn]
  · change hA.eigenvectorCoordinates (((‖WithLp.toLp 2 y‖⁻¹ : ℝ) : 𝕜) • y) i ≠ 0
    rw [hA.eigenvectorCoordinates_smul]
    exact mul_ne_zero hc hy

/-- Local cubic contraction for the squared angle of the actual normalized inverse step.
The constants use any positive lower gap and upper spectral spread; hence apply to the
minimum and maximum spectral distances in the atlas card.
atlas: rayleigh-quotient-iteration (partial) -/
theorem tangentSq_step_le (hA : A.IsHermitian) {i : n} {g M : ℝ}
    (hg : 0 < g) (hM : 0 < M)
    (hgap : ∀ j, j ≠ i → g ≤ |hA.eigenvalues j - hA.eigenvalues i|)
    (hdiam : ∀ j, j ≠ i → |hA.eigenvalues j - hA.eigenvalues i| ≤ M)
    {x : n → 𝕜} (hx : hA.eigenvectorCoordinates x i ≠ 0)
    (hlocal : tangentSq hA i x ≤ g / (4 * M))
    (hμ : ∀ j, hA.eigenvalues j ≠ rayleighQuotient A x) :
    tangentSq hA i (step A x) ≤ (2 * M / g) ^ 2 * tangentSq hA i x ^ 3 ∧
      tangentSq hA i (step A x) ≤ tangentSq hA i x / 4 := by
  let e := |rayleighQuotient A x - hA.eigenvalues i|
  have herr := abs_rayleighQuotient_sub_le hA hdiam hx
  have heg := error_le_gap_div_four hg hM (tangentSq_nonneg hA i x) hlocal herr
  have hge : 0 < g - e := by dsimp [e]; linarith
  have hsep : ∀ j, j ≠ i → g - e ≤ |hA.eigenvalues j - rayleighQuotient A x| := by
    intro j hj
    have htri := abs_sub_le (hA.eigenvalues j) (rayleighQuotient A x) (hA.eigenvalues i)
    have hgj := hgap j hj
    dsimp [e]
    linarith
  have hs := tangentSq_inverse_le hA hμ hge hsep hx
  rw [← (step_norm_and_coordinates_ne_zero hA hx hμ).2.2] at hs
  rw [abs_sub_comm (hA.eigenvalues i)] at hs
  exact tangent_sq_cubic_le hg hM (tangentSq_nonneg hA i x) (abs_nonneg _) hlocal herr hs

/-- Local cubic convergence of the eigenvector-line angle, and the explicit one-half
contraction, for the actual real or complex Hermitian RQI step.
atlas: rayleigh-quotient-iteration (partial) -/
theorem tangent_step_le (hA : A.IsHermitian) {i : n} {g M : ℝ}
    (hg : 0 < g) (hM : 0 < M)
    (hgap : ∀ j, j ≠ i → g ≤ |hA.eigenvalues j - hA.eigenvalues i|)
    (hdiam : ∀ j, j ≠ i → |hA.eigenvalues j - hA.eigenvalues i| ≤ M)
    {x : n → 𝕜} (hx : hA.eigenvectorCoordinates x i ≠ 0)
    (hlocal : tangentSq hA i x ≤ g / (4 * M))
    (hμ : ∀ j, hA.eigenvalues j ≠ rayleighQuotient A x) :
    tangent hA i (step A x) ≤ (2 * M / g) * tangent hA i x ^ 3 ∧
      tangent hA i (step A x) ≤ tangent hA i x / 2 := by
  have hs := tangentSq_step_le hA hg hM hgap hdiam hx hlocal hμ
  have ht : 0 ≤ tangent hA i x := Real.sqrt_nonneg _
  have ht' : 0 ≤ tangent hA i (step A x) := Real.sqrt_nonneg _
  have hsq := tangent_sq hA i x
  have hsq' := tangent_sq hA i (step A x)
  constructor
  · have hpos : 0 ≤ (2 * M / g) * tangent hA i x ^ 3 := by positivity
    have hpow : ((2 * M / g) * tangent hA i x ^ 3) ^ 2 =
        (2 * M / g) ^ 2 * tangentSq hA i x ^ 3 := by rw [← hsq]; ring
    nlinarith [hs.1]
  · nlinarith [hs.2]

/-- The local angle neighborhood is invariant under every valid normalized step.
atlas: rayleigh-quotient-iteration (partial) -/
theorem tangentSq_step_le_neighborhood (hA : A.IsHermitian) {i : n} {g M : ℝ}
    (hg : 0 < g) (hM : 0 < M)
    (hgap : ∀ j, j ≠ i → g ≤ |hA.eigenvalues j - hA.eigenvalues i|)
    (hdiam : ∀ j, j ≠ i → |hA.eigenvalues j - hA.eigenvalues i| ≤ M)
    {x : n → 𝕜} (hx : hA.eigenvectorCoordinates x i ≠ 0)
    (hlocal : tangentSq hA i x ≤ g / (4 * M))
    (hμ : ∀ j, hA.eigenvalues j ≠ rayleighQuotient A x) :
    tangentSq hA i (step A x) ≤ g / (4 * M) := by
  have hs := (tangentSq_step_le hA hg hM hgap hdiam hx hlocal hμ).2
  have hq := tangentSq_nonneg hA i x
  linarith

/-- Sixth-order Rayleigh quotient error from the incoming angle in one normalized RQI step.
atlas: rayleigh-quotient-iteration (partial) -/
theorem abs_rayleighQuotient_step_sub_le (hA : A.IsHermitian) {i : n} {g M : ℝ}
    (hg : 0 < g) (hM : 0 < M)
    (hgap : ∀ j, j ≠ i → g ≤ |hA.eigenvalues j - hA.eigenvalues i|)
    (hdiam : ∀ j, j ≠ i → |hA.eigenvalues j - hA.eigenvalues i| ≤ M)
    {x : n → 𝕜} (hx : hA.eigenvectorCoordinates x i ≠ 0)
    (hlocal : tangentSq hA i x ≤ g / (4 * M))
    (hμ : ∀ j, hA.eigenvalues j ≠ rayleighQuotient A x) :
    |rayleighQuotient A (step A x) - hA.eigenvalues i| ≤
      (4 * M ^ 3 / g ^ 2) * tangent hA i x ^ 6 := by
  have hx' := (step_norm_and_coordinates_ne_zero hA hx hμ).2.1
  have herr := abs_rayleighQuotient_sub_le hA hdiam hx'
  have hq := tangentSq_nonneg hA i (step A x)
  have he : |rayleighQuotient A (step A x) - hA.eigenvalues i| ≤
      M * tangentSq hA i (step A x) := by
    apply herr.trans
    apply (div_le_iff₀ (show 0 < 1 + tangentSq hA i (step A x) by positivity)).2
    nlinarith [mul_nonneg (mul_nonneg hM.le hq) hq]
  have h := error_le_tangent_sq_cube hM.le
    (tangentSq_step_le hA hg hM hgap hdiam hx hlocal hμ).1 he
  convert h using 1
  rw [← tangent_sq hA i x]
  ring

end NLAlib.RayleighQuotientIteration
