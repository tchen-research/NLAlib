import NLAlib.Krylov.Spectral.RayleighQuotientGeometry

/-!
# The extremal-eigenvalue variant of RQI

At a simple smallest or largest eigenvalue the signed spectral errors cannot cancel. This
precludes a singular nonterminal shift in the local neighborhood, and upgrades cubic
eigenvector-line convergence to cubic Rayleigh-quotient convergence.
Source: Trefethen–Bau (1997), Lecture 27, finite spectral proof with explicit constants.
-/

noncomputable section
open scoped Matrix
open Matrix

namespace NLAlib.RayleighQuotientIteration

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
variable {A : Matrix n n 𝕜}

/-- At an extremal target eigenvalue, the Rayleigh quotient error bounds the off-axis
weight from below by the spectral gap. -/
theorem gap_mul_tangentSq_div_le_abs_rayleighQuotient_sub (hA : A.IsHermitian)
    {i : n} {g : ℝ}
    (hgap : ∀ j, j ≠ i → g ≤ |hA.eigenvalues j - hA.eigenvalues i|)
    (hextreme : (∀ j, hA.eigenvalues i ≤ hA.eigenvalues j) ∨
      (∀ j, hA.eigenvalues j ≤ hA.eigenvalues i))
    {x : n → 𝕜} (hx : hA.eigenvectorCoordinates x i ≠ 0) :
    g * tangentSq hA i x / (1 + tangentSq hA i x) ≤
      |rayleighQuotient A x - hA.eigenvalues i| := by
  rcases hextreme with hmin | hmax
  · have hl (j : n) (hj : j ≠ i) : g ≤ hA.eigenvalues j - hA.eigenvalues i := by
      simpa only [abs_of_nonneg (sub_nonneg.mpr (hmin j))] using hgap j hj
    have h := gap_mul_weight_ratio_le_weighted_average_sub
      (fun j => sq_nonneg ‖hA.eigenvectorCoordinates x j‖)
      (sq_pos_of_pos (norm_pos_iff.mpr hx)) hl
    rw [← hA.rayleighQuotient_eq_sum_eigenvectorCoordinates] at h
    exact h.trans (le_abs_self _)
  · have hl (j : n) (hj : j ≠ i) :
        g ≤ -hA.eigenvalues j - -hA.eigenvalues i := by
      have h := hgap j hj
      rw [abs_of_nonpos (sub_nonpos.mpr (hmax j))] at h
      linarith
    have h := gap_mul_weight_ratio_le_weighted_average_sub
      (fun j => sq_nonneg ‖hA.eigenvectorCoordinates x j‖)
      (sq_pos_of_pos (norm_pos_iff.mpr hx)) hl
    simp only [neg_mul, Finset.sum_neg_distrib, neg_div] at h
    rw [← hA.rayleighQuotient_eq_sum_eigenvectorCoordinates] at h
    have ha := neg_le_abs (rayleighQuotient A x - hA.eigenvalues i)
    change g * tangentSq hA i x / (1 + tangentSq hA i x) ≤ _ at h
    linarith

/-- Every nonterminal local iterate for a simple extremal eigenvalue has a nonsingular
shift. Thus the algorithm cannot break down in this variant.
atlas: rayleigh-quotient-iteration (partial) -/
theorem eigenvalues_ne_rayleighQuotient_of_extremal (hA : A.IsHermitian) {i : n} {g M : ℝ}
    (hg : 0 < g) (hM : 0 < M)
    (hgap : ∀ j, j ≠ i → g ≤ |hA.eigenvalues j - hA.eigenvalues i|)
    (hdiam : ∀ j, j ≠ i → |hA.eigenvalues j - hA.eigenvalues i| ≤ M)
    (hextreme : (∀ j, hA.eigenvalues i ≤ hA.eigenvalues j) ∨
      (∀ j, hA.eigenvalues j ≤ hA.eigenvalues i))
    {x : n → 𝕜} (hx : hA.eigenvectorCoordinates x i ≠ 0)
    (hlocal : tangentSq hA i x ≤ g / (4 * M))
    (hnot : A *ᵥ x ≠ rayleighQuotient A x • x) :
    ∀ j, hA.eigenvalues j ≠ rayleighQuotient A x := by
  have herr := abs_rayleighQuotient_sub_le hA hdiam hx
  have heg := error_le_gap_div_four hg hM (tangentSq_nonneg hA i x) hlocal herr
  have hlow := gap_mul_tangentSq_div_le_abs_rayleighQuotient_sub hA hgap hextreme hx
  have hq := tangentSq_pos_of_not_eigenvector hA hx hnot
  have hepos : 0 < |rayleighQuotient A x - hA.eigenvalues i| :=
    lt_of_lt_of_le (by positivity) hlow
  intro j hj
  by_cases hji : j = i
  · subst j
    rw [← hj, sub_self, abs_zero] at hepos
    exact lt_irrefl _ hepos
  · have hgj := hgap j hji
    rw [hj] at hgj
    linarith

/-- Explicit scalar cubic convergence at a smallest or largest simple eigenvalue:
`|ρ(x₊)-λ| ≤ (8 M/g³)|ρ(x)-λ|³`. The inverse step is justified by the preceding theorem.
atlas: rayleigh-quotient-iteration (partial) -/
theorem abs_rayleighQuotient_step_sub_le_cube_of_extremal (hA : A.IsHermitian)
    {i : n} {g M : ℝ} (hg : 0 < g) (hgM : g ≤ M)
    (hgap : ∀ j, j ≠ i → g ≤ |hA.eigenvalues j - hA.eigenvalues i|)
    (hdiam : ∀ j, j ≠ i → |hA.eigenvalues j - hA.eigenvalues i| ≤ M)
    (hextreme : (∀ j, hA.eigenvalues i ≤ hA.eigenvalues j) ∨
      (∀ j, hA.eigenvalues j ≤ hA.eigenvalues i))
    {x : n → 𝕜} (hx : hA.eigenvectorCoordinates x i ≠ 0)
    (hlocal : tangentSq hA i x ≤ g / (4 * M))
    (hnot : A *ᵥ x ≠ rayleighQuotient A x • x) :
    |rayleighQuotient A (step A x) - hA.eigenvalues i| ≤
      (8 * M / g ^ 3) * |rayleighQuotient A x - hA.eigenvalues i| ^ 3 := by
  have hM : 0 < M := hg.trans_le hgM
  have hμ := eigenvalues_ne_rayleighQuotient_of_extremal hA hg hM hgap hdiam
    hextreme hx hlocal hnot
  have hx' := (step_norm_and_coordinates_ne_zero hA hx hμ).2.1
  have herr := abs_rayleighQuotient_sub_le hA hdiam hx
  have heg := error_le_gap_div_four hg hM (tangentSq_nonneg hA i x) hlocal herr
  let e := |rayleighQuotient A x - hA.eigenvalues i|
  have hge : 0 < g - e := by dsimp [e]; linarith
  have hsep : ∀ j, j ≠ i → g - e ≤ |hA.eigenvalues j - rayleighQuotient A x| := by
    intro j hj
    have ht := abs_sub_le (hA.eigenvalues j) (rayleighQuotient A x) (hA.eigenvalues i)
    have hjg := hgap j hj
    dsimp [e]
    linarith
  have hstep := tangentSq_inverse_le hA hμ hge hsep hx
  rw [← (step_norm_and_coordinates_ne_zero hA hx hμ).2.2,
    abs_sub_comm (hA.eigenvalues i)] at hstep
  have hqone : tangentSq hA i x ≤ 1 := by
    have hb := (le_div_iff₀ (show 0 < 4 * M by positivity)).mp hlocal
    nlinarith
  have herr' : |rayleighQuotient A (step A x) - hA.eigenvalues i| ≤
      M * tangentSq hA i (step A x) := by
    apply (abs_rayleighQuotient_sub_le hA hdiam hx').trans
    have hq := tangentSq_nonneg hA i (step A x)
    apply (div_le_iff₀ (show 0 < 1 + tangentSq hA i (step A x) by positivity)).2
    nlinarith [mul_nonneg (mul_nonneg hM.le hq) hq]
  exact error_step_le_cube hg hM.le (tangentSq_nonneg hA i x) (abs_nonneg _) hqone heg
    (gap_mul_tangentSq_div_le_abs_rayleighQuotient_sub hA hgap hextreme hx) hstep herr'

end NLAlib.RayleighQuotientIteration
