import NLAlib.Krylov.Spectral.RayleighQuotientIteration

/-!
# Geometric meaning of the RQI angle

The coordinate tangent is exactly the norm of the orthogonal residual divided by the
absolute overlap with any unit eigenvector for the selected simple eigenvalue. Consequently
the convergence theorem concerns an eigenvector line, independently of its sign or phase.
Source: Trefethen–Bau (1997), Lecture 27.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib.RayleighQuotientIteration

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
variable {A : Matrix n n 𝕜}

/-- The off-axis coordinate energy is exactly the squared orthogonal-residual norm. -/
theorem sum_sq_coordinates_erase_eq_norm_sub_sq (hA : A.IsHermitian) (i : n) (x : n → 𝕜) :
    (∑ j ∈ Finset.univ.erase i, ‖hA.eigenvectorCoordinates x j‖ ^ 2) =
      ‖WithLp.toLp 2 (x - hA.eigenvectorCoordinates x i • ⇑(hA.eigenvectorBasis i))‖ ^ 2 := by
  rw [← hA.sum_sq_norm_eigenvectorCoordinates,
    ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp only [hA.eigenvectorCoordinates_sub, hA.eigenvectorCoordinates_smul,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hA.eigenvectorCoordinates_eigenvectorBasis]
  simp only [ite_true, mul_one, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  simp [(Finset.mem_erase.mp hj).1]

/-- The coordinate tangent is the standard geometric tangent to the selected eigenvector
line. Both totalized expressions are zero at zero overlap; convergence uses nonzero overlap. -/
theorem tangent_eq_norm_sub_div (hA : A.IsHermitian) (i : n) (x : n → 𝕜) :
    tangent hA i x =
      ‖WithLp.toLp 2 (x - (star ⇑(hA.eigenvectorBasis i) ⬝ᵥ x) •
        ⇑(hA.eigenvectorBasis i))‖ / ‖star ⇑(hA.eigenvectorBasis i) ⬝ᵥ x‖ := by
  rw [tangent, tangentSq, sum_sq_coordinates_erase_eq_norm_sub_sq]
  rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _), hA.eigenvectorCoordinates_apply]

/-- A vector for a simple selected eigenvalue is a scalar multiple of the corresponding
orthonormal eigenbasis vector. -/
theorem eq_coordinate_smul_eigenvectorBasis (hA : A.IsHermitian) {i : n}
    (hsimple : ∀ j, j ≠ i → hA.eigenvalues j ≠ hA.eigenvalues i)
    {u : n → 𝕜} (hu : A *ᵥ u = hA.eigenvalues i • u) :
    u = hA.eigenvectorCoordinates u i • ⇑(hA.eigenvectorBasis i) := by
  apply hA.eigenvectorCoordinates_injective
  ext j
  rw [hA.eigenvectorCoordinates_smul, Pi.smul_apply, smul_eq_mul,
    hA.eigenvectorCoordinates_eigenvectorBasis]
  by_cases hj : j = i
  · simp [hj]
  · rw [if_neg hj, mul_zero]
    have he := hA.eigenvectorCoordinates_mulVec u j
    rw [hu, RCLike.real_smul_eq_coe_smul (K := 𝕜),
      hA.eigenvectorCoordinates_smul, Pi.smul_apply, smul_eq_mul] at he
    have hsub : ((hA.eigenvalues j - hA.eigenvalues i : ℝ) : 𝕜) *
        hA.eigenvectorCoordinates u j = 0 := by
      rw [RCLike.ofReal_sub, sub_mul, he, sub_self]
    exact (mul_eq_zero.mp hsub).resolve_left
      (RCLike.ofReal_ne_zero.mpr (sub_ne_zero.mpr (hsimple j hj)))

/-- The geometric RQI tangent agrees for every choice of unit vector on the simple
eigenvector line, including arbitrary complex phase choices.
atlas: rayleigh-quotient-iteration (partial) -/
theorem tangent_eq_norm_sub_div_of_eigenvector (hA : A.IsHermitian) {i : n}
    (hsimple : ∀ j, j ≠ i → hA.eigenvalues j ≠ hA.eigenvalues i)
    {u : n → 𝕜} (hu : A *ᵥ u = hA.eigenvalues i • u)
    (hu1 : ‖WithLp.toLp 2 u‖ = 1) (x : n → 𝕜) :
    tangent hA i x = ‖WithLp.toLp 2 (x - (star u ⬝ᵥ x) • u)‖ / ‖star u ⬝ᵥ x‖ := by
  have heu := eq_coordinate_smul_eigenvectorBasis hA hsimple hu
  let c := hA.eigenvectorCoordinates u i
  have hc : ‖c‖ = 1 := by
    rw [heu, WithLp.toLp_smul, norm_smul] at hu1
    simpa only [WithLp.toLp_ofLp, OrthonormalBasis.norm_eq_one, mul_one] using hu1
  have hcc : star c * c = 1 := by
    rw [RCLike.star_def, RCLike.conj_mul, hc]
    norm_num
  have hover : star u ⬝ᵥ x = star c * (star ⇑(hA.eigenvectorBasis i) ⬝ᵥ x) := by
    rw [heu, star_smul, smul_dotProduct, smul_eq_mul]
  have hproj : (star u ⬝ᵥ x) • u =
      (star ⇑(hA.eigenvectorBasis i) ⬝ᵥ x) • ⇑(hA.eigenvectorBasis i) := by
    rw [hover, heu, smul_smul]
    congr 1
    change (star c * _) * c = _
    rw [mul_right_comm, hcc, one_mul]
  rw [hproj, hover, norm_mul, norm_star, hc, one_mul]
  exact tangent_eq_norm_sub_div hA i x

/-- Nonzero overlap with any unit target eigenvector is equivalent to a nonzero selected
eigenbasis coordinate. This transfers the native convergence domain to the atlas domain. -/
theorem coordinate_ne_zero_iff_overlap_ne_zero (hA : A.IsHermitian) {i : n}
    (hsimple : ∀ j, j ≠ i → hA.eigenvalues j ≠ hA.eigenvalues i)
    {u : n → 𝕜} (hu : A *ᵥ u = hA.eigenvalues i • u)
    (hu1 : ‖WithLp.toLp 2 u‖ = 1) (x : n → 𝕜) :
    hA.eigenvectorCoordinates x i ≠ 0 ↔ star u ⬝ᵥ x ≠ 0 := by
  have heu := eq_coordinate_smul_eigenvectorBasis hA hsimple hu
  have hc : hA.eigenvectorCoordinates u i ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at heu
    rw [heu] at hu1
    simp at hu1
  rw [heu, star_smul, smul_dotProduct, smul_eq_mul,
    ← hA.eigenvectorCoordinates_apply]
  simp only [ne_eq, mul_eq_zero, star_eq_zero, hc, false_or]

/-- Zero off-axis tangent with nonzero overlap is an exact eigenvector for the target
eigenvalue, and its Rayleigh quotient is that eigenvalue. -/
theorem exact_eigenvector_of_tangentSq_eq_zero (hA : A.IsHermitian) {i : n} {x : n → 𝕜}
    (hx : hA.eigenvectorCoordinates x i ≠ 0) (hq : tangentSq hA i x = 0) :
    A *ᵥ x = hA.eigenvalues i • x ∧ rayleighQuotient A x = hA.eigenvalues i := by
  have hsum : (∑ j ∈ Finset.univ.erase i, ‖hA.eigenvectorCoordinates x j‖ ^ 2) = 0 :=
    (div_eq_zero_iff.mp hq).resolve_right (pow_ne_zero _ (norm_ne_zero_iff.mpr hx))
  have hcoords : ∀ j, j ≠ i → hA.eigenvectorCoordinates x j = 0 := by
    intro j hj
    have hsq := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hsum j
      (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
    exact norm_eq_zero.mp (by nlinarith)
  constructor
  · apply hA.eigenvectorCoordinates_injective
    ext j
    rw [hA.eigenvectorCoordinates_mulVec, RCLike.real_smul_eq_coe_smul (K := 𝕜),
      hA.eigenvectorCoordinates_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hj : j = i
    · simp [hj]
    · simp [hcoords j hj]
  · have hnum : (∑ j, hA.eigenvalues j * ‖hA.eigenvectorCoordinates x j‖ ^ 2) =
        hA.eigenvalues i * ‖hA.eigenvectorCoordinates x i‖ ^ 2 := by
      apply Finset.sum_eq_single i
      · intro j _ hj; simp [hcoords j hj]
      · simp
    have hden : (∑ j, ‖hA.eigenvectorCoordinates x j‖ ^ 2) =
        ‖hA.eigenvectorCoordinates x i‖ ^ 2 := by
      apply Finset.sum_eq_single i
      · intro j _ hj; simp [hcoords j hj]
      · simp
    rw [hA.rayleighQuotient_eq_sum_eigenvectorCoordinates, hnum, hden,
      mul_div_cancel_right₀ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hx))]

/-- A nonterminal state with nonzero target overlap has positive off-axis tangent. -/
theorem tangentSq_pos_of_not_eigenvector (hA : A.IsHermitian) {i : n} {x : n → 𝕜}
    (hx : hA.eigenvectorCoordinates x i ≠ 0)
    (hnot : A *ᵥ x ≠ rayleighQuotient A x • x) : 0 < tangentSq hA i x := by
  apply lt_of_le_of_ne (tangentSq_nonneg hA i x)
  intro hzero
  have he := exact_eigenvector_of_tangentSq_eq_zero hA hx hzero.symm
  exact hnot (by rw [he.2]; exact he.1)

/-- In dimension one every unit vector is already an exact Rayleigh eigenvector.
atlas: rayleigh-quotient-iteration (partial) -/
theorem mulVec_eq_rayleighQuotient_smul_of_unique [Unique n] (hA : A.IsHermitian)
    {x : n → 𝕜} (hx : ‖WithLp.toLp 2 x‖ = 1) :
    A *ᵥ x = rayleighQuotient A x • x := by
  have hc : hA.eigenvectorCoordinates x default ≠ 0 := by
    have hp := hA.sum_sq_norm_eigenvectorCoordinates x
    simp only [Finset.univ_unique, Finset.sum_singleton, hx, one_pow] at hp
    intro hz
    simp [hz] at hp
  have hq : tangentSq hA default x = 0 := by
    simp [tangentSq, Finset.univ_unique]
  have he := exact_eigenvector_of_tangentSq_eq_zero hA hc hq
  rw [he.2]
  exact he.1

end NLAlib.RayleighQuotientIteration
