import NLAlib.Matrix.Functions.HermitianResolvent
import NLAlib.Matrix.Spectral.HausdorffSpectrum
import Mathlib.Data.Finset.Max

/-!
# Spectral inclusion from actual nonreal resolvent comparisons

Finite Hermitian spectral coordinates identify an actual eigenvalue attaining
resolvent norm. A comparison at vertical shifts of the source spectrum then
produces a nearby point in the target spectrum. These are deterministic
bridges for Brailovskaya--van Handel, arXiv:2201.05142v3, Lemma 7.1.
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

omit [Nonempty n] in
open scoped Matrix.Norms.L2Operator in
private theorem specNorm_resolvent_eq_pi_norm {A : Matrix n n ℂ}
    (hA : A.IsHermitian) {ζ : ℂ} (hζ : ζ.im ≠ 0) :
    specNorm (resolvent A ζ) = ‖fun i => (ζ - (hA.eigenvalues i : ℂ))⁻¹‖ := by
  rw [resolvent_eq_eigenvectorUnitary_conj_diagonal hA hζ, specNorm_eq_norm,
    Unitary.conjStarAlgAut_apply]
  change ‖(hA.eigenvectorUnitary : Matrix n n ℂ) *
    Matrix.diagonal (fun i => (ζ - (hA.eigenvalues i : ℂ))⁻¹) *
    ((star hA.eigenvectorUnitary : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ)‖ = _
  rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]

/-- The norm of a nonreal Hermitian resolvent is attained at an actual point
of its real spectrum, without choosing any eigenvector basis in the statement. -/
theorem exists_mem_spectrum_specNorm_resolvent_eq {A : Matrix n n ℂ}
    (hA : A.IsHermitian) {ζ : ℂ} (hζ : ζ.im ≠ 0) :
    ∃ β ∈ spectrum ℝ A, specNorm (resolvent A ζ) = ‖ζ - (β : ℂ)‖⁻¹ := by
  classical
  let f : n → ℂ := fun i => (ζ - (hA.eigenvalues i : ℂ))⁻¹
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖f j‖)
    Finset.univ_nonempty
  refine ⟨hA.eigenvalues i, ?_, ?_⟩
  · rw [hA.spectrum_real_eq_range_eigenvalues]
    exact ⟨i, rfl⟩
  · rw [specNorm_resolvent_eq_pi_norm hA hζ]
    have heq : ‖f‖ = ‖f i‖ := le_antisymm
      ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun j => hi j (Finset.mem_univ j)))
      (norm_le_pi_norm f i)
    simpa only [f, norm_inv] using heq

omit [Nonempty n] in
/-- Directly above an actual Hermitian eigenvalue at positive height, the
resolvent has exactly inverse-height spectral norm. -/
theorem specNorm_resolvent_eq_inv_of_mem_spectrum {A : Matrix n n ℂ}
    (hA : A.IsHermitian) {ξ η : ℝ} (hξ : ξ ∈ spectrum ℝ A) (hη : 0 < η) :
    specNorm (resolvent A ((ξ : ℂ) + (η : ℂ) * Complex.I)) = η⁻¹ := by
  have hζ : ((ξ : ℂ) + (η : ℂ) * Complex.I).im ≠ 0 := by
    simpa using ne_of_gt hη
  apply le_antisymm
  · simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
      add_zero, zero_add, abs_of_pos hη] using hA.specNorm_resolvent_le hζ
  · rw [hA.spectrum_real_eq_range_eigenvalues] at hξ
    obtain ⟨i, hi⟩ := hξ
    rw [specNorm_resolvent_eq_pi_norm hA hζ]
    have hnorm : ‖((ξ : ℂ) + (η : ℂ) * Complex.I - (hA.eigenvalues i : ℂ))⁻¹‖ = η⁻¹ := by
      rw [hi]
      have hs : (ξ : ℂ) + (η : ℂ) * Complex.I - (ξ : ℂ) = (η : ℂ) * Complex.I := by ring
      rw [hs, norm_inv, norm_mul, Complex.norm_real, Complex.norm_I,
        mul_one, Real.norm_eq_abs, abs_of_pos hη]
    rw [← hnorm]
    exact norm_le_pi_norm (fun j : n =>
      (((ξ : ℂ) + (η : ℂ) * Complex.I) - (hA.eigenvalues j : ℂ))⁻¹) i

/-- A resolvent comparison with error at most half the source inverse height
produces a target spectral point at distance at most twice C times the height.
The source and target are actual Hermitian matrices; no spectral-distance
conclusion is assumed. -/
theorem exists_mem_spectrum_dist_le_of_resolvent_comparison
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {ξ η C δ : ℝ} (hξ : ξ ∈ spectrum ℝ A) (hη : 0 < η)
    (hδ : δ ≤ (2 * η)⁻¹)
    (hcmp : specNorm (resolvent A ((ξ : ℂ) + (η : ℂ) * Complex.I)) ≤
      C * specNorm (resolvent B ((ξ : ℂ) + (η : ℂ) * Complex.I)) + δ) :
    ∃ β ∈ spectrum ℝ B, dist ξ β ≤ 2 * C * η := by
  have hζ : ((ξ : ℂ) + (η : ℂ) * Complex.I).im ≠ 0 := by
    simpa using ne_of_gt hη
  obtain ⟨β, hβ, hnorm⟩ := exists_mem_spectrum_specNorm_resolvent_eq hB hζ
  rw [specNorm_resolvent_eq_inv_of_mem_spectrum hA hξ hη, hnorm] at hcmp
  have hdpos : 0 < ‖(ξ : ℂ) + (η : ℂ) * Complex.I - (β : ℂ)‖ := by
    apply norm_pos_iff.mpr
    intro hz
    have hh := congrArg Complex.im hz
    exact hζ (by simpa using hh)
  have hhalf : (2 * η)⁻¹ ≤ C * ‖(ξ : ℂ) + (η : ℂ) * Complex.I - (β : ℂ)‖⁻¹ := by
    have hs : η⁻¹ = 2 * (2 * η)⁻¹ := by field_simp
    linarith
  have hnormle : ‖(ξ : ℂ) + (η : ℂ) * Complex.I - (β : ℂ)‖ ≤ 2 * C * η := by
    have hs := (mul_le_mul_of_nonneg_right hhalf (le_of_lt hdpos))
    rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hdpos), mul_one] at hs
    have hm := mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ 2 * η)
    have heq : ((2 * η)⁻¹ * ‖(ξ : ℂ) + (η : ℂ) * Complex.I - (β : ℂ)‖) * (2 * η) =
        ‖(ξ : ℂ) + (η : ℂ) * Complex.I - (β : ℂ)‖ := by field_simp
    rw [heq] at hm
    nlinarith
  refine ⟨β, hβ, ?_⟩
  have hre := Complex.abs_re_le_norm ((ξ : ℂ) + (η : ℂ) * Complex.I - (β : ℂ))
  have hre' : dist ξ β ≤ ‖(ξ : ℂ) + (η : ℂ) * Complex.I - (β : ℂ)‖ := by
    simpa only [Real.dist_eq, Complex.sub_re, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero] using hre
  exact hre'.trans hnormle

/-- Actual resolvent comparisons in both directions give the displayed
Hausdorff bound for the native real spectral sets. The common error is bounded
by half the inverse height; its nonnegativity is not needed. -/
theorem hausdorffDist_spectrum_le_of_resolvent_comparison
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {η C δ : ℝ} (hη : 0 < η) (hδ : δ ≤ (2 * η)⁻¹)
    (hAB : ∀ ξ ∈ spectrum ℝ A,
      specNorm (resolvent A ((ξ : ℂ) + (η : ℂ) * Complex.I)) ≤
        C * specNorm (resolvent B ((ξ : ℂ) + (η : ℂ) * Complex.I)) + δ)
    (hBA : ∀ ξ ∈ spectrum ℝ B,
      specNorm (resolvent B ((ξ : ℂ) + (η : ℂ) * Complex.I)) ≤
        C * specNorm (resolvent A ((ξ : ℂ) + (η : ℂ) * Complex.I)) + δ) :
    Metric.hausdorffDist (spectrum ℝ A) (spectrum ℝ B) ≤ 2 * C * η := by
  have hAB' (ξ : ℝ) (hξ : ξ ∈ spectrum ℝ A) :=
    exists_mem_spectrum_dist_le_of_resolvent_comparison hA hB hξ hη hδ (hAB ξ hξ)
  have hBA' (ξ : ℝ) (hξ : ξ ∈ spectrum ℝ B) :=
    exists_mem_spectrum_dist_le_of_resolvent_comparison hB hA hξ hη hδ (hBA ξ hξ)
  have hR : 0 ≤ 2 * C * η := by
    have hn : (spectrum ℝ A).Nonempty := by
      rw [hA.spectrum_real_eq_range_eigenvalues]
      exact Set.range_nonempty _
    obtain ⟨ξ, hξ⟩ := hn
    obtain ⟨β, _, hb⟩ := hAB' ξ hξ
    exact dist_nonneg.trans hb
  exact Metric.hausdorffDist_le_of_mem_dist hR hAB' hBA'

private theorem resolvent_error_le_half_inv {η K₁ K₂ K₃ : ℝ}
    (hη : 0 < η) (h₁ : 6 * K₁ ≤ η) (h₂ : 6 * K₂ ≤ η ^ 2)
    (h₃ : 6 * K₃ ≤ η ^ 3) :
    K₁ / η ^ 2 + K₂ / η ^ 3 + K₃ / η ^ 4 ≤ (2 * η)⁻¹ := by
  have hn : η ≠ 0 := ne_of_gt hη
  have hsum : K₁ / η ^ 2 + K₂ / η ^ 3 + K₃ / η ^ 4 =
      (K₁ * η ^ 2 + K₂ * η + K₃) / η ^ 4 := by field_simp
  rw [hsum]
  apply (div_le_iff₀ (by positivity : 0 < η ^ 4)).mpr
  have heq : (2 * η)⁻¹ * η ^ 4 = η ^ 3 / 2 := by field_simp
  rw [heq]
  have h₁' := mul_le_mul_of_nonneg_right h₁ (sq_nonneg η)
  have h₂' := mul_le_mul_of_nonneg_right h₂ hη.le
  nlinarith

/-- The inverse-height-square, cube and fourth-power error profile gives
actual directed spectral inclusion at any positive height satisfying the
three source scale bounds. This is Lemma 7.1 of Brailovskaya--van Handel,
arXiv:2201.05142v3, with the height left as a reusable explicit parameter. -/
theorem forall_exists_mem_spectrum_dist_le_of_resolvent_error_bounds
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {η C K₁ K₂ K₃ : ℝ} (hη : 0 < η)
    (h₁ : 6 * K₁ ≤ η) (h₂ : 6 * K₂ ≤ η ^ 2) (h₃ : 6 * K₃ ≤ η ^ 3)
    (hAB : ∀ ξ ∈ spectrum ℝ A,
      specNorm (resolvent A ((ξ : ℂ) + (η : ℂ) * Complex.I)) ≤
        C * specNorm (resolvent B ((ξ : ℂ) + (η : ℂ) * Complex.I)) +
          K₁ / η ^ 2 + K₂ / η ^ 3 + K₃ / η ^ 4) :
    ∀ ξ ∈ spectrum ℝ A, ∃ β ∈ spectrum ℝ B, dist ξ β ≤ 2 * C * η := by
  intro ξ hξ
  apply exists_mem_spectrum_dist_le_of_resolvent_comparison hA hB hξ hη
    (resolvent_error_le_half_inv hη h₁ h₂ h₃)
  simpa only [add_assoc] using hAB ξ hξ

end NLAlib
