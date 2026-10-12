import NLAlib.Matrix.Diagonalizable
import Mathlib.Analysis.Normed.Group.Seminorm
import Mathlib.Analysis.Complex.Basic

/-!
# Bauer–Fike for absolute vector norms

An absolute complex vector norm is represented by an additive group norm,
complex homogeneity, and monotonicity in coordinate magnitudes. A compatible
matrix norm supplies its usual induced action inequality. This formulation
covers every induced absolute norm, including the 1, 2 and infinity norms.
Source: Horn–Johnson (2013), Theorem 6.3.2 and Corollary 6.3.4;
atlas `bauer-fike`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An absolute vector norm expands under a diagonal residual by its
smallest diagonal distance. Source: Horn–Johnson (2013), proof of
Theorem 6.3.2; monotonicity in coordinate magnitudes is the absolute-norm
property used by the proof. -/
theorem mul_addGroupNorm_le_diagonal_residual (N : AddGroupNorm (n → ℂ))
    (hhom : ∀ (c : ℂ) (x : n → ℂ), N (c • x) = ‖c‖ * N x)
    (habs : ∀ (x y : n → ℂ), (∀ i, ‖x i‖ ≤ ‖y i‖) → N x ≤ N y)
    (d : n → ℂ) (μ : ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsep : ∀ i, δ ≤ ‖d i - μ‖) (x : n → ℂ) :
    δ * N x ≤ N (Matrix.diagonal d *ᵥ x - μ • x) := by
  have hscalar : N ((δ : ℂ) • x) = δ * N x := by
    rw [hhom, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ]
  rw [← hscalar]
  apply habs
  intro i
  simp only [Matrix.mulVec_diagonal, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [← sub_mul, norm_mul, norm_mul]
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ] using
    mul_le_mul_of_nonneg_right (hsep i) (norm_nonneg (x i))

/-- The residual Bauer–Fike bound for any induced absolute norm.
Source: Horn–Johnson (2013), Corollary 6.3.4; the matrix-action assumption
also permits any larger compatible norm bound. The nonzero approximate
eigenvector premise handles the denominator exactly.
atlas: bauer-fike (partial) -/
theorem exists_eigenvalue_distance_mul_norm_le_residual_of_absolute_norm
    (N : AddGroupNorm (n → ℂ))
    (hhom : ∀ (c : ℂ) (x : n → ℂ), N (c • x) = ‖c‖ * N x)
    (habs : ∀ (x y : n → ℂ), (∀ i, ‖x i‖ ≤ ‖y i‖) → N x ≤ N y)
    (Φ : Matrix n n ℂ → ℝ) (hΦ : ∀ M, 0 ≤ Φ M)
    (haction : ∀ M x, N (M *ᵥ x) ≤ Φ M * N x)
    {A V : Matrix n n ℂ} {d : n → ℂ} (hV : IsUnit V)
    (hA : A * V = V * Matrix.diagonal d) (x : n → ℂ) (hx : x ≠ 0) (μ : ℂ) :
    ∃ i, ‖d i - μ‖ * N x ≤ Φ V * Φ V⁻¹ * N (A *ᵥ x - μ • x) := by
  cases isEmpty_or_nonempty n with
  | inl hn => exact (hx (Subsingleton.elim _ _)).elim
  | inr hn =>
    obtain ⟨i, hi, hmin⟩ := Finset.univ.exists_min_image (fun j => ‖d j - μ‖) Finset.univ_nonempty
    let y := V⁻¹ *ᵥ x
    let r := A *ᵥ x - μ • x
    have hdet := V.isUnit_iff_isUnit_det.mp hV
    have hVy : V *ᵥ y = x := by
      change V *ᵥ (V⁻¹ *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv V hdet, Matrix.one_mulVec]
    have hDA : Matrix.diagonal d * V⁻¹ = V⁻¹ * A := by
      have hD : V⁻¹ * A * V = Matrix.diagonal d := by
        rw [Matrix.mul_assoc, hA, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul V hdet,
          Matrix.one_mul]
      calc
        Matrix.diagonal d * V⁻¹ = (V⁻¹ * A * V) * V⁻¹ := by rw [hD]
        _ = _ := by rw [Matrix.mul_assoc (V⁻¹ * A), Matrix.mul_nonsing_inv V hdet, Matrix.mul_one]
    have hres : Matrix.diagonal d *ᵥ y - μ • y = V⁻¹ *ᵥ r := by
      change Matrix.diagonal d *ᵥ (V⁻¹ *ᵥ x) - μ • (V⁻¹ *ᵥ x) =
        V⁻¹ *ᵥ (A *ᵥ x - μ • x)
      rw [Matrix.mulVec_mulVec, hDA, ← Matrix.mulVec_mulVec,
        Matrix.mulVec_sub, Matrix.mulVec_smul]
    have hdiag := mul_addGroupNorm_le_diagonal_residual N hhom habs d μ
      (norm_nonneg _) (fun j => hmin j (Finset.mem_univ j)) y
    rw [hres] at hdiag
    have hxbound : N x ≤ Φ V * N y := by
      simpa only [hVy] using haction V y
    refine ⟨i, ?_⟩
    calc
      ‖d i - μ‖ * N x ≤ ‖d i - μ‖ * (Φ V * N y) :=
        mul_le_mul_of_nonneg_left hxbound (norm_nonneg _)
      _ = Φ V * (‖d i - μ‖ * N y) := by ring
      _ ≤ Φ V * N (V⁻¹ *ᵥ r) := mul_le_mul_of_nonneg_left hdiag (hΦ V)
      _ ≤ Φ V * (Φ V⁻¹ * N r) :=
        mul_le_mul_of_nonneg_left (haction V⁻¹ r) (hΦ V)
      _ = _ := by ring

/-- The residual inclusion in the source's quotient form, for every induced
absolute norm. Source: Horn–Johnson (2013), Corollary 6.3.4.
atlas: bauer-fike (partial) -/
theorem exists_eigenvalue_distance_le_residual_div_of_absolute_norm
    (N : AddGroupNorm (n → ℂ))
    (hhom : ∀ (c : ℂ) (x : n → ℂ), N (c • x) = ‖c‖ * N x)
    (habs : ∀ (x y : n → ℂ), (∀ i, ‖x i‖ ≤ ‖y i‖) → N x ≤ N y)
    (Φ : Matrix n n ℂ → ℝ) (hΦ : ∀ M, 0 ≤ Φ M)
    (haction : ∀ M x, N (M *ᵥ x) ≤ Φ M * N x)
    {A V : Matrix n n ℂ} {d : n → ℂ} (hV : IsUnit V)
    (hA : A * V = V * Matrix.diagonal d) (x : n → ℂ) (hx : x ≠ 0) (μ : ℂ) :
    ∃ i, ‖d i - μ‖ ≤ (Φ V * Φ V⁻¹) * N (A *ᵥ x - μ • x) / N x := by
  obtain ⟨i, hi⟩ := exists_eigenvalue_distance_mul_norm_le_residual_of_absolute_norm
    N hhom habs Φ hΦ haction hV hA x hx μ
  exact ⟨i, (le_div_iff₀ (map_pos_of_ne_zero N hx)).mpr hi⟩

/-- Every perturbed spectral point lies in the Bauer–Fike disks for any
induced absolute norm. Source: Horn–Johnson (2013), Theorem 6.3.2; neither
the original nor perturbed matrix needs a simple spectrum.
atlas: bauer-fike (partial) -/
theorem exists_eigenvalue_distance_le_perturbation_of_absolute_norm
    (N : AddGroupNorm (n → ℂ))
    (hhom : ∀ (c : ℂ) (x : n → ℂ), N (c • x) = ‖c‖ * N x)
    (habs : ∀ (x y : n → ℂ), (∀ i, ‖x i‖ ≤ ‖y i‖) → N x ≤ N y)
    (Φ : Matrix n n ℂ → ℝ) (hΦ : ∀ M, 0 ≤ Φ M)
    (haction : ∀ M x, N (M *ᵥ x) ≤ Φ M * N x)
    {A V E : Matrix n n ℂ} {d : n → ℂ} (hV : IsUnit V)
    (hA : A * V = V * Matrix.diagonal d) {μ : ℂ} (hμ : μ ∈ spectrum ℂ (A + E)) :
    ∃ i, ‖d i - μ‖ ≤ (Φ V * Φ V⁻¹) * Φ E := by
  obtain ⟨x, hx, hAx⟩ := exists_mulVec_eq_smul_of_mem_spectrum hμ
  obtain ⟨i, hi⟩ := exists_eigenvalue_distance_mul_norm_le_residual_of_absolute_norm
    N hhom habs Φ hΦ haction hV hA x hx μ
  have hres : A *ᵥ x - μ • x = -(E *ᵥ x) := by
    have h := hAx
    rw [Matrix.add_mulVec] at h
    calc
      A *ᵥ x - μ • x = A *ᵥ x - (A *ᵥ x + E *ᵥ x) := by rw [h]
      _ = -(E *ᵥ x) := by abel
  rw [hres, map_neg_eq_map] at hi
  have hκ : 0 ≤ Φ V * Φ V⁻¹ := mul_nonneg (hΦ V) (hΦ V⁻¹)
  have hh := hi.trans (mul_le_mul_of_nonneg_left (haction E x) hκ)
  refine ⟨i, (mul_le_mul_iff_right₀ (map_pos_of_ne_zero N hx)).mp ?_⟩
  convert hh using 1 <;> ring

end NLAlib
