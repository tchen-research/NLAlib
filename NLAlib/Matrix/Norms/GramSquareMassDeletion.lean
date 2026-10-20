import NLAlib.Matrix.Norms.LoewnerBounds
import NLAlib.Matrix.Spectral.NumericalRange

/-!
# Common maximizing probes for sums of matrix Gram squares

The summed-square spectral norm has an actual unit-ball maximizing probe.
One such probe controls every deletion gap, including empty dimensions.
-/

noncomputable section
set_option autoImplicit false
open Matrix Finset
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib
variable {ι n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The native complex Gram quadratic form equals the sum of actual squared
Euclidean lengths. No Hermitian assumption on the individual matrices is needed. -/
theorem sum_norm_sq_mulVec_eq_re_quadForm_sum_gram
    (D : ι → Matrix n n ℂ) (s : Finset ι) (u : EuclideanSpace ℂ n) :
    ∑ i ∈ s, ‖WithLp.toLp 2 (D i *ᵥ u.ofLp)‖ ^ 2 =
      (quadForm (∑ i ∈ s, (D i)ᴴ * D i) u.ofLp).re := by
  have he : quadForm (∑ i ∈ s, (D i)ᴴ * D i) u.ofLp =
      ∑ i ∈ s, quadForm ((D i)ᴴ * D i) u.ofLp := by
    simp only [quadForm, Matrix.sum_mulVec, dotProduct_sum]
  rw [he, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [quadForm_conjTranspose_mul_self, norm_toLp_sq_eq_re_star_dotProduct]
  rfl

/-- Every unit-ball vector gives a sum of actual squared lengths below the
native named spectral norm of the summed Gram squares. -/
theorem sum_norm_sq_mulVec_le_specNorm_sum_gram
    (D : ι → Matrix n n ℂ) (s : Finset ι) (u : EuclideanSpace ℂ n) (hu : ‖u‖ ≤ 1) :
    ∑ i ∈ s, ‖WithLp.toLp 2 (D i *ᵥ u.ofLp)‖ ^ 2 ≤
      specNorm (∑ i ∈ s, (D i)ᴴ * D i) := by
  rw [sum_norm_sq_mulVec_eq_re_quadForm_sum_gram]
  calc _ ≤ ‖quadForm (∑ i ∈ s, (D i)ᴴ * D i) u.ofLp‖ := Complex.re_le_norm _
    _ ≤ specNorm (∑ i ∈ s, (D i)ᴴ * D i) * ‖u‖ ^ 2 := by
      simpa only [WithLp.toLp_ofLp] using
        norm_quadForm_le_specNorm (∑ i ∈ s, (D i)ᴴ * D i) u.ofLp
    _ ≤ specNorm (∑ i ∈ s, (D i)ᴴ * D i) := by
      have hs := (sq_le_sq₀ (norm_nonneg u) (by norm_num : (0 : ℝ) ≤ 1)).mpr hu
      nlinarith [specNorm_nonneg (∑ i ∈ s, (D i)ᴴ * D i)]

open scoped Matrix.Norms.L2Operator in
/-- The actual spectral norm is attained by a common Euclidean unit-ball
probe. Empty matrix dimensions use the zero vector. -/
theorem exists_specNorm_sum_gram_eq (D : ι → Matrix n n ℂ) (s : Finset ι) :
    ∃ u : EuclideanSpace ℂ n, ‖u‖ ≤ 1 ∧
      specNorm (∑ i ∈ s, (D i)ᴴ * D i) =
        ∑ i ∈ s, ‖WithLp.toLp 2 (D i *ᵥ u.ofLp)‖ ^ 2 := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn =>
      let := hn
      have he : (∑ i ∈ s, (D i)ᴴ * D i) = (0 : Matrix n n ℂ) := Subsingleton.elim _ _
      exact ⟨0, by simp, by simp [he, specNorm]⟩
  | inr hn =>
      let := hn
      let G : Matrix n n ℂ := ∑ i ∈ s, (D i)ᴴ * D i
      have hG : G.PosSemidef :=
        Matrix.posSemidef_sum s (fun i _ => Matrix.posSemidef_conjTranspose_mul_self (D i))
      have hreal : specNorm G ∈ spectrum ℝ G := by
        simpa only [specNorm_eq_norm] using CStarAlgebra.norm_mem_spectrum_of_nonneg hG.nonneg
      have hcomplex : (specNorm G : ℂ) ∈ spectrum ℂ G := spectrum.algebraMap_mem ℂ hreal
      obtain ⟨x, hx, hq⟩ := spectrum_subset_numericalRange G hcomplex
      refine ⟨WithLp.toLp 2 x, hx.le, ?_⟩
      rw [sum_norm_sq_mulVec_eq_re_quadForm_sum_gram]
      change specNorm G = (quadForm G x).re
      rw [hq, Complex.ofReal_re]

open scoped Matrix.Norms.L2Operator in
/-- Summing more Gram squares increases their actual spectral norm. -/
theorem specNorm_sum_gram_mono (D : ι → Matrix n n ℂ) {s t : Finset ι} (hst : s ⊆ t) :
    specNorm (∑ i ∈ s, (D i)ᴴ * D i) ≤ specNorm (∑ i ∈ t, (D i)ᴴ * D i) := by
  have hpos : (∑ i ∈ s, (D i)ᴴ * D i).PosSemidef :=
    Matrix.posSemidef_sum s (fun i _ => Matrix.posSemidef_conjTranspose_mul_self (D i))
  have hle : (∑ i ∈ s, (D i)ᴴ * D i) ≤ ∑ i ∈ t, (D i)ᴴ * D i :=
    Finset.sum_le_sum_of_subset_of_nonneg hst
      (fun i _ _ => (Matrix.posSemidef_conjTranspose_mul_self (D i)).nonneg)
  simpa only [specNorm_eq_norm] using
    CStarAlgebra.norm_le_norm_of_nonneg_of_le hpos.nonneg hle

/-- One actually constructed common maximizing probe controls every deletion
gap of the native summed-Gram spectral norm. -/
theorem exists_specNorm_sum_gram_erase_gap_le [Fintype ι] [DecidableEq ι] (D : ι → Matrix n n ℂ) :
    ∃ u : EuclideanSpace ℂ n, ‖u‖ ≤ 1 ∧
      specNorm (∑ i, (D i)ᴴ * D i) = ∑ i, ‖WithLp.toLp 2 (D i *ᵥ u.ofLp)‖ ^ 2 ∧
      ∀ i, specNorm (∑ j, (D j)ᴴ * D j) -
        specNorm (∑ j ∈ Finset.univ.erase i, (D j)ᴴ * D j) ≤
          ‖WithLp.toLp 2 (D i *ᵥ u.ofLp)‖ ^ 2 := by
  obtain ⟨u, hu, he⟩ := exists_specNorm_sum_gram_eq D Finset.univ
  refine ⟨u, hu, he, fun i => ?_⟩
  have h := sum_norm_sq_mulVec_le_specNorm_sum_gram D (Finset.univ.erase i) u hu
  have hsum := Finset.sum_erase_add Finset.univ
    (fun j => ‖WithLp.toLp 2 (D j *ᵥ u.ofLp)‖ ^ 2) (Finset.mem_univ i)
  linarith

open scoped Matrix.Norms.L2Operator in
/-- The true Gram norm is bounded by the sum of the squared matrix norms. -/
theorem specNorm_sum_gram_le_sum_specNorm_sq (D : ι → Matrix n n ℂ) (s : Finset ι) :
    specNorm (∑ i ∈ s, (D i)ᴴ * D i) ≤ ∑ i ∈ s, specNorm (D i) ^ 2 := by
  calc
    _ ≤ ∑ i ∈ s, specNorm ((D i)ᴴ * D i) := by
      simpa only [specNorm_eq_norm] using norm_sum_le s (fun i => (D i)ᴴ * D i)
    _ = _ := Finset.sum_congr rfl (fun i _ =>
      (specNorm_sq_eq_specNorm_conjTranspose_mul_self (D i)).symm)

end NLAlib
