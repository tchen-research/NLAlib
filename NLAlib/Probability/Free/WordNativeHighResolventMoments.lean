import NLAlib.Probability.Free.WordNativeMatrixLinearCombination
import NLAlib.Probability.Free.WordMatrixSpectralVacuumVectors
import NLAlib.Probability.Free.WordMatrixVectorMoments
import NLAlib.ForMathlib.Analysis.InnerProductSpace.ResolventVectorLowerBound
import NLAlib.ForMathlib.Algebra.ResolventHom

/-!
# Genuine high-height free resolvent ultracontractivity

An actual mean eigenvector produces a unit embedded vacuum vector with a
controlled residual. Normality of the actual resolvent and scalar Jensen
on its actual vector state then give the genuine amplified vacuum-moment
bound at heights above the centered free scale.
Source: arXiv:2406.11453v2, the high-height case of Corollary 4.4.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical ComplexOrder

namespace NLAlib

variable {D ι : Type*} [Fintype D] [DecidableEq D] [Fintype ι]
local notation "W" => WordHilbertSpace ι
local notation "M" => CStarMatrix D D (W →L[ℂ] W)

/-- The actual coefficient free resolvent is controlled by its actual
rooted amplified vacuum moment above the true centered free scale. The
real part of the parameter belongs to the actual free spectrum. The exact
dimension factor is retained for a later logarithmic-order estimate.

Source: arXiv:2406.11453v2, the high-height case of Corollary 4.4.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem norm_resolvent_wordNativeMatrixLinearCombination_le_evenMoment_high
    (q : ℕ) (hq : 0<q) {A₀ : Matrix D D ℂ} (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix D D ℂ) (hA : ∀ k, (A k).IsHermitian)
    {z : ℂ} (hz : 0<z.im)
    (hση : Real.sqrt (specNorm (∑ k, A k^2))≤z.im)
    (hspec : z.re∈spectrum ℝ (wordNativeMatrixLinearCombination A₀ A)) :
    ‖resolvent (wordNativeMatrixLinearCombination A₀ A) z‖ ≤
      5*(Fintype.card D : ℝ)^(1/(4*q : ℝ))*
        ((wordMatrixVacuumExpectation (D := D) (ι := ι)
          ((star (resolvent (wordNativeMatrixLinearCombination A₀ A) z)*
            resolvent (wordNativeMatrixLinearCombination A₀ A) z)^(2*q))).re)^
              (1/(4*q : ℝ)) := by
  let X := wordNativeMatrixLinearCombination A₀ A
  let V := CStarMatrix.toPiLpStarAlgHom (D := D) (H := W)
  let R := resolvent X z
  let b : ℝ := (Fintype.card D : ℝ)*
    (wordMatrixVacuumExpectation (D := D) (ι := ι) ((star R*R)^(2*q))).re
  have hself : IsSelfAdjoint X := isSelfAdjoint_wordNativeMatrixLinearCombination hA₀ hA
  have hVX : V X=wordMatrixLinearCombination A₀ A := toPiLp_wordNativeMatrixLinearCombination A₀ A
  have hspecV : z.re∈spectrum ℝ (V X) := by
    rw [hself.map_spectrum_real V CStarMatrix.toPiLpStarAlgHom_injective]
    exact hspec
  obtain ⟨v,hv,hres⟩ := exists_unit_wordMatrixVacuumEmbedding_residual_le hA₀ A hA hz hση
    (by rwa [hVX] at hspecV)
  let u := wordMatrixVacuumEmbedding (ι := ι) v
  have hu : ‖u‖=1 := by simpa only [u,LinearIsometry.norm_map] using hv
  have hVR : V R=resolvent (V X) z := V.toAlgHom.map_resolvent
    (hself.isUnit_algebraMap_sub_of_im_ne_zero hz.ne')
  have hlower : (5*z.im)⁻¹≤‖V R u‖ := by
    rw [hVR,hVX]
    exact (isSelfAdjoint_wordMatrixLinearCombination hA₀ hA).inv_le_norm_resolvent_apply_of_residual_le
      hz.ne' hu (by positivity) hres
  have hmoment : ‖V R u‖≤b^(1/(4*q : ℝ)) := by
    have h := norm_toPiLp_wordMatrixVacuumEmbedding_le_gramMoment R v hv (2*q) (by omega)
    have he : ((2 : ℝ)*(2*q : ℕ))⁻¹=1/(4*q : ℝ) := by push_cast; ring
    simpa only [he] using h
  have hnorm : ‖R‖≤z.im⁻¹ := by
    simpa only [abs_of_pos hz] using hself.norm_resolvent_le hz.ne'
  have hinv : 5*(5*z.im)⁻¹=z.im⁻¹ := by field_simp [hz.ne']
  have hbound : ‖R‖≤5*b^(1/(4*q : ℝ)) := by
    calc
      _ ≤ z.im⁻¹ := hnorm
      _ = 5*(5*z.im)⁻¹ := hinv.symm
      _ ≤ 5*‖V R u‖ := mul_le_mul_of_nonneg_left hlower (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left hmoment (by norm_num)
  have hτ : 0≤(wordMatrixVacuumExpectation (D := D) (ι := ι) ((star R*R)^(2*q))).re :=
    (Complex.nonneg_iff.mp ((wordMatrixVacuumPositiveMap (D := D) (ι := ι)).map_nonneg
      (CStarAlgebra.pow_nonneg (star_mul_self_nonneg R) (2*q)))).1
  have hfactor : b^(1/(4*q : ℝ))=
      (Fintype.card D : ℝ)^(1/(4*q : ℝ))*
        ((wordMatrixVacuumExpectation (D := D) (ι := ι) ((star R*R)^(2*q))).re)^
          (1/(4*q : ℝ)) := Real.mul_rpow (Nat.cast_nonneg _) hτ
  rw [hfactor,← mul_assoc] at hbound
  exact hbound

end NLAlib

end
