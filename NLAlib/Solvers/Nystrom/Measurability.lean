import NLAlib.Solvers.Nystrom.Condition
import NLAlib.Matrix.Measurability.FunctionalCalculus
import NLAlib.Matrix.Measurability.GramPseudoinverse
import NLAlib.Matrix.Measurability.SpectralMeasurable

/-!
# Measurability of the FTU preconditioned condition number

The shifted fixed scalar calculus proves measurability without choosing random
eigenvectors. The preconditioner spectrum has a fixed compact positive enclosure,
so the same argument applies to its inverse square root.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped Matrix MatrixOrder
namespace NLAlib
variable {n Ω : Type*} [Fintype n] [DecidableEq n] [MeasurableSpace Ω]

open scoped Matrix.Norms.L2Operator in
/-- The native FTU preconditioner is measurable for bounded PSD approximations
and bounded nonnegative floors. -/
theorem measurable_nystromPreconditioner {B : Ω → Matrix n n ℝ} {a : Ω → ℝ}
    (hB : Measurable B) (ha : Measurable a) (hPSD : ∀ ω, (B ω).PosSemidef)
    {R : ℝ} (_hR : 0 ≤ R) (hBN : ∀ ω, specNorm (B ω) ≤ R)
    (ha0 : ∀ ω, 0 ≤ a ω) (haR : ∀ ω, a ω ≤ R) (μ : ℝ) :
    Measurable (fun ω => nystromPreconditioner (B ω) (a ω) μ) := by
  have hH : Measurable (fun ω => B ω - a ω • (1 : Matrix n n ℝ)) := by
    apply Matrix.measurable_iff_entries.mpr
    intro i j
    exact ((Matrix.measurable_entry i j).comp hB).sub (ha.mul_const _)
  have hHS : ∀ ω, (B ω - a ω • (1 : Matrix n n ℝ)).IsHermitian := fun ω =>
    (hPSD ω).isHermitian.sub (Matrix.isHermitian_one.smul (isSelfAdjoint_iff.mpr (star_trivial _)))
  have hHN : ∀ ω, specNorm (B ω - a ω • (1 : Matrix n n ℝ)) ≤ 2 * R := by
    intro ω
    have hh : specNorm (a ω • (1 : Matrix n n ℝ)) = a ω * specNorm (1 : Matrix n n ℝ) := by
      simp only [specNorm_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha0 ω)]
    have hI : specNorm (a ω • (1 : Matrix n n ℝ)) ≤ a ω := by
      rw [hh]
      exact mul_le_of_le_one_right (ha0 ω) specNorm_one_le
    exact (specNorm_sub_le _ _).trans (by linarith [hBN ω, haR ω])
  have hC := measurable_cfc_of_specNorm_le hH hHS hHN
    (fun t : ℝ => max (-t) 0) (by fun_prop)
  have he : (fun ω => nystromPreconditioner (B ω) (a ω) μ) =
      fun ω => (a ω + μ)⁻¹ • (B ω + μ • 1 +
        cfc (fun t : ℝ => max (-t) 0) (B ω - a ω • 1)) := by
    funext ω
    exact nystromPreconditioner_eq_cfc_shift (hPSD ω).isHermitian _ _
  rw [he]
  apply Matrix.measurable_iff_entries.mpr
  intro i j
  exact (ha.add_const μ).inv.mul ((((Matrix.measurable_entry i j).comp hB).add_const _).add
    ((Matrix.measurable_entry i j).comp hC))

open scoped Matrix.Norms.L2Operator in
/-- Every eigenvalue of a bounded PSD spectral-floor preconditioner lies in a
fixed compact interval bounded away from zero. -/
theorem spectrum_nystromPreconditioner_subset [Nonempty n] {B : Matrix n n ℝ}
    (hB : B.PosSemidef) {R a μ : ℝ} (hR : 0 ≤ R) (hBN : specNorm B ≤ R)
    (ha0 : 0 ≤ a) (haR : a ≤ R) (hμ : 0 < μ) :
    spectrum ℝ (nystromPreconditioner B a μ) ⊆ Set.Icc 1 ((R+μ)/μ) := by
  intro z hz
  rw [nystromPreconditioner] at hz
  have he := cfc_map_spectrum (R := ℝ) (a := B)
    (f := fun t : ℝ => (max t a + μ) / (a + μ)) hB.isHermitian.isSelfAdjoint (by fun_prop)
  rw [he] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg hB.nonneg ht
  have htR : t ≤ R := by
    have h := spectrum.norm_le_norm_of_mem ht
    rw [← specNorm_eq_norm, Real.norm_eq_abs, abs_of_nonneg ht0] at h
    exact h.trans hBN
  have hm : max t a ≤ R := max_le htR haR
  have hd : 0 < a+μ := add_pos_of_nonneg_of_pos ha0 hμ
  refine ⟨(one_le_div hd).mpr (by linarith [le_max_right t a]), ?_⟩
  apply (div_le_div_iff₀ hd hμ).mpr
  nlinarith

open scoped Matrix.Norms.L2Operator in
/-- The actual symmetric preconditioned matrix is measurable along bounded PSD
approximations and measurable floors. -/
theorem measurable_nystromPreconditionedMatrix [Nonempty n] (A : Matrix n n ℝ)
    {B : Ω → Matrix n n ℝ} {a : Ω → ℝ}
    (hB : Measurable B) (ha : Measurable a) (hPSD : ∀ ω, (B ω).PosSemidef)
    {R : ℝ} (hR : 0 ≤ R) (hBN : ∀ ω, specNorm (B ω) ≤ R)
    (ha0 : ∀ ω, 0 ≤ a ω) (haR : ∀ ω, a ω ≤ R) {μ : ℝ} (hμ : 0 < μ) :
    Measurable (fun ω => nystromPreconditionedMatrix A (B ω) (a ω) μ) := by
  have hP := measurable_nystromPreconditioner hB ha hPSD hR hBN ha0 haR μ
  have hPS : ∀ ω, (nystromPreconditioner (B ω) (a ω) μ).IsHermitian := fun ω =>
    (nystromPreconditioner_posDef (hPSD ω) (ha0 ω) hμ).isHermitian
  have hR := measurable_cfc_of_spectrum_subset hP hPS isCompact_Icc
    (fun ω => spectrum_nystromPreconditioner_subset (hPSD ω) hR (hBN ω)
      (ha0 ω) (haR ω) hμ) (fun t : ℝ => (Real.sqrt t)⁻¹) (by
        apply ContinuousOn.inv₀ Real.continuous_sqrt.continuousOn
        intro t ht
        exact ne_of_gt (Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one ht.1)))
  exact (hR.matrix_mul measurable_const).matrix_mul hR

end NLAlib
