import NLAlib.ForMathlib.Topology.MetricSpace.CompactRealHausdorff
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # Actual spectral extremes across different C-star algebras -/

noncomputable section
set_option autoImplicit false
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B] [Nontrivial A] [Nontrivial B]

private theorem real_spectrum_nonempty {a : A} (ha : IsSelfAdjoint a) : (spectrum ℝ a).Nonempty := by
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum ha with hp | hn
  · exact ⟨_,hp⟩
  · exact ⟨_,hn⟩

private theorem norm_le_norm_add_spectrum_hausdorffDist
    {a : A} {b : B} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    ‖a‖ ≤ ‖b‖ + Metric.hausdorffDist (spectrum ℝ a) (spectrum ℝ b) := by
  have hAn := real_spectrum_nonempty ha
  have hBn := real_spectrum_nonempty hb
  have hA := spectrum.isCompact (𝕜 := ℝ) a
  have hB := spectrum.isCompact (𝕜 := ℝ) b
  have hf := Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded hAn hBn hA.isBounded hB.isBounded
  obtain ⟨x,hx,hn⟩ : ∃ x ∈ spectrum ℝ a, ‖x‖ = ‖a‖ := by
    rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum ha with hp | hn
    · exact ⟨_,hp,by simp⟩
    · exact ⟨_,hn,by simp⟩
  obtain ⟨y,hy,he⟩ := hB.exists_infDist_eq_dist hBn x
  have hd := Metric.infDist_le_hausdorffDist_of_mem hx hf
  rw [he] at hd
  have hyb : ‖y‖ ≤ ‖b‖ := spectrum.norm_le_norm_of_mem hy
  have ht : ‖x‖ ≤ ‖x-y‖+‖y‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x-y) y
  rw [← dist_eq_norm,hn] at ht
  linarith only [ht,hyb,hd]

/-- The native norms of actual self-adjoint elements of different nontrivial
C-star algebras differ by at most the Hausdorff distance of their real spectra. -/
theorem IsSelfAdjoint.abs_norm_sub_norm_le_hausdorffDist_real_spectrum
    {a : A} {b : B} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    |‖a‖-‖b‖| ≤ Metric.hausdorffDist (spectrum ℝ a) (spectrum ℝ b) := by
  have hAB := norm_le_norm_add_spectrum_hausdorffDist ha hb
  have hBA := norm_le_norm_add_spectrum_hausdorffDist hb ha
  rw [Metric.hausdorffDist_comm] at hBA
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- The actual upper spectral edges in different nontrivial C-star algebras
differ by at most the real spectral Hausdorff distance. -/
theorem IsSelfAdjoint.abs_sSup_spectrum_sub_le_hausdorffDist
    {a : A} {b : B} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    |sSup (spectrum ℝ a)-sSup (spectrum ℝ b)| ≤
      Metric.hausdorffDist (spectrum ℝ a) (spectrum ℝ b) :=
    Metric.abs_csSup_sub_csSup_le_hausdorffDist (spectrum.isCompact a) (spectrum.isCompact b)
      (real_spectrum_nonempty ha) (real_spectrum_nonempty hb)

/-- The actual lower spectral edges in different nontrivial C-star algebras
differ by at most the real spectral Hausdorff distance. -/
theorem IsSelfAdjoint.abs_sInf_spectrum_sub_le_hausdorffDist
    {a : A} {b : B} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    |sInf (spectrum ℝ a)-sInf (spectrum ℝ b)| ≤
      Metric.hausdorffDist (spectrum ℝ a) (spectrum ℝ b) :=
    Metric.abs_csInf_sub_csInf_le_hausdorffDist (spectrum.isCompact a) (spectrum.isCompact b)
      (real_spectrum_nonempty ha) (real_spectrum_nonempty hb)
