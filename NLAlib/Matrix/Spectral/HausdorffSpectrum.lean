import NLAlib.Matrix.Spectral.CourantFischer
import NLAlib.ForMathlib.MeasureTheory.Matrix
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Hausdorff distance of Hermitian spectra

Weyl's inequality controls the actual real spectra in Hausdorff distance by
the spectral norm of the matrix difference. Distance to a fixed spectral set
is consequently a Lipschitz observable on Hermitian matrices. Projecting to
the Hermitian part supplies a continuous extension and measurability for
random matrices that are Hermitian almost everywhere.

These are deterministic observable helpers for the spectral-universality
arguments of Brailovskaya–van Handel, arXiv:2201.05142v3, §7, and the atlas
entry `independent-sum-spectrum-universality`.
-/

noncomputable section

open scoped Matrix
open MeasureTheory

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜]
  {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

open scoped Matrix.Norms.L2Operator in
private theorem eigenvalues₀_sub_le_specNorm_sub {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (i : Fin (Fintype.card n)) :
    hA.eigenvalues₀ i - hB.eigenvalues₀ i ≤ specNorm (A - B) := by
  let z : Fin (Fintype.card n) := ⟨0, Fintype.card_pos⟩
  have hu := hB.eigenvalues₀_add_le (hA.sub hB) i z (by simp [z])
  simp only [z, Nat.add_zero, Fin.eta] at hu
  have heq : B + (A - B) = A := by abel
  have hcongr := (hB.add (hA.sub hB)).eigenvalues₀_congr hA heq i
  rw [hcongr] at hu
  have hmem : RCLike.ofReal ((hA.sub hB).eigenvalues₀ z) ∈ spectrum 𝕜 (A - B) := by
    rw [(hA.sub hB).spectrum_eq_image_range,
      ← (hA.sub hB).range_eigenvalues₀]
    exact ⟨_, ⟨z, rfl⟩, rfl⟩
  have hb : (hA.sub hB).eigenvalues₀ z ≤ specNorm (A - B) := by
    have hn : ‖(RCLike.ofReal ((hA.sub hB).eigenvalues₀ z) : 𝕜)‖ ≤ ‖A - B‖ :=
      spectrum.norm_le_norm_of_mem hmem
    exact (le_abs_self _).trans (by simpa only [RCLike.norm_ofReal, specNorm_eq_norm] using hn)
  linarith only [hu, hb]

private theorem abs_eigenvalues₀_sub_le_specNorm_sub {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (i : Fin (Fintype.card n)) :
    |hA.eigenvalues₀ i - hB.eigenvalues₀ i| ≤ specNorm (A - B) := by
  have hu := eigenvalues₀_sub_le_specNorm_sub hA hB i
  have hl := eigenvalues₀_sub_le_specNorm_sub hB hA i
  have he : specNorm (B - A) = specNorm (A - B) := by
    rw [← neg_sub A B, specNorm_neg]
  rw [he] at hl
  exact abs_le.mpr ⟨by linarith only [hl], hu⟩

/-- The Hausdorff distance between the actual real spectra of two Hermitian
matrices is at most the spectral norm of their difference. -/
theorem hausdorffDist_spectrum_le_specNorm_sub {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Metric.hausdorffDist (spectrum ℝ A) (spectrum ℝ B) ≤ specNorm (A - B) := by
  apply Metric.hausdorffDist_le_of_mem_dist (specNorm_nonneg _)
  · intro x hx
    rw [hA.spectrum_real_eq_range_eigenvalues, ← hA.range_eigenvalues₀] at hx
    obtain ⟨i, rfl⟩ := hx
    refine ⟨hB.eigenvalues₀ i, ?_, ?_⟩
    · rw [hB.spectrum_real_eq_range_eigenvalues, ← hB.range_eigenvalues₀]
      exact ⟨i, rfl⟩
    · simpa only [Real.dist_eq] using abs_eigenvalues₀_sub_le_specNorm_sub hA hB i
  · intro x hx
    rw [hB.spectrum_real_eq_range_eigenvalues, ← hB.range_eigenvalues₀] at hx
    obtain ⟨i, rfl⟩ := hx
    refine ⟨hA.eigenvalues₀ i, ?_, ?_⟩
    · rw [hA.spectrum_real_eq_range_eigenvalues, ← hA.range_eigenvalues₀]
      exact ⟨i, rfl⟩
    · simpa only [Real.dist_eq, abs_sub_comm] using
        abs_eigenvalues₀_sub_le_specNorm_sub hA hB i

private theorem hausdorffEDist_spectrum_ne_top {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Metric.hausdorffEDist (spectrum ℝ A) (spectrum ℝ B) ≠ ⊤ := by
  apply Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
  · rw [hA.spectrum_real_eq_range_eigenvalues]
    exact Set.range_nonempty _
  · rw [hB.spectrum_real_eq_range_eigenvalues]
    exact Set.range_nonempty _
  · exact A.finite_real_spectrum.isBounded
  · exact B.finite_real_spectrum.isBounded

/-- Hausdorff distance from a Hermitian spectrum to any fixed real set is
1-Lipschitz in the spectral norm. A native spectral reference is obtained by
taking `s = spectrum ℝ C`; no approximation hypotheses are needed. -/
theorem abs_hausdorffDist_spectrum_sub_le_specNorm_sub {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (s : Set ℝ) :
    |Metric.hausdorffDist (spectrum ℝ A) s - Metric.hausdorffDist (spectrum ℝ B) s| ≤
      specNorm (A - B) := by
  have hu := Metric.hausdorffDist_triangle (u := s) (hausdorffEDist_spectrum_ne_top hA hB)
  have hl := Metric.hausdorffDist_triangle (u := s) (hausdorffEDist_spectrum_ne_top hB hA)
  rw [Metric.hausdorffDist_comm (s := spectrum ℝ B) (t := spectrum ℝ A)] at hl
  have hb := hausdorffDist_spectrum_le_specNorm_sub hA hB
  exact abs_le.mpr ⟨by linarith only [hl, hb], by linarith only [hu, hb]⟩

open scoped Matrix.Norms.L2Operator in
/-- On the native self-adjoint matrix space, Hausdorff distance to a fixed
real set is a 1-Lipschitz observable. -/
theorem lipschitzWith_hausdorffDist_spectrum (s : Set ℝ) :
    LipschitzWith 1 (fun A : selfAdjoint (Matrix n n 𝕜) =>
      Metric.hausdorffDist (spectrum ℝ (A : Matrix n n 𝕜)) s) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  change |Metric.hausdorffDist (spectrum ℝ (A : Matrix n n 𝕜)) s -
      Metric.hausdorffDist (spectrum ℝ (B : Matrix n n 𝕜)) s| ≤
    ‖(A : Matrix n n 𝕜) - (B : Matrix n n 𝕜)‖
  simpa only [specNorm_eq_norm] using
    abs_hausdorffDist_spectrum_sub_le_specNorm_sub A.property.isHermitian B.property.isHermitian s

open scoped Matrix.Norms.L2Operator in
/-- Projecting to the Hermitian part gives a continuous, globally defined
extension of the actual spectral-distance observable. -/
theorem continuous_hausdorffDist_spectrum_selfAdjointPart (s : Set ℝ) :
    Continuous (fun A : Matrix n n 𝕜 =>
      Metric.hausdorffDist (spectrum ℝ (selfAdjointPart ℝ A : Matrix n n 𝕜)) s) := by
  have hp : Continuous (selfAdjointPart ℝ : Matrix n n 𝕜 → selfAdjoint (Matrix n n 𝕜)) :=
    continuous_selfAdjointPart ℝ (Matrix n n 𝕜)
  exact (lipschitzWith_hausdorffDist_spectrum s).continuous.comp hp

/-- A measurable complex random matrix that is Hermitian almost everywhere
has an almost everywhere measurable native spectral-distance observable. -/
theorem aemeasurable_hausdorffDist_spectrum {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → Matrix n n ℂ} (hX : AEMeasurable X μ)
    (hHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian) (s : Set ℝ) :
    AEMeasurable (fun ω => Metric.hausdorffDist (spectrum ℝ (X ω)) s) μ := by
  have hm := (continuous_hausdorffDist_spectrum_selfAdjointPart (𝕜 := ℂ) (n := n) s).measurable
  apply (hm.comp_aemeasurable hX).congr
  filter_upwards [hHerm] with ω hω
  exact congrArg (fun A : Matrix n n ℂ => Metric.hausdorffDist (spectrum ℝ A) s)
    (hω.isSelfAdjoint.coe_selfAdjointPart_apply ℝ)

end NLAlib
