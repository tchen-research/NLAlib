import NLAlib.ForMathlib.Analysis.CStarAlgebra.SpectrumPerturbation
import NLAlib.Probability.Free.WordMatrixCreationNorm

/-!
# Actual free linear reference spectra and their deterministic mean

Faithfulness of the concrete coefficient representation preserves the real
spectrum of the deterministic mean. Normal spectral perturbation and the
dimension-free creation norm estimate then put the two actual spectra within
twice the square root of the coefficient square mass.

This proves the concrete spectral enclosure used in Lemma 4.7 of
Bandeira--Cipolloni--Schroeder--van Handel, arXiv:2406.11453v2. The sharp
Gaussian/free comparison is a separate theorem.
-/

noncomputable section
set_option autoImplicit false
open scoped ComplexOrder

namespace NLAlib

variable {D ι : Type*} [Fintype D] [DecidableEq D]

/-- The faithful concrete coefficient embedding preserves the actual real
spectrum of a Hermitian matrix, including empty matrix dimension. -/
theorem spectrum_wordMatrixCoefficientHom {A : Matrix D D ℂ} (hA : A.IsHermitian) :
    spectrum ℝ (wordMatrixCoefficientHom (ι := ι) A) = spectrum ℝ A := by
  let e : Matrix D D ℂ ≃⋆ₐ[ℂ] CStarMatrix D D ℂ := CStarMatrix.ofMatrixStarAlgEquiv
  have hC : IsSelfAdjoint (e A) := hA.isSelfAdjoint.map e.toStarAlgHom
  change spectrum ℝ (wordCStarCoefficientHom (D := D) (ι := ι) (e A)) = spectrum ℝ A
  calc
    _ = spectrum ℝ (e A) := hC.map_spectrum_real
      (wordCStarCoefficientHom (D := D) (ι := ι))
      (wordCStarCoefficientHom_injective (D := D) (ι := ι))
    _ = spectrum ℝ A := AlgEquiv.spectrum_eq (e.toAlgEquiv.restrictScalars ℝ) A

/-- Every actual free linear reference spectral point is within `2σ` of an
actual eigenvalue of its deterministic mean. All multiplicities, empty
families and empty matrix dimensions are retained.
Source: arXiv:2406.11453v2, Lemma 4.7. -/
theorem exists_mem_mean_spectrum_dist_le_wordMatrixLinearCombination [Fintype ι]
    {A₀ : Matrix D D ℂ} (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix D D ℂ) (hA : ∀ i, (A i).IsHermitian)
    {x : ℝ} (hx : x ∈ spectrum ℝ (wordMatrixLinearCombination A₀ A)) :
    ∃ y ∈ spectrum ℝ A₀,
      dist x y ≤ 2 * Real.sqrt (specNorm (∑ i, A i ^ 2)) := by
  obtain ⟨y, hy, hd⟩ := IsSelfAdjoint.exists_mem_spectrum_real_dist_le_norm_sub
    (isSelfAdjoint_wordMatrixCoefficientHom (ι := ι) hA₀) hx
  have hspec : spectrum ℝ (wordMatrixCoefficientHom (ι := ι) A₀) = spectrum ℝ A₀ :=
    spectrum_wordMatrixCoefficientHom (ι := ι) hA₀
  refine ⟨y, hspec.subset hy, hd.trans ?_⟩
  rw [norm_sub_rev]
  exact norm_wordMatrixLinearCombination_sub_mean_le A₀ A hA

/-- Conversely every deterministic mean eigenvalue is within `2σ` of the
actual free reference spectrum, by self-adjoint spectral stability. -/
theorem exists_mem_wordMatrixLinearCombination_spectrum_dist_le_mean [Fintype ι]
    {A₀ : Matrix D D ℂ} (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix D D ℂ) (hA : ∀ i, (A i).IsHermitian)
    {x : ℝ} (hx : x ∈ spectrum ℝ A₀) :
    ∃ y ∈ spectrum ℝ (wordMatrixLinearCombination A₀ A),
      dist x y ≤ 2 * Real.sqrt (specNorm (∑ i, A i ^ 2)) := by
  have hx' : x ∈ spectrum ℝ (wordMatrixCoefficientHom (ι := ι) A₀) := by
    rwa [spectrum_wordMatrixCoefficientHom (ι := ι) hA₀]
  obtain ⟨y, hy, hd⟩ := IsSelfAdjoint.exists_mem_spectrum_real_dist_le_norm_sub
    (isSelfAdjoint_wordMatrixLinearCombination hA₀ hA) hx'
  exact ⟨y, hy, hd.trans (norm_wordMatrixLinearCombination_sub_mean_le A₀ A hA)⟩

/-- The actual free reference spectrum and its mean spectrum have Hausdorff
distance at most `2σ`, with no dimension factor or nonzero-variance premise.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem hausdorffDist_spectrum_wordMatrixLinearCombination_mean_le [Fintype ι]
    {A₀ : Matrix D D ℂ} (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix D D ℂ) (hA : ∀ i, (A i).IsHermitian) :
    Metric.hausdorffDist (spectrum ℝ (wordMatrixLinearCombination A₀ A)) (spectrum ℝ A₀) ≤
      2 * Real.sqrt (specNorm (∑ i, A i ^ 2)) := by
  apply Metric.hausdorffDist_le_of_mem_dist (by positivity)
  · exact fun _ hx => exists_mem_mean_spectrum_dist_le_wordMatrixLinearCombination hA₀ A hA hx
  · exact fun _ hx => exists_mem_wordMatrixLinearCombination_spectrum_dist_le_mean hA₀ A hA hx

end NLAlib

end
