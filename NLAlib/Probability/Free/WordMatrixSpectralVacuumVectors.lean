import NLAlib.Probability.Free.WordMatrixVacuumEmbedding
import NLAlib.Probability.Free.WordMatrixSpectrum
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Actual approximate spectral vectors inside the amplified vacuum subspace

A free spectral point is close to a genuine mean eigenvalue. Its actual
unit matrix eigenvector, tensored with the genuine word vacuum, has shifted
residual at most five times the imaginary height above the free-series
scale. This is the geometric input to the large-height moment estimate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical ComplexOrder

namespace NLAlib

variable {D ι : Type*} [Fintype D] [DecidableEq D] [Fintype ι]
local notation "W" => WordHilbertSpace ι
local notation "K" => WordMatrixHilbertSpace D ι

omit [Fintype ι] in
/-- A genuine coefficient eigenvector remains an actual eigenvector of its
matrix mean after embedding into the existing vacuum subspace. -/
theorem wordMatrixCoefficientHom_wordMatrixVacuumEmbedding_eigenvector
    {A₀ : Matrix D D ℂ} (hA₀ : A₀.IsHermitian) (k : D) :
    wordMatrixCoefficientHom A₀ (wordMatrixVacuumEmbedding (ι := ι) (hA₀.eigenvectorBasis k)) =
      (hA₀.eigenvalues k : ℂ)•
        wordMatrixVacuumEmbedding (ι := ι) (hA₀.eigenvectorBasis k) := by
  apply PiLp.ext
  intro i
  rw [wordMatrixCoefficientHom_apply]
  simp only [PiLp.smul_apply,wordMatrixVacuumEmbedding_apply,smul_smul]
  rw [← Finset.sum_smul]
  have he := congrFun (hA₀.mulVec_eigenvectorBasis k) i
  change (∑ j, A₀ i j*(hA₀.eigenvectorBasis k) j)=
    (hA₀.eigenvalues k : ℂ)*(hA₀.eigenvectorBasis k) i at he
  change (∑ j, A₀ i j*(hA₀.eigenvectorBasis k) j)•wordVacuum ι=
    ((hA₀.eigenvalues k : ℂ)*(hA₀.eigenvectorBasis k) i)•wordVacuum ι
  exact congrArg (fun c : ℂ => c•wordVacuum ι) he

/-- Above the actual centered free-series scale, each actual free spectral
point produces a unit coefficient vacuum vector with shifted residual at
most five times the actual imaginary height. Empty dimensions require no
separate assumption, because the actual spectrum membership is impossible.

Source: arXiv:2406.11453v2, the large-height case of Corollary 4.4. -/
theorem exists_unit_wordMatrixVacuumEmbedding_residual_le
    {A₀ : Matrix D D ℂ} (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix D D ℂ) (hA : ∀ k, (A k).IsHermitian)
    {z : ℂ} (hz : 0<z.im)
    (hση : Real.sqrt (specNorm (∑ k, A k^2))≤z.im)
    (hspec : z.re∈spectrum ℝ (wordMatrixLinearCombination A₀ A)) :
    ∃ v : EuclideanSpace ℂ D, ‖v‖=1 ∧
      ‖(algebraMap ℂ (K →L[ℂ] K) z-wordMatrixLinearCombination A₀ A)
        (wordMatrixVacuumEmbedding (ι := ι) v)‖≤5*z.im := by
  let σ := Real.sqrt (specNorm (∑ k, A k^2))
  obtain ⟨t,ht,hdist⟩ := exists_mem_mean_spectrum_dist_le_wordMatrixLinearCombination hA₀ A hA hspec
  obtain ⟨k,hk⟩ := hA₀.spectrum_real_eq_range_eigenvalues ▸ ht
  let v := hA₀.eigenvectorBasis k
  let u := wordMatrixVacuumEmbedding (ι := ι) v
  let X := wordMatrixLinearCombination A₀ A
  let d := wordMatrixCoefficientHom (ι := ι) A₀
  let Y := X-d
  have hv : ‖v‖=1 := hA₀.eigenvectorBasis.orthonormal.norm_eq_one k
  have hu : ‖u‖=1 := by simpa only [u,LinearIsometry.norm_map] using hv
  have hdu : d u=(t : ℂ)•u := by
    rw [← hk]
    exact wordMatrixCoefficientHom_wordMatrixVacuumEmbedding_eigenvector hA₀ k
  have hY : ‖Y‖≤2*σ := norm_wordMatrixLinearCombination_sub_mean_le A₀ A hA
  have hscalar : ‖z-(t : ℂ)‖≤2*σ+z.im := by
    have hd : |z.re-t|≤2*σ := by simpa only [Real.dist_eq] using hdist
    calc
      _ ≤ |(z-(t : ℂ)).re|+|(z-(t : ℂ)).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ _ := by
        simp only [Complex.sub_re,Complex.ofReal_re,Complex.sub_im,Complex.ofReal_im,
          sub_zero,abs_of_pos hz]
        exact add_le_add hd le_rfl
  have hXu : X u=d u+Y u := by
    dsimp only [Y]
    rw [sub_apply]
    abel
  have hres : (algebraMap ℂ (K →L[ℂ] K) z-X) u=(z-(t : ℂ))•u-Y u := by
    rw [sub_apply,Algebra.algebraMap_eq_smul_one,smul_apply,one_apply_eq_self,hXu,hdu,sub_smul]
    abel
  refine ⟨v,hv,?_⟩
  change ‖(algebraMap ℂ (K →L[ℂ] K) z-X) u‖≤5*z.im
  rw [hres]
  calc
    _ ≤ ‖(z-(t : ℂ))•u‖+‖Y u‖ := norm_sub_le _ _
    _ ≤ ‖z-(t : ℂ)‖*‖u‖+‖Y‖*‖u‖ :=
      add_le_add (norm_smul _ _).le (Y.le_opNorm u)
    _ ≤ (2*σ+z.im)*1+(2*σ)*1 := by
      rw [hu]
      exact add_le_add (mul_le_mul_of_nonneg_right hscalar zero_le_one)
        (mul_le_mul_of_nonneg_right hY zero_le_one)
    _ ≤ _ := by nlinarith only [hση]

end NLAlib

end
