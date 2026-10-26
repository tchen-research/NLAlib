import NLAlib.RandomMatrix.Gaussian.Basic.GaussianMatrix

/-!
# Independent column blocks of a Gaussian matrix

Rearranging the actual independent Gaussian entries into row-indexed blocks gives a
product of Gaussian matrix laws. This supplies independence of block events without
assuming it separately. Source: finite products of independent Gaussian coordinates.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace NLAlib

variable {Ω n b t : Type*} [MeasurableSpace Ω] [Fintype n] [Fintype b] [Fintype t]
  {μ : Measure Ω} {G : Ω → Matrix n (b × t) ℝ}

/-- A column block of a standard Gaussian matrix has its native standard Gaussian law. -/
theorem hasLaw_gaussianMatrix_columnBlock
    (hG : HasLaw G (gaussianMatrix n (b × t)) μ) (a : b) :
    HasLaw (fun ω => Matrix.of fun i j => G ω i (a, j)) (gaussianMatrix n t) μ := by
  apply hasLaw_gaussianMatrix_of_iIndepFun
  · intro ij
    exact hG.hasLaw_entry_gaussianReal ij.1 (a, ij.2)
  · exact iIndepFun.precomp (g := fun ij : n × t => (ij.1, (a, ij.2)))
      (by intro i j h; cases i; cases j; simpa using h)
      hG.iIndepFun_entry_of_gaussianMatrix

/-- All column blocks jointly have the product of their native Gaussian matrix laws. -/
theorem hasLaw_gaussianMatrix_columnBlocks
    (hG : HasLaw G (gaussianMatrix n (b × t)) μ) :
    HasLaw (fun ω a => Matrix.of fun i j => G ω i (a, j))
      (Measure.pi fun _ : b => gaussianMatrix n t) μ := by
  let H : Ω → Matrix b (n × t) ℝ := fun ω => Matrix.of fun a ij => G ω ij.1 (a, ij.2)
  have hH : HasLaw H (gaussianMatrix b (n × t)) μ := by
    apply hasLaw_gaussianMatrix_of_iIndepFun
    · intro aij
      exact hG.hasLaw_entry_gaussianReal aij.2.1 (aij.1, aij.2.2)
    · exact iIndepFun.precomp (g := fun aij : b × (n × t) =>
          (aij.2.1, (aij.1, aij.2.2)))
        (by intro ⟨a,i,j⟩ ⟨a',i',j'⟩ h; simpa [Prod.mk.injEq, and_comm, and_left_comm] using h)
        hG.iIndepFun_entry_of_gaussianMatrix
  have hrows := measurePreserving_ofMeasurableEquiv_gaussianMatrix.symm.hasLaw.comp hH
  let e := (MeasurableEquiv.curry n t ℝ).trans Matrix.ofMeasurableEquiv
  have he : MeasurePreserving e (Measure.pi fun _ : n × t => gaussianReal 0 1)
      (gaussianMatrix n t) :=
    ⟨e.measurable, gaussianMatrix_eq_map_curry.symm⟩
  exact (measurePreserving_pi (fun _ : b => Measure.pi fun _ : n × t => gaussianReal 0 1)
    (fun _ : b => gaussianMatrix n t) (fun _ => he)).hasLaw.comp hrows

/-- The actual Gaussian column blocks are mutually independent. -/
theorem iIndepFun_gaussianMatrix_columnBlocks
    (hG : HasLaw G (gaussianMatrix n (b × t)) μ) :
    iIndepFun (fun a ω => Matrix.of fun i j => G ω i (a, j)) μ := by
  let : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  exact (iIndepFun_iff_hasLaw_pi_pi (hasLaw_gaussianMatrix_columnBlock hG)).2
    (hasLaw_gaussianMatrix_columnBlocks hG)

end NLAlib
