import NLAlib.Probability.Gaussian.Basic.StandardVector
import NLAlib.Matrix.Subspaces.OrthogonalProducts
import NLAlib.Matrix.Subspaces.Projections
import NLAlib.ForMathlib.MeasureTheory.ProductSelection

/-!
# Gaussian vectors under orthogonal coordinate maps

Square orthogonal maps preserve the finite product of standard real Gaussian
laws. A matrix with orthonormal rows maps it to the corresponding smaller
product law, including empty coordinate types.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- A real square matrix with orthonormal columns preserves the actual finite
product standard Gaussian law, for arbitrary finite coordinate types. -/
theorem hasLaw_mulVec_gaussianVector_orthogonal
    (U : Matrix n n ℝ) (hU : HasOrthonormalCols U) :
    HasLaw (fun x => U *ᵥ x) (gaussianVector n) (gaussianVector n) := by
  let L := hU.toLinearIsometry
  let e := L.toLinearIsometryEquiv rfl
  have he : HasLaw e (stdGaussian (EuclideanSpace ℝ n))
      (stdGaussian (EuclideanSpace ℝ n)) :=
    ⟨e.continuous.measurable.aemeasurable, stdGaussian_map e⟩
  have hof : HasLaw (WithLp.ofLp : EuclideanSpace ℝ n → n → ℝ)
      (gaussianVector n) (stdGaussian (EuclideanSpace ℝ n)) := by
    refine ⟨(by fun_prop : Measurable (WithLp.ofLp : EuclideanSpace ℝ n → n → ℝ)).aemeasurable, ?_⟩
    rw [← gaussianVector_map_toLp_eq_stdGaussian,
      Measure.map_map (by fun_prop) (by fun_prop)]
    exact Measure.map_id
  have hf : (WithLp.ofLp ∘ e ∘ WithLp.toLp 2) = fun x => U *ᵥ x := by
    funext x
    change WithLp.ofLp (L.toLinearIsometryEquiv rfl (WithLp.toLp 2 x)) = _
    rw [LinearIsometry.toLinearIsometryEquiv_apply]
    rfl
  rw [← hf]
  exact hof.comp (he.comp (hasLaw_toLp_gaussianVector (n := n)))

/-- An actual real matrix with orthonormal rows maps a finite standard Gaussian
vector to a vector of independent standard Gaussians. The result allows a
smaller target coordinate family and derives its joint law by orthogonal
completion and injective coordinate selection. -/
theorem hasLaw_mulVec_gaussianVector_orthonormalRows
    (U : Matrix m n ℝ) (hU : HasOrthonormalCols Uᵀ) :
    HasLaw (fun x => U *ᵥ x) (gaussianVector m) (gaussianVector n) := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (card_le_card_of_hasOrthonormalCols hU)
  obtain ⟨W, hW, hWe⟩ := exists_unitary_completion Uᵀ hU e
  have hWt : HasOrthonormalCols Wᵀ := by
    change W * Wᵀ = 1
    exact mul_eq_one_comm.mp (show Wᵀ * W = 1 from hW)
  have hrot := hasLaw_mulVec_gaussianVector_orthogonal Wᵀ hWt
  have hsel := hasLaw_pi_select (fun _ : n => gaussianReal 0 1) e e.injective
  have h := hsel.comp hrot
  have hf : (fun x : n → ℝ => fun j => (Wᵀ *ᵥ x) (e j)) = fun x => U *ᵥ x := by
    ext x j
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hWe]
  change HasLaw (fun x : n → ℝ => fun j => (Wᵀ *ᵥ x) (e j)) _ _ at h
  rw [hf] at h
  exact h

end NLAlib
