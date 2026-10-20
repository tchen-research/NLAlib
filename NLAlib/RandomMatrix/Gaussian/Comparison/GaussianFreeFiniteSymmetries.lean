import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteInterpolation
import NLAlib.Probability.Gaussian.Basic.CoordinateSymmetries

/-!
# Native signed-permutation symmetries of the finite-N interpolant

The ensemble conjugations are realized by explicit measure-preserving maps
on the actual independent real Gaussian coordinates. This establishes the
source symmetries without assuming invariance of any matrix expectation.
Source: arXiv:2108.06312v2, Lemma 5.2.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix Kronecker

namespace NLAlib

variable {ι n d : Type*} [Fintype ι] [Fintype n] [Fintype d]
  [DecidableEq ι] [DecidableEq n] [DecidableEq d]

/-- Reindex both ensemble coordinates of the genuine GUE family and the
single ensemble coordinate of the genuine diagonal family. -/
def gaussianFreeEnsembleCoordinatePerm (σ : Equiv.Perm n) :
    Equiv.Perm (GaussianFreeFiniteCoordinate ι n) :=
  Equiv.sumCongr (Equiv.prodCongr (Equiv.refl ι) σ)
    (Equiv.prodCongr (Equiv.refl ι)
      (Equiv.prodCongr (Equiv.refl Unit)
        (Equiv.prodCongr σ (Equiv.prodCongr σ (Equiv.refl (Fin 2))))))

omit [DecidableEq ι] [DecidableEq n] in
/-- The sample-coordinate ensemble permutation preserves the actual
canonical Gaussian probability measure. -/
theorem measurePreserving_gaussianFreeEnsemble_permute (σ : Equiv.Perm n) :
    MeasurePreserving
      (fun x : GaussianFreeFiniteCoordinate ι n → ℝ =>
        fun k => x (gaussianFreeEnsembleCoordinatePerm σ k))
      (gaussianVector (GaussianFreeFiniteCoordinate ι n))
      (gaussianVector (GaussianFreeFiniteCoordinate ι n)) :=
  measurePreserving_gaussianVector_coordinate_permute _

omit [Fintype d] [DecidableEq ι] [DecidableEq d] in
/-- An explicit sample-coordinate permutation realizes the actual ensemble
permutation of the source matrix at every real interpolation parameter. -/
theorem gaussianFreeFiniteInterpolation_permute
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (q : ℝ)
    (x : GaussianFreeFiniteCoordinate ι n → ℝ) (σ : Equiv.Perm n) :
    gaussianFreeFiniteInterpolation A₀ A q
      (fun k => x (gaussianFreeEnsembleCoordinatePerm σ k)) =
      (fun ab ce => gaussianFreeFiniteInterpolation A₀ A q x
        (ab.1,σ ab.2) (ce.1,σ ce.2)) := by
  rw [gaussianFreeFiniteInterpolation_eq_diagonal_add_gue]
  ext ab ce
  rcases ab with ⟨a,r⟩
  rcases ce with ⟨b,s⟩
  rw [gaussianFreeFiniteInterpolation_eq_diagonal_add_gue]
  simp [gaussianFreeEnsembleCoordinatePerm,Matrix.diagonal_apply,
    Matrix.one_apply,Matrix.add_apply,Matrix.smul_apply,Matrix.sum_apply,
    gueMatrix,gueRawMatrix,Matrix.conjTranspose_apply,σ.injective.eq_iff]

/-- A coordinate is negated precisely when its GUE entry has exactly one
ensemble endpoint at the reflected coordinate. Diagonal coordinates stay fixed. -/
def gaussianFreeEnsembleCoordinateFlip (r : n) : GaussianFreeFiniteCoordinate ι n → Bool
  | .inl _ => false
  | .inr (_,_,u,v,_) => Bool.xor (decide (u=r)) (decide (v=r))

/-- Actual selected Gaussian coordinate reflection realizing one ensemble
diagonal sign conjugation. -/
def gaussianFreeEnsembleReflect (r : n)
    (x : GaussianFreeFiniteCoordinate ι n → ℝ) : GaussianFreeFiniteCoordinate ι n → ℝ :=
  fun k => if gaussianFreeEnsembleCoordinateFlip r k then -x k else x k

omit [DecidableEq ι] in
/-- The explicit reflection preserves the actual independent Gaussian
product law, including all degenerate dimensions. -/
theorem measurePreserving_gaussianFreeEnsemble_reflect (r : n) :
    MeasurePreserving (gaussianFreeEnsembleReflect (ι := ι) r)
      (gaussianVector (GaussianFreeFiniteCoordinate ι n))
      (gaussianVector (GaussianFreeFiniteCoordinate ι n)) :=
  measurePreserving_gaussianVector_coordinate_negate
    (fun k => gaussianFreeEnsembleCoordinateFlip r k = true)

omit [Fintype d] [DecidableEq ι] [DecidableEq d] in
/-- One ensemble sign reflection is realized pointwise by its exact
Gaussian coordinate negations. This is a true native matrix identity. -/
theorem gaussianFreeFiniteInterpolation_reflect
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (q : ℝ)
    (x : GaussianFreeFiniteCoordinate ι n → ℝ) (r : n) :
    gaussianFreeFiniteInterpolation A₀ A q (gaussianFreeEnsembleReflect r x) =
      (fun ab ce => (if ab.2=r then (-1 : ℂ) else 1)*
        gaussianFreeFiniteInterpolation A₀ A q x ab ce*
          (if ce.2=r then (-1 : ℂ) else 1)) := by
  rw [gaussianFreeFiniteInterpolation_eq_diagonal_add_gue]
  ext ab ce
  rcases ab with ⟨a,u⟩
  rcases ce with ⟨b,v⟩
  rw [gaussianFreeFiniteInterpolation_eq_diagonal_add_gue]
  by_cases hu : u=r <;> by_cases hv : v=r
  all_goals
    have hv' : (r=v) ↔ (v=r) := eq_comm
    simp [gaussianFreeEnsembleReflect,gaussianFreeEnsembleCoordinateFlip,
      Matrix.diagonal_apply,Matrix.one_apply,Matrix.add_apply,
      Matrix.smul_apply,Matrix.sum_apply,gueMatrix,gueRawMatrix,
      Matrix.conjTranspose_apply,hu,hv,hv',Finset.mul_sum]
  all_goals
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring

end NLAlib

end
