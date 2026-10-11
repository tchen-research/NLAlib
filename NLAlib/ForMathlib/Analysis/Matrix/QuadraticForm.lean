import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Continuous matrix quadratic forms and complex polarization

Quadratic forms commute with actual integrals and conditional expectations through
continuous linear maps. Mathlib's complex polarization identifies Hermitian matrices.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A deterministic-vector quadratic form is a continuous complex-linear map of the
matrix argument. Source: finite quadratic-form algebra; supports the supplied audit
`audit:local-moment` and `matrix-freedman` (partial). -/
def matrixQuadraticFormCLM (u : n → ℂ) : Matrix n n ℂ →L[ℂ] ℂ :=
  (show Matrix n n ℂ →ₗ[ℂ] ℂ from
    { toFun := fun A => star u ⬝ᵥ (A *ᵥ u)
      map_add' := by intros; simp [Matrix.add_mulVec, dotProduct_add]
      map_smul' := by intros; simp [Matrix.smul_mulVec, dotProduct_smul] }).toContinuousLinearMap

omit [DecidableEq n] in
/-- The complex quadratic-form linear map evaluates the actual finite vector action.
Source: the exact construction; `matrix-freedman` (partial). -/
@[simp] theorem matrixQuadraticFormCLM_apply (u : n → ℂ) (A : Matrix n n ℂ) :
    matrixQuadraticFormCLM u A = star u ⬝ᵥ (A *ᵥ u) := rfl

/-- The real quadratic form is a continuous real-linear map of a complex matrix.
Source: real part of the complex quadratic-form map; `matrix-freedman` (partial). -/
def matrixRealQuadraticFormCLM (u : n → ℂ) : Matrix n n ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp ((matrixQuadraticFormCLM u).restrictScalars ℝ)

omit [DecidableEq n] in
/-- The real quadratic-form linear map is the real part of the actual complex form.
Source: the exact construction; `matrix-freedman` (partial). -/
@[simp] theorem matrixRealQuadraticFormCLM_apply (u : n → ℂ) (A : Matrix n n ℂ) :
    matrixRealQuadraticFormCLM u A = (star u ⬝ᵥ (A *ᵥ u)).re := rfl

/-- The actual Hermitian squared quadratic form is the squared Euclidean norm of the
matrix-vector image. Source: the Gram identity and complex scalar norm squares;
supports `audit:local-moment`, `matrix-freedman` (partial). -/
theorem re_star_dotProduct_sq_mulVec_eq_sum_sq_norm_of_isHermitian
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (u : n → ℂ) :
    (star u ⬝ᵥ (A ^ 2 *ᵥ u)).re = ∑ i, ‖(A *ᵥ u) i‖ ^ 2 := by
  have hsq : A ^ 2 = Aᴴ * A := by rw [hA.eq, sq]
  rw [hsq, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
  simp only [dotProduct, Complex.re_sum, Pi.star_apply, RCLike.star_def,
    Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- Real quadratic-form equality determines a Hermitian complex matrix. Hermitian
quadratic forms have zero imaginary part; Mathlib's complex polarization then identifies
the associated Euclidean linear maps and hence the original matrices.
Source: complex polarization; supplied audit `audit:combined`;
atlas `matrix-freedman` (partial). -/
theorem matrix_eq_of_isHermitian_of_re_dotProduct_mulVec_eq
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hq : ∀ u : n → ℂ, (star u ⬝ᵥ (A *ᵥ u)).re = (star u ⬝ᵥ (B *ᵥ u)).re) : A = B := by
  have hfull : ∀ u : n → ℂ, star u ⬝ᵥ (A *ᵥ u) = star u ⬝ᵥ (B *ᵥ u) := by
    intro u
    apply Complex.ext (hq u)
    have hAi : (star u ⬝ᵥ (A *ᵥ u)).im = 0 := hA.im_star_dotProduct_mulVec_self u
    have hBi : (star u ⬝ᵥ (B *ᵥ u)).im = 0 := hB.im_star_dotProduct_mulVec_self u
    exact hAi.trans hBi.symm
  apply Matrix.toEuclideanLin.injective
  apply (ext_inner_map _ _).mp
  intro x
  have hinner : inner ℂ x (Matrix.toEuclideanLin A x) = inner ℂ x (Matrix.toEuclideanLin B x) := by
    simpa only [PiLp.inner_apply, Matrix.toLpLin_apply, RCLike.inner_apply', dotProduct,
      starRingEnd_apply, Pi.star_apply] using hfull (WithLp.ofLp x)
  have hconj := congrArg star hinner
  simpa only [RCLike.star_def, inner_conj_symm] using hconj

end NLAlib
