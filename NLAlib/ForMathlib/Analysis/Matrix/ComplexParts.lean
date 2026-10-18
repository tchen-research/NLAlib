import NLAlib.ForMathlib.MeasureTheory.Matrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Real parts of finite complex matrices

The entrywise real part is a continuous real-linear map. It preserves the
Hermitian condition as a real symmetry condition, and complexification
recovers the original matrix exactly when every imaginary entry vanishes.
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- Taking the real part of every matrix entry as a continuous real-linear map. -/
def reCLM : Matrix m n ℂ →L[ℝ] Matrix m n ℝ :=
  (show Matrix m n ℂ →ₗ[ℝ] Matrix m n ℝ from
    { toFun := fun A => A.map Complex.re
      map_add' := by intro A B; ext i j; exact Complex.add_re _ _
      map_smul' := by intro c A; ext i j; simp only [map_apply, Matrix.smul_apply,
        Complex.smul_re, RingHom.id_apply] }).toContinuousLinearMap

omit [DecidableEq n] in
/-- The continuous matrix real-part map is entrywise real part. -/
@[simp] theorem reCLM_apply (A : Matrix m n ℂ) : reCLM A = A.map Complex.re := rfl

omit [DecidableEq n] in
/-- Taking real parts after complexification recovers the real matrix. -/
@[simp] theorem reCLM_map_ofReal (A : Matrix m n ℝ) :
    reCLM (A.map Complex.ofReal) = A := by ext i j; simp

omit [DecidableEq n] in
/-- A matrix with zero imaginary entries is exactly the complexification
of its entrywise real part. -/
theorem map_ofReal_reCLM_of_im_eq_zero (A : Matrix m n ℂ)
    (hA : ∀ i j, (A i j).im = 0) :
    (reCLM A).map Complex.ofReal = A := by
  ext i j
  apply Complex.ext
  · rfl
  · exact (hA i j).symm

omit [DecidableEq n] in
/-- The entrywise real part of a Hermitian matrix is real symmetric. -/
theorem IsHermitian.reCLM {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (reCLM A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simpa only [reCLM_apply, map_apply, star_trivial, Complex.star_def, Complex.conj_re] using
    congrArg Complex.re (hA.apply i j)

end Matrix
