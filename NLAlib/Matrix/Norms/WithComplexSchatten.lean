import NLAlib.Matrix.Norms.ComplexSchattenNorms
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import NLAlib.ForMathlib.MeasureTheory.Matrix

/-!
# Complex matrices as a real Banach space with the native Schatten norm

For a fixed finite exponent at least one the norm is exactly
`schattenNormReal`. The type synonym preserves the ordinary complex matrix
instances and supplies the real Banach-space structure needed by Bochner
conditional expectation. Its construction includes zero and empty matrices.
-/

noncomputable section

open MeasureTheory
open scoped Matrix

namespace NLAlib

/-- Complex square matrices with their native finite Schatten norm, regarded
as a real normed vector space. -/
def WithComplexSchatten (p : ℝ) (_hp : 1 ≤ p) (n : Type*) := Matrix n n ℂ

namespace WithComplexSchatten

variable {p : ℝ} {hp : 1 ≤ p} {n : Type*} [Fintype n] [DecidableEq n]

/-- The additive group is inherited from the underlying complex matrices. -/
instance : AddCommGroup (WithComplexSchatten p hp n) :=
  inferInstanceAs (AddCommGroup (Matrix n n ℂ))

/-- Real scalar multiplication is inherited from the underlying complex matrices. -/
instance : Module ℝ (WithComplexSchatten p hp n) :=
  inferInstanceAs (Module ℝ (Matrix n n ℂ))

/-- Equip an ordinary complex matrix with its fixed Schatten norm. -/
def ofMatrix (A : Matrix n n ℂ) : WithComplexSchatten p hp n := A

/-- The underlying ordinary complex matrix. -/
def toMatrix (A : WithComplexSchatten p hp n) : Matrix n n ℂ := A

/-- The identity of underlying real vector spaces. -/
def matrixLinearEquiv : Matrix n n ℂ ≃ₗ[ℝ] WithComplexSchatten p hp n where
  toFun := ofMatrix
  invFun := toMatrix
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

/-- The additive norm is the finite Schatten norm with the fixed exponent. -/
instance : NormedAddCommGroup (WithComplexSchatten p hp n) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun A => schattenNormReal (toMatrix A) p
      map_zero' := schattenNormReal_zero (lt_of_lt_of_le zero_lt_one hp)
      add_le' := fun A B => schattenNormReal_add_le_complex (toMatrix A) (toMatrix B) hp
      neg' := by
        intro A
        change schattenNormReal (-toMatrix A) p = schattenNormReal (toMatrix A) p
        rw [← neg_one_smul ℝ (toMatrix A), schattenNormReal_real_smul_complex _ _
          (lt_of_lt_of_le zero_lt_one hp)]
        norm_num
      eq_zero_of_map_eq_zero' := fun A hA =>
        (schattenNormReal_eq_zero_iff _ (lt_of_lt_of_le zero_lt_one hp)).1 hA }

/-- The finite Schatten norm is compatible with real scalar multiplication. -/
instance : NormedSpace ℝ (WithComplexSchatten p hp n) where
  norm_smul_le c A := by
    change schattenNormReal (c • toMatrix A) p ≤ ‖c‖ * schattenNormReal (toMatrix A) p
    rw [schattenNormReal_real_smul_complex _ _ (lt_of_lt_of_le zero_lt_one hp), Real.norm_eq_abs]

/-- The Schatten matrix space is finite-dimensional over the reals. -/
instance : FiniteDimensional ℝ (WithComplexSchatten p hp n) := matrixLinearEquiv.finiteDimensional

/-- The finite-dimensional Schatten matrix space is complete. -/
instance : CompleteSpace (WithComplexSchatten p hp n) := FiniteDimensional.complete ℝ _

/-- The measurable sets are the Borel sets of the Schatten norm topology. -/
instance : MeasurableSpace (WithComplexSchatten p hp n) := borel _

/-- The chosen measurable structure is the Borel structure. -/
instance : BorelSpace (WithComplexSchatten p hp n) := ⟨rfl⟩

/-- The norm is the native finite Schatten norm, with its exact normalization. -/
@[simp] theorem norm_ofMatrix (A : Matrix n n ℂ) :
    ‖(ofMatrix A : WithComplexSchatten p hp n)‖ = schattenNormReal A p := rfl

/-- Reading the matrix retains the exact native norm. -/
@[simp] theorem norm_eq_schattenNormReal (A : WithComplexSchatten p hp n) :
    ‖A‖ = schattenNormReal (toMatrix A) p := rfl

/-- Changing between the two finite-dimensional matrix norms is a continuous
real linear equivalence. -/
def matrixContinuousLinearEquiv : Matrix n n ℂ ≃L[ℝ] WithComplexSchatten p hp n :=
  matrixLinearEquiv.toContinuousLinearEquiv

/-- The ordinary-to-Schatten map is measurable. -/
theorem measurable_ofMatrix :
    Measurable (ofMatrix : Matrix n n ℂ → WithComplexSchatten p hp n) :=
  matrixContinuousLinearEquiv.continuous.measurable

open scoped Matrix.Norms.L2Operator in
/-- Bochner integration commutes with the change to the native complex
Schatten norm. -/
theorem integral_ofMatrix {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → Matrix n n ℂ} (hf : Integrable f μ) :
    (∫ ω, (ofMatrix (f ω) : WithComplexSchatten p hp n) ∂μ) = ofMatrix (∫ ω, f ω ∂μ) :=
  matrixContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm hf

end WithComplexSchatten

open scoped Matrix.Norms.L2Operator in
/-- Conditional expectation contracts finite Schatten moments of actual
complex matrix-valued functions. Both exponents are arbitrary reals at least
one, and no independence or matrix-distribution premise is needed. -/
theorem integral_schattenNormReal_complex_condExp_rpow_le
    {n Ω : Type*} [Fintype n] [DecidableEq n]
    [MeasurableSpace Ω] {s : MeasurableSpace Ω} {μ : Measure Ω}
    {p : ℝ} (hp : 1 ≤ p) {q : ℝ} (hq : 1 ≤ q)
    {f : Ω → Matrix n n ℂ} (hf : Integrable f μ)
    (hfm : Integrable (fun ω => schattenNormReal (f ω) p ^ q) μ) :
    (∫ ω, schattenNormReal (μ[f | s] ω) p ^ q ∂μ) ≤
      ∫ ω, schattenNormReal (f ω) p ^ q ∂μ := by
  let T : Matrix n n ℂ →L[ℝ] WithComplexSchatten p hp n :=
    WithComplexSchatten.matrixContinuousLinearEquiv.toContinuousLinearMap
  have hcomm := T.comp_condExp_comm (m := s) hf
  have h := integral_norm_condExp_rpow_le (m := s) hq (f := T ∘ f) (by exact hfm)
  calc
    _ = ∫ ω, ‖μ[T ∘ f | s] ω‖ ^ q ∂μ := by
      apply integral_congr_ae
      filter_upwards [hcomm] with ω hω
      change ‖T (μ[f | s] ω)‖ ^ q = _
      exact congrArg (fun A : WithComplexSchatten p hp n => ‖A‖ ^ q)
        (by simpa only [Function.comp_apply] using hω)
    _ ≤ _ := h

end NLAlib
