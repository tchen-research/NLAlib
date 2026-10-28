import NLAlib.ForMathlib.MeasureTheory.MatrixEntriesIntegral

/-!
# Fixed matrix factors commute with Bochner integration

Finite-dimensional matrix multiplication is a continuous linear map in the
random middle factor. This transports actual integrability and matrix means.
-/

noncomputable section
open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
variable {K Ω a b c d : Type*} [RCLike K] [MeasurableSpace Ω]
  [Fintype a] [Fintype b] [Fintype c] [Fintype d]
  [DecidableEq b] [DecidableEq d] {μ : Measure Ω}

private local instance {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] :
    NormedSpace ℝ (Matrix m n K) := NormedSpace.restrictScalars ℝ K (Matrix m n K)

/-- Fixed rectangular factors preserve integrability and commute with the
actual finite real or complex matrix integral. -/
theorem integrable_and_integral_matrix_sandwich (L : Matrix c a K) (R : Matrix b d K)
    {f : Ω → Matrix a b K} (hf : Integrable f μ) :
    Integrable (fun ω => L*f ω*R) μ ∧
      (∫ ω,L*f ω*R ∂μ)=L*(∫ ω,f ω ∂μ)*R := by
  let T : Matrix a b K →ₗ[K] Matrix c d K :=
    { toFun := fun X => L*X*R
      map_add' := by intro X Y; simp only [Matrix.mul_add,Matrix.add_mul]
      map_smul' := by intro k X; simp only [Matrix.mul_smul,Matrix.smul_mul,RingHom.id_apply] }
  let Tc : Matrix a b K →L[K] Matrix c d K := T.toContinuousLinearMap
  exact ⟨Tc.integrable_comp hf,Tc.integral_comp_comm hf⟩

end NLAlib
