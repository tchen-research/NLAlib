import NLAlib.Matrix.Functions.MatrixDysonExterior
import NLAlib.Matrix.Functions.MatrixDysonNormalization
import NLAlib.ForMathlib.Analysis.Matrix.HerglotzRepresentation
import NLAlib.ForMathlib.Analysis.Matrix.ImaginaryInvertibility

/-! # The matrix Dyson solution is a compactly supported Stieltjes transform

Every holomorphic positive-imaginary solution of the actual matrix Dyson
equation has a unique native positive matrix measure of total mass `I`.
The exact support radius and `1 / Im z` bound are derived from the equation;
no scalar representation, exterior bound, or normalization is assumed.

Source: Ajanki--Erdős--Krüger, §2.1, Proposition 2.1, and (4.1)--(4.8).
Atlas: `matrix-dyson-stieltjes-representation`.
-/

noncomputable section
open Matrix MeasureTheory Filter Set
open scoped Topology Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The spectral support radius uses the matrix spectral norm and the
induced spectral-to-spectral norm of the positive linear map. -/
def matrixDysonRadius (A : Matrix n n ℂ)
    (S : Matrix n n ℂ →L[ℂ] Matrix n n ℂ) : ℝ :=
  specNorm A + 2 * Real.sqrt ‖S‖

/-- The polynomial Dyson identity constructs the unique positive matrix
Stieltjes measure with exact support radius. Positivity of the linear map
suffices; Hilbert--Schmidt self-adjointness is not needed for this conclusion. -/
theorem existsUnique_positiveMatrixMeasure_of_matrixDyson
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (S : Matrix n n ℂ →L[ℂ] Matrix n n ℂ)
    (hS : ∀ X : Matrix n n ℂ, 0 ≤ X → 0 ≤ S X)
    (M : ℂ → Matrix n n ℂ)
    (hM : AnalyticOnNhd ℂ M {z : ℂ | 0 < z.im})
    (hpos : ∀ z : ℂ, 0 < z.im → 0 ≤ (imaginaryPart (M z) : Matrix n n ℂ))
    (heq : ∀ z : ℂ, 0 < z.im → (z • 1 - A + S (M z)) * M z = -1) :
    ∃! P : PositiveMatrixMeasure ℝ n,
      P Set.univ = 1 ∧
      (∀ E : Set ℝ, MeasurableSet E →
        E ⊆ (Icc (-matrixDysonRadius A S) (matrixDysonRadius A S))ᶜ → P E = 0) ∧
      ∀ z : ℂ, 0 < z.im → ∀ i j : n, P.entryStieltjesTransform z i j = M z i j := by
  apply Matrix.existsUnique_positiveMatrixMeasure_stieltjes_eq M hM
    (fun z hz => (hpos z hz).posSemidef)
    (tendsto_mul_I_smul_matrixDyson A hA S hS M hpos heq) (matrixDysonRadius A S)
  intro c hc
  refine ⟨4 / ((c - specNorm A) ^ 2 - 4 * ‖S‖), ?_⟩
  intro z hz hcz
  exact norm_imaginaryPart_le_of_matrixDyson_exterior A hA S hS M hM.continuousOn
    hpos heq hc hz hcz

/-- The holomorphic positive-imaginary solution of `-M⁻¹ = zI-A+S[M]`
has a unique actual PSD matrix measure, total mass `I`, exact compact
support, and the Euclidean operator bound `‖M(z)‖₂ ≤ 1 / Im z`.
The input is the inverse equation from the source: invertibility is
proved from positive definiteness of the imaginary part, not assumed.
Source: Ajanki--Erdős--Krüger, §2.1 and Proposition 2.1, bound (4.1).
atlas: matrix-dyson-stieltjes-representation -/
theorem existsUnique_positiveMatrixMeasure_and_specNorm_le_of_matrixDyson_inverse
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (S : Matrix n n ℂ →L[ℂ] Matrix n n ℂ)
    (hS : ∀ X : Matrix n n ℂ, 0 ≤ X → 0 ≤ S X)
    (M : ℂ → Matrix n n ℂ)
    (hM : DifferentiableOn ℂ M {z : ℂ | 0 < z.im})
    (hpos : ∀ z : ℂ, 0 < z.im → (imaginaryPart (M z) : Matrix n n ℂ).PosDef)
    (heq : ∀ z : ℂ, 0 < z.im → -(M z)⁻¹ = z • 1 - A + S (M z)) :
    (∃! P : PositiveMatrixMeasure ℝ n,
      P Set.univ = 1 ∧
      (∀ E : Set ℝ, MeasurableSet E →
        E ⊆ (Icc (-matrixDysonRadius A S) (matrixDysonRadius A S))ᶜ → P E = 0) ∧
      ∀ z : ℂ, 0 < z.im → ∀ i j : n, P.entryStieltjesTransform z i j = M z i j) ∧
    ∀ z : ℂ, 0 < z.im → specNorm (M z) ≤ z.im⁻¹ := by
  have hpol : ∀ z : ℂ, 0 < z.im → (z • 1 - A + S (M z)) * M z = -1 :=
    fun z hz => Matrix.mul_eq_neg_one_of_neg_inv_eq_of_posDef_imaginaryPart (hpos z hz) (heq z hz)
  have hp : ∀ z : ℂ, 0 < z.im → 0 ≤ (imaginaryPart (M z) : Matrix n n ℂ) :=
    fun z hz => (hpos z hz).posSemidef.nonneg
  have ha : AnalyticOnNhd ℂ M {z : ℂ | 0 < z.im} :=
    (Complex.analyticOnNhd_iff_differentiableOn
      (isOpen_lt continuous_const Complex.continuous_im)).mpr hM
  exact ⟨existsUnique_positiveMatrixMeasure_of_matrixDyson A hA S hS M ha hp hpol,
    fun z hz => specNorm_le_inv_im_of_matrixDyson A hA S hS hz (M z) (hp z hz) (hpol z hz)⟩

end NLAlib
