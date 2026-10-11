import NLAlib.Concentration.Matrix.Defs.Probability
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Genuine finite local conditional second moments

The interface is the audited extended-integral equality for every deterministic vector
and every conditioning-measurable set. It assumes neither global square integrability
nor a Bochner conditional expectation of a nonintegrable square.
-/

noncomputable section

open MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal

namespace NLAlib

variable {Ω n : Type*} {m mΩ : MeasurableSpace Ω} [Fintype n] {μ : Measure Ω}

/-- The actual squared Euclidean norm of the image of a deterministic vector, written
as a finite coordinate sum to avoid the default supremum norm on a function type.
Source: audited local-moment identity `audit:local-moment`; `matrix-freedman` (partial). -/
def matrixVectorSqNorm (A : Matrix n n ℂ) (u : n → ℂ) : ℝ :=
  ∑ i, ‖(A *ᵥ u) i‖ ^ 2

/-- The real Hermitian quadratic form of a matrix at a deterministic vector.
Source: audited local-moment identity `audit:local-moment`; `matrix-freedman` (partial). -/
def matrixQuadraticFormReal (A : Matrix n n ℂ) (u : n → ℂ) : ℝ :=
  (star u ⬝ᵥ (A *ᵥ u)).re

/-- The actual squared vector-image norm is nonnegative.
Source: finite sum of squared norms; `audit:local-moment`, `matrix-freedman` (partial). -/
theorem matrixVectorSqNorm_nonneg (A : Matrix n n ℂ) (u : n → ℂ) :
    0 ≤ matrixVectorSqNorm A u := Finset.sum_nonneg (fun _i _ => sq_nonneg _)

/-- A coordinate vector extracts the squared Euclidean column norm.
Source: the coordinate-basis sum in `audit:combined`; `matrix-freedman` (partial). -/
@[simp] theorem matrixVectorSqNorm_single [DecidableEq n] (A : Matrix n n ℂ) (j : n) :
    matrixVectorSqNorm A (Pi.single j 1) = ∑ i, ‖A i j‖ ^ 2 := by
  simp only [matrixVectorSqNorm, Matrix.mulVec_single_one, Matrix.col_apply]

/-- A coordinate quadratic form is exactly the real diagonal entry.
Source: the coordinate-basis sum in `audit:combined`; `matrix-freedman` (partial). -/
@[simp] theorem matrixQuadraticFormReal_single [DecidableEq n] (A : Matrix n n ℂ) (j : n) :
    matrixQuadraticFormReal A (Pi.single j 1) = (A j j).re := by
  have hstar : star (Pi.single j (1 : ℂ) : n → ℂ) = (Pi.single j 1 : n → ℂ) := by
    simp only [Pi.star_single, star_one]
  rw [matrixQuadraticFormReal, hstar, single_one_dotProduct, Matrix.mulVec_single_one]
  rfl

/-- A finite predictable PSD matrix is a genuine local conditional second moment when
its quadratic forms have exactly the same nonnegative extended set integrals as the
squared images of the increment, for every deterministic vector and every set measurable
under conditioning. No global square integrability or variance integrability is assumed.
Source: supplied audit `audit:local-moment`, Part VII; atlas `matrix-freedman` (partial). -/
def HasLocalMatrixSecondMoment (μ : Measure Ω) (m : MeasurableSpace Ω)
    (X V : Ω → Matrix n n ℂ) : Prop :=
  Measurable[m] V ∧ (∀ᵐ ω ∂μ, (V ω).PosSemidef) ∧
    ∀ (u : n → ℂ) (B : Set Ω), MeasurableSet[m] B →
      (∫⁻ ω in B, ENNReal.ofReal (matrixVectorSqNorm (X ω) u) ∂μ) =
        ∫⁻ ω in B, ENNReal.ofReal (matrixQuadraticFormReal (V ω) u) ∂μ

/-- Genuine local conditional moment matrices are predictable.
Source: the exact `audit:local-moment` interface; `matrix-freedman` (partial). -/
theorem HasLocalMatrixSecondMoment.measurable {X V : Ω → Matrix n n ℂ}
    (h : HasLocalMatrixSecondMoment μ m X V) : Measurable[m] V := h.1

/-- Genuine local conditional moment matrices are PSD almost everywhere.
Source: the exact `audit:local-moment` interface; `matrix-freedman` (partial). -/
theorem HasLocalMatrixSecondMoment.ae_posSemidef {X V : Ω → Matrix n n ℂ}
    (h : HasLocalMatrixSecondMoment μ m X V) : ∀ᵐ ω ∂μ, (V ω).PosSemidef := h.2.1

/-- The actual extended quadratic-form identity on every conditioning-measurable set.
Source: `audit:local-moment`; immediate API for `matrix-freedman` (partial). -/
theorem HasLocalMatrixSecondMoment.setLIntegral_eq {X V : Ω → Matrix n n ℂ}
    (h : HasLocalMatrixSecondMoment μ m X V) (u : n → ℂ) (B : Set Ω) (hB : MeasurableSet[m] B) :
    (∫⁻ ω in B, ENNReal.ofReal (matrixVectorSqNorm (X ω) u) ∂μ) =
      ∫⁻ ω in B, ENNReal.ofReal (matrixQuadraticFormReal (V ω) u) ∂μ := h.2.2 u B hB

end NLAlib
