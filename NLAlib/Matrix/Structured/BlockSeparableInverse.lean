import NLAlib.Matrix.Subspaces.ProjectorTrace
import NLAlib.Matrix.Structured.ConformalBlocks
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.Ring.Idempotent

/-!
# Block-separable inverse reduction without inverting the coupling

For `D + U C V*`, invertibility reduces to `C + (V* D⁻¹ U)⁻¹`.
The coupling `C` is allowed to be singular. All statements include empty
coarse spaces and the full-dimensional endpoint.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {K n k : Type*} [RCLike K] [Fintype n] [Fintype k]
  [DecidableEq n] [DecidableEq k]

/-- The small matrix governing block-separable inversion. -/
def inverseReductionCore (D : Matrix n n K) (U V : Matrix n k K) : Matrix k k K :=
  Vᴴ * D⁻¹ * U

/-- The left factor in the reduced inverse. -/
def inverseReductionLeft (D : Matrix n n K) (U V : Matrix n k K) : Matrix n k K :=
  D⁻¹ * U * (inverseReductionCore D U V)⁻¹

/-- The right factor (already in adjoint orientation) in the reduced inverse. -/
def inverseReductionRight (D : Matrix n n K) (U V : Matrix n k K) : Matrix k n K :=
  (inverseReductionCore D U V)⁻¹ * Vᴴ * D⁻¹

/-- The fine-scale part of the inverse reduction. -/
def inverseReductionRemainder (D : Matrix n n K) (U V : Matrix n k K) : Matrix n n K :=
  D⁻¹ - D⁻¹ * U * (inverseReductionCore D U V)⁻¹ * Vᴴ * D⁻¹

/-- The determinant identity behind the reduction, requiring invertibility of
`D` and of the compressed inverse interaction, but never of `C`. -/
theorem det_add_mul_mul_conjTranspose (D : Matrix n n K) (U V : Matrix n k K)
    (C : Matrix k k K) (hD : IsUnit D.det) (hM : IsUnit (inverseReductionCore D U V).det) :
    (D + U * C * Vᴴ).det = D.det * (inverseReductionCore D U V).det *
      (C + (inverseReductionCore D U V)⁻¹).det := by
  rw [Matrix.det_add_mul (U * C) Vᴴ hD]
  have heq : 1 + Vᴴ * D⁻¹ * (U * C) =
      inverseReductionCore D U V * (C + (inverseReductionCore D U V)⁻¹) := by
    rw [Matrix.mul_add, Matrix.mul_nonsing_inv _ hM]
    simp only [inverseReductionCore, Matrix.mul_assoc]
    abel
  rw [heq, Matrix.det_mul, mul_assoc]

/-- Invertibility of a block-separable matrix is equivalent to invertibility
of the reduced core; the coupling itself need not be invertible.
Source: user derivations, block-separable inverse reduction.
atlas: block-separable-inverse-reduction (partial) -/
theorem isUnit_add_mul_mul_conjTranspose_iff (D : Matrix n n K) (U V : Matrix n k K)
    (C : Matrix k k K) (hD : IsUnit D.det) (hM : IsUnit (inverseReductionCore D U V).det) :
    IsUnit (D + U * C * Vᴴ) ↔ IsUnit (C + (inverseReductionCore D U V)⁻¹) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det,
    det_add_mul_mul_conjTranspose D U V C hD hM]
  constructor
  · intro h
    exact isUnit_of_mul_isUnit_right h
  · intro h
    exact (hD.mul hM).mul h

private theorem mul_inverseReductionLeft (D : Matrix n n K) (U V : Matrix n k K)
    (C : Matrix k k K) (hD : IsUnit D.det) (hM : IsUnit (inverseReductionCore D U V).det) :
    (D + U * C * Vᴴ) * inverseReductionLeft D U V =
      U * (C + (inverseReductionCore D U V)⁻¹) := by
  have h₁ : D * inverseReductionLeft D U V = U * (inverseReductionCore D U V)⁻¹ := by
    simp [inverseReductionLeft, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hD]
  have h₂ : Vᴴ * inverseReductionLeft D U V = 1 := by
    change Vᴴ * (D⁻¹ * U * (inverseReductionCore D U V)⁻¹) = 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
    exact Matrix.mul_nonsing_inv _ hM
  rw [Matrix.add_mul, h₁, Matrix.mul_assoc, h₂, Matrix.mul_one, Matrix.mul_add]
  abel

/-- The reduced inverse formula, proved by multiplying the actual matrix by
the proposed inverse. Source: user derivations, block-separable inverse.
atlas: block-separable-inverse-reduction (partial) -/
theorem inverse_add_mul_mul_conjTranspose (D : Matrix n n K) (U V : Matrix n k K)
    (C : Matrix k k K) (hD : IsUnit D.det) (hM : IsUnit (inverseReductionCore D U V).det)
    (hS : IsUnit (C + (inverseReductionCore D U V)⁻¹).det) :
    (D + U * C * Vᴴ)⁻¹ = inverseReductionLeft D U V *
      (C + (inverseReductionCore D U V)⁻¹)⁻¹ * inverseReductionRight D U V +
        inverseReductionRemainder D U V := by
  apply Matrix.inv_eq_right_inv
  have hE := mul_inverseReductionLeft D U V C hD hM
  have hG : (D + U * C * Vᴴ) * inverseReductionRemainder D U V =
      1 - U * inverseReductionRight D U V := by
    change (D + U * C * Vᴴ) * (D⁻¹ - inverseReductionLeft D U V * Vᴴ * D⁻¹) = _
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hE]
    simp only [Matrix.add_mul, Matrix.mul_nonsing_inv _ hD, Matrix.mul_add,
      inverseReductionRight, Matrix.mul_assoc]
    noncomm_ring
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hE]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hS, Matrix.one_mul]
  rw [← Matrix.mul_assoc U C Vᴴ, hG]
  abel

/-- The complementary projection underlying the fine-scale remainder. -/
theorem inverseReduction_projection_idempotent (D : Matrix n n K) (U V : Matrix n k K)
    (hM : IsUnit (inverseReductionCore D U V).det) :
    IsIdempotentElem (D⁻¹ * U * (inverseReductionCore D U V)⁻¹ * Vᴴ) := by
  change (D⁻¹ * U * (inverseReductionCore D U V)⁻¹ * Vᴴ) *
    (D⁻¹ * U * (inverseReductionCore D U V)⁻¹ * Vᴴ) = _
  calc
    _ = D⁻¹ * U * (inverseReductionCore D U V)⁻¹ *
        (inverseReductionCore D U V * (inverseReductionCore D U V)⁻¹) * Vᴴ := by
      simp only [inverseReductionCore, Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hM]; simp

/-- The fine-scale remainder has precisely the complementary dimension,
including an empty coarse space and a coarse space of full size.
Source: user derivations, complementary projection in block-separable inverse.
atlas: block-separable-inverse-reduction (partial) -/
theorem rank_inverseReductionRemainder (D : Matrix n n K) (U V : Matrix n k K)
    (hD : IsUnit D.det) (hM : IsUnit (inverseReductionCore D U V).det) :
    (inverseReductionRemainder D U V).rank = Fintype.card n - Fintype.card k := by
  let P := D⁻¹ * U * (inverseReductionCore D U V)⁻¹ * Vᴴ
  have hP : IsIdempotentElem P := inverseReduction_projection_idempotent D U V hM
  have htrace : P.trace = (Fintype.card k : K) := by
    calc
      P.trace = (Vᴴ * (D⁻¹ * U * (inverseReductionCore D U V)⁻¹)).trace :=
        Matrix.trace_mul_comm _ _
      _ = (inverseReductionCore D U V * (inverseReductionCore D U V)⁻¹).trace := by
        simp only [inverseReductionCore, Matrix.mul_assoc]
      _ = _ := by rw [Matrix.mul_nonsing_inv _ hM]; simp
  have hPrank : P.rank = Fintype.card k := by
    apply Nat.cast_injective (R := K)
    rw [← trace_eq_rank_of_isIdempotentElem P hP]
    exact htrace
  have hcast : (((1 - P).rank + P.rank : ℕ) : K) = (Fintype.card n : K) := by
    rw [Nat.cast_add, ← trace_eq_rank_of_isIdempotentElem (1 - P) hP.one_sub,
      ← trace_eq_rank_of_isIdempotentElem P hP, ← Matrix.trace_add]
    simp
  have hdim : (1 - P).rank + P.rank = Fintype.card n := Nat.cast_injective hcast
  have hG : inverseReductionRemainder D U V = (1 - P) * D⁻¹ := by
    simp [inverseReductionRemainder, P, Matrix.sub_mul]
  rw [hG, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (D.isUnit_nonsing_inv_det hD)]
  omega

/-- Conformal block-diagonal input factors give block-diagonal reduction
factors. Thus all off-diagonal inverse blocks come from the reduced inverse
term in `inverse_add_mul_mul_conjTranspose`.
Source: user derivations, block-separable inverse reduction.
atlas: block-separable-inverse-reduction -/
theorem inverseReduction_conformalBlockDiagonal {ι : Type*} [LinearOrder ι]
    (row : n → ι) (coarse : k → ι) (D : Matrix n n K) (U V : Matrix n k K)
    (hD : IsUnit D.det) (hM : IsUnit (inverseReductionCore D U V).det)
    (hDb : ConformalBlockDiagonal D row row)
    (hUb : ConformalBlockDiagonal U row coarse)
    (hVb : ConformalBlockDiagonal V row coarse) :
    ConformalBlockDiagonal (inverseReductionLeft D U V) row coarse ∧
      ConformalBlockDiagonal (inverseReductionRight D U V) coarse row ∧
      ConformalBlockDiagonal (inverseReductionRemainder D U V) row row := by
  have hDi := hDb.inv hD
  have hMb : ConformalBlockDiagonal (inverseReductionCore D U V) coarse coarse :=
    (hVb.conjTranspose.mul hDi).mul hUb
  have hMi := hMb.inv hM
  exact ⟨(hDi.mul hUb).mul hMi, (hMi.mul hVb.conjTranspose).mul hDi,
    hDi.sub ((((hDi.mul hUb).mul hMi).mul hVb.conjTranspose).mul hDi)⟩

end NLAlib
