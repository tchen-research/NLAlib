import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Matrix norms

The two norms every NLAlib statement is written in.

* `NLAlib.frobInner`, `NLAlib.frobSq`, `NLAlib.frobNorm`: the Frobenius inner product, its
  squared norm and the norm, as explicit sums so that algebraic identities close by `simp`/`ring`.
* `NLAlib.specNorm`: the spectral (ℓ₂ operator) norm, which is Mathlib's `‖A‖` under
  `open scoped Matrix.Norms.L2Operator`. Defined as a name so statements read like the sources;
  `specNorm_eq_norm` is the bridge.

Atlas: `norms-frob-spec`.
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Frobenius inner product `⟨A, B⟩_F = ∑ᵢⱼ Aᵢⱼ Bᵢⱼ`. -/
def frobInner (A B : Matrix m n ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

/-- Squared Frobenius norm `‖A‖_F²`. -/
def frobSq (A : Matrix m n ℝ) : ℝ := frobInner A A

/-- Frobenius norm `‖A‖_F`. -/
def frobNorm (A : Matrix m n ℝ) : ℝ := Real.sqrt (frobSq A)

/-- Spectral norm `‖A‖₂`, the largest singular value: Mathlib's ℓ₂ operator norm. -/
def specNorm [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) : ℝ := ‖A‖

theorem specNorm_eq_norm [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) :
    specNorm A = ‖A‖ := rfl

theorem specNorm_nonneg [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) : 0 ≤ specNorm A :=
  norm_nonneg A

theorem frobInner_comm (A B : Matrix m n ℝ) : frobInner A B = frobInner B A := by
  unfold frobInner
  simp_rw [mul_comm]

theorem frobInner_eq_trace (A B : Matrix m n ℝ) : frobInner A B = (Aᵀ * B).trace := by
  unfold frobInner Matrix.trace
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

theorem frobSq_nonneg (A : Matrix m n ℝ) : 0 ≤ frobSq A := by
  unfold frobSq frobInner
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _

@[simp] theorem frobSq_zero : frobSq (0 : Matrix m n ℝ) = 0 := by
  unfold frobSq frobInner; simp

theorem frobNorm_nonneg (A : Matrix m n ℝ) : 0 ≤ frobNorm A := Real.sqrt_nonneg _

theorem frobNorm_sq (A : Matrix m n ℝ) : frobNorm A ^ 2 = frobSq A :=
  Real.sq_sqrt (frobSq_nonneg A)

end NLAlib
