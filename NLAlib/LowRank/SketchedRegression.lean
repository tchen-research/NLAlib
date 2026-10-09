import Mathlib.Analysis.CStarAlgebra.Matrix
import NLAlib.Matrix.Norms
import NLAlib.Matrix.Projections
import NLAlib.Matrix.Pseudoinverse

/-!
# Deterministic content of the sketched-regression (generalized Nyström) analysis

The purely linear-algebraic identities behind the sketched least-squares fit of the core
matrix in the generalized Nyström / two-pass low-rank approximation:

* Chen–Persson, *One- and two-pass algorithms for low-rank approximation*, Lemma
  `lem:completion` (exact Gaussian completion), Lemma `lem:tGN-core` (core noise), and the
  displays `eq:tGN-fitted-core` / `eq:tGN-split` in the proof of `thm:tGN`;
* Tropp–Webber, *Randomized algorithms for low-rank matrix approximation: design, analysis,
  and applications*, 2023, §5 (sketched regression / generalized Nyström).

All probabilistic content (Gaussian moments, independence of `G₁ = ΨᵀQ` and `G₂ = ΨᵀQ⊥`) lives
elsewhere; every statement here is an identity valid for **every fixed** sketch `Ψ`.

Ported from the LRA project, `LRA/Deterministic/SketchedRegression.lean` (Chen–Persson
formalization, same Mathlib pin), namespace renamed to `NLAlib`. The residual facts of the
source (`mul_add_residual`, `transpose_mul_residual_eq_zero`, `frobInner_residual_mul`,
`frobSq_sub_mul_eq`) are the existing `NLAlib.mul_transpose_mul_add_residual`,
`NLAlib.transpose_mul_residual`, `NLAlib.frobInner_mul_residual`, `NLAlib.frobSq_sub_mul_eq`
in `NLAlib.Matrix.Projections`. The source's `‖·‖` under `Matrix.Norms.L2Operator` is
`NLAlib.specNorm` here (definitionally equal, `specNorm_eq_norm`).

## Set-up (matching the paper)

* `Q : Matrix m (Fin q) ℝ` with orthonormal columns (`hQ`);
* `Qp : Matrix m (Fin r) ℝ` is the paper's `Q⊥`: orthonormal columns (`hQp`), `Qᵀ Q⊥ = 0`
  (`hQQp`) and completeness `Q Qᵀ + Q⊥ Q⊥ᵀ = I` (`hcomp`), i.e. `[Q  Q⊥]` is orthogonal;
* `Ψ : Matrix m (Fin s) ℝ` is the (fixed) sketch, `G₁ := Ψᵀ Q`, `G₂ := Ψᵀ Q⊥`;
* `residual Q A = A - Q(QᵀA)` is the paper's `E = (I - QQᵀ)A` (called `A⊥` in `lem:tGN-core`);
* `hG₁ : IsUnit (G₁ᵀ G₁)` encodes "`G₁` has full column rank"; the paper's `G₁†` is `pinvL G₁`
  and the only property used is `pinvL G₁ * G₁ = 1` (`NLAlib.pinvL_mul`);
* `sketchedCore Q Ψ A = pinvL (ΨᵀQ) (ΨᵀA)` is the fitted core `X̂ = (ΨᵀQ)† ΨᵀA`,
  `sketchedOutput Q Ψ A = Q X̂` is the paper's `Â`, and
  `coreNoise Q Ψ A = pinvL (ΨᵀQ) (Ψᵀ A⊥)` is the paper's `E_core`.

Atlas: `sketched-regression`.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable {q r s : ℕ}

/-- The sketched core `X̂ = (ΨᵀQ)† ΨᵀA`, with `†` the left pseudoinverse `pinvL`
(Chen–Persson, `eq:tGN-fitted-core`; Tropp–Webber 2023 §5). Atlas `sketched-regression`. -/
def sketchedCore (Q : Matrix m (Fin q) ℝ) (Ψ : Matrix m (Fin s) ℝ) (A : Matrix m n ℝ) :
    Matrix (Fin q) n ℝ := pinvL (Ψᵀ * Q) * (Ψᵀ * A)

/-- The sketched output `Â = Q X̂ = Q (ΨᵀQ)† ΨᵀA` (Chen–Persson, `lem:completion`;
Tropp–Webber 2023 §5). Atlas `sketched-regression`. -/
def sketchedOutput (Q : Matrix m (Fin q) ℝ) (Ψ : Matrix m (Fin s) ℝ) (A : Matrix m n ℝ) :
    Matrix m n ℝ := Q * sketchedCore Q Ψ A

/-- The core noise `E_core = (ΨᵀQ)† Ψᵀ A⊥` with `A⊥ = (I - QQᵀ)A` (Chen–Persson,
`eq:tGN-fitted-core`, `lem:tGN-core`). Not in the LRA source, which writes the expression
out. Atlas `sketched-regression`. -/
def coreNoise (Q : Matrix m (Fin q) ℝ) (Ψ : Matrix m (Fin s) ℝ) (A : Matrix m n ℝ) :
    Matrix (Fin q) n ℝ := pinvL (Ψᵀ * Q) * (Ψᵀ * residual Q A)

/-! ### Facts that need only `QᵀQ = I` -/

section OnlyQ

variable (Q : Matrix m (Fin q) ℝ) (A : Matrix m n ℝ)

/-- Rank-deficient remark in the proofs of `thm:GN` / `thm:tGN` (Chen–Persson): if
`A = Q(QᵀA)` (i.e. `E = 0`) and `ΨᵀQ` has full column rank, the fitted core is exactly `QᵀA`.
Atlas `sketched-regression`. -/
theorem sketchedCore_eq_of_eq_mul (Ψ : Matrix m (Fin s) ℝ) (hG₁ : IsUnit ((Ψᵀ * Q)ᵀ * (Ψᵀ * Q)))
    (hA : A = Q * (Qᵀ * A)) : sketchedCore Q Ψ A = Qᵀ * A := by
  unfold sketchedCore
  conv_lhs => rw [hA]
  rw [← Matrix.mul_assoc Ψᵀ, ← Matrix.mul_assoc, pinvL_mul hG₁, Matrix.one_mul]

/-- Rank-deficient remark (Chen–Persson, proofs of `thm:GN` / `thm:tGN`): if `A = Q(QᵀA)` and
`ΨᵀQ` has full column rank, then `Â = A`. Atlas `sketched-regression`. -/
theorem sketchedOutput_eq_of_eq_mul (Ψ : Matrix m (Fin s) ℝ)
    (hG₁ : IsUnit ((Ψᵀ * Q)ᵀ * (Ψᵀ * Q))) (hA : A = Q * (Qᵀ * A)) :
    sketchedOutput Q Ψ A = A := by
  unfold sketchedOutput
  rw [sketchedCore_eq_of_eq_mul Q A Ψ hG₁ hA, ← hA]

end OnlyQ

/-! ### Facts using the orthogonal completion `[Q  Q⊥]` -/

section Completion

variable (Q : Matrix m (Fin q) ℝ) (Qp : Matrix m (Fin r) ℝ) (Ψ : Matrix m (Fin s) ℝ)
  (A : Matrix m n ℝ)

/-- `Q⊥ᵀ Q = 0`, the transpose of `hQQp` (Chen–Persson, set-up of `lem:completion`).
Atlas `sketched-regression`. -/
theorem transpose_perp_mul (hQQp : Qᵀ * Qp = 0) : Qpᵀ * Q = 0 := by
  have h := congrArg Matrix.transpose hQQp
  simpa using h

/-- Item 1 in the proof of `lem:completion` (Chen–Persson): `E = Q⊥ (Q⊥ᵀ E)`, since
`E = (QQᵀ + Q⊥Q⊥ᵀ)E` and `QᵀE = 0`. Atlas `sketched-regression`. -/
theorem residual_eq_perp_mul (hQ : HasOrthonormalCols Q) (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1) :
    residual Q A = Qp * (Qpᵀ * residual Q A) := by
  have h : (Q * Qᵀ + Qp * Qpᵀ) * residual Q A = residual Q A := by
    rw [hcomp, Matrix.one_mul]
  rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, transpose_mul_residual hQ A,
    Matrix.mul_zero, zero_add] at h
  exact h.symm

/-- `Ψᵀ E = G₂ (Q⊥ᵀ E)` where `G₂ = Ψᵀ Q⊥` (Chen–Persson, proof of `lem:completion`).
Atlas `sketched-regression`. -/
theorem transpose_mul_residual_eq (hQ : HasOrthonormalCols Q) (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1) :
    Ψᵀ * residual Q A = (Ψᵀ * Qp) * (Qpᵀ * residual Q A) := by
  conv_lhs => rw [residual_eq_perp_mul Q Qp A hQ hcomp]
  rw [Matrix.mul_assoc]

/-- First display in the proof of `lem:completion` (Chen–Persson):
`Ψᵀ A = G₁ (QᵀA) + G₂ (Q⊥ᵀ E)` with `G₁ = ΨᵀQ`, `G₂ = ΨᵀQ⊥`. Atlas `sketched-regression`. -/
theorem sketch_decomp (hQ : HasOrthonormalCols Q) (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1) :
    Ψᵀ * A = (Ψᵀ * Q) * (Qᵀ * A) + (Ψᵀ * Qp) * (Qpᵀ * residual Q A) := by
  calc Ψᵀ * A = Ψᵀ * (Q * (Qᵀ * A) + residual Q A) := by
        rw [mul_transpose_mul_add_residual]
    _ = (Ψᵀ * Q) * (Qᵀ * A) + (Ψᵀ * Qp) * (Qpᵀ * residual Q A) := by
      rw [Matrix.mul_add, ← Matrix.mul_assoc, transpose_mul_residual_eq Q Qp Ψ A hQ hcomp]

/-- Second display in the proof of `lem:completion`, also `eq:tGN-fitted-core` (Chen–Persson;
Tropp–Webber 2023 §5): `X̂ = (ΨᵀQ)† ΨᵀA = QᵀA + G₁† G₂ (Q⊥ᵀ E)`, using `G₁† G₁ = I`.
Atlas `sketched-regression`. -/
theorem sketchedCore_eq (hQ : HasOrthonormalCols Q) (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1)
    (hG₁ : IsUnit ((Ψᵀ * Q)ᵀ * (Ψᵀ * Q))) :
    sketchedCore Q Ψ A =
      Qᵀ * A + pinvL (Ψᵀ * Q) * (Ψᵀ * Qp) * (Qpᵀ * residual Q A) := by
  unfold sketchedCore
  rw [sketch_decomp Q Qp Ψ A hQ hcomp, Matrix.mul_add,
    ← Matrix.mul_assoc (pinvL (Ψᵀ * Q)) (Ψᵀ * Q), pinvL_mul hG₁, Matrix.one_mul,
    ← Matrix.mul_assoc]

/-- Error decomposition in the proof of `lem:completion` (Chen–Persson):
`A - Â = E - Q G₁† G₂ (Q⊥ᵀ E)`. Atlas `sketched-regression`. -/
theorem error_decomp (hQ : HasOrthonormalCols Q) (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1)
    (hG₁ : IsUnit ((Ψᵀ * Q)ᵀ * (Ψᵀ * Q))) :
    A - sketchedOutput Q Ψ A =
      residual Q A - Q * (pinvL (Ψᵀ * Q) * (Ψᵀ * Qp) * (Qpᵀ * residual Q A)) := by
  unfold sketchedOutput
  rw [sketchedCore_eq Q Qp Ψ A hQ hcomp hG₁, Matrix.mul_add]
  unfold residual
  rw [sub_add_eq_sub_sub]

/-- Pythagorean identity in the proof of `lem:completion` (Chen–Persson; Tropp–Webber 2023 §5):
`‖A - Â‖_F² = ‖(I - QQᵀ)A‖_F² + ‖G₁† G₂ Q⊥ᵀ E‖_F²`. The two terms of `error_decomp` lie in
`range(Q⊥)` and `range(Q)`, which are orthogonal. Atlas `sketched-regression`. -/
theorem frobSq_error (hQ : HasOrthonormalCols Q) (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1)
    (hG₁ : IsUnit ((Ψᵀ * Q)ᵀ * (Ψᵀ * Q))) :
    frobSq (A - sketchedOutput Q Ψ A) =
      frobSq (residual Q A) + frobSq (pinvL (Ψᵀ * Q) * (Ψᵀ * Qp) * (Qpᵀ * residual Q A)) := by
  rw [error_decomp Q Qp Ψ A hQ hcomp hG₁,
    frobSq_sub_of_frobInner_eq_zero _ _ (by
      rw [frobInner_comm]; exact frobInner_mul_residual hQ _ A),
    frobSq_mul_left_of_orthonormal hQ]

/-- `‖Q⊥ᵀ E‖_F² = ‖E‖_F²` (Chen–Persson, end of the proof of `lem:completion` and proof of
`lem:tGN-core`, `‖B‖_F = ‖A⊥‖_F`). Atlas `sketched-regression`. -/
theorem frobSq_perp_mul_residual (hQ : HasOrthonormalCols Q) (hQp : HasOrthonormalCols Qp)
    (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1) :
    frobSq (Qpᵀ * residual Q A) = frobSq (residual Q A) := by
  conv_rhs => rw [residual_eq_perp_mul Q Qp A hQ hcomp]
  rw [frobSq_mul_left_of_orthonormal hQp]

/-- Deterministic core of `lem:tGN-core` and `eq:tGN-fitted-core` (Chen–Persson): the noise
term `E_core = (ΨᵀQ)† Ψᵀ A⊥` equals `G† H B` with `G = ΨᵀQ`, `H = ΨᵀQ⊥`, `B = Q⊥ᵀ A⊥`, where
`A⊥ = (I - QQᵀ)A = residual Q A`. The left side is `coreNoise Q Ψ A` by definition (written
out, as in the source). Atlas `sketched-regression`. -/
theorem core_noise_eq (hQ : HasOrthonormalCols Q) (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1) :
    pinvL (Ψᵀ * Q) * (Ψᵀ * residual Q A) =
      pinvL (Ψᵀ * Q) * (Ψᵀ * Qp) * (Qpᵀ * residual Q A) := by
  rw [transpose_mul_residual_eq Q Qp Ψ A hQ hcomp, ← Matrix.mul_assoc (pinvL (Ψᵀ * Q))]

/-- `eq:tGN-fitted-core` (Chen–Persson; Tropp–Webber 2023 §5): `X̂ = C + E_core` with `C = QᵀA`
and `E_core = (ΨᵀQ)† Ψᵀ A⊥`. Atlas `sketched-regression`. -/
theorem sketchedCore_eq_add_core_noise (hQ : HasOrthonormalCols Q)
    (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1) (hG₁ : IsUnit ((Ψᵀ * Q)ᵀ * (Ψᵀ * Q))) :
    sketchedCore Q Ψ A = Qᵀ * A + pinvL (Ψᵀ * Q) * (Ψᵀ * residual Q A) := by
  rw [sketchedCore_eq Q Qp Ψ A hQ hcomp hG₁, core_noise_eq Q Qp Ψ A hQ hcomp]

/-- `eq:tGN-fitted-core` with the named noise term: `X̂ = QᵀA + coreNoise Q Ψ A`
(Chen–Persson). Not in the LRA source (it is `sketchedCore_eq_add_core_noise` folded).
Atlas `sketched-regression`. -/
theorem sketchedCore_eq_add_coreNoise (hQ : HasOrthonormalCols Q)
    (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1) (hG₁ : IsUnit ((Ψᵀ * Q)ᵀ * (Ψᵀ * Q))) :
    sketchedCore Q Ψ A = Qᵀ * A + coreNoise Q Ψ A :=
  sketchedCore_eq_add_core_noise Q Qp Ψ A hQ hcomp hG₁

/-- `coreNoise Q Ψ A = G₁† G₂ (Q⊥ᵀ E)` (Chen–Persson, `lem:tGN-core`; `core_noise_eq` with the
named noise term). Not in the LRA source. Atlas `sketched-regression`. -/
theorem coreNoise_eq (hQ : HasOrthonormalCols Q) (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1) :
    coreNoise Q Ψ A = pinvL (Ψᵀ * Q) * (Ψᵀ * Qp) * (Qpᵀ * residual Q A) :=
  core_noise_eq Q Qp Ψ A hQ hcomp

end Completion

/-! ### Spectral norm -/

section Spectral

open scoped Matrix.Norms.L2Operator

variable {k l : Type*} [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l]

/-- The spectral norm of the identity is at most `1` (it is `1` when the index type is
nonempty and `0` when it is empty). Standard. Atlas `sketched-regression`. -/
theorem l2_opNorm_one_le : specNorm (1 : Matrix k k ℝ) ≤ 1 := by
  rw [specNorm_eq_norm, ← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simp

/-- A matrix with orthonormal columns has spectral norm at most `1`. Standard.
Atlas `sketched-regression`. -/
theorem l2_opNorm_le_one_of_orthonormal (P : Matrix m k ℝ) (hP : HasOrthonormalCols P) :
    specNorm P ≤ 1 := by
  rw [specNorm_eq_norm]
  have h : ‖P‖ * ‖P‖ ≤ 1 := by
    have h1 := Matrix.l2_opNorm_conjTranspose_mul_self P
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hP] at h1
    rw [← h1]
    exact l2_opNorm_one_le
  nlinarith [norm_nonneg P]

/-- Spectral isometry under a matrix with orthonormal columns: if `X = P (Pᵀ X)` (i.e.
`range(X) ⊆ range(P)`) and `PᵀP = I`, then `‖Pᵀ X‖₂ = ‖X‖₂`. Used in the proof of
`lem:tGN-core` (Chen–Persson) as `‖B‖ = ‖A⊥‖` with `B = Q⊥ᵀ A⊥`. Atlas `sketched-regression`. -/
theorem l2_opNorm_transpose_mul_of_eq (P : Matrix m k ℝ) (hP : HasOrthonormalCols P)
    (X : Matrix m l ℝ) (hX : X = P * (Pᵀ * X)) : specNorm (Pᵀ * X) = specNorm X := by
  have hP1 : specNorm P ≤ 1 := l2_opNorm_le_one_of_orthonormal P hP
  have hPt : specNorm Pᵀ ≤ 1 := by rw [specNorm_transpose]; exact hP1
  apply le_antisymm
  · calc specNorm (Pᵀ * X) ≤ specNorm Pᵀ * specNorm X := specNorm_mul_le _ _
      _ ≤ 1 * specNorm X := by gcongr; exact specNorm_nonneg _
      _ = specNorm X := one_mul _
  · calc specNorm X = specNorm (P * (Pᵀ * X)) := by rw [← hX]
      _ ≤ specNorm P * specNorm (Pᵀ * X) := specNorm_mul_le _ _
      _ ≤ 1 * specNorm (Pᵀ * X) := by gcongr; exact specNorm_nonneg _
      _ = specNorm (Pᵀ * X) := one_mul _

/-- `‖Q⊥ᵀ E‖₂ = ‖E‖₂` for the spectral norm (Chen–Persson, proof of `lem:tGN-core`:
`‖B‖ = ‖A⊥‖`; the LRA project's former `SpectralIsometry`). Atlas `sketched-regression`. -/
theorem l2_opNorm_perp_mul_residual (Q : Matrix m (Fin q) ℝ) (hQ : HasOrthonormalCols Q)
    (Qp : Matrix m (Fin r) ℝ) (hQp : HasOrthonormalCols Qp)
    (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1) (A : Matrix m n ℝ) :
    specNorm (Qpᵀ * residual Q A) = specNorm (residual Q A) :=
  l2_opNorm_transpose_mul_of_eq Qp hQp _ (residual_eq_perp_mul Q Qp A hQ hcomp)

end Spectral

end NLAlib
