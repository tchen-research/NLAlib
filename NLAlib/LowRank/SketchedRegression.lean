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
`frobSq_sub_mul_eq`, `transpose_perp_mul`, `residual_eq_perp_mul`) are
`NLAlib.mul_transpose_mul_add_residual`, `NLAlib.transpose_mul_residual`,
`NLAlib.frobInner_mul_residual`, `NLAlib.frobSq_sub_mul_eq`, `NLAlib.transpose_mul_eq_zero_comm`
and `NLAlib.residual_eq_mul_transpose_mul_residual` in `NLAlib.Matrix.Projections`; its spectral
facts (`l2_opNorm_one_le`, `l2_opNorm_le_one_of_orthonormal`, `l2_opNorm_transpose_mul_of_eq`)
are `NLAlib.specNorm_one_le`, `NLAlib.specNorm_le_one_of_orthonormal` and
`NLAlib.specNorm_transpose_mul_of_eq_mul` in `NLAlib.Matrix.Norms`. The source's `‖·‖` under
`Matrix.Norms.L2Operator` is `NLAlib.specNorm` here (definitionally equal, `specNorm_eq_norm`).

## Set-up (matching the paper)

* `Q : Matrix m q ℝ` with orthonormal columns (`hQ`);
* `Qp : Matrix m r ℝ` is the paper's `Q⊥`: orthonormal columns (`hQp`), `Qᵀ Q⊥ = 0`
  (`hQQp`) and completeness `Q Qᵀ + Q⊥ Q⊥ᵀ = I` (`hcomp`), i.e. `[Q  Q⊥]` is orthogonal;
* `Ψ : Matrix m s ℝ` is the (fixed) sketch, `G₁ := Ψᵀ Q`, `G₂ := Ψᵀ Q⊥`;
* `residual Q A = A - Q(QᵀA)` is the paper's `E = (I - QQᵀ)A` (called `A⊥` in `lem:tGN-core`);
* `hG₁ : IsUnit (G₁ᵀ G₁)` encodes "`G₁` has full column rank"; the paper's `G₁†` is `pinvL G₁`
  and the only property used is `pinvL G₁ * G₁ = 1` (`NLAlib.pinvL_mul`);
* `sketchedCore Q Ψ A = pinvL (ΨᵀQ) (ΨᵀA)` is the fitted core `X̂ = (ΨᵀQ)† ΨᵀA`,
  `sketchedOutput Q Ψ A = Q X̂` is the paper's `Â`, and
  `coreNoise Q Ψ A = pinvL (ΨᵀQ) (Ψᵀ A⊥)` is the paper's `E_core`.
* All index types are arbitrary `Fintype`s (the source's `Fin q`, `Fin r`, `Fin s` are the
  instances used by the Gaussian files).

Atlas: `sketched-regression`.
-/

noncomputable section
set_option autoImplicit false

open scoped Matrix

namespace NLAlib

variable {m n q r s : Type*} [Fintype m] [Fintype q] [Fintype r] [Fintype s]
  [DecidableEq q]

/-- The sketched core `X̂ = (ΨᵀQ)† ΨᵀA`, with `†` the left pseudoinverse `pinvL`
(Chen–Persson, `eq:tGN-fitted-core`; Tropp–Webber 2023 §5). Atlas `sketched-regression`.
atlas: sketched-regression -/
def sketchedCore (Q : Matrix m q ℝ) (Ψ : Matrix m s ℝ) (A : Matrix m n ℝ) :
    Matrix q n ℝ := pinvL (Ψᵀ * Q) * (Ψᵀ * A)

/-- The sketched output `Â = Q X̂ = Q (ΨᵀQ)† ΨᵀA` (Chen–Persson, `lem:completion`;
Tropp–Webber 2023 §5). Atlas `sketched-regression`.
atlas: sketched-regression -/
def sketchedOutput (Q : Matrix m q ℝ) (Ψ : Matrix m s ℝ) (A : Matrix m n ℝ) :
    Matrix m n ℝ := Q * sketchedCore Q Ψ A

/-- The core noise `E_core = (ΨᵀQ)† Ψᵀ A⊥` with `A⊥ = (I - QQᵀ)A` (Chen–Persson,
`eq:tGN-fitted-core`, `lem:tGN-core`). Not in the LRA source, which writes the expression
out. Atlas `sketched-regression`.
atlas: sketched-regression -/
def coreNoise (Q : Matrix m q ℝ) (Ψ : Matrix m s ℝ) (A : Matrix m n ℝ) :
    Matrix q n ℝ := pinvL (Ψᵀ * Q) * (Ψᵀ * residual Q A)

/-! ### Facts that need only `QᵀQ = I` -/

section OnlyQ

variable (Q : Matrix m q ℝ) (A : Matrix m n ℝ)

/-- Rank-deficient remark in the proofs of `thm:GN` / `thm:tGN` (Chen–Persson): if
`A = Q(QᵀA)` (i.e. `E = 0`) and `ΨᵀQ` has full column rank, the fitted core is exactly `QᵀA`.
Atlas `sketched-regression`. -/
theorem sketchedCore_eq_of_eq_mul (Ψ : Matrix m s ℝ) (hG₁ : IsUnit ((Ψᵀ * Q)ᵀ * (Ψᵀ * Q)))
    (hA : A = Q * (Qᵀ * A)) : sketchedCore Q Ψ A = Qᵀ * A := by
  unfold sketchedCore
  conv_lhs => rw [hA]
  rw [← Matrix.mul_assoc Ψᵀ, ← Matrix.mul_assoc, pinvL_mul hG₁, Matrix.one_mul]

/-- Rank-deficient remark (Chen–Persson, proofs of `thm:GN` / `thm:tGN`): if `A = Q(QᵀA)` and
`ΨᵀQ` has full column rank, then `Â = A`. Atlas `sketched-regression`. -/
theorem sketchedOutput_eq_of_eq_mul (Ψ : Matrix m s ℝ)
    (hG₁ : IsUnit ((Ψᵀ * Q)ᵀ * (Ψᵀ * Q))) (hA : A = Q * (Qᵀ * A)) :
    sketchedOutput Q Ψ A = A := by
  unfold sketchedOutput
  rw [sketchedCore_eq_of_eq_mul Q A Ψ hG₁ hA, ← hA]

end OnlyQ

/-! ### Facts using the orthogonal completion `[Q  Q⊥]` -/

section Completion

variable [DecidableEq m]
variable (Q : Matrix m q ℝ) (Qp : Matrix m r ℝ) (Ψ : Matrix m s ℝ)
  (A : Matrix m n ℝ)

omit [Fintype s] in
/-- `Ψᵀ E = G₂ (Q⊥ᵀ E)` where `G₂ = Ψᵀ Q⊥` (Chen–Persson, proof of `lem:completion`).
Atlas `sketched-regression`. -/
theorem transpose_mul_residual_eq (hQ : HasOrthonormalCols Q) (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1) :
    Ψᵀ * residual Q A = (Ψᵀ * Qp) * (Qpᵀ * residual Q A) := by
  conv_lhs => rw [residual_eq_mul_transpose_mul_residual hQ hcomp A]
  rw [Matrix.mul_assoc]

omit [Fintype s] in
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
`range(Q⊥)` and `range(Q)`, which are orthogonal. Atlas `sketched-regression`.
atlas: sketched-regression -/
theorem frobSq_error [Fintype n] (hQ : HasOrthonormalCols Q) (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1)
    (hG₁ : IsUnit ((Ψᵀ * Q)ᵀ * (Ψᵀ * Q))) :
    frobSq (A - sketchedOutput Q Ψ A) =
      frobSq (residual Q A) + frobSq (pinvL (Ψᵀ * Q) * (Ψᵀ * Qp) * (Qpᵀ * residual Q A)) := by
  rw [error_decomp Q Qp Ψ A hQ hcomp hG₁,
    frobSq_sub_of_frobInner_eq_zero _ _ (by
      rw [frobInner_comm]; exact frobInner_mul_residual hQ _ A),
    frobSq_mul_left_of_orthonormal hQ]

/-- `‖Q⊥ᵀ E‖_F² = ‖E‖_F²` (Chen–Persson, end of the proof of `lem:completion` and proof of
`lem:tGN-core`, `‖B‖_F = ‖A⊥‖_F`). Atlas `sketched-regression`.
atlas: sketched-regression -/
theorem frobSq_transpose_mul_residual [Fintype n] [DecidableEq r] (hQ : HasOrthonormalCols Q)
    (hQp : HasOrthonormalCols Qp) (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1) :
    frobSq (Qpᵀ * residual Q A) = frobSq (residual Q A) := by
  conv_rhs => rw [residual_eq_mul_transpose_mul_residual hQ hcomp A]
  rw [frobSq_mul_left_of_orthonormal hQp]

/-- Deterministic core of `lem:tGN-core` and `eq:tGN-fitted-core` (Chen–Persson): the noise
term `E_core = (ΨᵀQ)† Ψᵀ A⊥` equals `G₁† G₂ B` with `G₁ = ΨᵀQ`, `G₂ = ΨᵀQ⊥`, `B = Q⊥ᵀ A⊥`, where
`A⊥ = (I - QQᵀ)A = residual Q A` (LRA `core_noise_eq`, there with the noise written out).
Atlas `sketched-regression`. -/
theorem coreNoise_eq (hQ : HasOrthonormalCols Q) (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1) :
    coreNoise Q Ψ A = pinvL (Ψᵀ * Q) * (Ψᵀ * Qp) * (Qpᵀ * residual Q A) := by
  rw [coreNoise, transpose_mul_residual_eq Q Qp Ψ A hQ hcomp,
    ← Matrix.mul_assoc (pinvL (Ψᵀ * Q))]

/-- `eq:tGN-fitted-core` (Chen–Persson; Tropp–Webber 2023 §5): `X̂ = C + E_core` with `C = QᵀA`
and `E_core = coreNoise Q Ψ A = (ΨᵀQ)† Ψᵀ A⊥` (LRA `sketchedCore_eq_add_core_noise`).
Atlas `sketched-regression`.
atlas: sketched-regression -/
theorem sketchedCore_eq_add_coreNoise (hQ : HasOrthonormalCols Q)
    (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1) (hG₁ : IsUnit ((Ψᵀ * Q)ᵀ * (Ψᵀ * Q))) :
    sketchedCore Q Ψ A = Qᵀ * A + coreNoise Q Ψ A := by
  rw [sketchedCore_eq Q Qp Ψ A hQ hcomp hG₁, coreNoise_eq Q Qp Ψ A hQ hcomp]

end Completion

/-! ### Spectral norm -/

/-- `‖Q⊥ᵀ E‖₂ = ‖E‖₂` for the spectral norm (Chen–Persson, proof of `lem:tGN-core`:
`‖B‖ = ‖A⊥‖`; the LRA project's former `SpectralIsometry`). Atlas `sketched-regression`.
atlas: sketched-regression -/
theorem specNorm_transpose_mul_residual [Fintype n] [DecidableEq m] [DecidableEq n] [DecidableEq r]
    {Q : Matrix m q ℝ} (hQ : HasOrthonormalCols Q) {Qp : Matrix m r ℝ} (hQp : HasOrthonormalCols Qp)
    (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1) (A : Matrix m n ℝ) :
    specNorm (Qpᵀ * residual Q A) = specNorm (residual Q A) :=
  specNorm_transpose_mul_of_eq_mul hQp (residual_eq_mul_transpose_mul_residual hQ hcomp A)

end NLAlib
