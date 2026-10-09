import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.Group.Idempotent
import NLAlib.Matrix.Norms

/-!
# Pseudoinverses

Full-rank special cases of the Moore–Penrose pseudoinverse, as the sources use them:

* `NLAlib.pinvL G = (Gᵀ G)⁻¹ Gᵀ`, equal to `G†` when `G` has full column rank;
* `NLAlib.pinvR G = Gᵀ (G Gᵀ)⁻¹`, equal to `G†` when `G` has full row rank.

Mathlib's `⁻¹` on matrices is total (it returns `0` on singular input), so these are honest
definitions; the only property most arguments use is the one-sided inverse identity, which
holds under the corresponding `IsUnit` hypothesis. The general Moore–Penrose definition with
the four Penrose identities is atlas target `pseudoinverse`.

Proved here for the full-rank cases (HMT 2011 §A.2, Horn–Johnson §7.3):

* `pinvL_transpose`, `pinvR_transpose`: `(G⁺)ᵀ = (Gᵀ)⁺`, with left and right swapped;
* the Penrose identities `G G⁺ G = G`, `G⁺ G G⁺ = G⁺` for both `pinvL` and `pinvR`;
* `G G⁺` (resp. `G⁺ G`) is symmetric and idempotent, i.e. an orthogonal projector;
* `frobSq_pinvR : ‖G†‖_F² = tr (G Gᵀ)⁻¹` and its column-rank twin `frobSq_pinvL`.

Atlas: `pseudoinverse`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Left pseudoinverse `(Gᵀ G)⁻¹ Gᵀ`. -/
def pinvL [DecidableEq n] (G : Matrix m n ℝ) : Matrix n m ℝ := (Gᵀ * G)⁻¹ * Gᵀ

/-- Right pseudoinverse `Gᵀ (G Gᵀ)⁻¹`. -/
def pinvR [DecidableEq m] (G : Matrix m n ℝ) : Matrix n m ℝ := Gᵀ * (G * Gᵀ)⁻¹

theorem pinvL_mul [DecidableEq n] {G : Matrix m n ℝ} (h : IsUnit (Gᵀ * G)) :
    pinvL G * G = 1 := by
  unfold pinvL
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp h)]

theorem mul_pinvR [DecidableEq m] {G : Matrix m n ℝ} (h : IsUnit (G * Gᵀ)) :
    G * pinvR G = 1 := by
  unfold pinvR
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp h)]

/-! ### Transposes -/

/-- `((GᵀG)⁻¹Gᵀ)ᵀ = G(GᵀG)⁻¹`, i.e. `(pinvL G)ᵀ = pinvR Gᵀ`. Holds unconditionally (both sides
are `G (GᵀG)⁻¹` with Mathlib's total inverse). HMT 2011 §A.2; atlas `pseudoinverse`. -/
theorem pinvL_transpose [DecidableEq n] (G : Matrix m n ℝ) : (pinvL G)ᵀ = pinvR Gᵀ := by
  unfold pinvL pinvR
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.transpose_mul,
    Matrix.transpose_transpose]

/-- `(pinvR G)ᵀ = pinvL Gᵀ`. Holds unconditionally. HMT 2011 §A.2; atlas `pseudoinverse`. -/
theorem pinvR_transpose [DecidableEq m] (G : Matrix m n ℝ) : (pinvR G)ᵀ = pinvL Gᵀ := by
  unfold pinvL pinvR
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.transpose_mul,
    Matrix.transpose_transpose]

/-! ### Penrose identities -/

/-- Penrose identity `G G⁺ G = G` for the left pseudoinverse (full column rank).
Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem mul_pinvL_mul [DecidableEq n] {G : Matrix m n ℝ} (h : IsUnit (Gᵀ * G)) :
    G * pinvL G * G = G := by
  rw [Matrix.mul_assoc, pinvL_mul h, Matrix.mul_one]

/-- Penrose identity `G⁺ G G⁺ = G⁺` for the left pseudoinverse (full column rank).
Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem pinvL_mul_pinvL [DecidableEq n] {G : Matrix m n ℝ} (h : IsUnit (Gᵀ * G)) :
    pinvL G * G * pinvL G = pinvL G := by
  rw [pinvL_mul h, Matrix.one_mul]

/-- Penrose identity `G G⁺ G = G` for the right pseudoinverse (full row rank).
Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem mul_pinvR_mul [DecidableEq m] {G : Matrix m n ℝ} (h : IsUnit (G * Gᵀ)) :
    G * pinvR G * G = G := by
  rw [mul_pinvR h, Matrix.one_mul]

/-- Penrose identity `G⁺ G G⁺ = G⁺` for the right pseudoinverse (full row rank).
Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem pinvR_mul_pinvR [DecidableEq m] {G : Matrix m n ℝ} (h : IsUnit (G * Gᵀ)) :
    pinvR G * G * pinvR G = pinvR G := by
  rw [Matrix.mul_assoc, mul_pinvR h, Matrix.mul_one]

/-! ### Orthogonal projectors `G G⁺` and `G⁺ G` -/

/-- `G (GᵀG)⁻¹ Gᵀ` is symmetric (unconditionally). Penrose identity `(GG⁺)ᵀ = GG⁺`;
HMT 2011 §A.2; atlas `pseudoinverse`. -/
theorem mul_pinvL_isSymm [DecidableEq n] (G : Matrix m n ℝ) : (G * pinvL G).IsSymm := by
  unfold Matrix.IsSymm pinvL
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- `G (GᵀG)⁻¹ Gᵀ` is idempotent when `GᵀG` is invertible, so it is the orthogonal projector
onto `range G`. HMT 2011 §A.2; atlas `pseudoinverse`. -/
theorem mul_pinvL_isIdempotentElem [DecidableEq n] {G : Matrix m n ℝ} (h : IsUnit (Gᵀ * G)) :
    IsIdempotentElem (G * pinvL G) := by
  unfold IsIdempotentElem
  rw [← Matrix.mul_assoc, mul_pinvL_mul h]

/-- `Gᵀ (GGᵀ)⁻¹ G` is symmetric (unconditionally). Penrose identity `(G⁺G)ᵀ = G⁺G`;
HMT 2011 §A.2; atlas `pseudoinverse`. -/
theorem pinvR_mul_isSymm [DecidableEq m] (G : Matrix m n ℝ) : (pinvR G * G).IsSymm := by
  unfold Matrix.IsSymm pinvR
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- `Gᵀ (GGᵀ)⁻¹ G` is idempotent when `GGᵀ` is invertible, so it is the orthogonal projector
onto `range Gᵀ`. HMT 2011 §A.2; atlas `pseudoinverse`. -/
theorem pinvR_mul_isIdempotentElem [DecidableEq m] {G : Matrix m n ℝ} (h : IsUnit (G * Gᵀ)) :
    IsIdempotentElem (pinvR G * G) := by
  unfold IsIdempotentElem
  rw [← Matrix.mul_assoc, pinvR_mul_pinvR h]

/-- The trivial projectors: `pinvL G * G = 1` is symmetric. Recorded for completeness of the
four Penrose identities for `pinvL`. Atlas `pseudoinverse`. -/
theorem pinvL_mul_isSymm [DecidableEq n] {G : Matrix m n ℝ} (h : IsUnit (Gᵀ * G)) :
    (pinvL G * G).IsSymm := by
  rw [pinvL_mul h]; exact Matrix.isSymm_one

/-- `G * pinvR G = 1` is symmetric. Recorded for completeness of the four Penrose identities
for `pinvR`. Atlas `pseudoinverse`. -/
theorem mul_pinvR_isSymm [DecidableEq m] {G : Matrix m n ℝ} (h : IsUnit (G * Gᵀ)) :
    (G * pinvR G).IsSymm := by
  rw [mul_pinvR h]; exact Matrix.isSymm_one

/-! ### Frobenius norm of the pseudoinverse -/

/-- `‖G†‖_F² = tr (G Gᵀ)⁻¹` for `G` of full row rank (`IsUnit (G Gᵀ)`), with `G† = pinvR G`.
The identity behind the Gaussian inverse-moment results (HMT 2011 §A.2, proof of Prop 10.1).
Atlas `pseudoinverse`. -/
theorem frobSq_pinvR [DecidableEq m] {G : Matrix m n ℝ} (h : IsUnit (G * Gᵀ)) :
    frobSq (pinvR G) = ((G * Gᵀ)⁻¹).trace := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp h
  have hsymm : ((G * Gᵀ)⁻¹)ᵀ = (G * Gᵀ)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose]
  unfold frobSq pinvR
  rw [frobInner_eq_trace, Matrix.transpose_mul, Matrix.transpose_transpose, hsymm,
    Matrix.mul_assoc, ← Matrix.mul_assoc G, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]

/-- `‖G†‖_F² = tr (Gᵀ G)⁻¹` for `G` of full column rank (`IsUnit (GᵀG)`), with `G† = pinvL G`.
HMT 2011 §A.2; atlas `pseudoinverse`. -/
theorem frobSq_pinvL [DecidableEq n] {G : Matrix m n ℝ} (h : IsUnit (Gᵀ * G)) :
    frobSq (pinvL G) = ((Gᵀ * G)⁻¹).trace := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp h
  have hsymm : ((Gᵀ * G)⁻¹)ᵀ = (Gᵀ * G)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose]
  unfold frobSq pinvL
  rw [frobInner_eq_trace, Matrix.transpose_mul, Matrix.transpose_transpose, hsymm,
    Matrix.trace_mul_comm, Matrix.mul_assoc, ← Matrix.mul_assoc Gᵀ, Matrix.mul_nonsing_inv _ hd,
    Matrix.mul_one]

end NLAlib
