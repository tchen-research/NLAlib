import NLAlib.Matrix.Norms.Core
/-!
# Pseudoinverses

Full-rank special cases of the Moore–Penrose pseudoinverse, as the sources use them, over any
`RCLike` field `𝕜` (ℝ or ℂ):

* `NLAlib.pinvL G = (Gᴴ G)⁻¹ Gᴴ`, equal to `G†` when `G` has full column rank;
* `NLAlib.pinvR G = Gᴴ (G Gᴴ)⁻¹`, equal to `G†` when `G` has full row rank.

At `𝕜 = ℝ` these are definitionally the transpose forms `(Gᵀ G)⁻¹ Gᵀ` and `Gᵀ (G Gᵀ)⁻¹`; in real
proofs `rw [pinvL, Matrix.conjTranspose_eq_transpose_of_trivial]` unfolds to the transpose form.

Mathlib's `⁻¹` on matrices is total (it returns `0` on singular input), so these are honest
definitions; the only property most arguments use is the one-sided inverse identity, which
holds under the corresponding `IsUnit` hypothesis. The general Moore–Penrose definition with
the four Penrose identities is atlas target `pseudoinverse`.

Proved here for the full-rank cases (HMT 2011 §A.2, Horn–Johnson §7.3):

* `pinvL_conjTranspose`, `pinvL_transpose` and their `pinvR` twins: `(G⁺)ᴴ = (Gᴴ)⁺` and
  `(G⁺)ᵀ = (Gᵀ)⁺`, with left and right swapped;
* the Penrose identities `G G⁺ G = G`, `G⁺ G G⁺ = G⁺` for both `pinvL` and `pinvR`;
* `G G⁺` (resp. `G⁺ G`) is Hermitian and idempotent, i.e. an orthogonal projector;
* `frobSq_pinvR_eq_trace_inv : ‖G†‖_F² = Re tr (G Gᴴ)⁻¹` and its column-rank twin.

Lemmas with an invertibility hypothesis take `IsUnit (Gᴴ * G)` (resp. `IsUnit (G * Gᴴ)`). Over `ℝ`
a hypothesis `IsUnit (Gᵀ * G)` is accepted definitionally; when `G` is a compound matrix such as
`Ψᵀ * Q`, name it (`pinvL_mul (G := Ψᵀ * Q) h`), otherwise Lean solves `?Gᴴ =?= (Ψᵀ * Q)ᵀ` by
unfolding and `rw` no longer finds `pinvL (Ψᵀ * Q)`.

Atlas: `pseudoinverse`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- Left pseudoinverse `(Gᴴ G)⁻¹ Gᴴ` (at `𝕜 = ℝ`: `(Gᵀ G)⁻¹ Gᵀ`).
atlas: pseudoinverse -/
def pinvL [DecidableEq n] (G : Matrix m n 𝕜) : Matrix n m 𝕜 := (Gᴴ * G)⁻¹ * Gᴴ

/-- Right pseudoinverse `Gᴴ (G Gᴴ)⁻¹` (at `𝕜 = ℝ`: `Gᵀ (G Gᵀ)⁻¹`).
atlas: pseudoinverse -/
def pinvR [DecidableEq m] (G : Matrix m n 𝕜) : Matrix n m 𝕜 := Gᴴ * (G * Gᴴ)⁻¹

/-! ### One-sided inverse identities -/

/-- The left pseudoinverse is a left inverse when `Gᴴ G` is invertible: `G⁺ G = 1`.
atlas: pseudoinverse -/
theorem pinvL_mul [DecidableEq n] {G : Matrix m n 𝕜}
    (h : IsUnit (Gᴴ * G)) : pinvL G * G = 1 := by
  unfold pinvL
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp h)]

/-- The right pseudoinverse is a right inverse when `G Gᴴ` is invertible: `G G⁺ = 1`.
atlas: pseudoinverse -/
theorem mul_pinvR [DecidableEq m] {G : Matrix m n 𝕜}
    (h : IsUnit (G * Gᴴ)) : G * pinvR G = 1 := by
  unfold pinvR
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp h)]

/-! ### Conjugate transposes and transposes -/

/-- `((GᴴG)⁻¹Gᴴ)ᴴ = G(GᴴG)⁻¹`, i.e. `(pinvL G)ᴴ = pinvR Gᴴ`. Holds unconditionally (both sides
are `G (GᴴG)⁻¹` with Mathlib's total inverse). HMT 2011 §A.2; atlas `pseudoinverse`. -/
theorem pinvL_conjTranspose [DecidableEq n] (G : Matrix m n 𝕜) : (pinvL G)ᴴ = pinvR Gᴴ := by
  unfold pinvL pinvR
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

/-- `(pinvR G)ᴴ = pinvL Gᴴ`. Holds unconditionally. HMT 2011 §A.2; atlas `pseudoinverse`. -/
theorem pinvR_conjTranspose [DecidableEq m] (G : Matrix m n 𝕜) : (pinvR G)ᴴ = pinvL Gᴴ := by
  unfold pinvL pinvR
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

/-- `(pinvL G)ᵀ = pinvR Gᵀ` (both sides are `Ḡ (Gᵀ Ḡ)⁻¹`). Holds unconditionally, over any
`RCLike` field. HMT 2011 §A.2; atlas `pseudoinverse`.
atlas: pseudoinverse -/
theorem pinvL_transpose [DecidableEq n] (G : Matrix m n 𝕜) : (pinvL G)ᵀ = pinvR Gᵀ := by
  unfold pinvL pinvR
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.transpose_mul,
    Matrix.conjTranspose_transpose_eq_transpose_conjTranspose]

/-- `(pinvR G)ᵀ = pinvL Gᵀ`. Holds unconditionally, over any `RCLike` field. HMT 2011 §A.2;
atlas `pseudoinverse`. -/
theorem pinvR_transpose [DecidableEq m] (G : Matrix m n 𝕜) : (pinvR G)ᵀ = pinvL Gᵀ := by
  unfold pinvL pinvR
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.transpose_mul,
    Matrix.conjTranspose_transpose_eq_transpose_conjTranspose]

/-! ### Penrose identities -/

/-- Penrose identity `G G⁺ G = G` for the left pseudoinverse (full column rank).
Horn–Johnson §7.3; atlas `pseudoinverse`.
atlas: pseudoinverse -/
theorem mul_pinvL_mul [DecidableEq n] {G : Matrix m n 𝕜}
    (h : IsUnit (Gᴴ * G)) : G * pinvL G * G = G := by
  rw [Matrix.mul_assoc, pinvL_mul h, Matrix.mul_one]

/-- Penrose identity `G⁺ G G⁺ = G⁺` for the left pseudoinverse (full column rank).
Horn–Johnson §7.3; atlas `pseudoinverse`.
atlas: pseudoinverse -/
theorem pinvL_mul_pinvL [DecidableEq n] {G : Matrix m n 𝕜}
    (h : IsUnit (Gᴴ * G)) : pinvL G * G * pinvL G = pinvL G := by
  rw [pinvL_mul h, Matrix.one_mul]

/-- Penrose identity `G G⁺ G = G` for the right pseudoinverse (full row rank).
Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem mul_pinvR_mul [DecidableEq m] {G : Matrix m n 𝕜}
    (h : IsUnit (G * Gᴴ)) : G * pinvR G * G = G := by
  rw [mul_pinvR h, Matrix.one_mul]

/-- Penrose identity `G⁺ G G⁺ = G⁺` for the right pseudoinverse (full row rank).
Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem pinvR_mul_pinvR [DecidableEq m] {G : Matrix m n 𝕜}
    (h : IsUnit (G * Gᴴ)) : pinvR G * G * pinvR G = pinvR G := by
  rw [Matrix.mul_assoc, mul_pinvR h, Matrix.mul_one]

/-! ### Orthogonal projectors `G G⁺` and `G⁺ G` -/

/-- `G (GᴴG)⁻¹ Gᴴ` is Hermitian (unconditionally). Penrose identity `(GG⁺)ᴴ = GG⁺`;
HMT 2011 §A.2; atlas `pseudoinverse`.
atlas: pseudoinverse -/
theorem mul_pinvL_isHermitian [DecidableEq n] (G : Matrix m n 𝕜) :
    (G * pinvL G).IsHermitian := by
  unfold Matrix.IsHermitian pinvL
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- `Gᴴ (GGᴴ)⁻¹ G` is Hermitian (unconditionally). Penrose identity `(G⁺G)ᴴ = G⁺G`;
HMT 2011 §A.2; atlas `pseudoinverse`. -/
theorem pinvR_mul_isHermitian [DecidableEq m] (G : Matrix m n 𝕜) :
    (pinvR G * G).IsHermitian := by
  unfold Matrix.IsHermitian pinvR
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- `G (GᴴG)⁻¹ Gᴴ` is idempotent when `GᴴG` is invertible, so it is the orthogonal projector
onto `range G`. HMT 2011 §A.2; atlas `pseudoinverse`.
atlas: pseudoinverse -/
theorem mul_pinvL_isIdempotentElem [DecidableEq n]
    {G : Matrix m n 𝕜} (h : IsUnit (Gᴴ * G)) : IsIdempotentElem (G * pinvL G) := by
  unfold IsIdempotentElem
  rw [← Matrix.mul_assoc, mul_pinvL_mul h]

/-- `Gᴴ (GGᴴ)⁻¹ G` is idempotent when `GGᴴ` is invertible, so it is the orthogonal projector
onto `range Gᴴ`. HMT 2011 §A.2; atlas `pseudoinverse`. -/
theorem pinvR_mul_isIdempotentElem [DecidableEq m]
    {G : Matrix m n 𝕜} (h : IsUnit (G * Gᴴ)) : IsIdempotentElem (pinvR G * G) := by
  unfold IsIdempotentElem
  rw [← Matrix.mul_assoc, pinvR_mul_pinvR h]

/-- The trivial projector `pinvL G * G = 1` is Hermitian when `Gᴴ G` is invertible. Recorded for
completeness of the four Penrose identities for `pinvL`. Atlas `pseudoinverse`. -/
theorem pinvL_mul_isHermitian [DecidableEq n] {G : Matrix m n 𝕜} (h : IsUnit (Gᴴ * G)) :
    (pinvL G * G).IsHermitian := by
  rw [pinvL_mul h]; exact Matrix.isHermitian_one

/-- The trivial projector `G * pinvR G = 1` is Hermitian when `G Gᴴ` is invertible. Recorded for
completeness of the four Penrose identities for `pinvR`. Atlas `pseudoinverse`. -/
theorem mul_pinvR_isHermitian [DecidableEq m] {G : Matrix m n 𝕜} (h : IsUnit (G * Gᴴ)) :
    (G * pinvR G).IsHermitian := by
  rw [mul_pinvR h]; exact Matrix.isHermitian_one

/-! ### Frobenius norm of the pseudoinverse -/

/-- `‖G†‖_F² = Re tr (G Gᴴ)⁻¹` for every matrix `G` over `𝕜`, with `G† = pinvR G`. If `G Gᴴ` is
singular both sides are `0`, by Mathlib's convention `A⁻¹ = 0`. The identity behind the Gaussian
inverse-moment results (HMT 2011 §A.2, proof of Prop 10.1). Atlas `pseudoinverse`.
atlas: pseudoinverse, pinv-frob-moment -/
theorem frobSq_pinvR_eq_trace_inv [DecidableEq m] (G : Matrix m n 𝕜) :
    frobSq (pinvR G) = RCLike.re ((G * Gᴴ)⁻¹).trace := by
  by_cases h : IsUnit (G * Gᴴ)
  · have hd := (Matrix.isUnit_iff_isUnit_det _).mp h
    have hherm : ((G * Gᴴ)⁻¹)ᴴ = (G * Gᴴ)⁻¹ := by
      rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    unfold frobSq pinvR
    rw [frobInner_eq_trace, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hherm,
      Matrix.mul_assoc, ← Matrix.mul_assoc G, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  · have h0 : (G * Gᴴ)⁻¹ = 0 :=
      Matrix.nonsing_inv_apply_not_isUnit _ (by rwa [← Matrix.isUnit_iff_isUnit_det])
    have hp : pinvR G = 0 := by simp [pinvR, h0]
    rw [h0, hp, Matrix.trace_zero, frobSq_zero, map_zero]

/-- `‖G†‖_F² = Re tr (Gᴴ G)⁻¹` for every matrix `G` over `𝕜`, with `G† = pinvL G` (both sides
are `0` when `Gᴴ G` is singular). HMT 2011 §A.2; atlas `pseudoinverse`. -/
theorem frobSq_pinvL_eq_trace_inv [DecidableEq n] (G : Matrix m n 𝕜) :
    frobSq (pinvL G) = RCLike.re ((Gᴴ * G)⁻¹).trace := by
  by_cases h : IsUnit (Gᴴ * G)
  · have hd := (Matrix.isUnit_iff_isUnit_det _).mp h
    have hherm : ((Gᴴ * G)⁻¹)ᴴ = (Gᴴ * G)⁻¹ := by
      rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    unfold frobSq pinvL
    rw [frobInner_eq_trace, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hherm,
      Matrix.trace_mul_comm, Matrix.mul_assoc, ← Matrix.mul_assoc Gᴴ, Matrix.mul_nonsing_inv _ hd,
      Matrix.mul_one]
  · have h0 : (Gᴴ * G)⁻¹ = 0 :=
      Matrix.nonsing_inv_apply_not_isUnit _ (by rwa [← Matrix.isUnit_iff_isUnit_det])
    have hp : pinvL G = 0 := by simp [pinvL, h0]
    rw [h0, hp, Matrix.trace_zero, frobSq_zero, map_zero]

end NLAlib
