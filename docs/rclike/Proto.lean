import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.Star
/-! Prototype of the RCLike vocabulary (stage A) with real corollaries. Scratch only. -/
noncomputable section
set_option linter.unusedSectionVars false
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlibRC
variable {𝕜 : Type*} [RCLike 𝕜] {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]

/-! ### Definitions -/
def frobInner (A B : Matrix m n 𝕜) : ℝ := RCLike.re (∑ i, ∑ j, star (A i j) * B i j)
def frobSq (A : Matrix m n 𝕜) : ℝ := frobInner A A
def frobNorm (A : Matrix m n 𝕜) : ℝ := Real.sqrt (frobSq A)
def specNorm [DecidableEq m] [DecidableEq n] (A : Matrix m n 𝕜) : ℝ := ‖A‖
def HasOrthonormalCols [DecidableEq q] (Q : Matrix m q 𝕜) : Prop := Qᴴ * Q = 1
def residual (Q : Matrix m q 𝕜) (A : Matrix m n 𝕜) : Matrix m n 𝕜 := A - Q * (Qᴴ * A)
def quadForm (A : Matrix n n 𝕜) (z : n → 𝕜) : 𝕜 := star z ⬝ᵥ (A *ᵥ z)

/-! ### Real bridges (definitional) -/
theorem frobInner_eq_sum_mul (A B : Matrix m n ℝ) : frobInner A B = ∑ i, ∑ j, A i j * B i j := rfl
theorem quadForm_eq_dotProduct (A : Matrix n n ℝ) (z : n → ℝ) : quadForm A z = z ⬝ᵥ (A *ᵥ z) := rfl
theorem residual_eq_sub_mul_transpose_mul (Q : Matrix m q ℝ) (A : Matrix m n ℝ) :
    residual Q A = A - Q * (Qᵀ * A) := rfl
theorem hasOrthonormalCols_iff_transpose_mul_self [DecidableEq q] {Q : Matrix m q ℝ} :
    HasOrthonormalCols Q ↔ Qᵀ * Q = 1 := Iff.rfl
theorem HasOrthonormalCols.transpose_mul_self [DecidableEq q] {Q : Matrix m q ℝ}
    (hQ : HasOrthonormalCols Q) : Qᵀ * Q = 1 := hQ
theorem HasOrthonormalCols.conjTranspose_mul_self [DecidableEq q] {Q : Matrix m q 𝕜}
    (hQ : HasOrthonormalCols Q) : Qᴴ * Q = 1 := hQ

/-! ### General API (ported proofs) -/
theorem frobInner_comm (A B : Matrix m n 𝕜) : frobInner A B = frobInner B A := by
  unfold frobInner
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← RCLike.conj_re (star (B i j) * A i j), ← RCLike.star_def, star_mul, star_star]

theorem frobInner_eq_re_trace (A B : Matrix m n 𝕜) :
    frobInner A B = RCLike.re (Aᴴ * B).trace := by
  unfold frobInner Matrix.trace
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]

/-- real corollary keeps the old name and statement -/
theorem frobInner_eq_trace (A B : Matrix m n ℝ) : frobInner A B = (Aᵀ * B).trace := by
  simpa using frobInner_eq_re_trace A B

theorem frobInner_add_left (A B C : Matrix m n 𝕜) :
    frobInner (A + B) C = frobInner A C + frobInner B C := by
  unfold frobInner
  simp [add_mul, Finset.sum_add_distrib]

theorem frobSq_eq_sum_norm_sq (A : Matrix m n 𝕜) : frobSq A = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  unfold frobSq frobInner
  simp only [map_sum, RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

theorem frobSq_eq_sum_sq (A : Matrix m n ℝ) : frobSq A = ∑ i, ∑ j, A i j ^ 2 := by
  simp [frobSq_eq_sum_norm_sq]

theorem frobSq_nonneg (A : Matrix m n 𝕜) : 0 ≤ frobSq A := by
  rw [frobSq_eq_sum_norm_sq]; positivity

theorem frobSq_eq_zero_iff (A : Matrix m n 𝕜) : frobSq A = 0 ↔ A = 0 := by
  rw [frobSq_eq_sum_norm_sq, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)]
  simp only [Finset.mem_univ, true_implies]
  constructor
  · intro h; ext i j
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).1 (h i) j (Finset.mem_univ _)
    simpa using this
  · rintro rfl; simp

theorem frobSq_smul (c : 𝕜) (A : Matrix m n 𝕜) : frobSq (c • A) = ‖c‖ ^ 2 * frobSq A := by
  simp only [frobSq_eq_sum_norm_sq, Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow,
    Finset.mul_sum]

theorem conjTranspose_mul_residual [DecidableEq q] {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix m n 𝕜) : Qᴴ * residual Q A = 0 := by
  unfold residual HasOrthonormalCols at *
  rw [Matrix.mul_sub, ← Matrix.mul_assoc, hQ, Matrix.one_mul, sub_self]

/-- real corollary under the old name -/
theorem transpose_mul_residual [DecidableEq q] {Q : Matrix m q ℝ} (hQ : HasOrthonormalCols Q)
    (A : Matrix m n ℝ) : Qᵀ * residual Q A = 0 := by
  simpa using conjTranspose_mul_residual hQ A

theorem frobInner_mul_residual [DecidableEq q] {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q)
    (X : Matrix q n 𝕜) (A : Matrix m n 𝕜) : frobInner (Q * X) (residual Q A) = 0 := by
  rw [frobInner_eq_re_trace, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    conjTranspose_mul_residual hQ, Matrix.mul_zero, Matrix.trace_zero, map_zero]

theorem specNorm_conjTranspose [DecidableEq m] [DecidableEq n] (A : Matrix m n 𝕜) :
    specNorm Aᴴ = specNorm A := Matrix.l2_opNorm_conjTranspose A

theorem specNorm_mul_le [DecidableEq m] [DecidableEq n] [DecidableEq p] (A : Matrix m n 𝕜)
    (B : Matrix n p 𝕜) : specNorm (A * B) ≤ specNorm A * specNorm B :=
  Matrix.l2_opNorm_mul A B

open scoped ComplexOrder in
theorem quadForm_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef) (z : n → 𝕜) :
    0 ≤ quadForm A z := hA.dotProduct_mulVec_nonneg z

/-! ### Downstream real snippets copied verbatim from NLAlib (must compile unchanged) -/
-- Projections.mul_transpose_mul_mul_transpose (proof via `have h : Qᵀ * Q = 1 := hQ`)
theorem mul_transpose_mul_mul_transpose [DecidableEq q] {Q : Matrix m q ℝ}
    (hQ : HasOrthonormalCols Q) : Q * Qᵀ * (Q * Qᵀ) = Q * Qᵀ := by
  have h : Qᵀ * Q = 1 := hQ
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Qᵀ, h, Matrix.one_mul]
-- residual_residual (uses `show` + the real corollary)
theorem residual_residual [DecidableEq q] {Q : Matrix m q ℝ} (hQ : HasOrthonormalCols Q)
    (A : Matrix m n ℝ) : residual Q (residual Q A) = residual Q A := by
  show residual Q A - Q * (Qᵀ * residual Q A) = residual Q A
  rw [transpose_mul_residual hQ, Matrix.mul_zero, sub_zero]
-- a FrameContractions-style line: rw [frobNorm, frobSq, frobInner_eq_trace, hQ, trace_one]
example [DecidableEq q] {Q : Matrix m q ℝ} (hQ : Qᵀ * Q = 1) :
    frobSq Q = Fintype.card q := by
  rw [frobSq, frobInner_eq_trace, hQ, Matrix.trace_one]
-- a site that breaks: old `rw [hQ]` with the def-typed hypothesis
example [DecidableEq q] {Q : Matrix m q ℝ} (hQ : HasOrthonormalCols Q) (X : Matrix q n ℝ) :
    Qᵀ * (Q * X) = X := by
  rw [← Matrix.mul_assoc, hQ.transpose_mul_self, Matrix.one_mul]   -- recipe: hQ ↦ hQ.transpose_mul_self
-- quadForm site recipe: `simp only [quadForm, …]` ↦ `simp only [quadForm_eq_dotProduct, …]`
example (A : Matrix n n ℝ) (z : n → ℝ) : quadForm A z = ∑ i, ∑ j, A i j * (z i * z j) := by
  simp only [quadForm_eq_dotProduct, dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
-- linarith with the general nonneg lemma at ℝ
example {A : Matrix n n ℝ} (hA : A.PosSemidef) (z : n → ℝ) (c : ℝ) (h : quadForm A z ≤ c) : 0 ≤ c := by
  have := quadForm_nonneg hA z; linarith
-- specNorm at ℝ uses the same instance as before
example [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) : specNorm A = ‖A‖ := rfl
end NLAlibRC
