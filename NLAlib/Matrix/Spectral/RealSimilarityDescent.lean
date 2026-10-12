import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Data.Complex.BigOperators

/-!
# Descending complex similarities to real similarities

The determinant pencil of the real and imaginary parts has a nonzero
real evaluation whenever the complex matrix is nonsingular. The same real
pencil intertwines every member of an arbitrary family.
Source: Horn–Johnson (2013), Lemma 1.3.28 and Theorem 1.3.29;
atlas `real-similarity-descent`.
-/

noncomputable section
open Polynomial
open scoped Matrix

namespace NLAlib

variable {n ι : Type*} [Fintype n] [DecidableEq n]

/-- A nonsingular complex pencil `C+iD` has a nonsingular real member
`C+tD`. Source: Horn–Johnson (2013), Lemma 1.3.28; a nonzero determinant
polynomial has only finitely many real roots. -/
theorem exists_isUnit_add_smul_of_isUnit_complex_pencil (C D : Matrix n n ℝ)
    (hS : IsUnit (C.map Complex.ofReal + Complex.I • D.map Complex.ofReal)) :
    ∃ t : ℝ, IsUnit (C + t • D) := by
  classical
  let M : Matrix n n ℝ[X] := fun i j => Polynomial.C (C i j) + Polynomial.X * Polynomial.C (D i j)
  let p : ℝ[X] := M.det
  have hcomplex : p.eval₂ Complex.ofRealHom Complex.I =
      (C.map Complex.ofReal + Complex.I • D.map Complex.ofReal).det := by
    change (Polynomial.eval₂RingHom Complex.ofRealHom Complex.I) M.det = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    change Polynomial.eval₂ Complex.ofRealHom Complex.I
      (Polynomial.C (C i j) + Polynomial.X * Polynomial.C (D i j)) =
        Complex.ofReal (C i j) + Complex.I * Complex.ofReal (D i j)
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X]
    rfl
  have hp : p ≠ 0 := by
    intro hp0
    have hdet := (C.map Complex.ofReal + Complex.I • D.map Complex.ofReal).isUnit_iff_isUnit_det.mp hS
    rw [← hcomplex, hp0, Polynomial.eval₂_zero] at hdet
    exact not_isUnit_zero hdet
  have ht : ∃ t : ℝ, p.eval t ≠ 0 := by
    by_contra h
    push Not at h
    apply hp
    apply Polynomial.funext
    intro t
    simpa only [Polynomial.eval_zero] using h t
  obtain ⟨t, ht⟩ := ht
  refine ⟨t, (C + t • D).isUnit_iff_isUnit_det.mpr ?_⟩
  apply isUnit_iff_ne_zero.mpr
  have heval : p.eval t = (C + t • D).det := by
    change (Polynomial.evalRingHom t) M.det = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    change Polynomial.eval t (Polynomial.C (C i j) + Polynomial.X * Polynomial.C (D i j)) =
      C i j + t * D i j
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  exact heval ▸ ht

omit [DecidableEq n] in
/-- The real and imaginary parts of a complex intertwiner each intertwine
real matrices. Source: Horn–Johnson (2013), proof of Theorem 1.3.29. -/
theorem real_imaginary_parts_intertwine {A B : Matrix n n ℝ} {S : Matrix n n ℂ}
    (hS : A.map Complex.ofReal * S = S * B.map Complex.ofReal) :
    A * S.map Complex.re = S.map Complex.re * B ∧
      A * S.map Complex.im = S.map Complex.im * B := by
  constructor
  · ext i j
    have h := congrArg (fun M : Matrix n n ℂ => (M i j).re) hS
    simpa only [Matrix.mul_apply, Matrix.map_apply, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero] using h
  · ext i j
    have h := congrArg (fun M : Matrix n n ℂ => (M i j).im) hS
    simpa only [Matrix.mul_apply, Matrix.map_apply, Complex.im_sum, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, zero_add, add_zero] using h

/-- One nonsingular complex intertwiner for arbitrary real matrix families
descends to one nonsingular real intertwiner. Source: Horn–Johnson (2013),
Theorem 1.3.29; neither normality nor finiteness of the family is required.
atlas: real-similarity-descent (partial) -/
theorem exists_real_isUnit_intertwiner_of_complex {A B : ι → Matrix n n ℝ}
    {S : Matrix n n ℂ} (hS : IsUnit S)
    (hAB : ∀ i, (A i).map Complex.ofReal * S = S * (B i).map Complex.ofReal) :
    ∃ T : Matrix n n ℝ, IsUnit T ∧ ∀ i, A i * T = T * B i := by
  let C := S.map Complex.re
  let D := S.map Complex.im
  have hsplit : S = C.map Complex.ofReal + Complex.I • D.map Complex.ofReal := by
    ext i j
    simpa only [C, D, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, mul_comm] using (Complex.re_add_im (S i j)).symm
  have hCD := hsplit ▸ hS
  obtain ⟨t, ht⟩ := exists_isUnit_add_smul_of_isUnit_complex_pencil C D hCD
  refine ⟨C + t • D, ht, fun i => ?_⟩
  have hparts := real_imaginary_parts_intertwine (hAB i)
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.add_mul, Matrix.smul_mul,
    hparts.1, hparts.2]

/-- One common complex similarity between real matrix families descends
to one common real similarity. Source: Horn–Johnson (2013), Theorem 1.3.29;
the invertibility and family quantifiers are retained explicitly.
atlas: real-similarity-descent (partial) -/
theorem exists_real_similarity_of_complex_similarity {A B : ι → Matrix n n ℝ}
    {S : Matrix n n ℂ} (hS : IsUnit S)
    (hAB : ∀ i, (A i).map Complex.ofReal = S * (B i).map Complex.ofReal * S⁻¹) :
    ∃ T : Matrix n n ℝ, IsUnit T ∧ ∀ i, A i = T * B i * T⁻¹ := by
  have hinter (i : ι) : (A i).map Complex.ofReal * S = S * (B i).map Complex.ofReal := by
    rw [hAB i, Matrix.mul_assoc, Matrix.nonsing_inv_mul S (S.isUnit_iff_isUnit_det.mp hS),
      Matrix.mul_one]
  obtain ⟨T, hT, hAT⟩ := exists_real_isUnit_intertwiner_of_complex hS hinter
  refine ⟨T, hT, fun i => ?_⟩
  calc
    A i = A i * (T * T⁻¹) := by
      rw [Matrix.mul_nonsing_inv T (T.isUnit_iff_isUnit_det.mp hT), Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, hAT i]

end NLAlib
