import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic

/-!
# Analytic coefficients of affine characteristic polynomials

Every coefficient of the characteristic polynomial of an affine matrix pencil
is polynomial, hence analytic, in its parameter. The construction works in
dimension zero and imposes no simplicity or normality hypothesis.
-/

noncomputable section

open Polynomial
open scoped Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Each characteristic coefficient of an affine pencil is the evaluation of
one fixed polynomial in the pencil parameter. -/
theorem exists_polynomial_charpoly_coeff_affine
    (A E : Matrix n n ℂ) (k : ℕ) :
    ∃ p : ℂ[X], ∀ t : ℂ, p.eval t = (A + t • E).charpoly.coeff k := by
  let M : Matrix n n ℂ[X] := A.map C + (X : ℂ[X]) • E.map C
  refine ⟨M.charpoly.coeff k, fun t => ?_⟩
  have hmap : M.charpoly.map (evalRingHom t) = (A + t • E).charpoly := by
    rw [← Matrix.charpoly_map]
    congr 1
    ext i j
    simp [M, Matrix.map_apply]
    ring
  simpa only [coeff_map, coe_evalRingHom] using congrArg (fun p => p.coeff k) hmap

/-- Characteristic coefficients of an affine complex matrix pencil are
analytic even at multiple roots. -/
theorem analyticAt_charpoly_coeff_affine
    (A E : Matrix n n ℂ) (k : ℕ) (t : ℂ) :
    AnalyticAt ℂ (fun u : ℂ => (A + u • E).charpoly.coeff k) t := by
  obtain ⟨p, hp⟩ := exists_polynomial_charpoly_coeff_affine A E k
  simpa [hp, Polynomial.aeval_def] using
    (analyticAt_id (𝕜 := ℂ) (z := t)).aeval_polynomial p

end Matrix
