import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.Polynomial.DegreeLT

/-! # The canonical projection to bounded-degree polynomials

Truncating the monomial coefficients gives a total linear projection to the
degree-bounded polynomial submodule. Composing any fixed basis's coordinates
with this projection extends its duals canonically to all polynomials.
-/

noncomputable section
open Polynomial Finset
namespace Polynomial
variable {𝕜 : Type*} [Field 𝕜]

/-- The finite monomial coefficient truncation below degree `d`. -/
def degreeTruncation (d : ℕ) : 𝕜[X] →ₗ[𝕜] 𝕜[X] :=
  ∑ i : Fin d, (lcoeff 𝕜 i.val).smulRight (X^i.val)

/-- Degree truncation is its actual finite monomial coefficient sum. -/
@[simp] theorem degreeTruncation_apply (d : ℕ) (p : 𝕜[X]) :
    degreeTruncation d p = ∑ i : Fin d, C (p.coeff i.val)*X^i.val := by
  simp only [degreeTruncation, LinearMap.sum_apply, LinearMap.smulRight_apply,
    lcoeff_apply, smul_eq_C_mul]

/-- The canonical coefficient truncation as a map into the bounded-degree
polynomial submodule, including its zero-dimensional case. -/
def degreeLTProjection (d : ℕ) : 𝕜[X] →ₗ[𝕜] degreeLT 𝕜 d :=
  (degreeTruncation d).codRestrict (degreeLT 𝕜 d) (by
    intro p
    rw [mem_degreeLT, degreeTruncation_apply]
    exact degree_sum_fin_lt _)

/-- On a polynomial already below the degree bound, projection is the identity. -/
@[simp] theorem degreeLTProjection_coe {d : ℕ} (p : degreeLT 𝕜 d) :
    degreeLTProjection d (p : 𝕜[X]) = p := by
  apply Subtype.ext
  change degreeTruncation d (p : 𝕜[X]) = _
  rw [degreeTruncation_apply]
  have hp : (p : 𝕜[X]).degree < d := mem_degreeLT.mp p.property
  by_cases hp0 : (p : 𝕜[X]) = 0
  · simp [hp0]
  simp only [C_mul_X_pow_eq_monomial]
  exact (Fin.sum_univ_eq_sum_range
    (fun i : ℕ => monomial i ((p : 𝕜[X]).coeff i)) d).trans
      (((p : 𝕜[X]).as_sum_range' d ((natDegree_lt_iff_degree_lt hp0).mpr hp)).symm)

end Polynomial
