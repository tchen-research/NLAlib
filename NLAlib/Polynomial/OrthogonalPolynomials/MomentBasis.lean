import NLAlib.Polynomial.OrthogonalPolynomials.MomentCoordinates
import NLAlib.ForMathlib.LinearAlgebra.PolynomialDegreeLT

/-! # Actual modified moments in an arbitrary fixed polynomial basis

The basis duals are constructed by canonical coefficient truncation, rather
than assumed. Their moment chart agrees with the original functional on every
polynomial in the bounded-degree space, so generic coordinate derivatives are
the derivatives with respect to the actual modified moments of that basis.
Source: Gautschi (2004), §2.1; operator derivations AQ26--AQ31.
-/

noncomputable section
open Polynomial Module Finset
namespace NLAlib
variable {𝕜 : Type*} [Field 𝕜] {d : ℕ}

/-- The actual fixed basis's coefficient functional, extended to all polynomials
by canonical degree truncation. This extension has no positivity interpretation
above the degree bound. -/
def polynomialBasisCoordinate (b : Basis (Fin d) 𝕜 (degreeLT 𝕜 d)) (i : Fin d) :
    𝕜[X] →ₗ[𝕜] 𝕜 := (b.coord i).comp (degreeLTProjection d)

/-- The extended basis coefficient equals the native basis representation
coefficient of each polynomial already below the degree bound. -/
@[simp] theorem polynomialBasisCoordinate_apply_coe
    (b : Basis (Fin d) 𝕜 (degreeLT 𝕜 d)) (i : Fin d) (p : degreeLT 𝕜 d) :
    polynomialBasisCoordinate b i (p : 𝕜[X]) = b.repr p i := by
  simp only [polynomialBasisCoordinate, LinearMap.comp_apply,
    degreeLTProjection_coe, Basis.coord_apply]

/-- The constructed coordinate of an actual bounded-degree polynomial is its
native basis representation coefficient. -/
theorem polynomialBasisCoordinate_apply_of_degree_lt
    (b : Basis (Fin d) 𝕜 (degreeLT 𝕜 d)) (i : Fin d) (p : 𝕜[X]) (hp : p.degree < d) :
    polynomialBasisCoordinate b i p = b.repr ⟨p, mem_degreeLT.mpr hp⟩ i :=
  polynomialBasisCoordinate_apply_coe b i ⟨p, mem_degreeLT.mpr hp⟩

/-- The constructed coefficient functionals are dual to the actual fixed
polynomial basis. -/
@[simp] theorem polynomialBasisCoordinate_apply_basis
    (b : Basis (Fin d) 𝕜 (degreeLT 𝕜 d)) (i j : Fin d) :
    polynomialBasisCoordinate b i (b j : 𝕜[X]) = if i = j then 1 else 0 := by
  rw [polynomialBasisCoordinate_apply_coe, b.repr_self]
  simp only [Finsupp.single_apply, eq_comm]

/-- The moment vector of a functional in the actual prescribed polynomial
basis, whose basis choice is independent of the vector. -/
def polynomialBasisMomentVector (b : Basis (Fin d) 𝕜 (degreeLT 𝕜 d))
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) : Fin d → 𝕜 := fun i => L (b i : 𝕜[X])

/-- The actual native polynomial basis's modified moment coordinates equal
the original functional on every polynomial below the degree bound, not only
on the individual basis vectors. Source: AQ26--AQ31 fixed-basis chart.
atlas: recurrence-coefficient-moment-sensitivity (partial) -/
theorem coordinateMomentFunctional_polynomialBasis_eq_of_degree_lt
    (b : Basis (Fin d) 𝕜 (degreeLT 𝕜 d)) (L : 𝕜[X] →ₗ[𝕜] 𝕜)
    {p : 𝕜[X]} (hp : p.degree < d) :
    coordinateMomentFunctional (polynomialBasisCoordinate b) (polynomialBasisMomentVector b L) p = L p := by
  let p' : degreeLT 𝕜 d := ⟨p, mem_degreeLT.mpr hp⟩
  have hcoord (i : Fin d) : polynomialBasisCoordinate b i p = b.repr p' i :=
    polynomialBasisCoordinate_apply_coe b i p'
  have hsum : (∑ i : Fin d, (b.repr p' i) • (b i : 𝕜[X])) = p := by
    have h := congrArg (fun q : degreeLT 𝕜 d => (q : 𝕜[X])) (b.sum_repr p')
    simpa only [Submodule.coe_sum, Submodule.coe_smul, p'] using h
  rw [coordinateMomentFunctional_apply]
  simp only [polynomialBasisMomentVector, hcoord]
  rw [← hsum, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- An arbitrary moment vector in the fixed basis has precisely the prescribed
actual modified moments at every basis polynomial. -/
theorem coordinateMomentFunctional_polynomialBasis_apply_basis
    (b : Basis (Fin d) 𝕜 (degreeLT 𝕜 d)) (m : Fin d → 𝕜) (j : Fin d) :
    coordinateMomentFunctional (polynomialBasisCoordinate b) m (b j : 𝕜[X]) = m j :=
  coordinateMomentFunctional_apply_dual _ _ _ (polynomialBasisCoordinate_apply_basis b) j

/-- A fixed arbitrary polynomial basis chart gives exactly the original
canonical order-`n` polynomial whenever the coordinate degree is at least
`2n`. Thus no extra moment beyond the declared chart enters the construction.
Source: AQ22 and AQ31.
atlas: recurrence-coefficient-moment-sensitivity (partial) -/
theorem monicOrthogonalPolynomial_coordinate_polynomialBasis_eq
    (b : Basis (Fin d) 𝕜 (degreeLT 𝕜 d)) (L : 𝕜[X] →ₗ[𝕜] 𝕜) {n : ℕ} (hd : 2*n ≤ d) :
    monicOrthogonalPolynomial
      (coordinateMomentFunctional (polynomialBasisCoordinate b) (polynomialBasisMomentVector b L)) n =
      monicOrthogonalPolynomial L n := by
  apply monicOrthogonalPolynomial_eq_of_moments_eq
  intro k hk
  apply coordinateMomentFunctional_polynomialBasis_eq_of_degree_lt
  rw [degree_X_pow]
  exact_mod_cast hk.trans_le hd

end NLAlib
