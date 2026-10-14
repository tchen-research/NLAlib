import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.RingTheory.AdjoinRoot

/-!
# Frobenius companion matrices

The columns are the shift columns followed by the negatives of the polynomial
coefficients. Mathlib's quotient power basis identifies this concrete matrix
with multiplication by the residue class of `X`, giving both characteristic
and minimal polynomials. Source: Horn–Johnson (2013), Theorem 3.2.4.2;
operator derivations, Section 6. Atlas: `companion-matrix`.
-/

noncomputable section
open Polynomial
open scoped Matrix
namespace NLAlib

/-- The Frobenius companion matrix of a polynomial: shift columns and the final
column of negated coefficients. The size is its natural degree; a constant
polynomial gives the empty matrix. The companion theorems require monicity.
Source: Horn–Johnson (2013), Definition 3.2.4.1; operator derivations, (S2).
atlas: companion-matrix (partial) -/
def companionMatrix {K : Type*} [Ring K] (p : K[X]) :
    Matrix (Fin p.natDegree) (Fin p.natDegree) K :=
  fun i j => if j.val + 1 = p.natDegree then -p.coeff i.val
    else if i.val = j.val + 1 then 1 else 0

variable {K : Type*} [Field K] {p : K[X]}

/-- A monic polynomial is the minimal polynomial of the quotient's distinguished root.
This also applies to the zero-dimensional quotient for `p=1`. -/
private theorem minpoly_adjoinRoot_eq (hp : p.Monic) :
    minpoly K (AdjoinRoot.root p) = p := by
  rw [AdjoinRoot.minpoly_root hp.ne_zero, hp.leadingCoeff, inv_one, C_1, mul_one]

/-- The concrete companion matrix represents multiplication by `X` in the quotient's
power basis. Source: operator derivations, (S2). -/
theorem leftMulMatrix_adjoinRoot_eq_companionMatrix (hp : p.Monic) :
    Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hp).basis (AdjoinRoot.root p) =
      companionMatrix p := by
  have h := (AdjoinRoot.powerBasis' hp).leftMulMatrix
  apply Matrix.ext
  intro i j
  have hij := congrArg (fun M => M i j) h
  simpa only [PowerBasis.minpolyGen_eq, AdjoinRoot.powerBasis'_gen,
    minpoly_adjoinRoot_eq hp, AdjoinRoot.powerBasis'_dim, Matrix.of_apply,
    companionMatrix] using hij

/-- A monic polynomial is exactly the characteristic polynomial of its companion matrix,
including the constant monic polynomial one and the empty companion matrix.
Source: Horn–Johnson (2013), Theorem 3.2.4.2.
atlas: companion-matrix (partial) -/
theorem charpoly_companionMatrix (hp : p.Monic) :
    (companionMatrix p).charpoly = p := by
  rw [← leftMulMatrix_adjoinRoot_eq_companionMatrix hp]
  exact (charpoly_leftMulMatrix (AdjoinRoot.powerBasis' hp)).trans (minpoly_adjoinRoot_eq hp)

/-- A monic polynomial is exactly the minimal polynomial of its companion matrix,
with no nonzero degree assumption. Source: Horn–Johnson (2013), Theorem 3.2.4.2.
atlas: companion-matrix (partial) -/
theorem minpoly_companionMatrix (hp : p.Monic) :
    minpoly K (companionMatrix p) = p := by
  rw [← leftMulMatrix_adjoinRoot_eq_companionMatrix hp]
  exact (minpoly.algHom_eq (Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hp).basis)
    (Algebra.leftMulMatrix_injective _) (AdjoinRoot.root p)).trans (minpoly_adjoinRoot_eq hp)

end NLAlib
