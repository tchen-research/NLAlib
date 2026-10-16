import NLAlib.Matrix.Functions.PolynomialLoewnerDerivative
import Mathlib.LinearAlgebra.Matrix.Hadamard

/-!
# The divided-difference derivative operator

The Hadamard formula is packaged as an actual real continuous linear map.
Polynomial differentiation and algebraic transport establish it in any
chosen unitary eigenbasis. Tropp (2022), Theorem 14.13.
-/

noncomputable section
open Matrix Polynomial
open scoped Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real linear divided-difference operator in a supplied unitary
eigenbasis. It is defined on the ambient matrix space; its derivative
meaning is along the real subspace of Hermitian matrices. -/
def loewnerDerivative (f : ℝ → ℝ) (ev : n → ℝ) (U : unitary (Matrix n n ℂ)) :
    Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun H := (U : Matrix n n ℂ) *
        ((loewnerMatrix f ev).map Complex.ofReal ⊙
          ((U : Matrix n n ℂ).conjTranspose * H * U)) * (U : Matrix n n ℂ).conjTranspose
      map_add' H K := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.hadamard_add]
      map_smul' c H := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.hadamard_smul, RingHom.id_apply] }

/-- Evaluation of the real linear Hadamard derivative operator. -/
theorem loewnerDerivative_apply (f : ℝ → ℝ) (ev : n → ℝ)
    (U : unitary (Matrix n n ℂ)) (H : Matrix n n ℂ) :
    loewnerDerivative f ev U H = (U : Matrix n n ℂ) *
      ((loewnerMatrix f ev).map Complex.ofReal ⊙
        ((U : Matrix n n ℂ).conjTranspose * H * U)) * (U : Matrix n n ℂ).conjTranspose := rfl

/-- Polynomial derivatives equal their divided-difference operators in
every unitary eigenbasis, including repeated nodes. -/
theorem frechetDerivative_eq_loewnerDerivative (p : ℝ[X]) (ev : n → ℝ)
    (U : unitary (Matrix n n ℂ)) {A : Matrix n n ℂ}
    (hA : A = (U : Matrix n n ℂ) * diagonal (fun i => (ev i : ℂ)) *
      (U : Matrix n n ℂ).conjTranspose) : p.frechetDerivative A = loewnerDerivative p.eval ev U := by
  let E := Unitary.conjStarAlgAut ℝ (Matrix n n ℂ) U
  have hU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ).conjTranspose = 1 :=
    Unitary.coe_mul_star_self U
  apply ContinuousLinearMap.ext
  intro H
  let K := (U : Matrix n n ℂ).conjTranspose * H * U
  have hK : E K = H := by
    change (U : Matrix n n ℂ) * ((U : Matrix n n ℂ).conjTranspose * H * U) *
      (U : Matrix n n ℂ).conjTranspose = H
    calc
      _ = ((U : Matrix n n ℂ) * (U : Matrix n n ℂ).conjTranspose) * H *
        ((U : Matrix n n ℂ) * (U : Matrix n n ℂ).conjTranspose) := by noncomm_ring
      _ = H := by rw [hU, Matrix.one_mul, Matrix.mul_one]
  have hEA : E (diagonal (fun i => (ev i : ℂ))) = A := hA.symm
  calc
    _ = E (p.frechetDerivative (diagonal (fun i => (ev i : ℂ))) K) := by
      have hm : E (p.frechetDerivative (diagonal (fun i => (ev i : ℂ))) K) =
          p.frechetDerivative (E (diagonal (fun i => (ev i : ℂ)))) (E K) :=
        Polynomial.map_frechetDerivative_apply E.toAlgEquiv.toAlgHom p _ K
      rw [hEA, hK] at hm
      exact hm.symm
    _ = E (Matrix.of (fun i j =>
        (((p.dividedDifference (ev i)).eval (ev j) : ℝ) : ℂ) * K i j)) := by
      rw [frechetDerivative_diagonal_apply]
    _ = _ := by
      rw [loewnerDerivative_apply]
      change (U : Matrix n n ℂ) * _ * (U : Matrix n n ℂ).conjTranspose = _
      congr 2
      ext i j
      simp only [Matrix.of_apply, Matrix.hadamard_apply, Matrix.map_apply, loewnerMatrix,
        dslope_polynomial_eq_eval_dividedDifference]
      rfl

/-- Matching scalar values and derivatives at the nodes gives the same
divided-difference operator, including confluent entries. -/
theorem loewnerDerivative_eq_of_values_deriv (p : ℝ[X]) (f : ℝ → ℝ) (ev : n → ℝ)
    (U : unitary (Matrix n n ℂ)) (hv : ∀ i, p.eval (ev i) = f (ev i))
    (hd : ∀ i, p.derivative.eval (ev i) = deriv f (ev i)) :
    loewnerDerivative p.eval ev U = loewnerDerivative f ev U := by
  have heq : loewnerMatrix p.eval ev = loewnerMatrix f ev := by
    ext i j
    change dslope p.eval (ev i) (ev j) = dslope f (ev i) (ev j)
    by_cases hij : ev i = ev j
    · rw [hij, dslope_same, dslope_same, (p.hasDerivAt (ev j)).deriv, hd]
    · rw [dslope_of_ne _ (Ne.symm hij), dslope_of_ne _ (Ne.symm hij)]
      simp only [slope, vsub_eq_sub, hv]
  ext H
  simp only [loewnerDerivative_apply, heq]

end NLAlib
