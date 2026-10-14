import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic.ComputeDegree

/-! # Finite Hermite interpolation with double nodes

The explicit cardinal formula matches a value and first derivative at every distinct
node. It is the algebraic interpolant (AQ3) used by the derivative remainder of Gauss
quadrature, and is independent of probability measures or matrix representations.
-/

noncomputable section
open Polynomial Finset Set

namespace Lagrange

variable {ι : Type*} [DecidableEq ι]

/-- The cardinal polynomial for a function value in double-node Hermite interpolation:
`(1−2ℓᵢ′(vᵢ)(X−vᵢ))ℓᵢ²`. Source: finite Hermite formula (AQ3). -/
def hermiteValueBasis (s : Finset ι) (v : ι → ℝ) (i : ι) : ℝ[X] :=
  (1 - C (2 * (Lagrange.basis s v i).derivative.eval (v i)) * (X - C (v i))) *
    Lagrange.basis s v i ^ 2

/-- The cardinal polynomial for a first derivative in double-node Hermite interpolation:
`(X−vᵢ)ℓᵢ²`. Source: finite Hermite formula (AQ3). -/
def hermiteDerivativeBasis (s : Finset ι) (v : ι → ℝ) (i : ι) : ℝ[X] :=
  (X - C (v i)) * Lagrange.basis s v i ^ 2

/-- The explicit finite Hermite interpolant matching values `yᵢ` and derivatives `dᵢ`
at the distinct nodes `vᵢ`. It is zero for an empty interpolation set.
Source: operator derivations, (AQ3). -/
def hermiteInterpolate (s : Finset ι) (v y d : ι → ℝ) : ℝ[X] :=
  ∑ i ∈ s, (C (y i) * hermiteValueBasis s v i + C (d i) * hermiteDerivativeBasis s v i)

/-- Every term in the finite Hermite formula has degree at most twice the number of
nodes minus one. Source: operator derivations, (AQ3). -/
theorem natDegree_hermite_term_le {s : Finset ι} {v : ι → ℝ} (hv : InjOn v s)
    (y d : ι → ℝ) {i : ι} (hi : i ∈ s) :
    (C (y i) * hermiteValueBasis s v i + C (d i) * hermiteDerivativeBasis s v i).natDegree ≤
      2 * s.card - 1 := by
  have hs : 0 < s.card := card_pos.mpr ⟨i, hi⟩
  have hb := natDegree_basis hv hi
  have hv₁ : (1 - C (2 * (Lagrange.basis s v i).derivative.eval (v i)) *
      (X - C (v i)) : ℝ[X]).natDegree ≤ 1 := by compute_degree
  have hv₂ : (X - C (v i) : ℝ[X]).natDegree ≤ 1 := by compute_degree
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply (natDegree_C_mul_le _ _).trans
    apply (natDegree_mul_le.trans (Nat.add_le_add_right hv₁ _)).trans
    rw [natDegree_pow, hb]
    omega
  · apply (natDegree_C_mul_le _ _).trans
    apply (natDegree_mul_le.trans (Nat.add_le_add_right hv₂ _)).trans
    rw [natDegree_pow, hb]
    omega

/-- A finite Hermite interpolant on a nonempty distinct-node family has degree strictly
below twice the number of nodes. Source: operator derivations, (AQ3). -/
theorem degree_hermiteInterpolate_lt {s : Finset ι} (hs : s.Nonempty) {v : ι → ℝ}
    (hv : InjOn v s) (y d : ι → ℝ) :
    (hermiteInterpolate s v y d).degree < (2 * s.card : ℕ) := by
  unfold hermiteInterpolate
  apply (degree_sum_le _ _).trans_lt
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro i hi
  apply (degree_le_natDegree).trans_lt
  exact_mod_cast (lt_of_le_of_lt (natDegree_hermite_term_le hv y d hi)
    (by have := hs.card_pos; omega : 2 * s.card - 1 < 2 * s.card))

/-- A Hermite value cardinal polynomial is one at its own node and zero at the others. -/
theorem eval_hermiteValueBasis {s : Finset ι} {v : ι → ℝ} (hv : InjOn v s)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    (hermiteValueBasis s v i).eval (v j) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [hermiteValueBasis, eval_basis_self hv hi]
  · simp [hermiteValueBasis, hij, eval_basis_of_ne hij hj]

/-- A Hermite derivative cardinal polynomial vanishes at every node. -/
theorem eval_hermiteDerivativeBasis {s : Finset ι} {v : ι → ℝ} (hv : InjOn v s)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    (hermiteDerivativeBasis s v i).eval (v j) = 0 := by
  by_cases hij : i = j
  · subst j
    simp [hermiteDerivativeBasis, eval_basis_self hv hi]
  · simp [hermiteDerivativeBasis, eval_basis_of_ne hij hj]

/-- The derivative of a Hermite value cardinal polynomial vanishes at every node. -/
theorem eval_derivative_hermiteValueBasis {s : Finset ι} {v : ι → ℝ} (hv : InjOn v s)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    (hermiteValueBasis s v i).derivative.eval (v j) = 0 := by
  by_cases hij : i = j
  · subst j
    simp [hermiteValueBasis, derivative_mul, derivative_sub, derivative_pow,
      eval_basis_self hv hi]
  · simp [hermiteValueBasis, derivative_mul, derivative_sub, derivative_pow,
      eval_basis_of_ne hij hj]

/-- A Hermite derivative cardinal polynomial has derivative one at its own node and
zero at every other node. -/
theorem eval_derivative_hermiteDerivativeBasis {s : Finset ι} {v : ι → ℝ} (hv : InjOn v s)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    (hermiteDerivativeBasis s v i).derivative.eval (v j) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [hermiteDerivativeBasis, derivative_mul, derivative_sub, derivative_pow,
      eval_basis_self hv hi]
  · simp [hermiteDerivativeBasis, derivative_mul, derivative_sub, derivative_pow,
      hij, eval_basis_of_ne hij hj]

/-- The explicit finite Hermite interpolant matches all specified function values. -/
theorem eval_hermiteInterpolate_at_node {s : Finset ι} {v : ι → ℝ} (hv : InjOn v s)
    (y d : ι → ℝ) {j : ι} (hj : j ∈ s) :
    (hermiteInterpolate s v y d).eval (v j) = y j := by
  simp only [hermiteInterpolate, eval_finsetSum, eval_add, eval_mul, eval_C]
  rw [sum_eq_single j]
  · rw [eval_hermiteValueBasis hv hj hj, eval_hermiteDerivativeBasis hv hj hj]
    simp
  · intro i hi hij
    rw [eval_hermiteValueBasis hv hi hj, eval_hermiteDerivativeBasis hv hi hj, if_neg hij]
    simp
  · exact fun h => (h hj).elim

/-- The explicit finite Hermite interpolant matches all specified first derivatives. -/
theorem eval_derivative_hermiteInterpolate_at_node {s : Finset ι} {v : ι → ℝ}
    (hv : InjOn v s) (y d : ι → ℝ) {j : ι} (hj : j ∈ s) :
    (hermiteInterpolate s v y d).derivative.eval (v j) = d j := by
  simp only [hermiteInterpolate, derivative_sum, derivative_add, derivative_C_mul,
    eval_finsetSum, eval_add, eval_mul, eval_C]
  rw [sum_eq_single j]
  · rw [eval_derivative_hermiteValueBasis hv hj hj,
      eval_derivative_hermiteDerivativeBasis hv hj hj]
    simp
  · intro i hi hij
    rw [eval_derivative_hermiteValueBasis hv hi hj,
      eval_derivative_hermiteDerivativeBasis hv hi hj, if_neg hij]
    simp
  · exact fun h => (h hj).elim

end Lagrange
