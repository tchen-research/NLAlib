import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.AdjoinRoot

/-! # Colleague matrices as Chebyshev coordinates of quotient multiplication

Multiplication by the residue class of `X` on `ℝ[X]/(p)` has characteristic
polynomial equal to the monic normalization of `p`, including repeated roots.
-/

noncomputable section
open Polynomial Polynomial.Chebyshev Module Algebra
open scoped Matrix
namespace NLAlib

private theorem linearIndependent_aeval_T_adjoinRoot {p : ℝ[X]} (hp : p ≠ 0) :
    LinearIndependent ℝ (fun i : Fin p.natDegree => aeval (AdjoinRoot.root p) (T ℝ i)) := by
  apply linearIndependent_iff'.mpr
  intro s c hzero i hi
  let P : ℝ[X] := ∑ j ∈ s, c j • T ℝ (j : ℤ)
  have hPdeg : P.degree < p.natDegree := by
    apply mem_degreeLT.mp
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    apply mem_degreeLT.mpr
    rw [degree_T, Int.natAbs_natCast]
    exact_mod_cast j.isLt
  have hPeval : aeval (AdjoinRoot.root p) P = 0 := by
    simpa only [P, map_sum, map_smul] using hzero
  have hPzero : P = 0 := by
    by_contra hP
    have hmin := minpoly.degree_le_of_ne_zero ℝ (AdjoinRoot.root p) hP hPeval
    rw [AdjoinRoot.minpoly_root hp, degree_mul, degree_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hp)),
      add_zero, degree_eq_natDegree hp] at hmin
    exact (not_le_of_gt hPdeg) hmin
  have hlin : LinearIndependent ℝ (fun j : Fin p.natDegree => T ℝ (j : ℤ)) :=
    (chebyshevTsequence ℝ).linearIndependent.comp Fin.val Fin.val_injective
  exact linearIndependent_iff'.mp hlin s c hPzero i hi

/-- The first `deg p` Chebyshev polynomials form a basis of the quotient by any
nonzero real polynomial `p`. Source: triangular Chebyshev change of basis and
polynomial division; the finite-basis ingredient of ATAP Theorem 18.1. -/
def chebyshevQuotientBasis (p : ℝ[X]) (hp : p ≠ 0) :
    Basis (Fin p.natDegree) ℝ (AdjoinRoot p) := by
  letI : Module.Finite ℝ (AdjoinRoot p) := Module.Finite.of_basis (AdjoinRoot.powerBasis hp).basis
  exact basisOfLinearIndependentOfCardEqFinrank'
    (fun i : Fin p.natDegree => aeval (AdjoinRoot.root p) (T ℝ i))
    (linearIndependent_aeval_T_adjoinRoot hp)
    (by rw [Fintype.card_fin, (AdjoinRoot.powerBasis hp).finrank]; rfl)

/-- Each quotient Chebyshev basis vector is the residue of its Chebyshev polynomial.
Source: the basis construction for ATAP Theorem 18.1. -/
@[simp] theorem chebyshevQuotientBasis_apply (p : ℝ[X]) (hp : p ≠ 0) (i : Fin p.natDegree) :
    chebyshevQuotientBasis p hp i = aeval (AdjoinRoot.root p) (T ℝ i) := by
  simp [chebyshevQuotientBasis]

/-- The colleague matrix is the evaluation-recurrence transpose of multiplication
by `X` modulo `p`, in the first-kind Chebyshev basis. Source: Trefethen, ATAP,
Theorem 18.1. A nonzero constant polynomial has the empty colleague matrix. -/
def colleagueMatrix (p : ℝ[X]) (hp : p ≠ 0) : Matrix (Fin p.natDegree) (Fin p.natDegree) ℝ :=
  (leftMulMatrix (chebyshevQuotientBasis p hp) (AdjoinRoot.root p))ᵀ

/-- The characteristic polynomial of the colleague matrix is the monic normalization
of its polynomial, with root multiplicities preserved. Source: Trefethen, ATAP,
Theorem 18.1; proved by quotient multiplication and basis invariance.
atlas: colleague-matrix (partial) -/
theorem charpoly_colleagueMatrix (p : ℝ[X]) (hp : p ≠ 0) :
    (colleagueMatrix p hp).charpoly = p * C p.leadingCoeff⁻¹ := by
  let : Module.Finite ℝ (AdjoinRoot p) := Module.Finite.of_basis (AdjoinRoot.powerBasis hp).basis
  let : Module.Free ℝ (AdjoinRoot p) := Module.Free.of_basis (AdjoinRoot.powerBasis hp).basis
  rw [colleagueMatrix, Matrix.charpoly_transpose, leftMulMatrix_apply,
    LinearMap.charpoly_toMatrix]
  have h := charpoly_leftMulMatrix (AdjoinRoot.powerBasis hp)
  rw [leftMulMatrix_apply, LinearMap.charpoly_toMatrix,
    AdjoinRoot.minpoly_powerBasis_gen hp] at h
  exact h

/-- Entries of the evaluation-recurrence colleague matrix are Chebyshev coordinates
of multiplication by the residue of `X`. Source: ATAP Theorem 18.1. -/
theorem colleagueMatrix_apply (p : ℝ[X]) (hp : p ≠ 0) (j k : Fin p.natDegree) :
    colleagueMatrix p hp j k = (chebyshevQuotientBasis p hp).repr
      (AdjoinRoot.root p * chebyshevQuotientBasis p hp j) k := by
  rw [colleagueMatrix, Matrix.transpose_apply, leftMulMatrix_eq_repr_mul]

/-- In degrees at least two, the first colleague row has its single entry `1`
in column one. Source: ATAP (18.1); the special first-kind Chebyshev recurrence. -/
theorem colleagueMatrix_zero_row (p : ℝ[X]) (hp : p ≠ 0) (hn : 2 ≤ p.natDegree)
    (k : Fin p.natDegree) : colleagueMatrix p hp ⟨0, by omega⟩ k =
      if k.val = 1 then 1 else 0 := by
  rw [colleagueMatrix_apply, chebyshevQuotientBasis_apply]
  simp only [Nat.cast_zero, T_zero, map_one, mul_one]
  have hroot : AdjoinRoot.root p = chebyshevQuotientBasis p hp ⟨1, by omega⟩ := by
    rw [chebyshevQuotientBasis_apply]
    simp
  rw [hroot, Basis.repr_self]
  simp only [Finsupp.single_apply, Fin.ext_iff, eq_comm]

/-- Every interior colleague row has one-half in its two neighboring columns.
Source: Trefethen, ATAP (18.1), from the first-kind Chebyshev recurrence. -/
theorem colleagueMatrix_interior_row (p : ℝ[X]) (hp : p ≠ 0)
    (j k : Fin p.natDegree) (hj0 : 0 < j.val) (hjn : j.val + 1 < p.natDegree) :
    colleagueMatrix p hp j k = (1 / 2 : ℝ) *
      ((if j.val - 1 = k.val then 1 else 0) + (if j.val + 1 = k.val then 1 else 0)) := by
  let prev : Fin p.natDegree := ⟨j.val - 1, by omega⟩
  let next : Fin p.natDegree := ⟨j.val + 1, hjn⟩
  have hbprev : chebyshevQuotientBasis p hp prev =
      aeval (AdjoinRoot.root p) (T ℝ ((j.val : ℤ) - 1)) := by
    rw [chebyshevQuotientBasis_apply]
    congr 2
    exact_mod_cast (Nat.cast_sub (show 1 ≤ j.val by omega) :
      ((j.val - 1 : ℕ) : ℤ) = j.val - 1)
  have hbnext : chebyshevQuotientBasis p hp next =
      aeval (AdjoinRoot.root p) (T ℝ ((j.val : ℤ) + 1)) := by
    rw [chebyshevQuotientBasis_apply]
    congr 1
  have hrec : (2 : ℝ[X]) * X * T ℝ (j.val : ℤ) =
      T ℝ ((j.val : ℤ) - 1) + T ℝ ((j.val : ℤ) + 1) := by
    have h := T_add_two ℝ ((j.val : ℤ) - 1)
    rw [sub_add_cancel, show (j.val : ℤ) - 1 + 2 = j.val + 1 by omega] at h
    linear_combination -h
  have h2 : (2 : ℝ) • (AdjoinRoot.root p * chebyshevQuotientBasis p hp j) =
      chebyshevQuotientBasis p hp prev + chebyshevQuotientBasis p hp next := by
    rw [hbprev, hbnext, chebyshevQuotientBasis_apply]
    simpa only [map_mul, map_add, aeval_X, map_ofNat, Algebra.smul_def, mul_assoc] using
      congrArg (aeval (AdjoinRoot.root p)) hrec
  have hmul := congrArg (fun y => (1 / 2 : ℝ) • y) h2
  simp only [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at hmul
  rw [colleagueMatrix_apply, hmul, map_smul, map_add, Basis.repr_self, Basis.repr_self]
  simp only [Finsupp.smul_apply, Finsupp.add_apply, Finsupp.single_apply, Fin.ext_iff,
    smul_eq_mul, prev, next]

/-- The leading coefficient of a finite degree-indexed Chebyshev expansion is its
last coefficient times `2^(n−1)`. Source: ATAP Theorem 18.1. -/
theorem leadingCoeff_eq_pow_mul_of_chebyshev_expansion (p : ℝ[X]) (a : ℕ → ℝ)
    (ha : p = ∑ j ∈ Finset.range (p.natDegree + 1), a j • T ℝ (j : ℤ)) :
    p.leadingCoeff = 2 ^ (p.natDegree - 1) * a p.natDegree := by
  have hc := congrArg (fun P : ℝ[X] => P.coeff p.natDegree) ha
  change p.coeff p.natDegree = _
  rw [hc, finsetSum_coeff, Finset.sum_eq_single p.natDegree]
  · rw [coeff_smul]
    have hT : (T ℝ (p.natDegree : ℤ)).coeff p.natDegree = 2 ^ (p.natDegree - 1) := by
      have hnd : (T ℝ (p.natDegree : ℤ)).natDegree = p.natDegree := by
        simp only [natDegree_T, Int.natAbs_natCast]
      calc
        _ = (T ℝ (p.natDegree : ℤ)).coeff (T ℝ (p.natDegree : ℤ)).natDegree := by rw [hnd]
        _ = (T ℝ (p.natDegree : ℤ)).leadingCoeff := coeff_natDegree
        _ = _ := by rw [leadingCoeff_T, Int.natAbs_natCast]
    rw [hT, smul_eq_mul, mul_comm]
  · intro j hj hjn
    rw [coeff_smul, coeff_eq_zero_of_degree_lt, smul_zero]
    rw [degree_T, Int.natAbs_natCast]
    exact_mod_cast (show j < p.natDegree by have h := Finset.mem_range.mp hj; omega)
  · simp

private theorem repr_aeval_T_natDegree (p : ℝ[X]) (hp : p ≠ 0) (a : ℕ → ℝ)
    (ha : p = ∑ j ∈ Finset.range (p.natDegree + 1), a j • T ℝ (j : ℤ))
    (han : a p.natDegree ≠ 0) (k : Fin p.natDegree) :
    (chebyshevQuotientBasis p hp).repr (aeval (AdjoinRoot.root p) (T ℝ p.natDegree)) k =
      -a k.val / a p.natDegree := by
  have hpzero : aeval (AdjoinRoot.root p) p = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hzero := (congrArg (aeval (AdjoinRoot.root p)) ha).symm.trans hpzero
  rw [Finset.sum_range_succ, map_add, map_sum, map_smul] at hzero
  have hsum : (∑ j ∈ Finset.range p.natDegree,
      aeval (AdjoinRoot.root p) (a j • T ℝ (j : ℤ))) =
      ∑ j : Fin p.natDegree, a j.val • chebyshevQuotientBasis p hp j := by
    symm
    simpa only [chebyshevQuotientBasis_apply, map_smul] using
      Fin.sum_univ_eq_sum_range
        (fun j => aeval (AdjoinRoot.root p) (a j • T ℝ (j : ℤ))) p.natDegree
  rw [hsum] at hzero
  have hcoord := congrArg (fun y => (chebyshevQuotientBasis p hp).repr y k) hzero
  simp only [map_add, map_sum, map_smul, map_zero, Finsupp.add_apply, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, Basis.repr_self, Finsupp.single_apply, Finsupp.zero_apply, smul_eq_mul] at hcoord
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hcoord
  apply (eq_div_iff han).mpr
  linear_combination hcoord

/-- In degree at least two, the last colleague row is the half-scaled penultimate
basis coordinate minus `a_k/(2a_n)`. Source: Trefethen, ATAP (18.1).
atlas: colleague-matrix (partial) -/
theorem colleagueMatrix_last_row (p : ℝ[X]) (hp : p ≠ 0) (a : ℕ → ℝ)
    (ha : p = ∑ j ∈ Finset.range (p.natDegree + 1), a j • T ℝ (j : ℤ))
    (han : a p.natDegree ≠ 0) (hn : 2 ≤ p.natDegree) (k : Fin p.natDegree) :
    colleagueMatrix p hp ⟨p.natDegree - 1, by omega⟩ k =
      (if p.natDegree - 2 = k.val then (1 / 2 : ℝ) else 0) - a k.val / (2 * a p.natDegree) := by
  let last : Fin p.natDegree := ⟨p.natDegree - 1, by omega⟩
  let prev : Fin p.natDegree := ⟨p.natDegree - 2, by omega⟩
  have hrec : (2 : ℝ[X]) * X * T ℝ ((p.natDegree - 1 : ℕ) : ℤ) =
      T ℝ ((p.natDegree - 2 : ℕ) : ℤ) + T ℝ p.natDegree := by
    have h := T_add_two ℝ ((p.natDegree - 2 : ℕ) : ℤ)
    rw [show ((p.natDegree - 2 : ℕ) : ℤ) + 2 = p.natDegree by omega,
      show ((p.natDegree - 2 : ℕ) : ℤ) + 1 = ((p.natDegree - 1 : ℕ) : ℤ) by omega] at h
    linear_combination -h
  have h2 : (2 : ℝ) • (AdjoinRoot.root p * chebyshevQuotientBasis p hp last) =
      chebyshevQuotientBasis p hp prev + aeval (AdjoinRoot.root p) (T ℝ p.natDegree) := by
    rw [chebyshevQuotientBasis_apply, chebyshevQuotientBasis_apply]
    simpa only [map_mul, map_add, aeval_X, map_ofNat, Algebra.smul_def, mul_assoc] using
      congrArg (aeval (AdjoinRoot.root p)) hrec
  have hmul := congrArg (fun y => (1 / 2 : ℝ) • y) h2
  simp only [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at hmul
  change colleagueMatrix p hp last k = _
  rw [colleagueMatrix_apply, hmul, map_smul, map_add, Basis.repr_self]
  simp only [Finsupp.smul_apply, Finsupp.add_apply, Finsupp.single_apply, Fin.ext_iff,
    smul_eq_mul, prev]
  rw [repr_aeval_T_natDegree p hp a ha han k]
  split_ifs <;> ring

/-- For a degree-one polynomial `a₀+a₁X`, the colleague matrix is the single entry
`−a₀/a₁`. Source: Trefethen, ATAP, Theorem 18.1. This degree-one branch is distinct
from the half-scaled last-row recurrence, which requires degree at least two.
atlas: colleague-matrix -/
theorem colleagueMatrix_degree_one (p : ℝ[X]) (hp : p ≠ 0) (a : ℕ → ℝ)
    (ha : p = ∑ j ∈ Finset.range (p.natDegree + 1), a j • T ℝ (j : ℤ))
    (han : a p.natDegree ≠ 0) (hn : p.natDegree = 1) (j k : Fin p.natDegree) :
    colleagueMatrix p hp j k = -a 0 / a 1 := by
  have hj : j.val = 0 := by have h := j.isLt; omega
  have hk : k.val = 0 := by have h := k.isLt; omega
  rw [colleagueMatrix_apply, chebyshevQuotientBasis_apply]
  simp only [hj, Nat.cast_zero, T_zero, map_one, mul_one]
  have hroot : AdjoinRoot.root p = aeval (AdjoinRoot.root p) (T ℝ p.natDegree) := by
    rw [hn]
    simp
  rw [hroot, repr_aeval_T_natDegree p hp a ha han k, hk, hn]

/-- The characteristic polynomial of a colleague matrix for a Chebyshev expansion
is `p/(2^(n−1)a_n)`. Source: Trefethen, ATAP, Theorem 18.1. This identity preserves
multiplicities; the explicit recurrence rows are supplied by the adjacent lemmas.
atlas: colleague-matrix -/
theorem charpoly_colleagueMatrix_of_chebyshev_expansion (p : ℝ[X]) (hp : p ≠ 0) (a : ℕ → ℝ)
    (ha : p = ∑ j ∈ Finset.range (p.natDegree + 1), a j • T ℝ (j : ℤ)) :
    (colleagueMatrix p hp).charpoly = C (1 / (2 ^ (p.natDegree - 1) * a p.natDegree)) * p := by
  rw [charpoly_colleagueMatrix, leadingCoeff_eq_pow_mul_of_chebyshev_expansion p a ha]
  simp only [one_div, mul_comm]

end NLAlib
