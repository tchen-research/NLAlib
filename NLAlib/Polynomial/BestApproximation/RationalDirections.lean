import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Every rational descent numerator has a type-preserving direction

For a reduced nonzero fraction `p/q` of type `(m,n)`, every polynomial of degree at most
`max(m+deg q,n+deg p)` has the form `Pq-pQ` with `deg P≤m`, `deg Q≤n`.
The proof constructs a remainder using Bézout coefficients, rather than introducing
rank-nullity or a rational-function manifold.
Source: operator rederivations, `polybest:rational-linear-map`.
Atlas prerequisite: `rational-equioscillation`.
-/

noncomputable section

open Polynomial

namespace NLAlib

/-- On the `m+deg q` side of the degree maximum, a Bézout remainder gives every numerator
direction within the original type bounds. Source: the rational alternation derivation,
`polybest:rational-linear-map`, constructive Euclidean-division variant. -/
theorem exists_mul_sub_mul_eq_of_degree_le_add_natDegree {m n : ℕ} {p q H : ℝ[X]}
    (hcop : IsCoprime p q) (hq : q ≠ 0) (hpdeg : p.degree ≤ m) (hqdeg : q.degree ≤ n)
    (hH : H.degree ≤ ↑(m + q.natDegree)) :
    ∃ P Q : ℝ[X], P.degree ≤ m ∧ Q.degree ≤ n ∧ P * q - p * Q = H := by
  obtain ⟨A, B, hAB⟩ := hcop
  let Q := (-A * H) % q
  let P := B * H - p * ((-A * H) / q)
  have hmod : q * ((-A * H) / q) + Q = -A * H := EuclideanDomain.div_add_mod _ _
  have hrel : P * q - p * Q = H := by
    dsimp [P]
    linear_combination H * hAB - p * hmod
  have hQ : Q.degree ≤ n := (degree_mod_lt (-A * H) hq).le.trans hqdeg
  have hQq : Q.degree ≤ (q.natDegree : WithBot ℕ) :=
    (degree_mod_lt (-A * H) hq).le.trans degree_le_natDegree
  have hmul : (p * Q).degree ≤ ↑(m + q.natDegree) := by
    calc
      (p * Q).degree ≤ p.degree + Q.degree := degree_mul_le _ _
      _ ≤ (m : WithBot ℕ) + q.natDegree := add_le_add hpdeg hQq
      _ = ↑(m + q.natDegree) := by simp
  have hPq : (P * q).degree ≤ ↑(m + q.natDegree) := by
    have heq : P * q = H + p * Q := by linear_combination hrel
    rw [heq]
    exact (degree_add_le _ _).trans (max_le hH hmul)
  refine ⟨P, Q, ?_, hQ, hrel⟩
  by_cases hP : P = 0
  · simp [hP]
  · have hn : (P * q).natDegree ≤ m + q.natDegree :=
      natDegree_le_iff_degree_le.mpr hPq
    rw [natDegree_mul hP hq] at hn
    exact degree_le_natDegree.trans (by exact_mod_cast (show P.natDegree ≤ m by omega))

/-- The full polynomial tangent-numerator map of a reduced nonzero rational function is
surjective, with the exact defect-adjusted degree bound.
Source: operator rederivations, `polybest:rational-linear-map`; the constructive proof
uses Bézout remainders on the larger side of the degree maximum. -/
theorem exists_degree_le_mul_sub_mul_eq_of_isCoprime {m n : ℕ} {p q H : ℝ[X]}
    (hp : p ≠ 0) (hq : q ≠ 0) (hcop : IsCoprime p q)
    (hpdeg : p.degree ≤ m) (hqdeg : q.degree ≤ n)
    (hH : H.degree ≤ ↑(max (m + q.natDegree) (n + p.natDegree))) :
    ∃ P Q : ℝ[X], P.degree ≤ m ∧ Q.degree ≤ n ∧ P * q - p * Q = H := by
  rcases le_total (n + p.natDegree) (m + q.natDegree) with h | h
  · rw [max_eq_left h] at hH
    exact exists_mul_sub_mul_eq_of_degree_le_add_natDegree hcop hq hpdeg hqdeg hH
  · rw [max_eq_right h] at hH
    obtain ⟨Q, P, hQ, hP, hrel⟩ := exists_mul_sub_mul_eq_of_degree_le_add_natDegree
      hcop.symm hp hqdeg hpdeg (H := -H) (by simpa using hH)
    refine ⟨P, Q, hP, hQ, ?_⟩
    linear_combination -hrel

/-- The rational tangent degree agrees with the customary defect formula for nonzero
reduced fractions. Source: Trefethen, ATAP, Chapter 24, the defect definition. -/
theorem add_sub_min_sub_eq_max_add {m n μ ν : ℕ} (hμ : μ ≤ m) (hν : ν ≤ n) :
    m + n - min (m - μ) (n - ν) = max (m + ν) (n + μ) := by omega

end NLAlib
