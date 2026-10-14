import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.FieldDivision

/-! # Exactness of finite polynomial evaluation rules

Euclidean division characterizes exactness of a finite evaluation rule for any
polynomial linear functional. The result includes the zero extra-degree case.
-/

noncomputable section

open Polynomial Finset Set

namespace Lagrange

variable {𝕜 ι : Type*} [Field 𝕜] [DecidableEq ι]

/-- Any polynomial functional is reconstructed from its cardinal values below
the number of distinct nodes. -/
theorem linearMap_eq_sum_basis_mul_eval (L : 𝕜[X] →ₗ[𝕜] 𝕜)
    {s : Finset ι} {v : ι → 𝕜} (hv : InjOn v s) {p : 𝕜[X]}
    (hp : p.degree < s.card) :
    L p = ∑ i ∈ s, L (Lagrange.basis s v i) * p.eval (v i) := by
  conv_lhs => rw [eq_interpolate hv hp]
  rw [interpolate_apply, map_sum]
  apply sum_congr rfl
  intro i hi
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul]
  ring

/-- A rule on distinct nodes is exact below degree `#s+k` precisely when its
weights are the functional's cardinal values and the nodal polynomial is
orthogonal to every polynomial of degree below `k`. -/
theorem linearMap_eq_sum_weighted_eval_iff (L : 𝕜[X] →ₗ[𝕜] 𝕜)
    {s : Finset ι} (hs : s.Nonempty) {v : ι → 𝕜} (hv : InjOn v s)
    (w : ι → 𝕜) (k : ℕ) :
    (∀ p : 𝕜[X], p.degree < (s.card + k : ℕ) →
      L p = ∑ i ∈ s, w i * p.eval (v i)) ↔
      (∀ i ∈ s, w i = L (Lagrange.basis s v i)) ∧
        (∀ q : 𝕜[X], q.degree < k → L (nodal s v * q) = 0) := by
  have hs0 : 0 < s.card := hs.card_pos
  constructor
  · intro h
    constructor
    · intro i hi
      have hdeg : (Lagrange.basis s v i).degree < (s.card + k : ℕ) := by
        rw [degree_basis hv hi]
        exact_mod_cast (show s.card - 1 < s.card + k by omega)
      have he := h (Lagrange.basis s v i) hdeg
      rw [sum_eq_single i] at he
      · simpa only [eval_basis_self hv hi, mul_one] using he.symm
      · intro j hj hji
        rw [eval_basis_of_ne hji.symm hj, mul_zero]
      · exact fun hnot => (hnot hi).elim
    · intro q hq
      by_cases hq0 : q = 0
      · simp [hq0]
      have hqn : q.natDegree < k := (natDegree_lt_iff_degree_lt hq0).mpr hq
      have hdeg : (nodal s v * q).degree < (s.card + k : ℕ) := by
        rw [degree_mul, degree_nodal, degree_eq_natDegree hq0,
          ← Nat.cast_add]
        exact_mod_cast Nat.add_lt_add_left hqn s.card
      rw [h _ hdeg]
      apply sum_eq_zero
      intro i hi
      rw [eval_mul, eval_nodal_at_node hi, zero_mul, mul_zero]
  · rintro ⟨hw, horth⟩ p hp
    let Q := p /ₘ nodal s v
    let R := p %ₘ nodal s v
    have hQ : Q.degree < k := by
      by_cases hQ0 : Q = 0
      · simp [hQ0]
      by_cases hk0 : k = 0
      · have hp' : p.degree < (nodal s v).degree := by simpa [hk0, degree_nodal] using hp
        exact (hQ0 ((divByMonic_eq_zero_iff nodal_monic).mpr hp')).elim
      have hp0 : p ≠ 0 := by intro h; simp [Q, h] at hQ0
      have hpn := (natDegree_lt_iff_degree_lt hp0).mpr hp
      rw [degree_eq_natDegree hQ0]
      have hqn : Q.natDegree = p.natDegree - s.card := by
        simp only [Q, natDegree_divByMonic p nodal_monic, natDegree_nodal]
      rw [hqn]
      exact_mod_cast (show p.natDegree - s.card < k by omega)
    have hR : R.degree < s.card := by
      simpa only [R, degree_nodal] using
        degree_modByMonic_lt p (nodal_monic (s := s) (v := v))
    have hdiv : p = R + nodal s v * Q := (modByMonic_add_div p (nodal s v)).symm
    have hLp : L p = L R := by rw [hdiv, map_add, horth Q hQ, add_zero]
    rw [hLp, linearMap_eq_sum_basis_mul_eval L hv hR]
    apply sum_congr rfl
    intro i hi
    rw [hw i hi]
    have hnode : R.eval (v i) = p.eval (v i) := by
      rw [hdiv, eval_add, eval_mul, eval_nodal_at_node hi, zero_mul, add_zero]
    rw [hnode]

end Lagrange

namespace Polynomial

/-- Polynomial linear functionals agree below a given degree exactly when
their corresponding finitely many monomial moments agree. -/
theorem linearMap_eq_of_degree_lt_iff_pow {𝕜 : Type*} [Field 𝕜]
    (L M : 𝕜[X] →ₗ[𝕜] 𝕜) (d : ℕ) :
    (∀ p : 𝕜[X], p.degree < d → L p = M p) ↔
      (∀ k < d, L (X ^ k) = M (X ^ k)) := by
  constructor
  · intro h k hk
    exact h (X ^ k) (by simpa only [degree_X_pow] using Nat.cast_lt.mpr hk)
  · intro h p hp
    by_cases hp0 : p = 0
    · simp [hp0]
    have hpn := (natDegree_lt_iff_degree_lt hp0).mpr hp
    conv_lhs => rw [p.as_sum_range_C_mul_X_pow' hpn]
    conv_rhs => rw [p.as_sum_range_C_mul_X_pow' hpn]
    rw [map_sum, map_sum]
    apply sum_congr rfl
    intro k hk
    rw [← smul_eq_C_mul, map_smul, map_smul, h k (mem_range.mp hk)]

end Polynomial
