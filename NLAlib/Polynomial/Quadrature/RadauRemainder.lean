import NLAlib.Polynomial.Quadrature.HermiteRemainder
import NLAlib.Polynomial.Interpolation.HermiteEndpoints

/-! # Hermite derivative remainder with one prescribed endpoint

One simple prescribed endpoint and doubled interior nodes give a nodal remainder
`(x−t)π_q(x)²` of order `2q+1`. Left and right Radau use `t=a` and `t=b` respectively.
-/

noncomputable section
open Polynomial Finset Set

namespace NLAlib

/-- The actual one-endpoint Hermite interpolant has the order-`2q+1` remainder, including
`q=0` and evaluation at any node. The factor `x−t` determines the left/right Radau signs.
Source: Gautschi (2004), Theorems 3.3 and 3.7; operator derivations (AQ9)–(AQ10).
atlas: gauss-radau-lobatto (partial) -/
theorem exists_sub_eval_hermiteEndpointInterpolate_eq {q : ℕ}
    {a b t x : ℝ} (hab : a < b) (ht : t ∈ Icc a b) {v : Fin q → ℝ}
    (hv : Function.Injective v) (hva : ∀ i, v i ∈ Ioo a b) (htv : ∀ i, t ≠ v i)
    (hx : x ∈ Icc a b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ k < 2 * q + 1, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a b)) :
    ∃ ξ ∈ Ioo a b,
      f x - (Lagrange.hermiteEndpointInterpolate t (f t) v (f ∘ v) (deriv f ∘ v)).eval x =
        iteratedDeriv (2 * q + 1) f ξ / (2 * q + 1).factorial *
          ((x - t) * (Lagrange.nodal univ v).eval x ^ 2) := by
  classical
  let H := Lagrange.hermiteEndpointInterpolate t (f t) v (f ∘ v) (deriv f ∘ v)
  let π := Lagrange.nodal univ v
  let ω := (X - C t) * π ^ 2
  have hHt : H.eval t = f t := Lagrange.eval_hermiteEndpointInterpolate_endpoint _ _ _ _ _ htv
  have hHnode (i : Fin q) : H.eval (v i) = f (v i) :=
    Lagrange.eval_hermiteEndpointInterpolate_at_node _ _ hv _ _ i
  have hHderiv (i : Fin q) : H.derivative.eval (v i) = deriv f (v i) :=
    Lagrange.eval_derivative_hermiteEndpointInterpolate_at_node _ _ hv _ _ i
  have hπnode (i : Fin q) : π.eval (v i) = 0 := Lagrange.eval_nodal_at_node (mem_univ i)
  by_cases hωx : ω.eval x = 0
  · have hxroot : x = t ∨ ∃ i, x = v i := by
      have heq : (x - t) * π.eval x ^ 2 = 0 := by simpa [ω] using hωx
      rcases mul_eq_zero.mp heq with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · have hπ : π.eval x = 0 := sq_eq_zero_iff.mp h
        rw [Lagrange.eval_nodal, prod_eq_zero_iff] at hπ
        obtain ⟨i, _, hi⟩ := hπ
        exact Or.inr ⟨i, sub_eq_zero.mp hi⟩
    refine ⟨(a + b) / 2, ⟨by linarith, by linarith⟩, ?_⟩
    change f x - H.eval x = _ * ((x - t) * π.eval x ^ 2)
    rcases hxroot with rfl | ⟨i, rfl⟩
    · rw [hHt]; ring
    · rw [hHnode, hπnode]; ring
  let z : Multiset ℝ := (univ : Finset (Fin q)).val.map v
  let m : Multiset ℝ := z + z + {t}
  have hznd : z.Nodup := Multiset.Nodup.map hv univ.nodup
  have hzi (i : Fin q) : v i ∈ z := Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  have hzt : t ∉ z := by
    intro htmem
    obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp htmem
    exact htv i hi.symm
  have hzc (i : Fin q) : z.count (v i) = 1 := Multiset.count_eq_one_of_mem hznd (hzi i)
  have hmct : m.count t = 1 := by simp [m, Multiset.count_eq_zero_of_notMem hzt]
  have hmci (i : Fin q) : m.count (v i) = 2 := by simp [m, hzc i, (htv i).symm]
  have hmcard : m.card = 2 * q + 1 := by simp [m, z]; omega
  have hωmon : ω.Monic := (monic_X_sub_C t).mul (Lagrange.nodal_monic.pow 2)
  have hωdeg : ω.natDegree = m.card := by
    dsimp only [ω]
    rw [natDegree_mul (monic_X_sub_C t).ne_zero (Lagrange.nodal_monic.pow 2).ne_zero]
    simp only [natDegree_X_sub_C, natDegree_pow, Lagrange.natDegree_nodal,
      card_univ, Fintype.card_fin]
    omega
  have hmem : ∀ y ∈ m, y ∈ Icc a b := by
    intro y hy
    by_cases hyt : y = t
    · simpa only [hyt] using ht
    · have hyz : y ∈ z := by simpa [m, hyt] using hy
      obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hyz
      exact Ioo_subset_Icc_self (hva i)
  have hrep : ∀ y ∈ m, 1 < m.count y → y ∈ Ioo a b := by
    intro y hy hc
    have hyt : y ≠ t := by intro h; subst y; rw [hmct] at hc; omega
    have hyz : y ∈ z := by simpa [m, hyt] using hy
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hyz
    exact hva i
  have hωjet : ∀ y ∈ m, ∀ k < m.count y, (derivative^[k] ω).eval y = 0 := by
    intro y hy k hk
    by_cases hyt : y = t
    · subst y
      rw [hmct] at hk
      have hk0 : k = 0 := by omega
      simp [hk0, ω]
    · have hyz : y ∈ z := by simpa [m, hyt] using hy
      obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hyz
      rw [hmci i] at hk
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · simp [ω, hπnode i]
      · simp [ω, derivative_mul, derivative_pow, hπnode i]
  have hjet : ∀ y ∈ m, ∀ k < m.count y,
      iteratedDeriv k f y = (derivative^[k] H).eval y := by
    intro y hy k hk
    by_cases hyt : y = t
    · subst y
      rw [hmct] at hk
      have hk0 : k = 0 := by omega
      simpa [hk0] using hHt.symm
    · have hyz : y ∈ z := by simpa [m, hyt] using hy
      obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hyz
      rw [hmci i] at hk
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · simpa using (hHnode i).symm
      · simpa using (hHderiv i).symm
  have hHdegree : H.degree < m.card := by
    rw [hmcard]
    exact Lagrange.degree_hermiteEndpointInterpolate_lt _ _ hv _ _
  obtain ⟨ξ, hξ, he⟩ := exists_sub_eval_eq_iteratedDeriv_mul_of_multiset m
    (by rw [hmcard]; omega) hmem hrep hHdegree hωmon hωdeg hωjet hjet hf
    (by simpa only [hmcard] using hf') hx hωx
  refine ⟨ξ, hξ, ?_⟩
  simpa only [H, hmcard, ω, eval_mul, eval_sub, eval_X, eval_C, eval_pow] using he

end NLAlib
