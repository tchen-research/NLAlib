import NLAlib.Polynomial.Quadrature.HermiteRemainder
import NLAlib.Polynomial.Interpolation.HermiteEndpoints

/-! # Hermite derivative remainder with both interval endpoints

Two simple prescribed endpoints and doubled interior nodes give the order-`2q+2`
remainder `(x−a)(x−b)π_q(x)²`, whose weight is nonpositive on the spectral interval.
-/

noncomputable section
open Polynomial Finset Set

namespace NLAlib

/-- The actual two-endpoint Hermite interpolant has the order-`2q+2` Lobatto remainder.
The case `q=0` is ordinary two-endpoint linear interpolation; node evaluations are exact.
Source: Gautschi (2004), Theorem 3.7; operator derivations (AQ11).
atlas: gauss-radau-lobatto (partial) -/
theorem exists_sub_eval_hermiteTwoEndpointInterpolate_eq {q : ℕ}
    {a b x : ℝ} (hab : a < b) {v : Fin q → ℝ} (hv : Function.Injective v)
    (hva : ∀ i, v i ∈ Ioo a b) (hx : x ∈ Icc a b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ k < 2 * q + 2, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a b)) :
    ∃ ξ ∈ Ioo a b,
      f x - (Lagrange.hermiteTwoEndpointInterpolate a b (f a) (f b) v
        (f ∘ v) (deriv f ∘ v)).eval x =
        iteratedDeriv (2 * q + 2) f ξ / (2 * q + 2).factorial *
          ((x - a) * (x - b) * (Lagrange.nodal univ v).eval x ^ 2) := by
  classical
  let H := Lagrange.hermiteTwoEndpointInterpolate a b (f a) (f b) v (f ∘ v) (deriv f ∘ v)
  let π := Lagrange.nodal univ v
  let ω := (X - C a) * (X - C b) * π ^ 2
  have hav (i : Fin q) : a ≠ v i := (hva i).1.ne
  have hbv (i : Fin q) : b ≠ v i := (hva i).2.ne'
  have hHa : H.eval a = f a := Lagrange.eval_hermiteTwoEndpointInterpolate_left _ _ _ _ _ _ _ hav
  have hHb : H.eval b = f b :=
    Lagrange.eval_hermiteTwoEndpointInterpolate_right _ _ _ _ _ _ _ hab.ne hav hbv
  have hHnode (i : Fin q) : H.eval (v i) = f (v i) :=
    Lagrange.eval_hermiteTwoEndpointInterpolate_at_node _ _ _ _ hv _ _ i
  have hHderiv (i : Fin q) : H.derivative.eval (v i) = deriv f (v i) :=
    Lagrange.eval_derivative_hermiteTwoEndpointInterpolate_at_node _ _ _ _ hv _ _ i
  have hπnode (i : Fin q) : π.eval (v i) = 0 := Lagrange.eval_nodal_at_node (mem_univ i)
  by_cases hωx : ω.eval x = 0
  · have hxroot : x = a ∨ x = b ∨ ∃ i, x = v i := by
      have heq : (x - a) * (x - b) * π.eval x ^ 2 = 0 := by simpa [ω] using hωx
      rcases mul_eq_zero.mp heq with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact Or.inl (sub_eq_zero.mp h)
        · exact Or.inr (Or.inl (sub_eq_zero.mp h))
      · have hπ : π.eval x = 0 := sq_eq_zero_iff.mp h
        rw [Lagrange.eval_nodal, prod_eq_zero_iff] at hπ
        obtain ⟨i, _, hi⟩ := hπ
        exact Or.inr (Or.inr ⟨i, sub_eq_zero.mp hi⟩)
    refine ⟨(a + b) / 2, ⟨by linarith, by linarith⟩, ?_⟩
    change f x - H.eval x = _ * ((x - a) * (x - b) * π.eval x ^ 2)
    rcases hxroot with rfl | rfl | ⟨i, rfl⟩
    · rw [hHa]; ring
    · rw [hHb]; ring
    · rw [hHnode, hπnode]; ring
  let z : Multiset ℝ := (univ : Finset (Fin q)).val.map v
  let m : Multiset ℝ := z + z + {a} + {b}
  have hznd : z.Nodup := Multiset.Nodup.map hv univ.nodup
  have hzi (i : Fin q) : v i ∈ z := Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  have hza : a ∉ z := by
    intro h; obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp h; exact hav i hi.symm
  have hzb : b ∉ z := by
    intro h; obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp h; exact hbv i hi.symm
  have hzc (i : Fin q) : z.count (v i) = 1 := Multiset.count_eq_one_of_mem hznd (hzi i)
  have hmca : m.count a = 1 := by simp [m, Multiset.count_eq_zero_of_notMem hza, hab.ne]
  have hmcb : m.count b = 1 := by simp [m, Multiset.count_eq_zero_of_notMem hzb, hab.ne.symm]
  have hmci (i : Fin q) : m.count (v i) = 2 := by simp [m, hzc i, (hav i).symm, (hbv i).symm]
  have hmcard : m.card = 2 * q + 2 := by simp [m, z]; omega
  have hωmon : ω.Monic := ((monic_X_sub_C a).mul (monic_X_sub_C b)).mul
    (Lagrange.nodal_monic.pow 2)
  have hωdeg : ω.natDegree = m.card := by
    dsimp only [ω]
    rw [natDegree_mul ((monic_X_sub_C a).mul (monic_X_sub_C b)).ne_zero
      (Lagrange.nodal_monic.pow 2).ne_zero,
      natDegree_mul (monic_X_sub_C a).ne_zero (monic_X_sub_C b).ne_zero]
    simp only [natDegree_X_sub_C, natDegree_pow, Lagrange.natDegree_nodal,
      card_univ, Fintype.card_fin]
    omega
  have hmem : ∀ y ∈ m, y ∈ Icc a b := by
    intro y hy
    by_cases hya : y = a
    · subst y; exact ⟨le_rfl, hab.le⟩
    by_cases hyb : y = b
    · subst y; exact ⟨hab.le, le_rfl⟩
    have hyz : y ∈ z := by simpa [m, hya, hyb] using hy
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hyz
    exact Ioo_subset_Icc_self (hva i)
  have hrep : ∀ y ∈ m, 1 < m.count y → y ∈ Ioo a b := by
    intro y hy hc
    have hya : y ≠ a := by intro h; subst y; rw [hmca] at hc; omega
    have hyb : y ≠ b := by intro h; subst y; rw [hmcb] at hc; omega
    have hyz : y ∈ z := by simpa [m, hya, hyb] using hy
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hyz
    exact hva i
  have hωjet : ∀ y ∈ m, ∀ k < m.count y, (derivative^[k] ω).eval y = 0 := by
    intro y hy k hk
    by_cases hya : y = a
    · subst y
      rw [hmca] at hk
      have hk0 : k = 0 := by omega
      simp [hk0, ω]
    by_cases hyb : y = b
    · subst y
      rw [hmcb] at hk
      have hk0 : k = 0 := by omega
      simp [hk0, ω]
    have hyz : y ∈ z := by simpa [m, hya, hyb] using hy
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hyz
    rw [hmci i] at hk
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · simp [ω, hπnode i]
    · simp [ω, derivative_mul, derivative_pow, hπnode i]
  have hjet : ∀ y ∈ m, ∀ k < m.count y,
      iteratedDeriv k f y = (derivative^[k] H).eval y := by
    intro y hy k hk
    by_cases hya : y = a
    · subst y
      rw [hmca] at hk
      have hk0 : k = 0 := by omega
      simpa [hk0] using hHa.symm
    by_cases hyb : y = b
    · subst y
      rw [hmcb] at hk
      have hk0 : k = 0 := by omega
      simpa [hk0] using hHb.symm
    have hyz : y ∈ z := by simpa [m, hya, hyb] using hy
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hyz
    rw [hmci i] at hk
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · simpa using (hHnode i).symm
    · simpa using (hHderiv i).symm
  have hHdegree : H.degree < m.card := by
    rw [hmcard]
    exact Lagrange.degree_hermiteTwoEndpointInterpolate_lt _ _ _ _ hv _ _
  obtain ⟨ξ, hξ, he⟩ := exists_sub_eval_eq_iteratedDeriv_mul_of_multiset m
    (by rw [hmcard]; omega) hmem hrep hHdegree hωmon hωdeg hωjet hjet hf
    (by simpa only [hmcard] using hf') hx hωx
  refine ⟨ξ, hξ, ?_⟩
  simpa only [H, hmcard, ω, eval_mul, eval_sub, eval_X, eval_C, eval_pow] using he

end NLAlib
