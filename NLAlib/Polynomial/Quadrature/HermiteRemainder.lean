import NLAlib.Polynomial.Interpolation.Hermite
import NLAlib.Polynomial.Interpolation.Lagrange
import NLAlib.ForMathlib.Analysis.Calculus.RolleMultiplicity

/-! # Pointwise Hermite remainder for Gauss nodes

The actual finite Hermite interpolant (AQ3), with doubled interior nodes and a simple
evaluation point, has the derivative remainder (AQ4). No measurable selection of the
intermediate derivative point is needed.
-/

noncomputable section
open Polynomial Finset Set

namespace NLAlib

/-- A monic nodal polynomial with prescribed zero multiplicities gives the scalar
Hermite remainder for any lower-degree interpolant matching the same derivative jets.
Repeated nodes are interior; prescribed endpoints may have multiplicity one.
Source: finite multiplicity Rolle argument in operator derivations (AQ4), (AQ9)–(AQ11).
The evaluation point is assumed off the nodal roots; node values are exact separately. -/
theorem exists_sub_eval_eq_iteratedDeriv_mul_of_multiset
    {a b x : ℝ} (m : Multiset ℝ) (hm : 0 < m.card)
    (hmem : ∀ y ∈ m, y ∈ Icc a b)
    (hrep : ∀ y ∈ m, 1 < m.count y → y ∈ Ioo a b)
    {H ω : ℝ[X]} (hH : H.degree < m.card) (hω : ω.Monic) (hωdeg : ω.natDegree = m.card)
    (hωjet : ∀ y ∈ m, ∀ k < m.count y, (derivative^[k] ω).eval y = 0)
    {f : ℝ → ℝ} (hjet : ∀ y ∈ m, ∀ k < m.count y,
      iteratedDeriv k f y = (derivative^[k] H).eval y)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ k < m.card, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a b))
    (hx : x ∈ Icc a b) (hωx : ω.eval x ≠ 0) :
    ∃ ξ ∈ Ioo a b, f x - H.eval x =
      iteratedDeriv m.card f ξ / m.card.factorial * ω.eval x := by
  classical
  let K := (f x - H.eval x) / ω.eval x
  let p := H + C K * ω
  let g : ℝ → ℝ := fun y => f y - p.eval y
  have heq := iteratedDeriv_sub_eval_eqOn isOpen_Ioo p hf'
  have hxnot : x ∉ m := by
    intro hxmem
    exact hωx (by simpa using hωjet x hxmem 0 (Multiset.count_pos.mpr hxmem))
  have hgx : g x = 0 := by
    dsimp [g, p, K]
    simp only [eval_add, eval_mul, eval_C]
    field_simp
    ring
  have hgjet : ∀ y ∈ m, ∀ k < m.count y, iteratedDeriv k g y = 0 := by
    intro y hy k hk
    by_cases hk0 : k = 0
    · subst k
      have h₁ := hjet y hy 0 hk
      have h₂ := hωjet y hy 0 hk
      simp only [Function.iterate_zero, id_eq] at h₂
      simpa [g, p, h₂] using sub_eq_zero.mpr h₁
    · have hyi := hrep y hy (by omega)
      have hkcard : k < m.card := hk.trans_le (Multiset.count_le_card _ _)
      have he := heq k hkcard.le hyi
      change iteratedDeriv k g y = iteratedDeriv k f y - (derivative^[k] p).eval y at he
      dsimp only [p] at he
      rw [iterate_map_add, iterate_derivative_C_mul, eval_add, eval_mul, eval_C,
        hωjet y hy k hk, mul_zero, add_zero, ← hjet y hy k hk, sub_self] at he
      exact he
  let m' : Multiset ℝ := m + {x}
  have hcard : m'.card = (m.card - 1) + 2 := by simp [m']; omega
  have hcount (y : ℝ) (hyx : y ≠ x) : m'.count y = m.count y := by simp [m', hyx]
  have hcountx : m'.count x = 1 := by simp [m', Multiset.count_eq_zero_of_notMem hxnot]
  have hdistinct : ∃ y ∈ m', ∃ t ∈ m', y ≠ t := by
    obtain ⟨y, hy⟩ := Multiset.card_pos_iff_exists_mem.mp hm
    exact ⟨x, by simp [m'], y, by simp [m', hy], fun h => hxnot (h.symm ▸ hy)⟩
  obtain ⟨ξ, hξ, hξ0⟩ := exists_iteratedDeriv_eq_zero_of_multiset_multiplicities
    m' hcard hdistinct
    (by intro y hy; rcases Multiset.mem_add.mp hy with hy | hy
        · exact hmem y hy
        · have hyx := Multiset.mem_singleton.mp hy
          simpa only [hyx] using hx)
    (by
      intro y hy hc
      have hyx : y ≠ x := by intro h; subst y; rw [hcountx] at hc; omega
      have hym : y ∈ m := by simpa [m', hyx] using hy
      rw [hcount y hyx] at hc
      exact hrep y hym hc)
    (hf.sub (Polynomial.continuous _).continuousOn)
    (fun k hk => ((hf' (k + 1) (by omega)).continuousOn.sub
      (Polynomial.continuous _).continuousOn).congr (heq (k + 1) (by omega)))
    (by
      intro y hy k hk
      by_cases hyx : y = x
      · subst y
        rw [hcountx] at hk
        have hk0 : k = 0 := by omega
        simpa [hk0] using hgx
      · have hym : y ∈ m := by simpa [m', hyx] using hy
        rw [hcount y hyx] at hk
        exact hgjet y hym k hk)
  rw [show m.card - 1 + 1 = m.card by omega] at hξ0
  change iteratedDeriv m.card g ξ = 0 at hξ0
  have hpderiv : (derivative^[m.card] p).eval ξ = K * m.card.factorial := by
    dsimp only [p]
    rw [iterate_map_add, iterate_derivative_eq_zero_of_degree_lt hH, zero_add,
      iterate_derivative_C_mul, eval_mul, eval_C, ← hωdeg,
      eval_iterate_derivative_natDegree, hω.leadingCoeff, mul_one]
  have hh := heq m.card le_rfl hξ
  change iteratedDeriv m.card g ξ = iteratedDeriv m.card f ξ -
    (derivative^[m.card] p).eval ξ at hh
  rw [hξ0, hpderiv] at hh
  refine ⟨ξ, hξ, ?_⟩
  rw [show iteratedDeriv m.card f ξ = K * m.card.factorial by linarith]
  dsimp [K]
  have hfac : (m.card.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- The finite Hermite interpolant at `n` distinct interior nodes has the pointwise
order-`2n` remainder, including evaluation at a node or at an interval endpoint.
Source: operator derivations, (AQ3)–(AQ4); Gautschi (2004), Gauss derivative remainder.
This is the scalar interpolation component, before integration against the measure.
atlas: gauss-quadrature-derivative-remainder (partial) -/
theorem exists_sub_eval_hermiteInterpolate_eq {n : ℕ} (hn : 0 < n)
    {a b x : ℝ} (hab : a < b) {v : Fin n → ℝ} (hv : Function.Injective v)
    (hva : ∀ i, v i ∈ Ioo a b) (hx : x ∈ Icc a b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ k < 2 * n, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a b)) :
    ∃ ξ ∈ Ioo a b,
      f x - (Lagrange.hermiteInterpolate univ v (f ∘ v) (deriv f ∘ v)).eval x =
        iteratedDeriv (2 * n) f ξ / (2 * n).factorial *
          (Lagrange.nodal univ v).eval x ^ 2 := by
  classical
  let H := Lagrange.hermiteInterpolate univ v (f ∘ v) (deriv f ∘ v)
  let π := Lagrange.nodal univ v
  have hHnode (i : Fin n) : H.eval (v i) = f (v i) :=
    Lagrange.eval_hermiteInterpolate_at_node hv.injOn _ _ (mem_univ i)
  have hHderiv (i : Fin n) : H.derivative.eval (v i) = deriv f (v i) :=
    Lagrange.eval_derivative_hermiteInterpolate_at_node hv.injOn _ _ (mem_univ i)
  have hπnode (i : Fin n) : π.eval (v i) = 0 := Lagrange.eval_nodal_at_node (mem_univ i)
  by_cases hnode : ∃ i, x = v i
  · obtain ⟨i, rfl⟩ := hnode
    refine ⟨(a + b) / 2, ⟨by linarith, by linarith⟩, ?_⟩
    change f (v i) - H.eval (v i) = _ * π.eval (v i) ^ 2
    rw [hHnode, hπnode]
    ring
  have hnx (i : Fin n) : x ≠ v i := fun h => hnode ⟨i, h⟩
  have hπx : π.eval x ≠ 0 := by
    rw [Lagrange.eval_nodal]
    exact prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (hnx i)
  let K := (f x - H.eval x) / π.eval x ^ 2
  let p := H + C K * π ^ 2
  let g : ℝ → ℝ := fun t => f t - p.eval t
  have heq := iteratedDeriv_sub_eval_eqOn isOpen_Ioo p hf'
  have hgx : g x = 0 := by
    dsimp [g, p, K]
    simp only [eval_add, eval_mul, eval_C, eval_pow]
    field_simp
    ring
  have hgnode (i : Fin n) : g (v i) = 0 := by
    simp [g, p, hHnode i, hπnode i]
  have hgderiv (i : Fin n) : deriv g (v i) = 0 := by
    have hh := heq 1 (by omega) (hva i)
    simp only [iteratedDeriv_one, Function.iterate_one] at hh
    change deriv g (v i) = deriv f (v i) - p.derivative.eval (v i) at hh
    simpa [p, derivative_add, derivative_C_mul, derivative_pow,
      hπnode i, hHderiv i] using hh
  let z : Multiset ℝ := (univ : Finset (Fin n)).val.map v
  let m : Multiset ℝ := z + z + {x}
  have hznd : z.Nodup := Multiset.Nodup.map hv univ.nodup
  have hzi (i : Fin n) : v i ∈ z := Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  have hzx : x ∉ z := by
    intro hxz
    obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hxz
    exact hnx i hi.symm
  have hzc (i : Fin n) : z.count (v i) = 1 := Multiset.count_eq_one_of_mem hznd (hzi i)
  have hmcx : m.count x = 1 := by simp [m, Multiset.count_eq_zero_of_notMem hzx]
  have hmci (i : Fin n) : m.count (v i) = 2 := by simp [m, hzc i, (hnx i).symm]
  have hmcard : m.card = (2 * n - 1) + 2 := by simp [m, z]; omega
  have hmdistinct : ∃ y ∈ m, ∃ t ∈ m, y ≠ t := by
    exact ⟨x, by simp [m], v ⟨0, hn⟩, by simp [m, hzi], hnx _⟩
  have hmem : ∀ y ∈ m, y ∈ Icc a b := by
    intro y hy
    by_cases hyx : y = x
    · simpa [hyx] using hx
    · have hyz : y ∈ z := by simpa [m, hyx] using hy
      obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hyz
      exact Ioo_subset_Icc_self (hva i)
  have hrep : ∀ y ∈ m, 1 < m.count y → y ∈ Ioo a b := by
    intro y hy hc
    have hyx : y ≠ x := by intro h; subst y; rw [hmcx] at hc; omega
    have hyz : y ∈ z := by simpa [m, hyx] using hy
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hyz
    exact hva i
  have hjet : ∀ y ∈ m, ∀ k < m.count y, iteratedDeriv k g y = 0 := by
    intro y hy k hk
    by_cases hyx : y = x
    · subst y
      rw [hmcx] at hk
      have hk0 : k = 0 := by omega
      simpa [hk0] using hgx
    · have hyz : y ∈ z := by simpa [m, hyx] using hy
      obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hyz
      rw [hmci i] at hk
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · simpa using hgnode i
      · simpa using hgderiv i
  obtain ⟨ξ, hξ, hξ0⟩ := exists_iteratedDeriv_eq_zero_of_multiset_multiplicities
    m hmcard hmdistinct hmem hrep (hf.sub (Polynomial.continuous _).continuousOn)
    (fun k hk => ((hf' (k + 1) (by omega)).continuousOn.sub
      (Polynomial.continuous _).continuousOn).congr (heq (k + 1) (by omega))) hjet
  rw [show 2 * n - 1 + 1 = 2 * n by omega] at hξ0
  have hHdegree : H.degree < (2 * n : ℕ) := by
    simpa [H] using Lagrange.degree_hermiteInterpolate_lt
      (show (univ : Finset (Fin n)).Nonempty from ⟨⟨0, hn⟩, mem_univ _⟩)
      hv.injOn (f ∘ v) (deriv f ∘ v)
  have hπdegree : (π ^ 2).natDegree = 2 * n := by
    simp [π, natDegree_pow, Lagrange.natDegree_nodal, mul_comm]
  have hπmonic : (π ^ 2).leadingCoeff = 1 := (Lagrange.nodal_monic.pow 2)
  have hpderiv : (derivative^[2 * n] p).eval ξ = K * (2 * n).factorial := by
    dsimp only [p]
    rw [iterate_map_add, iterate_derivative_eq_zero_of_degree_lt hHdegree, zero_add,
      iterate_derivative_C_mul, eval_mul, eval_C, ← hπdegree,
      eval_iterate_derivative_natDegree, hπmonic, mul_one]
  have hh := heq (2 * n) le_rfl hξ
  change iteratedDeriv (2 * n) g ξ =
    iteratedDeriv (2 * n) f ξ - (derivative^[2 * n] p).eval ξ at hh
  change iteratedDeriv (2 * n) g ξ = 0 at hξ0
  rw [hξ0, hpderiv] at hh
  refine ⟨ξ, hξ, ?_⟩
  change f x - H.eval x = iteratedDeriv (2 * n) f ξ / (2 * n).factorial * π.eval x ^ 2
  rw [show iteratedDeriv (2 * n) f ξ = K * (2 * n).factorial by linarith]
  dsimp [K]
  have hfac : ((2 * n).factorial : ℝ) ≠ 0 := by positivity
  field_simp

end NLAlib
