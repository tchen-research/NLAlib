import NLAlib.Polynomial.Quadrature.RadauLobatto

/-! # Reindexing finite distinct-node rules by their prescribed endpoints

Finite permutations move one or both designated endpoint nodes to the leading indices.
Every other node then lies in the open interval when it differs from both endpoints.
-/

noncomputable section
open Finset Set

namespace NLAlib

/-- An injective `(q+1)`-node family containing `a` can be permuted to the endpoint
family `a,v₀,…,v_{q−1}`. -/
theorem exists_perm_endpointNodeFamily {q : ℕ} (t : Fin (q + 1) → ℝ)
    (ht : Function.Injective t) {a : ℝ} (ha : a ∈ Set.range t) :
    ∃ e : Equiv.Perm (Fin (q + 1)), ∃ v : Fin q → ℝ,
      Function.Injective v ∧ (∀ i, t (e i) = endpointNodeFamily a v i) := by
  classical
  obtain ⟨ia, hia⟩ := ha
  let e : Equiv.Perm (Fin (q + 1)) := Equiv.swap 0 ia
  let v : Fin q → ℝ := fun i => t (e i.succ)
  refine ⟨e, v, fun i j hij => Fin.succ_injective _ (e.injective (ht hij)), ?_⟩
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · simpa only [e, Equiv.swap_apply_left, endpointNodeFamily, Fin.cases_zero] using hia
  · rfl

/-- An injective `(q+2)`-node family containing both distinct interval endpoints can
be permuted to a two-endpoint family, with all the remaining nodes interior.
Source: finite spectral node reindexing for Gauss–Lobatto rules. -/
theorem exists_perm_twoEndpointNodeFamily {q : ℕ} (t : Fin (q + 2) → ℝ)
    (ht : Function.Injective t) {a b : ℝ} (hab : a < b)
    (htab : ∀ i, t i ∈ Icc a b) (ha : a ∈ Set.range t) (hb : b ∈ Set.range t) :
    ∃ e : Equiv.Perm (Fin (q + 2)), ∃ v : Fin q → ℝ,
      Function.Injective v ∧ (∀ i, v i ∈ Ioo a b) ∧
        ∀ i, t (e i) = twoEndpointNodeFamily a b v i := by
  classical
  obtain ⟨ia, hia⟩ := ha
  obtain ⟨ib, hib⟩ := hb
  let e₀ : Equiv.Perm (Fin (q + 2)) := Equiv.swap 0 ia
  let j := e₀.symm ib
  let one : Fin (q + 2) := Fin.succ 0
  have hone : one ≠ 0 := by simp [one]
  have hj : j ≠ 0 := by
    intro hj
    have hid : ib = ia := by
      calc ib = e₀ j := (e₀.apply_symm_apply ib).symm
        _ = e₀ 0 := by rw [hj]
        _ = ia := Equiv.swap_apply_left _ _
    exact hab.ne (hia.symm.trans ((congrArg t hid).symm.trans hib))
  let e := (Equiv.swap one j).trans e₀
  have he0 : t (e 0) = a := by
    simp only [e, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hone) (Ne.symm hj)]
    simpa only [e₀, Equiv.swap_apply_left] using hia
  have he1 : t (e one) = b := by
    simp only [e, Equiv.trans_apply, Equiv.swap_apply_left, j, Equiv.apply_symm_apply, hib]
  let v : Fin q → ℝ := fun i => t (e i.succ.succ)
  have hv : Function.Injective v := by
    intro i k hik
    exact Fin.succ_injective _ (Fin.succ_injective _ (e.injective (ht hik)))
  have hvi (i : Fin q) : v i ∈ Ioo a b := by
    have ha0 : v i ≠ a := by
      intro h
      have hi := e.injective (ht (h.trans he0.symm))
      have hi' := congrArg Fin.val hi
      simp at hi'
    have hb0 : v i ≠ b := by
      intro h
      have hi := e.injective (ht (h.trans he1.symm))
      have hi' := congrArg Fin.val hi
      simp [one] at hi'
    exact ⟨lt_of_le_of_ne (htab _).1 ha0.symm, lt_of_le_of_ne (htab _).2 hb0⟩
  refine ⟨e, v, hv, hvi, ?_⟩
  intro i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
  · exact he0
  · exact he1
  · rfl

/-- A designated endpoint permutation retains closed-interval location and proves
that the remaining distinct nodes exclude that endpoint. -/
theorem exists_perm_endpointNodeFamily_mem_Icc {q : ℕ} {a b t : ℝ}
    (v : Fin (q + 1) → ℝ) (hv : Function.Injective v)
    (hvi : ∀ i, v i ∈ Icc a b) (hvt : t ∈ Set.range v) :
    ∃ e : Equiv.Perm (Fin (q + 1)), ∃ u : Fin q → ℝ,
      Function.Injective u ∧ (∀ i, u i ∈ Icc a b) ∧ (∀ i, t ≠ u i) ∧
        ∀ i, v (e i) = endpointNodeFamily t u i := by
  obtain ⟨e, u, hu, heu⟩ := exists_perm_endpointNodeFamily v hv hvt
  have hui (i : Fin q) : u i ∈ Icc a b := by
    simpa only [heu, endpointNodeFamily, Fin.cases_succ] using hvi (e i.succ)
  have htu (i : Fin q) : t ≠ u i := by
    intro h
    have hid := e.injective (hv ((heu 0).trans (h.trans (heu i.succ).symm)))
    have hval := congrArg Fin.val hid
    simp at hval
  exact ⟨e, u, hu, hui, htu, heu⟩

end NLAlib
