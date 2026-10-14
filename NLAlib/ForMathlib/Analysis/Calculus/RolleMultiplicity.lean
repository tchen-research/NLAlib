import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-! # Rolle's theorem with repeated interior nodes

A nondecreasing node array represents zeros with multiplicities. Equal entries impose
the successive vanishing derivative conditions. Simple endpoints and repeated interior
nodes suffice for the Gauss, Radau and Lobatto Hermite remainder arguments.
-/

noncomputable section
open Set

private theorem exists_monotone_deriv_zeros {q : ℕ} {f : ℝ → ℝ}
    {v : Fin (q + 3) → ℝ} (hv : Monotone v)
    (hf : ContinuousOn f (Icc (v 0) (v (Fin.last _))))
    (hz : ∀ i j, i ≤ j → v i = v j → iteratedDeriv (j.val - i.val) f (v i) = 0) :
    ∃ c : Fin (q + 2) → ℝ, Monotone c ∧
      ∀ i, c i ∈ Icc (v i.castSucc) (v i.succ) ∧ deriv f (c i) = 0 ∧
        (v i.castSucc ≠ v i.succ → c i ∈ Ioo (v i.castSucc) (v i.succ)) := by
  have hex (i : Fin (q + 2)) : ∃ c,
      c ∈ Icc (v i.castSucc) (v i.succ) ∧ deriv f c = 0 ∧
        (v i.castSucc ≠ v i.succ → c ∈ Ioo (v i.castSucc) (v i.succ)) := by
    by_cases heq : v i.castSucc = v i.succ
    · refine ⟨v i.castSucc, ⟨le_rfl, heq.le⟩, ?_, by simp [heq]⟩
      have h := hz i.castSucc i.succ (Fin.castSucc_lt_succ.le) heq
      simpa using h
    · have hlt : v i.castSucc < v i.succ :=
        lt_of_le_of_ne (hv Fin.castSucc_lt_succ.le) heq
      obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero hlt (hf.mono
        (Icc_subset_Icc (hv (Fin.zero_le _)) (hv (Fin.le_last _))))
        (by have h₁ := hz i.castSucc i.castSucc le_rfl rfl
            have h₂ := hz i.succ i.succ le_rfl rfl
            simpa using h₁.trans h₂.symm)
      exact ⟨c, Ioo_subset_Icc_self hc, hc0, fun _ => hc⟩
  choose c hc using hex
  refine ⟨c, ?_, hc⟩
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | hij
  · exact le_rfl
  · exact (hc i).1.2.trans ((hv (Fin.succ_le_castSucc_iff.mpr hij)).trans (hc j).1.1)

/-- A function with a nondecreasing list of `q+2` zeros, counted with their prescribed
multiplicities, has a zero of its `(q+1)`st derivative in the outer open interval.
Repeated nodes must be interior, so only continuity of higher derivatives on that open
interval is needed. Two distinct extreme nodes are required.
Source: repeated Rolle argument for Hermite interpolation, operator derivations (AQ4).
This is a general real-analysis helper for the Gauss/Radau/Lobatto remainders. -/
theorem exists_iteratedDeriv_eq_zero_of_monotone_with_multiplicities
    {q : ℕ} {f : ℝ → ℝ} {a b : ℝ} {v : Fin (q + 2) → ℝ}
    (hv : Monotone v) (hspan : v 0 < v (Fin.last _))
    (hva : ∀ i, v i ∈ Icc a b)
    (hrep : ∀ i : Fin (q + 1), v i.castSucc = v i.succ → v i.castSucc ∈ Ioo a b)
    (hf : ContinuousOn f (Icc (v 0) (v (Fin.last _))))
    (hf' : ∀ k < q, ContinuousOn (iteratedDeriv (k + 1) f) (Ioo a b))
    (hz : ∀ i j, i ≤ j → v i = v j → iteratedDeriv (j.val - i.val) f (v i) = 0) :
    ∃ ξ ∈ Ioo a b, iteratedDeriv (q + 1) f ξ = 0 := by
  induction q generalizing f with
  | zero =>
    obtain ⟨ξ, hξ, hξ0⟩ := exists_deriv_eq_zero hspan hf
      (by have h₁ := hz 0 0 le_rfl rfl
          have h₂ := hz (Fin.last _) (Fin.last _) le_rfl rfl
          simpa using h₁.trans h₂.symm)
    exact ⟨ξ, ⟨(hva 0).1.trans_lt hξ.1, hξ.2.trans_le (hva _).2⟩,
      by simpa using hξ0⟩
  | succ q ih =>
    obtain ⟨c, hcm, hc⟩ := exists_monotone_deriv_zeros hv hf hz
    have hci (i : Fin (q + 2)) : c i ∈ Ioo a b := by
      by_cases heq : v i.castSucc = v i.succ
      · have hpoint : c i = v i.castSucc := le_antisymm
          ((hc i).1.2.trans_eq heq.symm) (hc i).1.1
        rw [hpoint]
        exact hrep i heq
      · have hi := (hc i).2.2 heq
        exact ⟨(hva _).1.trans_lt hi.1, hi.2.trans_le (hva _).2⟩
    have hcs : c 0 < c (Fin.last _) := by
      by_contra hnot
      have heq : c 0 = c (Fin.last _) := le_antisymm
        (hcm (Fin.zero_le _)) (not_lt.mp hnot)
      have hm : v (Fin.succ 0) ≤ v (Fin.last (q + 1)).castSucc := hv (by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_zero, Fin.val_castSucc, Fin.val_last]
        omega)
      have hfirst : v 0 = v (Fin.succ 0) := by
        by_contra hne
        have hh := (hc 0).2.2 hne
        have ht := (hc (Fin.last _)).1.1
        simp only [Fin.castSucc_zero] at hh
        rw [heq] at hh
        have hh2 := hh.2
        linarith
      have hlast : v (Fin.last (q + 1)).castSucc = v (Fin.last (q + 2)) := by
        by_contra hne
        have hh := (hc (Fin.last _)).2.2 hne
        have ht := (hc 0).1.2
        rw [← heq] at hh
        have hh1 := hh.1
        linarith
      have ht₁ := (hc 0).1.2
      have ht₂ := (hc (Fin.last _)).1.1
      change v 0 < v (Fin.last (q + 2)) at hspan
      rw [hfirst, ← hlast] at hspan
      rw [heq] at ht₁
      linarith
    have hcz : ∀ i j, i ≤ j → c i = c j →
        iteratedDeriv (j.val - i.val) (deriv f) (c i) = 0 := by
      intro i j hij heq
      rcases eq_or_lt_of_le hij with rfl | hij
      · simpa using (hc i).2.1
      have hm := hv (Fin.succ_le_castSucc_iff.mpr hij)
      have hupper := (hc i).1.2
      have hlower := (hc j).1.1
      have h₁ : c i = v i.succ := by rw [heq]; linarith
      have h₂ : c j = v j.castSucc := by rw [← heq]; linarith
      have hi : v i.castSucc = v i.succ := by
        by_contra hne
        have hh := (hc i).2.2 hne
        rw [h₁] at hh
        exact (lt_irrefl _ hh.2)
      have hj : v j.castSucc = v j.succ := by
        by_contra hne
        have hh := (hc j).2.2 hne
        rw [h₂] at hh
        exact (lt_irrefl _ hh.1)
      have hold := hz i.castSucc j.succ (by
        simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]
        have hijv : i.val < j.val := hij
        omega) (by linarith)
      rw [show j.succ.val - i.castSucc.val = (j.val - i.val) + 1 by
        simp only [Fin.val_succ, Fin.val_castSucc]; omega, iteratedDeriv_succ'] at hold
      simpa only [show c i = v i.castSucc by linarith] using hold
    have hsub : Icc (c 0) (c (Fin.last _)) ⊆ Ioo a b :=
      Icc_subset_Ioo (hci 0).1 (hci _).2
    have hdc : ContinuousOn (deriv f) (Ioo a b) := by simpa using hf' 0 (by omega)
    obtain ⟨ξ, hξ, hξ0⟩ := ih hcm hcs
      (fun i => Ioo_subset_Icc_self (hci i)) (fun i _ => hci _)
      (hdc.mono hsub)
      (fun k hk => by simpa only [iteratedDeriv_succ'] using hf' (k + 1) (by omega)) hcz
    exact ⟨ξ, hξ, by simpa only [iteratedDeriv_succ'] using hξ0⟩

private theorem card_filter_ge_of_monotone_eq {N : ℕ} {w : Fin N → ℝ}
    (hw : Monotone w) {i j : Fin N} (hij : i ≤ j) (heq : w i = w j) :
    j.val - i.val + 1 ≤ (Finset.univ.filter fun k => w k = w i).card := by
  let e : Fin (j.val - i.val + 1) ↪ Fin N :=
    ⟨fun k => ⟨i.val + k.val, by
      have := i.isLt
      have := j.isLt
      have := k.isLt
      have hijv : i.val ≤ j.val := hij
      omega⟩,
      by intro k l h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega⟩
  have hsub : Finset.univ.map e ⊆ Finset.univ.filter (fun k => w k = w i) := by
    intro k hk
    obtain ⟨t, _, rfl⟩ := Finset.mem_map.mp hk
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, le_antisymm ?_ ?_⟩
    · have hkj : e t ≤ j := by
        change i.val + t.val ≤ j.val
        have ht := t.isLt
        have hijv : i.val ≤ j.val := hij
        omega
      exact (hw hkj).trans_eq heq.symm
    · exact hw (by change i.val ≤ i.val + t.val; omega)
  simpa using Finset.card_le_card hsub

/-- Finite multiplicity Rolle: if zeros counted in a multiset have total multiplicity
`q+2`, every required derivative below each multiplicity vanishes, and at least two
distinct zeros occur, then the `(q+1)`st derivative vanishes in the outer open interval.
Only repeated zeros must be interior. This directly accepts the doubled Gauss nodes
plus a simple evaluation point, or simple prescribed Radau/Lobatto endpoints.
Source: operator derivations, finite multiplicity Rolle argument following (AQ4). -/
theorem exists_iteratedDeriv_eq_zero_of_multiset_multiplicities
    {q : ℕ} {f : ℝ → ℝ} {a b : ℝ} (m : Multiset ℝ) (hm : m.card = q + 2)
    (hdistinct : ∃ x ∈ m, ∃ y ∈ m, x ≠ y)
    (hmem : ∀ x ∈ m, x ∈ Icc a b)
    (hrep : ∀ x ∈ m, 1 < m.count x → x ∈ Ioo a b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ k < q, ContinuousOn (iteratedDeriv (k + 1) f) (Ioo a b))
    (hz : ∀ x ∈ m, ∀ k < m.count x, iteratedDeriv k f x = 0) :
    ∃ ξ ∈ Ioo a b, iteratedDeriv (q + 1) f ξ = 0 := by
  classical
  let l := m.sort (· ≤ ·)
  have hlen : l.length = q + 2 := by simp [l, hm]
  let w : Fin (q + 2) → ℝ := fun i => l.get (Fin.cast hlen.symm i)
  have hwm : Finset.univ.val.map w = m := by
    rw [Fin.univ_val_map]
    change (List.ofFn fun i : Fin (q + 2) => l.get (Fin.cast hlen.symm i) : Multiset ℝ) = m
    rw [← List.ofFn_congr hlen l.get, List.ofFn_get]
    exact Multiset.sort_eq _ _
  have hwi (i : Fin (q + 2)) : w i ∈ m := by
    rw [← hwm]
    exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  have hmono : Monotone w := by
    intro i j hij
    exact (Multiset.pairwise_sort m (· ≤ ·)).rel_get_of_le hij
  have hcount {i j : Fin (q + 2)} (hij : i ≤ j) (heq : w i = w j) :
      j.val - i.val + 1 ≤ m.count (w i) := by
    have h := card_filter_ge_of_monotone_eq hmono hij heq
    have hc : m.count (w i) = (Finset.univ.filter fun k => w k = w i).card := by
      rw [← hwm, Multiset.count_map]
      simp [← Finset.filter_val, eq_comm]
    rwa [hc]
  have hspan : w 0 < w (Fin.last _) := by
    by_contra hnot
    have heq : w 0 = w (Fin.last _) := le_antisymm (hmono (Fin.zero_le _)) (not_lt.mp hnot)
    have hall (i : Fin (q + 2)) : w i = w 0 :=
      le_antisymm ((hmono (Fin.le_last _)).trans_eq heq.symm) (hmono (Fin.zero_le _))
    obtain ⟨x, hx, y, hy, hxy⟩ := hdistinct
    rw [← hwm] at hx hy
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hx
    obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp hy
    exact hxy ((hall i).trans (hall j).symm)
  apply exists_iteratedDeriv_eq_zero_of_monotone_with_multiplicities hmono hspan
    (fun i => hmem _ (hwi i))
  · intro i hi
    have hc := hcount Fin.castSucc_lt_succ.le hi
    apply hrep _ (hwi _)
    simp only [Fin.val_succ, Fin.val_castSucc, Nat.add_sub_cancel_left] at hc
    omega
  · exact hf.mono (Icc_subset_Icc (hmem _ (hwi 0)).1 (hmem _ (hwi _)).2)
  · exact hf'
  · intro i j hij heq
    exact hz _ (hwi i) _ (by have := hcount hij heq; omega)
