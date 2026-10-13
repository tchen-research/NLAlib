import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Fin.Tuple
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Polynomial directions matching compact extremal sign sets

A compact real extremal set either contains a prescribed number of alternating points,
or admits a polynomial of smaller degree with the correct sign at every extremum.
The induction cuts off the first sign block at a gap between compact level sets.
Source: Cheney (1966), Chapter 3; operator rederivations, `polybest:signblocks`.
-/

noncomputable section

open Polynomial Set

namespace NLAlib

/-- Starting at an extremum, either there are `n+2` alternating extrema or a degree-`n`
polynomial matches every extremal sign. The polynomial also keeps the initial sign to the
left of the initial point; this makes the compact sign-block induction compositional.
Source: Cheney (1966), Chapter 3, alternation-theorem proof. -/
theorem exists_polynomial_extremal_sign_or_alternation (n : ℕ) :
    ∀ (e : ℝ → ℝ) (E a b : ℝ), Continuous e → 0 < E → a ≤ b → |e a| = E →
      (∃ p : ℝ[X], p.degree ≤ n ∧
        (∀ x ∈ Icc a b, |e x| = E → 0 < e x * p.eval x) ∧
        (∀ x ≤ a, 0 < e a * p.eval x)) ∨
      (∃ v : Fin (n + 2) → ℝ, StrictMono v ∧
        (∀ i, v i ∈ Icc a b ∧ |e (v i)| = E) ∧
        ∀ i : Fin (n + 1), e (v i.castSucc) * e (v i.succ) < 0) := by
  induction n with
  | zero =>
    intro e E a b he hE hab hEa
    have hea : e a ≠ 0 := by intro h; simp [h] at hEa; linarith
    by_cases hopp : ∃ y ∈ Icc a b, e y = -e a
    · obtain ⟨y, hy, hey⟩ := hopp
      have hay : a < y := lt_of_le_of_ne hy.1 (by intro h; rw [← h] at hey; exact hea (by linarith))
      right
      refine ⟨![a, y], ?_, ?_, ?_⟩
      · exact Fin.strictMono_cons.mpr ⟨by intro i; fin_cases i; exact hay, by intro i j hij; omega⟩
      · intro i; fin_cases i
        · exact ⟨⟨le_rfl, hab⟩, hEa⟩
        · exact ⟨hy, by change |e y| = E; rw [hey, abs_neg, hEa]⟩
      · intro i; fin_cases i; change e a * e y < 0; rw [hey]
        nlinarith [sq_pos_of_ne_zero hea]
    · left
      refine ⟨C (e a), degree_C_le, ?_, ?_⟩
      · intro x hx hext
        rcases abs_eq_abs.mp (hext.trans hEa.symm) with h | h
        · simp only [eval_C, h]; exact mul_self_pos.mpr hea
        · exact (hopp ⟨x, hx, h⟩).elim
      · intro x _; simp only [eval_C]; exact mul_self_pos.mpr hea
  | succ n ih =>
    intro e E a b he hE hab hEa
    have hea : e a ≠ 0 := by intro h; simp [h] at hEa; linarith
    by_cases hopp : ∃ y ∈ Icc a b, e y = -e a
    · let B := Icc a b ∩ e ⁻¹' {-e a}
      have hB : IsCompact B := isCompact_Icc.inter_right (isClosed_singleton.preimage he)
      have hBne : B.Nonempty := by
        obtain ⟨y, hy, hey⟩ := hopp
        exact ⟨y, hy, hey⟩
      obtain ⟨y, hy⟩ := hB.exists_isLeast hBne
      have hyab : y ∈ Icc a b := hy.1.1
      have hey : e y = -e a := hy.1.2
      have hay : a < y := lt_of_le_of_ne hyab.1 (by intro h; rw [← h] at hey; exact hea (by linarith))
      let A := Icc a y ∩ e ⁻¹' {e a}
      have hA : IsCompact A := isCompact_Icc.inter_right (isClosed_singleton.preimage he)
      have haA : a ∈ A := ⟨⟨le_rfl, hay.le⟩, rfl⟩
      obtain ⟨u, hu⟩ := hA.exists_isGreatest ⟨a, haA⟩
      have hua : a ≤ u := hu.2 haA
      have huy : u < y := lt_of_le_of_ne hu.1.1.2 (by
        intro h
        have heu : e u = e a := hu.1.2
        rw [h, hey] at heu
        exact hea (by linarith))
      let z := (u + y) / 2
      have huz : u < z := by dsimp [z]; linarith
      have hzy : z < y := by dsimp [z]; linarith
      have haz : a < z := hua.trans_lt huz
      have hprefix : ∀ x ∈ Icc a b, |e x| = E → x < y → e x = e a ∧ x ≤ u := by
        intro x hx hext hxy
        have hex : e x = e a := by
          rcases abs_eq_abs.mp (hext.trans hEa.symm) with h | h
          · exact h
          · have hmem : x ∈ B := ⟨hx, h⟩
            exact (not_lt_of_ge (hy.2 hmem) hxy).elim
        exact ⟨hex, hu.2 ⟨⟨hx.1, hxy.le⟩, hex⟩⟩
      rcases ih e E y b he hE hyab.2 (by rw [hey, abs_neg, hEa]) with
        ⟨p, hp, hpsign, hpleft⟩ | ⟨v, hv, hvext, hvsign⟩
      · left
        refine ⟨(X - C z) * p, ?_, ?_, ?_⟩
        · calc
            ((X - C z) * p).degree ≤ (X - C z : ℝ[X]).degree + p.degree := degree_mul_le _ _
            _ ≤ 1 + (n : WithBot ℕ) := by rw [degree_X_sub_C]; exact add_le_add le_rfl hp
            _ = ↑(n + 1) := by norm_cast; omega
        · intro x hx hext
          simp only [eval_mul, eval_sub, eval_X, eval_C]
          by_cases hxy : x < y
          · obtain ⟨hex, hxu⟩ := hprefix x hx hext hxy
            have hneg : e x * p.eval x < 0 := by
              have hpos := hpleft x hxy.le
              rw [hey, ← hex] at hpos
              linarith
            have hxz : x - z < 0 := by linarith
            nlinarith [mul_pos_of_neg_of_neg hxz hneg]
          · have hpos := hpsign x ⟨le_of_not_gt hxy, hx.2⟩ hext
            have hxz : 0 < x - z := by linarith
            nlinarith [mul_pos hxz hpos]
        · intro x hxa
          simp only [eval_mul, eval_sub, eval_X, eval_C]
          have hneg : e a * p.eval x < 0 := by
            have hpos := hpleft x (hxa.trans hay.le)
            rw [hey] at hpos; linarith
          have hxz : x - z < 0 := by linarith
          nlinarith [mul_pos_of_neg_of_neg hxz hneg]
      · right
        have hv0 : y ≤ v 0 := (hvext 0).1.1
        have hv0ext : |e (v 0)| = |e a| := (hvext 0).2.trans hEa.symm
        obtain ⟨r, hrab, hrv, hersign, hrext⟩ : ∃ r ∈ Icc a b,
            r < v 0 ∧ e r * e (v 0) < 0 ∧ |e r| = E := by
          rcases abs_eq_abs.mp hv0ext with h | h
          · refine ⟨y, hyab, lt_of_le_of_ne hv0 ?_, ?_, by rw [hey, abs_neg, hEa]⟩
            · intro hyeq; rw [← hyeq, hey] at h; exact hea (by linarith)
            · rw [hey, h]; nlinarith [sq_pos_of_ne_zero hea]
          · refine ⟨a, ⟨le_rfl, hab⟩, hay.trans_le hv0, ?_, hEa⟩
            rw [h]; nlinarith [sq_pos_of_ne_zero hea]
        refine ⟨Fin.cons r v, Fin.strictMono_cons.mpr ⟨?_, hv⟩, ?_, ?_⟩
        · intro i; exact hrv.trans_le (hv.monotone (Fin.zero_le i))
        · intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · exact ⟨hrab, hrext⟩
          · exact ⟨⟨hay.le.trans (hvext j).1.1, (hvext j).1.2⟩, (hvext j).2⟩
        · intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simpa using hersign
          · simpa using hvsign j
    · left
      refine ⟨C (e a), (degree_C_le).trans (by exact_mod_cast Nat.zero_le (n + 1)), ?_, ?_⟩
      · intro x hx hext
        rcases abs_eq_abs.mp (hext.trans hEa.symm) with h | h
        · simp only [eval_C, h]; exact mul_self_pos.mpr hea
        · exact (hopp ⟨x, hx, h⟩).elim
      · intro x _; simp only [eval_C]; exact mul_self_pos.mpr hea

end NLAlib
