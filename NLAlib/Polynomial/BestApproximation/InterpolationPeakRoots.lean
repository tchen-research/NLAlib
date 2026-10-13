import NLAlib.Polynomial.BestApproximation.InterpolationPeaks
import NLAlib.ForMathlib.Analysis.RealRootedPeaks

/-!
# Real-rootedness of the actual interpolation gap polynomial

Alternating nodal signs give one real root in every other gap. The polynomial
degree exceeds that root count by at most one, so all its roots are real.
-/

noncomputable section
open Polynomial Real Finset Set
namespace NLAlib

/-- Gap signs have magnitude one.
Source: fixed alternating cardinal signs; focused reroutes. -/
theorem abs_interpolationGapSign (n : ℕ) (i : Fin (n + 1)) (j : Fin (n + 2)) :
    |interpolationGapSign n i j| = 1 := by
  unfold interpolationGapSign
  split_ifs <;> simp

/-- The fixed signs alternate across every gap except their own gap.
Source: the explicit alternating nodal sign formula; focused reroutes. -/
theorem interpolationGapSign_succ_eq_neg {n : ℕ} (i k : Fin (n + 1)) (hki : k ≠ i) :
    interpolationGapSign n i k.succ = -interpolationGapSign n i k.castSucc := by
  unfold interpolationGapSign
  simp only [Fin.val_succ, Fin.val_castSucc]
  by_cases hk : k.val < i.val
  · have h0 : k.val ≤ i.val := by omega
    have h1 : k.val + 1 ≤ i.val := by omega
    rw [if_pos h0, if_pos h1]
    have he : i.val - k.val = (i.val - (k.val + 1)) + 1 := by omega
    rw [he, pow_succ]
    ring
  · have hik : i.val < k.val := by
      have hne : k.val ≠ i.val := fun h => hki (Fin.ext h)
      omega
    have h0 : ¬ k.val ≤ i.val := by omega
    have h1 : ¬ k.val + 1 ≤ i.val := by omega
    rw [if_neg h0, if_neg h1]
    have he : k.val + 1 - i.val - 1 = (k.val - i.val - 1) + 1 := by omega
    rw [he, pow_succ]
    ring

/-- Every other nodal gap contains a real root of the actual gap polynomial.
Source: alternating nodal signs and the intermediate value theorem; focused reroutes. -/
theorem exists_root_interpolationGapPolynomial_other_gap {n : ℕ} {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i k : Fin (n + 1)) (hki : k ≠ i) :
    ∃ r ∈ Ioo (canonicalIntervalNodes n t k.castSucc) (canonicalIntervalNodes n t k.succ),
      (interpolationGapPolynomial n t i).eval r = 0 := by
  let p := interpolationGapPolynomial n t i
  let a := canonicalIntervalNodes n t k.castSucc
  let b := canonicalIntervalNodes n t k.succ
  have hab : a < b := ht (show k.castSucc < k.succ from Fin.castSucc_lt_succ)
  have ha : p.eval a = interpolationGapSign n i k.castSucc := eval_interpolationGapPolynomial_node ht i _
  have hb : p.eval b = -p.eval a := by
    rw [show p.eval b = interpolationGapSign n i k.succ from eval_interpolationGapPolynomial_node ht i _,
      interpolationGapSign_succ_eq_neg i k hki, ha]
  have h0 : 0 ∈ uIcc (p.eval a) (p.eval b) := by
    by_cases hpa : 0 ≤ p.eval a
    · exact mem_uIcc_of_ge (by rw [hb]; linarith) hpa
    · exact mem_uIcc_of_le (le_of_not_ge hpa) (by rw [hb]; linarith)
  obtain ⟨r, hr, hroot⟩ := intermediate_value_uIcc p.continuousOn h0
  rw [uIcc_of_le hab.le] at hr
  have ha0 : p.eval a ≠ 0 := by
    have h := abs_interpolationGapSign n i k.castSucc
    rw [← ha] at h
    intro hz
    rw [hz, abs_zero] at h
    norm_num at h
  have hb0 : p.eval b ≠ 0 := by rw [hb]; exact neg_ne_zero.mpr ha0
  have hra : a < r := lt_of_le_of_ne hr.1 (fun he => ha0 (he ▸ hroot))
  have hrb : r < b := lt_of_le_of_ne hr.2 (fun he => hb0 (he ▸ hroot))
  exact ⟨r, ⟨hra, hrb⟩, hroot⟩

/-- The actual gap polynomial splits over the reals.
Source: roots in the other nodal gaps and the degree bound; focused reroutes. -/
theorem interpolationGapPolynomial_splits {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) :
    (interpolationGapPolynomial n t i).Splits := by
  classical
  let J := {k : Fin (n + 1) // k ∈ (univ.erase i : Finset (Fin (n + 1)))}
  have hex : ∀ k : J, ∃ r ∈ Ioo (canonicalIntervalNodes n t k.val.castSucc)
      (canonicalIntervalNodes n t k.val.succ), (interpolationGapPolynomial n t i).eval r = 0 := by
    intro k
    exact exists_root_interpolationGapPolynomial_other_gap ht i k.val (mem_erase.mp k.property).1
  choose r hr hroot using hex
  have hinj : Function.Injective r := by
    intro k l hkl
    apply Subtype.ext
    apply le_antisymm
    · by_contra hnot
      have hlk : l.val < k.val := lt_of_not_ge hnot
      have hnodes : canonicalIntervalNodes n t l.val.succ ≤ canonicalIntervalNodes n t k.val.castSucc :=
        ht.monotone (by change l.val.val + 1 ≤ k.val.val; omega)
      have hrlk : r l < r k := (hr l).2.trans_le hnodes |>.trans (hr k).1
      exact hrlk.ne hkl.symm
    · by_contra hnot
      have hkl' : k.val < l.val := lt_of_not_ge hnot
      have hnodes : canonicalIntervalNodes n t k.val.succ ≤ canonicalIntervalNodes n t l.val.castSucc :=
        ht.monotone (by change k.val.val + 1 ≤ l.val.val; omega)
      have hrkl : r k < r l := (hr k).2.trans_le hnodes |>.trans (hr l).1
      exact hrkl.ne hkl
  let s : Finset ℝ := univ.image r
  have hcard : s.card = n := by
    rw [Finset.card_image_of_injective _ hinj]
    simp only [card_univ, J, Fintype.card_coe, card_erase_of_mem (mem_univ i), card_univ,
      Fintype.card_fin, Nat.add_sub_cancel]
  have hp0 : interpolationGapPolynomial n t i ≠ 0 := by
    intro hp0
    apply derivative_interpolationGapPolynomial_ne_zero hn ht i
    rw [hp0, derivative_zero]
  apply polynomial_splits_of_natDegree_le_card_add_one hp0 s
  · intro x hx
    obtain ⟨k, _, rfl⟩ := mem_image.mp hx
    exact hroot k
  · rw [hcard]
    have hd := Lagrange.degree_interpolate_lt (s := univ) (interpolationGapSign n i) ht.injective.injOn
    have hnat : (interpolationGapPolynomial n t i).natDegree < n + 2 := by
      apply (natDegree_lt_iff_degree_lt hp0).mpr
      simpa only [interpolationGapPolynomial, card_univ, Fintype.card_fin] using hd
    omega

end NLAlib
