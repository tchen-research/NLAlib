import NLAlib.Polynomial.BestApproximation.EquioscillationCertificate
import NLAlib.Polynomial.BestApproximation.ExtremalSigns
import NLAlib.ForMathlib.Analysis.Normed.UniformApproximation
import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Order.Interval.Set.Infinite

/-!
# The polynomial equioscillation theorem

Best uniform approximation is characterized by `n+2` equal-magnitude alternating extrema.
Necessity uses the compact sign-block dichotomy and the uniform descent lemma.
Source: Trefethen, ATAP, Theorem 10.1; Cheney (1966), Chapter 3.
Atlas: `equioscillation`.
-/

noncomputable section

open Polynomial Set

namespace NLAlib

/-- A best polynomial with positive error has `n+2` alternating extremal samples.
Source: Trefethen, ATAP, Theorem 10.1, the compact sign-block perturbation proof. -/
theorem exists_alternating_extrema_of_norm_sub_eq_minimaxError {n : ℕ} {a b : ℝ}
    (hab : a < b) (f : C(Icc a b, ℝ)) {p : ℝ[X]} (hp : p.degree ≤ n)
    (hbest : ‖f - p.toContinuousMapOn (Icc a b)‖ = minimaxError n f)
    (hE : 0 < ‖f - p.toContinuousMapOn (Icc a b)‖) :
    ∃ v : Fin (n + 2) → Icc a b, StrictMono (fun i => (v i : ℝ)) ∧
      (∀ i, |f (v i) - p.eval (v i : ℝ)| = ‖f - p.toContinuousMapOn (Icc a b)‖) ∧
      ∀ i : Fin (n + 1),
        (f (v i.castSucc) - p.eval (v i.castSucc : ℝ)) *
          (f (v i.succ) - p.eval (v i.succ : ℝ)) < 0 := by
  let : Fact (a ≤ b) := ⟨hab.le⟩
  let g := f - p.toContinuousMapOn (Icc a b)
  let e : C(ℝ, ℝ) := ContinuousMap.IccExtendCM g
  let E := ‖g‖
  have heval : ∀ x (hx : x ∈ Icc a b), e x = g ⟨x, hx⟩ :=
    fun x hx => ContinuousMap.IccExtendCM_of_mem hx
  let K := Icc a b ∩ (fun x => |e x|) ⁻¹' {E}
  have hK : IsCompact K := isCompact_Icc.inter_right
    (isClosed_singleton.preimage (e.continuous.abs))
  have hKne : K.Nonempty := by
    by_contra hnone
    have hlt : ‖g‖ < E := (ContinuousMap.norm_lt_iff g hE).mpr (by
      intro x
      have hne : |g x| ≠ E := by
        intro hx
        exact hnone ⟨x, x.property, by
          change |e x| = E
          rw [heval _ x.property]; exact hx⟩
      exact lt_of_le_of_ne (g.norm_coe_le_norm x) hne)
    exact lt_irrefl E hlt
  obtain ⟨c, hc⟩ := hK.exists_isLeast hKne
  have hcab : c ∈ Icc a b := hc.1.1
  have hcE : |e c| = E := hc.1.2
  rcases exists_polynomial_extremal_sign_or_alternation n e E c b
      e.continuous hE hcab.2 hcE with ⟨q, hq, hqsign, _⟩ | ⟨v, hv, hvext, hvsign⟩
  · let h : C(Icc a b, ℝ) := q.toContinuousMapOn (Icc a b)
    have hsign : ∀ x : Icc a b, |g x| = ‖g‖ → 0 < g x * h x := by
      intro x hx
      have hex : |e x| = E := by rw [heval _ x.property]; exact hx
      have hcx : c ≤ x := hc.2 ⟨x.property, hex⟩
      have hpos := hqsign x ⟨hcx, x.property.2⟩ hex
      simpa [heval _ x.property, h] using hpos
    obtain ⟨t, ht, himprove⟩ := exists_pos_norm_sub_smul_lt_of_extremal_sign g h hE hsign
    have hnew : (p + t • q).degree ≤ n :=
      mem_degreeLE.mp ((degreeLE ℝ n).add_mem (mem_degreeLE.mpr hp)
        ((degreeLE ℝ n).smul_mem t (mem_degreeLE.mpr hq)))
    have heq : f - (p + t • q).toContinuousMapOn (Icc a b) = g - t • h := by
      ext x
      simp [g, h, eval_smul]
      ring
    have hbound := minimaxError_le_norm_sub f
      (mem_polynomialApproximationSpace_iff.mpr ⟨p + t • q, hnew, rfl⟩)
    rw [heq, ← hbest] at hbound
    exact (not_lt_of_ge hbound himprove).elim
  · let w : Fin (n + 2) → Icc a b := fun i =>
      ⟨v i, hcab.1.trans (hvext i).1.1, (hvext i).1.2⟩
    refine ⟨w, hv, ?_, ?_⟩
    · intro i
      have hext := (hvext i).2
      rw [heval _ (w i).property] at hext
      exact hext
    · intro i
      have hsig := hvsign i
      rw [heval _ (w i.castSucc).property, heval _ (w i.succ).property] at hsig
      exact hsig

/-- Opposite nonzero signs and equal absolute values force two real values to be negatives. -/
private lemma eq_neg_of_abs_eq_abs_of_mul_neg {x y : ℝ}
    (habs : |y| = |x|) (hxy : x * y < 0) : y = -x := by
  rcases abs_eq_abs.mp habs with h | h
  · rw [h] at hxy
    exact (not_lt_of_ge (mul_self_nonneg x) hxy).elim
  · exact h

/-- A best degree-`n` polynomial has an equal-magnitude alternating extremal list, including
the zero-error case. Source: Trefethen, ATAP, Theorem 10.1.
atlas: equioscillation -/
theorem exists_equioscillation_of_norm_sub_eq_minimaxError {n : ℕ} {a b : ℝ}
    (hab : a < b) (f : C(Icc a b, ℝ)) {p : ℝ[X]} (hp : p.degree ≤ n)
    (hbest : ‖f - p.toContinuousMapOn (Icc a b)‖ = minimaxError n f) :
    ∃ (v : Fin (n + 2) → Icc a b) (σ : ℝ),
      StrictMono (fun i => (v i : ℝ)) ∧ |σ| = 1 ∧
      ∀ i, f (v i) - p.eval (v i : ℝ) =
        σ * (-1) ^ (i : ℕ) * ‖f - p.toContinuousMapOn (Icc a b)‖ := by
  let g := f - p.toContinuousMapOn (Icc a b)
  let E := ‖g‖
  by_cases hE : E = 0
  · have hden : (0 : ℝ) < n + 2 := by positivity
    let v : Fin (n + 2) → Icc a b := fun i =>
      ⟨a + (b - a) * (i : ℕ) / (n + 2), by
        constructor
        · exact le_add_of_nonneg_right (by positivity)
        · have hi : (i : ℝ) ≤ n + 2 := by exact_mod_cast i.isLt.le
          have hmul := mul_le_mul_of_nonneg_left hi (sub_pos.mpr hab).le
          have hpart : (b - a) * (i : ℕ) / (n + 2) ≤ b - a :=
            (div_le_iff₀ hden).mpr hmul
          linarith⟩
    refine ⟨v, 1, ?_, by norm_num, ?_⟩
    · intro i j hij
      have hijR : (i : ℝ) < j := by exact_mod_cast hij
      dsimp [v]
      have hdiv := div_lt_div_of_pos_right
        (mul_lt_mul_of_pos_left hijR (sub_pos.mpr hab)) hden
      linarith
    · intro i
      have hval : g (v i) = 0 := by
        have := g.norm_coe_le_norm (v i)
        change ‖g (v i)‖ ≤ E at this
        rw [hE] at this
        exact norm_eq_zero.mp (le_antisymm this (norm_nonneg _))
      simpa [g, E, hE] using hval
  · have hEpos : 0 < E := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hE)
    obtain ⟨v, hv, hvabs, hvsign⟩ :=
      exists_alternating_extrema_of_norm_sub_eq_minimaxError hab f hp hbest hEpos
    let σ := (f (v 0) - p.eval (v 0 : ℝ)) / E
    refine ⟨v, σ, hv, ?_, ?_⟩
    · dsimp [σ]
      rw [abs_div, hvabs 0, abs_of_pos hEpos]
      exact div_self hEpos.ne'
    · intro i
      refine Fin.induction ?_ (fun j hj => ?_) i
      · simp only [Fin.val_zero, pow_zero, mul_one]
        change f (v 0) - p.eval (v 0 : ℝ) =
          (f (v 0) - p.eval (v 0 : ℝ)) / E * E
        rw [div_mul_cancel₀ _ hEpos.ne']
      · have hnext := eq_neg_of_abs_eq_abs_of_mul_neg
          ((hvabs j.succ).trans (hvabs j.castSucc).symm) (hvsign j)
        rw [hnext, hj]
        simp only [Fin.val_succ, Fin.val_castSucc, pow_succ]
        ring

/-- A degree-`n` polynomial is best if and only if it equioscillates at `n+2` ordered points.
Source: Trefethen, ATAP, Theorem 10.1.
atlas: equioscillation -/
theorem norm_sub_eq_minimaxError_iff_equioscillation {n : ℕ} {a b : ℝ}
    (hab : a < b) (f : C(Icc a b, ℝ)) {p : ℝ[X]} (hp : p.degree ≤ n) :
    ‖f - p.toContinuousMapOn (Icc a b)‖ = minimaxError n f ↔
      ∃ (v : Fin (n + 2) → Icc a b) (σ : ℝ),
        StrictMono (fun i => (v i : ℝ)) ∧ |σ| = 1 ∧
        ∀ i, f (v i) - p.eval (v i : ℝ) =
          σ * (-1) ^ (i : ℕ) * ‖f - p.toContinuousMapOn (Icc a b)‖ := by
  constructor
  · exact exists_equioscillation_of_norm_sub_eq_minimaxError hab f hp
  · rintro ⟨v, σ, hv, hσ, hosc⟩
    exact norm_sub_eq_minimaxError_of_equioscillation f hp hv hσ hosc

/-- Best uniform polynomial approximation on a nondegenerate real interval is unique.
Source: Trefethen, ATAP, Theorem 10.1. At the alternating extrema of the polynomial
midpoint, both minimizers must have the same saturated error.
atlas: equioscillation -/
theorem eq_of_norm_sub_eq_minimaxError {n : ℕ} {a b : ℝ} (hab : a < b)
    (f : C(Icc a b, ℝ)) {p q : ℝ[X]} (hp : p.degree ≤ n) (hq : q.degree ≤ n)
    (hfp : ‖f - p.toContinuousMapOn (Icc a b)‖ = minimaxError n f)
    (hfq : ‖f - q.toContinuousMapOn (Icc a b)‖ = minimaxError n f) : p = q := by
  let r : ℝ[X] := (1 / 2 : ℝ) • (p + q)
  have hr : r.degree ≤ n := mem_degreeLE.mp
    ((degreeLE ℝ n).smul_mem (1 / 2 : ℝ)
      ((degreeLE ℝ n).add_mem (mem_degreeLE.mpr hp) (mem_degreeLE.mpr hq)))
  have heq : f - r.toContinuousMapOn (Icc a b) = (1 / 2 : ℝ) •
      ((f - p.toContinuousMapOn (Icc a b)) + (f - q.toContinuousMapOn (Icc a b))) := by
    ext x; simp [r, eval_smul]; ring
  have hrupper : ‖f - r.toContinuousMapOn (Icc a b)‖ ≤ minimaxError n f := by
    rw [heq, norm_smul, Real.norm_eq_abs]
    norm_num
    have ht := norm_add_le (f - p.toContinuousMapOn (Icc a b))
      (f - q.toContinuousMapOn (Icc a b))
    rw [hfp, hfq] at ht
    linarith
  have hrbest : ‖f - r.toContinuousMapOn (Icc a b)‖ = minimaxError n f :=
    le_antisymm hrupper (minimaxError_le_norm_sub f
      (mem_polynomialApproximationSpace_iff.mpr ⟨r, hr, rfl⟩))
  obtain ⟨v, σ, hv, hσ, hosc⟩ :=
    exists_equioscillation_of_norm_sub_eq_minimaxError hab f hr hrbest
  apply Polynomial.eq_of_degree_sub_lt_of_eval_index_eq (s := Finset.univ)
    (v := fun i => (v i : ℝ)) hv.injective.injOn
  · rw [Finset.card_univ, Fintype.card_fin]
    exact ((degree_sub_le p q).trans (max_le hp hq)).trans_lt
      (by exact_mod_cast (show n < n + 2 by omega))
  · intro i _
    have hpb : |f (v i) - p.eval (v i : ℝ)| ≤ minimaxError n f := by
      have hb := (f - p.toContinuousMapOn (Icc a b)).norm_coe_le_norm (v i)
      rwa [hfp] at hb
    have hqb : |f (v i) - q.eval (v i : ℝ)| ≤ minimaxError n f := by
      have hb := (f - q.toContinuousMapOn (Icc a b)).norm_coe_le_norm (v i)
      rwa [hfq] at hb
    have hrabs : |f (v i) - r.eval (v i : ℝ)| = minimaxError n f := by
      rw [hosc, abs_mul, abs_mul, abs_pow, hσ]
      simp [hrbest, abs_of_nonneg (minimaxError_nonneg n f)]
    have hmid : 2 * (f (v i) - r.eval (v i : ℝ)) =
        (f (v i) - p.eval (v i : ℝ)) + (f (v i) - q.eval (v i : ℝ)) := by
      simp [r, eval_smul]; ring
    have hpb' := abs_le.mp hpb
    have hqb' := abs_le.mp hqb
    have hrabs' : |f (v i) - r.eval (v i : ℝ)| = |minimaxError n f| :=
      hrabs.trans (abs_of_nonneg (minimaxError_nonneg n f)).symm
    rcases abs_eq_abs.mp hrabs' with h | h <;> nlinarith

end NLAlib
