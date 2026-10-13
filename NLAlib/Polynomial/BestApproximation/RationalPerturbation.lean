import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Uniform improvement by a type-preserving rational perturbation

Squared cross errors turn the nonlinear perturbation into a polynomial in the step.
At an extremum its first derivative is `-2 e (Pq-pQ)`, which is strictly negative
for a matching descent numerator. Compactness makes the improvement uniform.
Source: operator rederivations, `polybest:rational-linear-map` and `polybest:improvement`.
-/

noncomputable section

open Polynomial
open scoped Topology

namespace NLAlib

/-- A numerator direction matching every extremal error sign produces a positive rational
step with no poles and uniformly smaller error. Source: the rational alternation derivation,
`polybest:rational-linear-map`. No denominator sign normalization is required. -/
theorem exists_pos_rational_perturbation_error_lt {s : Set ℝ} [CompactSpace s]
    (f : C(s, ℝ)) (p q P Q : ℝ[X])
    (hq : ∀ x : s, q.eval (x : ℝ) ≠ 0) {E : ℝ} (hE : 0 < E)
    (hbound : ∀ x : s, |f x - p.eval (x : ℝ) / q.eval (x : ℝ)| ≤ E)
    (hsign : ∀ x : s, |f x - p.eval (x : ℝ) / q.eval (x : ℝ)| = E →
      0 < (f x - p.eval (x : ℝ) / q.eval (x : ℝ)) * (P * q - p * Q).eval (x : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ x : s,
      (q + t • Q).eval (x : ℝ) ≠ 0 ∧
      |f x - (p + t • P).eval (x : ℝ) / (q + t • Q).eval (x : ℝ)| < E := by
  let e : s → ℝ := fun x => f x - p.eval (x : ℝ) / q.eval (x : ℝ)
  let A : s → ℝ := fun x => f x * q.eval (x : ℝ) - p.eval (x : ℝ)
  let C : s → ℝ := fun x => f x * Q.eval (x : ℝ) - P.eval (x : ℝ)
  let D : ℝ × s → ℝ := fun z => q.eval (z.2 : ℝ) + z.1 * Q.eval (z.2 : ℝ)
  let M : ℝ × s → ℝ := fun z =>
    (A z.2 + z.1 * C z.2) ^ 2 - E ^ 2 * (D z) ^ 2
  let B : ℝ × s → ℝ := fun z =>
    2 * A z.2 * C z.2 - 2 * E ^ 2 * q.eval (z.2 : ℝ) * Q.eval (z.2 : ℝ) +
      z.1 * ((C z.2) ^ 2 - E ^ 2 * (Q.eval (z.2 : ℝ)) ^ 2)
  have hA : ∀ x, A x = e x * q.eval (x : ℝ) := by
    intro x; dsimp [A, e]; field_simp [hq x]
  have hMzero : ∀ x : s, M (0, x) ≤ 0 := by
    intro x
    have hb : (e x) ^ 2 ≤ E ^ 2 := by
      have hx := hbound x
      nlinarith [sq_abs (e x), abs_nonneg (e x)]
    have hprod := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (q.eval (x : ℝ)))
      (sub_nonpos.mpr hb)
    dsimp [M, D]
    rw [hA]
    nlinarith
  have hDcont : Continuous D := by dsimp [D]; fun_prop
  have hMcont : Continuous M := by dsimp [M, A, C, D]; fun_prop
  have hBcont : Continuous B := by dsimp [B, A, C]; fun_prop
  have hlocal : ∀ x : s, ∀ᶠ z : ℝ × s in 𝓝 (0, x),
      D z ≠ 0 ∧ (0 < z.1 → M z < 0) := by
    intro x
    have hDne : ∀ᶠ z : ℝ × s in 𝓝 (0, x), D z ≠ 0 :=
      ((isOpen_ne : IsOpen {y : ℝ | y ≠ 0}).preimage hDcont).mem_nhds
        (by simpa [D] using hq x)
    by_cases hx : |e x| = E
    · have he2 : (e x) ^ 2 = E ^ 2 := by nlinarith [sq_abs (e x)]
      have hdir := hsign x hx
      change 0 < e x * (P * q - p * Q).eval (x : ℝ) at hdir
      have hC : q.eval (x : ℝ) * C x = e x * q.eval (x : ℝ) * Q.eval (x : ℝ) -
          (P * q - p * Q).eval (x : ℝ) := by
        dsimp [C, e]
        simp only [eval_sub, eval_mul]
        field_simp [hq x]
        ring
      have hBneg : B (0, x) < 0 := by
        dsimp [B]
        rw [hA]
        have heq : 2 * (e x * q.eval (x : ℝ)) * C x -
            2 * E ^ 2 * q.eval (x : ℝ) * Q.eval (x : ℝ) =
            -2 * e x * (P * q - p * Q).eval (x : ℝ) := by
          calc
            _ = 2 * e x * (q.eval (x : ℝ) * C x) -
                2 * E ^ 2 * q.eval (x : ℝ) * Q.eval (x : ℝ) := by ring
            _ = _ := by
              rw [hC]
              linear_combination 2 * q.eval (x : ℝ) * Q.eval (x : ℝ) * he2
        simp only [zero_mul, add_zero]
        rw [heq]
        nlinarith
      have hBne : ∀ᶠ z : ℝ × s in 𝓝 (0, x), B z < 0 :=
        (isOpen_lt hBcont continuous_const).mem_nhds hBneg
      filter_upwards [hDne, hBne] with z hzD hzB
      refine ⟨hzD, fun ht => ?_⟩
      have hprod := mul_neg_of_pos_of_neg ht hzB
      have hzero := hMzero z.2
      have heq : M z = M (0, z.2) + z.1 * B z := by dsimp [M, B, D]; ring
      rw [heq]
      linarith
    · have hxlt : |e x| < E := lt_of_le_of_ne (hbound x) hx
      have he2 : (e x) ^ 2 < E ^ 2 := by
        nlinarith [sq_abs (e x), abs_nonneg (e x)]
      have hprod := mul_neg_of_pos_of_neg (sq_pos_of_ne_zero (hq x))
        (sub_neg.mpr he2)
      have hMneg : M (0, x) < 0 := by dsimp [M, D]; rw [hA]; nlinarith
      have hMne : ∀ᶠ z : ℝ × s in 𝓝 (0, x), M z < 0 :=
        (isOpen_lt hMcont continuous_const).mem_nhds hMneg
      filter_upwards [hDne, hMne] with z hzD hzM
      exact ⟨hzD, fun _ => hzM⟩
  have huniform : ∀ᶠ t : ℝ in 𝓝 0, ∀ x : s,
      D (t, x) ≠ 0 ∧ (0 < t → M (t, x) < 0) :=
    isCompact_univ.eventually_forall_of_forall_eventually (fun x _ => hlocal x) |>.mono
      (fun _ ht x => ht x (Set.mem_univ x))
  obtain ⟨δ, hδ, hstep⟩ := Metric.eventually_nhds_iff.mp huniform
  let t := δ / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hnear : dist t (0 : ℝ) < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos ht]; dsimp [t]; linarith
  refine ⟨t, ht, fun x => ?_⟩
  have hD := (hstep hnear x).1
  have hM := (hstep hnear x).2 ht
  have hDpoly : (q + t • Q).eval (x : ℝ) = D (t, x) := by simp [D, eval_smul]
  have hNpoly : f x * (q + t • Q).eval (x : ℝ) - (p + t • P).eval (x : ℝ) =
      A x + t * C x := by simp [A, C, eval_smul]; ring
  refine ⟨by rw [hDpoly]; exact hD, ?_⟩
  have hDpos : 0 < |D (t, x)| := abs_pos.mpr hD
  have hNlt : |A x + t * C x| < E * |D (t, x)| := by
    have hpos := mul_pos hE hDpos
    change (A x + t * C x) ^ 2 - E ^ 2 * (D (t, x)) ^ 2 < 0 at hM
    nlinarith [sq_abs (A x + t * C x), sq_abs (D (t, x)), abs_nonneg (A x + t * C x)]
  have herr : f x - (p + t • P).eval (x : ℝ) / (q + t • Q).eval (x : ℝ) =
      (A x + t * C x) / D (t, x) := by
    rw [← hNpoly, ← hDpoly]
    field_simp [hDpoly, hD]
  rw [herr, abs_div]
  exact (div_lt_iff₀ hDpos).mpr hNlt

end NLAlib
