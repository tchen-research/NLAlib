import NLAlib.Polynomial.BestApproximation.RationalEquioscillation

/-!
# Uniqueness of best real rational approximation

Positive denominator representatives give a type-preserving weighted midpoint. At its
alternating extrema, the positive weighted average saturates only when both minimizers
have the same extremal error. Root-counting then identifies each with the midpoint.
Source: Trefethen, ATAP, Theorem 24.1; original operator rederivations,
`polybest:rational`, the weighted-midpoint proof.
Atlas: `rational-equioscillation`.
-/

noncomputable section

open Polynomial Set

namespace NLAlib

private theorem eq_of_weighted_error_abs_eq {A B x y z E : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hx : |x| ≤ E) (hy : |y| ≤ E) (hz : |z| = E)
    (hsum : (A + B) * z = A * x + B * y) : x = z ∧ y = z := by
  have hE : 0 ≤ E := (abs_nonneg x).trans hx
  have hx' := abs_le.mp hx
  have hy' := abs_le.mp hy
  have hz' : z = E ∨ z = -E := abs_eq_abs.mp (hz.trans (abs_of_nonneg hE).symm)
  rcases hz' with hz' | hz'
  · have hxe : x = E := by
      apply le_antisymm hx'.2
      by_contra hnot
      have hpos := mul_pos hA (sub_pos.mpr (lt_of_not_ge hnot))
      have hnonneg := mul_nonneg hB.le (sub_nonneg.mpr hy'.2)
      rw [hz'] at hsum
      nlinarith
    have hye : y = E := by rw [hxe, hz'] at hsum; nlinarith
    exact ⟨hxe.trans hz'.symm, hye.trans hz'.symm⟩
  · have hxe : x = -E := by
      apply le_antisymm ?_ hx'.1
      by_contra hnot
      have hpos := mul_pos hA (show 0 < x + E by linarith)
      have hnonneg := mul_nonneg hB.le (show 0 ≤ y + E by linarith)
      rw [hz'] at hsum
      nlinarith
    have hye : y = -E := by rw [hxe, hz'] at hsum; nlinarith
    exact ⟨hxe.trans hz'.symm, hye.trans hz'.symm⟩

/-- Best real type-`(m,n)` rational approximation on a nondegenerate interval is unique
as a rational function. Source: ATAP, Theorem 24.1; the type-preserving weighted midpoint
proof in `polybest:rational`. Both zero functions and zero approximation error are included.
atlas: rational-equioscillation -/
theorem eq_of_norm_sub_eq_rationalMinimaxError {a b : ℝ} (hab : a < b) {m n : ℕ}
    (f : C(Icc a b, ℝ)) (r u : RatFunc ℝ)
    (hr : IsPoleFreeRationalApproximation (Icc a b) m n r)
    (hu : IsPoleFreeRationalApproximation (Icc a b) m n u)
    (hfr : ‖f - rationalContinuousMap (Icc a b) r hr.2.2‖ = rationalMinimaxError m n f)
    (hfu : ‖f - rationalContinuousMap (Icc a b) u hu.2.2‖ = rationalMinimaxError m n f) : r = u := by
  classical
  let α := r.denom.eval a
  let β := u.denom.eval a
  let P := α • r.num + β • u.num
  let Q := α • r.denom + β • u.denom
  let E := rationalMinimaxError m n f
  have hA : ∀ x ∈ Icc a b, 0 < α * r.denom.eval x := fun x hx =>
    mul_pos_of_continuousOn_ne_zero r.denom.continuous.continuousOn hr.2.2 ⟨le_rfl, hab.le⟩ hx
  have hB : ∀ x ∈ Icc a b, 0 < β * u.denom.eval x := fun x hx =>
    mul_pos_of_continuousOn_ne_zero u.denom.continuous.continuousOn hu.2.2 ⟨le_rfl, hab.le⟩ hx
  have hQeval : ∀ x, Q.eval x = α * r.denom.eval x + β * u.denom.eval x := by
    intro x; simp [Q, eval_smul]
  have hQpos : ∀ x ∈ Icc a b, 0 < Q.eval x := by
    intro x hx; rw [hQeval]; exact add_pos (hA x hx) (hB x hx)
  have hQ0 : Q ≠ 0 := by intro hzero; have ha := hQpos a ⟨le_rfl, hab.le⟩; simp [hzero] at ha
  have hPdeg : P.degree ≤ m := mem_degreeLE.mp
    ((degreeLE ℝ m).add_mem ((degreeLE ℝ m).smul_mem α (mem_degreeLE.mpr hr.1))
      ((degreeLE ℝ m).smul_mem β (mem_degreeLE.mpr hu.1)))
  have hQdeg : Q.degree ≤ n := mem_degreeLE.mp
    ((degreeLE ℝ n).add_mem ((degreeLE ℝ n).smul_mem α (mem_degreeLE.mpr hr.2.1))
      ((degreeLE ℝ n).smul_mem β (mem_degreeLE.mpr hu.2.1)))
  let w := algebraMap ℝ[X] (RatFunc ℝ) P / algebraMap ℝ[X] (RatFunc ℝ) Q
  let hw := isPoleFreeRationalApproximation_div P Q hPdeg hQdeg hQ0
    (fun x hx => (hQpos x hx).ne')
  have hwval : ∀ x : Icc a b,
      rationalContinuousMap (Icc a b) w hw.2.2 x = P.eval (x : ℝ) / Q.eval (x : ℝ) :=
    rationalContinuousMap_div_apply_eq P Q hPdeg hQdeg hQ0 (fun x hx => (hQpos x hx).ne')
  have hweighted : ∀ x : Icc a b,
      Q.eval (x : ℝ) * (f x - rationalContinuousMap (Icc a b) w hw.2.2 x) =
        α * r.denom.eval (x : ℝ) * (f x - rationalContinuousMap (Icc a b) r hr.2.2 x) +
        β * u.denom.eval (x : ℝ) * (f x - rationalContinuousMap (Icc a b) u hu.2.2 x) := by
    intro x
    rw [hwval]
    dsimp [rationalContinuousMap]
    simp only [P, Q, eval_add, eval_smul, smul_eq_mul]
    have hden : α * r.denom.eval (x : ℝ) + β * u.denom.eval (x : ℝ) ≠ 0 := by
      rw [← hQeval]; exact (hQpos x x.property).ne'
    field_simp [hr.2.2 x x.property, hu.2.2 x x.property, hden]
    ring
  have hrbound : ∀ x : Icc a b,
      |f x - rationalContinuousMap (Icc a b) r hr.2.2 x| ≤ E := by
    intro x
    simpa [hfr] using (f - rationalContinuousMap (Icc a b) r hr.2.2).norm_coe_le_norm x
  have hubound : ∀ x : Icc a b,
      |f x - rationalContinuousMap (Icc a b) u hu.2.2 x| ≤ E := by
    intro x
    simpa [hfu] using (f - rationalContinuousMap (Icc a b) u hu.2.2).norm_coe_le_norm x
  have hwupper : ‖f - rationalContinuousMap (Icc a b) w hw.2.2‖ ≤ E := by
    apply (ContinuousMap.norm_le _ (rationalMinimaxError_nonneg m n f)).mpr
    intro x
    change |f x - rationalContinuousMap (Icc a b) w hw.2.2 x| ≤ E
    have hb : |Q.eval (x : ℝ) * (f x - rationalContinuousMap (Icc a b) w hw.2.2 x)| ≤
        Q.eval (x : ℝ) * E := by
      rw [hweighted]
      calc
        _ ≤ |α * r.denom.eval (x : ℝ) * (f x - rationalContinuousMap (Icc a b) r hr.2.2 x)| +
            |β * u.denom.eval (x : ℝ) * (f x - rationalContinuousMap (Icc a b) u hu.2.2 x)| := abs_add_le _ _
        _ = α * r.denom.eval (x : ℝ) * |f x - rationalContinuousMap (Icc a b) r hr.2.2 x| +
            β * u.denom.eval (x : ℝ) * |f x - rationalContinuousMap (Icc a b) u hu.2.2 x| := by
          rw [abs_mul, abs_of_pos (hA x x.property), abs_mul, abs_of_pos (hB x x.property)]
        _ ≤ Q.eval (x : ℝ) * E := by
          have ha := mul_le_mul_of_nonneg_left (hrbound x) (hA x x.property).le
          have hb := mul_le_mul_of_nonneg_left (hubound x) (hB x x.property).le
          rw [hQeval]; nlinarith
    rw [abs_mul, abs_of_pos (hQpos x x.property)] at hb
    exact le_of_mul_le_mul_left hb (hQpos x x.property)
  have hwbest : ‖f - rationalContinuousMap (Icc a b) w hw.2.2‖ = E :=
    le_antisymm hwupper (rationalMinimaxError_le_norm_sub m n f ⟨w, hw, rfl⟩)
  obtain ⟨v, σ, hv, hσ, hosc⟩ := exists_equioscillation_of_norm_sub_eq_rationalMinimaxError hab f w hw hwbest
  have hext : ∀ i, |f (v i) - rationalContinuousMap (Icc a b) w hw.2.2 (v i)| = E := by
    intro i
    rw [hosc, abs_mul, abs_mul, abs_pow, hσ]
    simp only [abs_neg, abs_one, one_pow, one_mul]
    rw [abs_of_nonneg (norm_nonneg _), hwbest]
  have hsamples : ∀ i,
      rationalContinuousMap (Icc a b) r hr.2.2 (v i) = rationalContinuousMap (Icc a b) w hw.2.2 (v i) ∧
      rationalContinuousMap (Icc a b) u hu.2.2 (v i) = rationalContinuousMap (Icc a b) w hw.2.2 (v i) := by
    intro i
    have hwgt := hweighted (v i)
    rw [hQeval] at hwgt
    obtain ⟨ha, hb⟩ := eq_of_weighted_error_abs_eq (hA _ (v i).property) (hB _ (v i).property)
      (hrbound (v i)) (hubound (v i)) (hext i) hwgt
    constructor <;> linarith
  have heq : ∀ (s : RatFunc ℝ) (hs : IsPoleFreeRationalApproximation (Icc a b) m n s),
      (∀ i, rationalContinuousMap (Icc a b) s hs.2.2 (v i) =
        rationalContinuousMap (Icc a b) w hw.2.2 (v i)) → s = w := by
    intro s hs hsval
    let H := if w = 0 then s.num else s.num * w.denom - w.num * s.denom
    have hH : H.degree ≤ rationalAlternationDegree m n w := degree_rational_difference_numerator_le w s hs
    have hHzero : H = 0 := by
      apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero (s := Finset.univ)
        (v := fun i => (v i : ℝ)) hv.injective.injOn
      · rw [Finset.card_univ, Fintype.card_fin]
        exact hH.trans_lt (by exact_mod_cast (show rationalAlternationDegree m n w < rationalAlternationDegree m n w + 2 by omega))
      · intro i _
        exact difference_numerator_eval_eq_zero_of_rationalContinuousMap_eq w s hw.2.2 hs.2.2 _ (hsval i)
    exact ratFunc_eq_of_difference_numerator_eq_zero w s hHzero
  exact (heq r hr (fun i => (hsamples i).1)).trans (heq u hu (fun i => (hsamples i).2)).symm

/-- Every continuous real function has a unique best pole-free rational approximant of
type `(m,n)`. Source: ATAP, Theorem 24.1. Uniqueness is of Mathlib `RatFunc` elements,
so representations differing by common scalar factors are automatically identified.
atlas: rational-equioscillation -/
theorem exists_unique_norm_sub_eq_rationalMinimaxError {a b : ℝ} (hab : a < b) (m n : ℕ)
    (f : C(Icc a b, ℝ)) :
    ∃! r : RatFunc ℝ, ∃ hr : IsPoleFreeRationalApproximation (Icc a b) m n r,
      ‖f - rationalContinuousMap (Icc a b) r hr.2.2‖ = rationalMinimaxError m n f := by
  obtain ⟨r, hr, hfr⟩ := exists_norm_sub_eq_rationalMinimaxError hab m n f
  refine ⟨r, ⟨hr, hfr⟩, ?_⟩
  rintro u ⟨hu, hfu⟩
  exact eq_of_norm_sub_eq_rationalMinimaxError hab f u r hu hr hfu hfr

end NLAlib
