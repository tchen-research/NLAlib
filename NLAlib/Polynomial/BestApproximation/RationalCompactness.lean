import NLAlib.Polynomial.BestApproximation.RationalCancellation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Interval.Set.Infinite

/-!
# Compactness of jointly normalized rational coefficient vectors

Joint normalization places both coefficient vectors on one compact sphere. A denominator
that vanished in the limit would force the numerator to vanish on the whole interval,
contradicting normalization. The cancellation theorem then removes all remaining real poles.
Source: the rational existence argument in operator rederivations, `polybest:rational-limit`,
with joint normalization replacing separate numerator boundedness.
-/

noncomputable section

open Polynomial Set Filter
open scoped Topology

namespace NLAlib

private def coefficientPolynomial (k : ℕ) (u : Fin (k + 1) → ℝ) : ℝ[X] :=
  ((degreeLTEquiv ℝ (k + 1)).symm u).val

private theorem degree_coefficientPolynomial_le (k : ℕ) (u : Fin (k + 1) → ℝ) :
    (coefficientPolynomial k u).degree ≤ k := by
  have h : coefficientPolynomial k u ∈ degreeLT ℝ (k + 1) :=
    ((degreeLTEquiv ℝ (k + 1)).symm u).property
  rw [degreeLT_succ_eq_degreeLE] at h
  exact mem_degreeLE.mp h

private theorem eval_coefficientPolynomial (k : ℕ) (u : Fin (k + 1) → ℝ) (x : ℝ) :
    (coefficientPolynomial k u).eval x = ∑ i, u i * x ^ (i : ℕ) := by
  have h := eval_eq_sum_degreeLTEquiv ((degreeLTEquiv ℝ (k + 1)).symm u).property x
  simpa [coefficientPolynomial] using h

private theorem coefficientPolynomial_eq_zero_iff (k : ℕ) (u : Fin (k + 1) → ℝ) :
    coefficientPolynomial k u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have heq : (degreeLTEquiv ℝ (k + 1)).symm u = 0 := Subtype.ext h
    have hmap := congrArg (degreeLTEquiv ℝ (k + 1)) heq
    simpa using hmap
  · rintro rfl; simp [coefficientPolynomial]

private theorem coefficientPolynomial_smul (k : ℕ) (c : ℝ) (u : Fin (k + 1) → ℝ) :
    coefficientPolynomial k (c • u) = c • coefficientPolynomial k u := by
  unfold coefficientPolynomial
  rw [LinearEquiv.map_smul]
  rfl

private theorem continuous_eval_coefficientPolynomial (k : ℕ) (x : ℝ) :
    Continuous (fun u : Fin (k + 1) → ℝ => (coefficientPolynomial k u).eval x) := by
  simp_rw [eval_coefficientPolynomial]
  fun_prop

/-- The class of attainable cross-multiplied rational error bounds is closed from above.
Source: the rational existence derivation `polybest:rational-limit`, joint coefficient
normalization and iterative pole cancellation. The approximating denominators need only
be nonzero polynomials; removable interval zeros are allowed in this general closure lemma. -/
theorem exists_cross_error_le_of_forall_pos {m n : ℕ} {a b E : ℝ}
    (hab : a < b) (f : ℝ → ℝ) (hf : Continuous f)
    (happrox : ∀ ε > 0, ∃ p q : ℝ[X], p.degree ≤ m ∧ q.degree ≤ n ∧ q ≠ 0 ∧
      ∀ x ∈ Icc a b, |f x * q.eval x - p.eval x| ≤ (E + ε) * |q.eval x|) :
    ∃ P Q : ℝ[X], P.degree ≤ m ∧ Q.degree ≤ n ∧
      ∀ x ∈ Icc a b, Q.eval x ≠ 0 ∧
        |f x * Q.eval x - P.eval x| ≤ E * |Q.eval x| := by
  choose p q hp hq hqzero herr using
    (fun j : ℕ => happrox (1 / ((j : ℝ) + 1)) (by positivity))
  let pc : ℕ → degreeLT ℝ (m + 1) := fun j =>
    ⟨p j, by rw [degreeLT_succ_eq_degreeLE]; exact mem_degreeLE.mpr (hp j)⟩
  let qc : ℕ → degreeLT ℝ (n + 1) := fun j =>
    ⟨q j, by rw [degreeLT_succ_eq_degreeLE]; exact mem_degreeLE.mpr (hq j)⟩
  let V := (Fin (m + 1) → ℝ) × (Fin (n + 1) → ℝ)
  let w : ℕ → V := fun j => (degreeLTEquiv ℝ (m + 1) (pc j),
    degreeLTEquiv ℝ (n + 1) (qc j))
  have hpolyP : ∀ j, coefficientPolynomial m (w j).1 = p j := by
    intro j; simp [coefficientPolynomial, w, pc]
  have hpolyQ : ∀ j, coefficientPolynomial n (w j).2 = q j := by
    intro j; simp [coefficientPolynomial, w, qc]
  have hnorm : ∀ j, 0 < ‖w j‖ := by
    intro j
    apply norm_pos_iff.mpr
    intro hw
    have hqcoord : (w j).2 = 0 := congrArg Prod.snd hw
    have hqpoly := (coefficientPolynomial_eq_zero_iff n (w j).2).mpr hqcoord
    rw [hpolyQ] at hqpoly
    exact hqzero j hqpoly
  let u : ℕ → V := fun j => ‖w j‖⁻¹ • w j
  have hunorm : ∀ j, ‖u j‖ = 1 := by
    intro j
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg (w j)),
      inv_mul_cancel₀ (hnorm j).ne']
  have huerr : ∀ j x, x ∈ Icc a b →
      |f x * (coefficientPolynomial n (u j).2).eval x -
        (coefficientPolynomial m (u j).1).eval x| ≤
        (E + 1 / ((j : ℝ) + 1)) * |(coefficientPolynomial n (u j).2).eval x| := by
    intro j x hx
    have hscale := mul_le_mul_of_nonneg_left (herr j x hx) (abs_nonneg ‖w j‖⁻¹)
    change |f x * (coefficientPolynomial n (‖w j‖⁻¹ • (w j).2)).eval x -
        (coefficientPolynomial m (‖w j‖⁻¹ • (w j).1)).eval x| ≤
        (E + 1 / ((j : ℝ) + 1)) * |(coefficientPolynomial n (‖w j‖⁻¹ • (w j).2)).eval x|
    simp only [coefficientPolynomial_smul, hpolyP,
      hpolyQ, eval_smul, smul_eq_mul]
    have heq : f x * (‖w j‖⁻¹ * (q j).eval x) - ‖w j‖⁻¹ * (p j).eval x =
        ‖w j‖⁻¹ * (f x * (q j).eval x - (p j).eval x) := by ring
    rw [heq, abs_mul, abs_mul]
    nlinarith [hscale]
  obtain ⟨v, hv, φ, hφ, huv⟩ := (isCompact_sphere (0 : V) 1).tendsto_subseq
    (fun j => by simpa [Metric.mem_sphere, dist_zero_right] using hunorm j)
  let P := coefficientPolynomial m v.1
  let Q := coefficientPolynomial n v.2
  have hvnorm : ‖v‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hv
  have hlimit : ∀ x ∈ Icc a b, |f x * Q.eval x - P.eval x| ≤ E * |Q.eval x| := by
    intro x hx
    have hP : Tendsto (fun j => (coefficientPolynomial m (u (φ j)).1).eval x)
        atTop (𝓝 (P.eval x)) :=
      ((continuous_eval_coefficientPolynomial m x).comp continuous_fst).continuousAt.tendsto.comp huv
    have hQ : Tendsto (fun j => (coefficientPolynomial n (u (φ j)).2).eval x)
        atTop (𝓝 (Q.eval x)) :=
      ((continuous_eval_coefficientPolynomial n x).comp continuous_snd).continuousAt.tendsto.comp huv
    have hε : Tendsto (fun j => E + 1 / ((φ j : ℝ) + 1)) atTop (𝓝 E) := by
      simpa only [add_zero, Function.comp_def] using (tendsto_const_nhds (x := E)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
    exact le_of_tendsto_of_tendsto' ((tendsto_const_nhds.mul hQ).sub hP).abs
      (hε.mul hQ.abs) (fun j => huerr (φ j) x hx)
  have hQzero : Q ≠ 0 := by
    intro hQ0
    have hPeval : ∀ x ∈ Icc a b, P.eval x = 0 := by
      intro x hx
      have hb := hlimit x hx
      simp only [hQ0, eval_zero, mul_zero, zero_sub, abs_neg, abs_zero] at hb
      exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
    have hP0 : P = 0 := Polynomial.eq_zero_of_infinite_isRoot P
      ((Icc_infinite hab).mono (fun x hx => hPeval x hx))
    have hvfst : v.1 = 0 := (coefficientPolynomial_eq_zero_iff m v.1).mp hP0
    have hvsnd : v.2 = 0 := (coefficientPolynomial_eq_zero_iff n v.2).mp hQ0
    have hv0 : v = 0 := Prod.ext hvfst hvsnd
    rw [hv0, norm_zero] at hvnorm
    norm_num at hvnorm
  obtain ⟨P', Q', hP', hQ', _, hbound⟩ :=
    exists_denominator_ne_zero_of_cross_error_le hab f hf P Q hQzero hlimit
  exact ⟨P', Q', hP'.trans (degree_coefficientPolynomial_le m v.1),
    hQ'.trans (degree_coefficientPolynomial_le n v.2), hbound⟩

end NLAlib
