import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Canceling denominator zeros in bounded rational limits

A cross-multiplied uniform error bound forces every denominator zero in the interval to
be a numerator zero. Dividing both once by the corresponding linear factor preserves the
bound away from the zero; continuity extends it back to the zero. Induction on denominator
degree removes all interval poles, including endpoint poles, without multiplicity bookkeeping.
Source: operator rederivations, `polybest:rational-limit`, equivalent iterative proof.
-/

noncomputable section

open Polynomial Set

namespace NLAlib

/-- A continuous inequality on a nondegenerate real interval extends over one missing point. -/
private theorem le_on_Icc_of_le_ne {F G : ℝ → ℝ} (hF : Continuous F) (hG : Continuous G)
    {a b z : ℝ} (hab : a < b)
    (hle : ∀ x ∈ Icc a b, x ≠ z → F x ≤ G x) : ∀ x ∈ Icc a b, F x ≤ G x := by
  intro x hx
  by_cases hxz : x = z
  · subst x
    have hclosed : IsClosed {x | F x ≤ G x} := isClosed_le hF hG
    by_cases hzb : z < b
    · have hsub : Ioo z b ⊆ {x | F x ≤ G x} := by
        intro x hxi
        exact hle x ⟨hx.1.trans hxi.1.le, hxi.2.le⟩ (ne_of_gt hxi.1)
      apply closure_minimal hsub hclosed
      rw [closure_Ioo hzb.ne]
      exact ⟨le_rfl, hzb.le⟩
    · have hza : a < z := hab.trans_le (le_of_not_gt hzb)
      have hsub : Ioo a z ⊆ {x | F x ≤ G x} := by
        intro x hxi
        exact hle x ⟨hxi.1.le, hxi.2.le.trans hx.2⟩ (ne_of_lt hxi.2)
      apply closure_minimal hsub hclosed
      rw [closure_Ioo hza.ne]
      exact ⟨hza.le, le_rfl⟩
  · exact hle x hx hxz

/-- A uniformly bounded rational limit has an equivalent representation whose denominator
has no zeros in the interval, with degrees no larger and the same cross-multiplied error
bound. Source: operator rederivations, `polybest:rational-limit`; iterative linear-factor
cancellation replaces the multiplicity/unboundedness argument and includes interval endpoints. -/
theorem exists_denominator_ne_zero_of_cross_error_le {a b E : ℝ} (hab : a < b)
    (f : ℝ → ℝ) (hf : Continuous f) (p q : ℝ[X]) (hq : q ≠ 0)
    (herror : ∀ x ∈ Icc a b, |f x * q.eval x - p.eval x| ≤ E * |q.eval x|) :
    ∃ P Q : ℝ[X], P.degree ≤ p.degree ∧ Q.degree ≤ q.degree ∧ q * P = p * Q ∧
      ∀ x ∈ Icc a b, Q.eval x ≠ 0 ∧
        |f x * Q.eval x - P.eval x| ≤ E * |Q.eval x| := by
  induction hd : q.natDegree using Nat.strong_induction_on generalizing p q with
  | h d ih =>
    by_cases hpoles : ∃ z ∈ Icc a b, q.eval z = 0
    · obtain ⟨z, hz, hqz⟩ := hpoles
      have hpz : p.eval z = 0 := by
        have he := herror z hz
        rw [hqz, mul_zero, zero_sub, abs_neg, abs_zero, mul_zero] at he
        exact abs_eq_zero.mp (le_antisymm he (abs_nonneg _))
      obtain ⟨P₀, hp0⟩ := (dvd_iff_isRoot (p := p) (a := z)).mpr hpz
      obtain ⟨Q₀, hq0⟩ := (dvd_iff_isRoot (p := q) (a := z)).mpr hqz
      have hfactor : (X - C z : ℝ[X]) ≠ 0 := X_sub_C_ne_zero z
      have hQ0 : Q₀ ≠ 0 := by intro hzero; rw [hq0, hzero, mul_zero] at hq; exact hq rfl
      have hqd : Q₀.natDegree < d := by
        rw [hq0, natDegree_mul hfactor hQ0, natDegree_X_sub_C] at hd
        omega
      have herr0 : ∀ x ∈ Icc a b,
          |f x * Q₀.eval x - P₀.eval x| ≤ E * |Q₀.eval x| := by
        apply le_on_Icc_of_le_ne (by fun_prop) (by fun_prop) hab
        intro x hx hxz
        have hb := herror x hx
        rw [hp0, hq0, eval_mul, eval_mul, eval_sub, eval_X, eval_C] at hb
        have heq : f x * ((x - z) * Q₀.eval x) - (x - z) * P₀.eval x =
            (x - z) * (f x * Q₀.eval x - P₀.eval x) := by ring
        rw [heq, abs_mul, abs_mul] at hb
        have hpos : 0 < |x - z| := abs_pos.mpr (sub_ne_zero.mpr hxz)
        have hb' : |x - z| * |f x * Q₀.eval x - P₀.eval x| ≤
            |x - z| * (E * |Q₀.eval x|) := by nlinarith [hb]
        exact le_of_mul_le_mul_left hb' hpos
      obtain ⟨P, Q, hP, hQ, hrel, hbound⟩ :=
        ih Q₀.natDegree hqd P₀ Q₀ hQ0 herr0 rfl
      refine ⟨P, Q, hP.trans ?_, hQ.trans ?_, ?_, hbound⟩
      · rw [hp0, mul_comm]
        exact degree_le_mul_left P₀ hfactor
      · rw [hq0, mul_comm]
        exact degree_le_mul_left Q₀ hfactor
      · rw [hp0, hq0]
        linear_combination (X - C z) * hrel
    · push Not at hpoles
      exact ⟨p, q, le_rfl, le_rfl, by ring, fun x hx => ⟨hpoles x hx, herror x hx⟩⟩

end NLAlib
