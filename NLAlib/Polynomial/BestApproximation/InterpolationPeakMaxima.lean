import NLAlib.Polynomial.BestApproximation.InterpolationPeakRoots
import NLAlib.Polynomial.BestApproximation.InterpolationProjection

/-!
# Unique nondegenerate maxima of actual Lebesgue gap polynomials

Polynomial compactness, strict interior values and the strict Laguerre inequality
identify each actual gap peak with its unique interior critical point.
-/

noncomputable section
open Polynomial Real Finset Set Filter
open scoped Topology
namespace NLAlib

/-- The actual Lebesgue function has value one at each distinct interpolation node.
Source: the Kronecker cardinal values; focused reroutes, interval peaks. -/
theorem lebesgueFunction_at_node {ι : Type*} [Fintype ι] [DecidableEq ι]
    {v : ι → ℝ} (hv : Function.Injective v) (j : ι) : lebesgueFunction v (v j) = 1 := by
  have hterm : ∀ k : ι, |(Lagrange.basis univ v k).eval (v j)| = if k = j then 1 else 0 := by
    intro k
    by_cases hkj : k = j
    · subst k
      rw [Lagrange.eval_basis_self hv.injOn (mem_univ j)]
      simp
    · rw [Lagrange.eval_basis_of_ne hkj (mem_univ j)]
      simp [hkj]
  simp only [lebesgueFunction, hterm]
  simp

/-- The actual gap polynomial agrees with the Lebesgue function on the closed gap,
including both endpoint values one.
Source: signed cardinal products and nodal values; focused reroutes. -/
theorem eval_interpolationGapPolynomial_eq_lebesgueFunction_closed {n : ℕ} {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Icc (canonicalIntervalNodes n t i.castSucc) (canonicalIntervalNodes n t i.succ)) :
    (interpolationGapPolynomial n t i).eval x = lebesgueFunction (canonicalIntervalNodes n t) x := by
  rcases eq_or_lt_of_le hx.1 with hleft | hleft
  · rw [← hleft, (eval_interpolationGapPolynomial_gap_endpoints ht i).1,
      lebesgueFunction_at_node ht.injective]
  rcases eq_or_lt_of_le hx.2 with hright | hright
  · rw [hright, (eval_interpolationGapPolynomial_gap_endpoints ht i).2,
      lebesgueFunction_at_node ht.injective]
  exact eval_interpolationGapPolynomial_eq_lebesgueFunction ht i ⟨hleft, hright⟩

/-- The actual Lebesgue peak equals the value at any maximizing point of its
signed polynomial on the closed gap.
Source: the canonical supremum norm and the signed cardinal identity; focused reroutes. -/
theorem interpolationGapPeak_eq_eval_of_isMaxOn {n : ℕ} {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) {τ : ℝ}
    (hτ : τ ∈ Icc (canonicalIntervalNodes n t i.castSucc) (canonicalIntervalNodes n t i.succ))
    (hmax : IsMaxOn (interpolationGapPolynomial n t i).eval
      (Icc (canonicalIntervalNodes n t i.castSucc) (canonicalIntervalNodes n t i.succ)) τ) :
    interpolationGapPeak n t i = (interpolationGapPolynomial n t i).eval τ := by
  apply le_antisymm
  · apply lebesgueConstant_le_of_forall
    · rw [eval_interpolationGapPolynomial_eq_lebesgueFunction_closed ht i hτ]
      exact lebesgueFunction_nonneg _ _
    · intro x hx
      rw [← eval_interpolationGapPolynomial_eq_lebesgueFunction_closed ht i hx]
      exact hmax hx
  · rw [eval_interpolationGapPolynomial_eq_lebesgueFunction_closed ht i hτ]
    exact lebesgueFunction_le_lebesgueConstant _ hτ

/-- Each actual gap has a unique interior critical point. It realizes its actual
Lebesgue peak, has value above one, and has strictly negative second derivative.
Source: real-rootedness, strict Laguerre inequality and compactness;
focused reroutes, interval peak nondegeneracy. -/
theorem exists_interpolationGapPeak_nondegenerate {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) :
    ∃ τ ∈ Ioo (canonicalIntervalNodes n t i.castSucc) (canonicalIntervalNodes n t i.succ),
      (interpolationGapPolynomial n t i).derivative.eval τ = 0 ∧
      (interpolationGapPolynomial n t i).derivative.derivative.eval τ < 0 ∧
      1 < (interpolationGapPolynomial n t i).eval τ ∧
      interpolationGapPeak n t i = (interpolationGapPolynomial n t i).eval τ ∧
      (∀ y ∈ Ioo (canonicalIntervalNodes n t i.castSucc) (canonicalIntervalNodes n t i.succ),
        (interpolationGapPolynomial n t i).derivative.eval y = 0 → y = τ) := by
  let p := interpolationGapPolynomial n t i
  let a := canonicalIntervalNodes n t i.castSucc
  let b := canonicalIntervalNodes n t i.succ
  have hab : a < b := ht (show i.castSucc < i.succ from Fin.castSucc_lt_succ)
  have hmid : (a + b) / 2 ∈ Ioo a b := by constructor <;> linarith
  have hmidval : 1 < p.eval ((a + b) / 2) := one_lt_eval_interpolationGapPolynomial hn ht i hmid
  obtain ⟨τ, hτ, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc a b).Nonempty from ⟨a, left_mem_Icc.mpr hab.le⟩) p.continuousOn
  have hval : 1 < p.eval τ := hmidval.trans_le (hmax ⟨hmid.1.le, hmid.2.le⟩)
  have hend := eval_interpolationGapPolynomial_gap_endpoints ht i
  have hτa : a < τ := lt_of_le_of_ne hτ.1 (fun he => by rw [← he, hend.1] at hval; linarith)
  have hτb : τ < b := lt_of_le_of_ne hτ.2 (fun he => by rw [he, hend.2] at hval; linarith)
  have hτo : τ ∈ Ioo a b := ⟨hτa, hτb⟩
  have hcrit : p.derivative.eval τ = 0 := by
    have hc := (hmax.isLocalMax (Icc_mem_nhds hτa hτb)).deriv_eq_zero
    rw [p.deriv] at hc
    exact hc
  have hs := interpolationGapPolynomial_splits hn ht i
  have hnconst := derivative_interpolationGapPolynomial_ne_zero hn ht i
  refine ⟨τ, hτo, hcrit, polynomial_second_derivative_neg_of_splits hs hnconst (by linarith) hcrit,
    hval, interpolationGapPeak_eq_eval_of_isMaxOn ht i hτ hmax, ?_⟩
  intro y hy hyc
  exact eq_of_polynomial_critical_of_splits hs hnconst
    (fun x hx => lt_trans zero_lt_one (one_lt_eval_interpolationGapPolynomial hn ht i hx))
    hy hτo hyc hcrit

end NLAlib
