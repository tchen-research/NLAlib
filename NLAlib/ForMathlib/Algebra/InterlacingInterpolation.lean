import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic

/-!
# Polynomial reconstruction from interlacing residues

Lagrange interpolation reconstructs the two secular polynomial identities
from their values at distinct original roots. Source: Horn--Johnson (2013),
Section 4.3; supports `interlacing-converse`.
-/

noncomputable section
open scoped BigOperators
open Polynomial
namespace NLAlib

/-- Equal-degree monic polynomials cancel their leading terms.
Horn--Johnson (2013), Section 4.3; inverse interlacing helper. -/
theorem degree_sub_lt_of_monic_natDegree_eq {p q : ℝ[X]} {n : ℕ}
    (hp : p.Monic) (hq : q.Monic) (hpn : p.natDegree = n)
    (hqn : q.natDegree = n) : (p - q).degree < n := by
  have hpd : p.degree = n := by rw [degree_eq_natDegree hp.ne_zero, hpn]
  have hqd : q.degree = n := by rw [degree_eq_natDegree hq.ne_zero, hqn]
  simpa only [hpd] using degree_sub_lt_left (hpd.trans hqd.symm) hp.ne_zero
    (hp.leadingCoeff.trans hq.leadingCoeff.symm)

/-- Matching the next coefficient cancels one further degree.
Horn--Johnson (2013), Section 4.3; inverse interlacing helper. -/
theorem degree_sub_lt_of_monic_nextCoeff_eq {p q : ℝ[X]} {n : ℕ}
    (hp : p.Monic) (hq : q.Monic) (hpn : p.natDegree = n + 1)
    (hqn : q.natDegree = n + 1) (hc : p.nextCoeff = q.nextCoeff) :
    (p - q).degree < n := by
  have hdeg := degree_sub_lt_of_monic_natDegree_eq hp hq hpn hqn
  apply (degree_lt_iff_coeff_zero _ _).mpr
  intro m hm
  rcases eq_or_lt_of_le hm with rfl | hlt
  · rw [coeff_sub]
    have hpc : p.nextCoeff = p.coeff n := by
      rw [nextCoeff_of_natDegree_pos (by omega), hpn, Nat.add_sub_cancel]
    have hqc : q.nextCoeff = q.coeff n := by
      rw [nextCoeff_of_natDegree_pos (by omega), hqn, Nat.add_sub_cancel]
    exact sub_eq_zero.mpr (hpc.symm.trans (hc.trans hqc))
  · exact coeff_eq_zero_of_degree_lt (hdeg.trans_le (by exact_mod_cast hlt))

/-- A polynomial remainder of degree below the number of distinct nodes
equals the sum of its simple residue numerators. Horn--Johnson (2013),
Section 4.3; inverse interlacing helper. -/
theorem polynomial_eq_base_sub_residue_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (hd : Function.Injective d) (q base : ℝ[X])
    (hdeg : (q - base).degree < Fintype.card ι)
    (hbase : ∀ j, base.eval (d j) = 0) :
    q = base - ∑ j, C (-q.eval (d j) /
      (∏ l ∈ Finset.univ.erase j, (d j - d l))) *
        (∏ l ∈ Finset.univ.erase j, (X - C (d l))) := by
  have heq := Lagrange.eq_interpolate (s := Finset.univ) (v := d)
    hd.injOn (by simpa using hdeg)
  have hr : q - base = ∑ j, C (q.eval (d j) /
      (∏ l ∈ Finset.univ.erase j, (d j - d l))) *
        (∏ l ∈ Finset.univ.erase j, (X - C (d l))) := by
    simpa only [Lagrange.interpolate_eq_sum, eval_sub, hbase, sub_zero] using heq
  simp only [neg_div, map_neg, neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add]
  linear_combination hr

end NLAlib
