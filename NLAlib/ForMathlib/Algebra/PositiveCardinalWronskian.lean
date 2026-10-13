import NLAlib.ForMathlib.Algebra.LagrangeWronskian
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Positive Wronskians from a finite cardinal partition

A positive scalar coefficient for every cross pair gives a strict sum-of-squares certificate
at every real point, including nodes.
Source: finite nodal Wronskian route to the interval peak comparison theorem.
-/

noncomputable section

open Polynomial Finset

namespace NLAlib

/-- A full partition of distinct real interpolation nodes gives strict positivity from
positive cardinal-pair coefficients. This includes evaluation at the interpolation nodes.
Source: the finite nodal sum-of-squares certificate. -/
theorem wronskian_lagrange_partition_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι → ℝ) (ht : Function.Injective t) (u v : Finset ι)
    (hdis : Disjoint u v) (hcover : u ∪ v = univ) (hun : u.Nonempty) (hvn : v.Nonempty)
    (a b : ι → ℝ)
    (hcoeff : ∀ i ∈ u, ∀ j ∈ v,
      0 < a i * b j * Lagrange.nodalWeight univ t i * Lagrange.nodalWeight univ t j * (t i - t j))
    (x : ℝ) :
    0 < (Polynomial.wronskian (∑ i ∈ u, C (a i) * Lagrange.basis univ t i)
      (∑ j ∈ v, C (b j) * Lagrange.basis univ t j)).eval x := by
  rw [wronskian_lagrange_partition_expansion univ u v t a b (subset_univ _) (subset_univ _) hdis]
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_prod, eval_sub, eval_X]
  obtain ⟨i₀, hi₀⟩ := hun
  obtain ⟨j₀, hj₀⟩ := hvn
  have hex : ∃ i ∈ u, ∃ j ∈ v, (∏ k ∈ (univ.erase i).erase j, (x - t k)) ≠ 0 := by
    by_cases hx : ∃ k, x = t k
    · obtain ⟨k, hk⟩ := hx
      have hkset : k ∈ u ∨ k ∈ v := by
        rw [← mem_union, hcover]
        exact mem_univ k
      rcases hkset with hku | hkv
      · refine ⟨k, hku, j₀, hj₀, ?_⟩
        apply prod_ne_zero_iff.mpr
        intro r hr
        have hrk : r ≠ k := (mem_erase.mp (mem_erase.mp hr).2).1
        rw [hk, sub_ne_zero]
        exact fun h => hrk (ht h.symm)
      · refine ⟨i₀, hi₀, k, hkv, ?_⟩
        apply prod_ne_zero_iff.mpr
        intro r hr
        have hrk : r ≠ k := (mem_erase.mp hr).1
        rw [hk, sub_ne_zero]
        exact fun h => hrk (ht h.symm)
    · refine ⟨i₀, hi₀, j₀, hj₀, ?_⟩
      apply prod_ne_zero_iff.mpr
      intro r hr
      exact sub_ne_zero.mpr (fun h => hx ⟨r, h⟩)
  obtain ⟨i, hi, j, hj, hp⟩ := hex
  apply sum_pos'
  · intro r hr
    exact sum_nonneg fun k hk => mul_nonneg (hcoeff r hr k hk).le (sq_nonneg _)
  · refine ⟨i, hi, ?_⟩
    apply sum_pos'
    · intro r hr
      exact mul_nonneg (hcoeff i hi r hr).le (sq_nonneg _)
    · exact ⟨j, hj, mul_pos (hcoeff i hi j hj) (sq_pos_of_ne_zero hp)⟩

end NLAlib
