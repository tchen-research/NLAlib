import NLAlib.Polynomial.BestApproximation.GapWeightSigns
import NLAlib.ForMathlib.Algebra.PositiveCardinalWronskian
import Mathlib.Tactic.Ring

/-!
# The strict Wronskian sign of actual interval peak polynomials

A direct nodal sum of squares proves the sign without auxiliary interlacing roots.
Source: focused rederivations, `polyretry:wronskian-sos`; the cardinal-pair expansion gives
an alternative finite certificate for the same Wronskian.
-/

noncomputable section

open Polynomial Finset

namespace NLAlib

private def outsideNodes {n : ℕ} (i j : Fin (n + 1)) : Finset (Fin (n + 2)) :=
  univ.filter (fun k => k.val ≤ i.val ∨ j.val < k.val)

private def insideNodes {n : ℕ} (i j : Fin (n + 1)) : Finset (Fin (n + 2)) :=
  univ.filter (fun k => i.val < k.val ∧ k.val ≤ j.val)

private theorem nodePartition {n : ℕ} (i j : Fin (n + 1)) :
    Disjoint (outsideNodes i j) (insideNodes i j) ∧ outsideNodes i j ∪ insideNodes i j = univ := by
  constructor
  · apply disjoint_left.mpr
    intro k hk hk'
    simp only [outsideNodes, insideNodes, mem_filter, mem_univ, true_and] at hk hk'
    omega
  · ext k
    simp only [outsideNodes, insideNodes, mem_union, mem_filter, mem_univ, true_and]
    constructor
    · intro hk; trivial
    · intro hk
      by_cases hki : k.val ≤ i.val
      · exact Or.inl (Or.inl hki)
      · by_cases hkj : j.val < k.val
        · exact Or.inl (Or.inr hkj)
        · exact Or.inr ⟨by omega, by omega⟩

private theorem gap_pair_cross_coefficient_pos {n : ℕ} {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i j : Fin (n + 1)) (hij : i < j)
    {a b : Fin (n + 2)} (ha : a ∈ outsideNodes i j) (hb : b ∈ insideNodes i j) :
    0 < interpolationGapSign n i a * interpolationGapSign n i b *
      Lagrange.nodalWeight univ (canonicalIntervalNodes n t) a *
      Lagrange.nodalWeight univ (canonicalIntervalNodes n t) b *
      (canonicalIntervalNodes n t a - canonicalIntervalNodes n t b) := by
  have hmono : StrictMono (canonicalIntervalNodes n t) := ht
  have hwa : 0 < |Lagrange.nodalWeight univ (canonicalIntervalNodes n t) a| := abs_pos.mpr
    (Lagrange.nodalWeight_ne_zero hmono.injective.injOn (mem_univ a))
  have hwb : 0 < |Lagrange.nodalWeight univ (canonicalIntervalNodes n t) b| := abs_pos.mpr
    (Lagrange.nodalWeight_ne_zero hmono.injective.injOn (mem_univ b))
  have heps : ((-1 : ℝ) ^ (i.val + n + 1)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  simp only [outsideNodes, insideNodes, mem_filter, mem_univ, true_and] at ha hb
  have hbni : ¬b.val ≤ i.val := by omega
  have hrewrite : interpolationGapSign n i a * interpolationGapSign n i b *
      Lagrange.nodalWeight univ (canonicalIntervalNodes n t) a *
      Lagrange.nodalWeight univ (canonicalIntervalNodes n t) b =
    (interpolationGapSign n i a * Lagrange.nodalWeight univ (canonicalIntervalNodes n t) a) *
    (interpolationGapSign n i b * Lagrange.nodalWeight univ (canonicalIntervalNodes n t) b) := by ring
  rw [hrewrite, interpolationGapSign_mul_nodalWeight hmono i a,
    interpolationGapSign_mul_nodalWeight hmono i b, if_neg hbni]
  rcases ha with hale | halt
  · rw [if_pos hale]
    have hab : a < b := by exact Fin.mk_lt_mk.mpr (by omega)
    have hd := sub_neg.mpr (hmono hab)
    have hscalar : (-1 : ℝ) ^ (i.val + n + 1) *
        |Lagrange.nodalWeight univ (canonicalIntervalNodes n t) a| *
        ((-1 : ℝ) ^ (i.val + n + 1) * -|Lagrange.nodalWeight univ (canonicalIntervalNodes n t) b|) =
        -(|Lagrange.nodalWeight univ (canonicalIntervalNodes n t) a| *
          |Lagrange.nodalWeight univ (canonicalIntervalNodes n t) b|) := by
      calc
        _ = -(((-1 : ℝ) ^ (i.val + n + 1)) ^ 2) *
          (|Lagrange.nodalWeight univ (canonicalIntervalNodes n t) a| *
            |Lagrange.nodalWeight univ (canonicalIntervalNodes n t) b|) := by ring
        _ = _ := by rw [heps]; ring
    rw [hscalar]
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos (mul_pos hwa hwb)) hd
  · have hani : ¬a.val ≤ i.val := by have := hij; omega
    rw [if_neg hani]
    have hba : b < a := by exact Fin.mk_lt_mk.mpr (by omega)
    have hd := sub_pos.mpr (hmono hba)
    have hscalar : (-1 : ℝ) ^ (i.val + n + 1) *
        -|Lagrange.nodalWeight univ (canonicalIntervalNodes n t) a| *
        ((-1 : ℝ) ^ (i.val + n + 1) * -|Lagrange.nodalWeight univ (canonicalIntervalNodes n t) b|) =
        |Lagrange.nodalWeight univ (canonicalIntervalNodes n t) a| *
          |Lagrange.nodalWeight univ (canonicalIntervalNodes n t) b| := by
      calc
        _ = (((-1 : ℝ) ^ (i.val + n + 1)) ^ 2) *
          (|Lagrange.nodalWeight univ (canonicalIntervalNodes n t) a| *
            |Lagrange.nodalWeight univ (canonicalIntervalNodes n t) b|) := by ring
        _ = _ := by rw [heps, one_mul]
    rw [hscalar]
    exact mul_pos (mul_pos hwa hwb) hd

/-- The actual gap polynomials have the strict pairwise Wronskian sign at every real point.
Source: focused rederivations, `polyretry:wronskian-sos`, via a finite nodal square certificate.
atlas: lebesgue-constant-lower-bound (partial) -/
theorem interpolationGapPolynomial_wronskian_sign {n : ℕ} {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i j : Fin (n + 1)) (hij : i < j) (x : ℝ) :
    0 < (-1 : ℝ) ^ (j.val - i.val) *
      ((interpolationGapPolynomial n t i).derivative.eval x * (interpolationGapPolynomial n t j).eval x -
        (interpolationGapPolynomial n t i).eval x * (interpolationGapPolynomial n t j).derivative.eval x) := by
  let nodes := canonicalIntervalNodes n t
  let f := fun k => C (interpolationGapSign n i k) * Lagrange.basis univ nodes k
  let U : ℝ[X] := ∑ k ∈ outsideNodes i j, f k
  let V : ℝ[X] := ∑ k ∈ insideNodes i j, f k
  let s : ℝ := (-1 : ℝ) ^ (j.val - i.val)
  have hv : StrictMono nodes := ht
  have hpart := nodePartition i j
  have hUn : (outsideNodes i j).Nonempty := ⟨0, by simp [outsideNodes]⟩
  have hVn : (insideNodes i j).Nonempty := ⟨i.succ, by
    simp only [insideNodes, mem_filter, mem_univ, true_and, Fin.val_succ]
    have hij' : i.val < j.val := hij
    omega⟩
  have hpos : 0 < (Polynomial.wronskian U V).eval x :=
    wronskian_lagrange_partition_pos nodes hv.injective _ _ hpart.1 hpart.2 hUn hVn
      (interpolationGapSign n i) (interpolationGapSign n i)
      (fun a ha b hb => gap_pair_cross_coefficient_pos ht i j hij ha hb) x
  have hi : interpolationGapPolynomial n t i = U + V := by
    unfold interpolationGapPolynomial
    rw [Lagrange.interpolate_apply]
    change (∑ k ∈ univ, f k) = U + V
    rw [← hpart.2, sum_union hpart.1]
  have hj : C s * interpolationGapPolynomial n t j = U - V := by
    unfold interpolationGapPolynomial
    rw [Lagrange.interpolate_apply, mul_sum]
    have hc : ∀ k, C s * (C (interpolationGapSign n j k) * Lagrange.basis univ nodes k) =
        if k ∈ insideNodes i j then -f k else f k := by
      intro k
      rw [← mul_assoc, ← map_mul, interpolationGapSign_relative hv i j hij.le k]
      simp only [insideNodes, mem_filter, mem_univ, true_and]
      split_ifs <;> simp [f, map_neg]
    rw [sum_congr rfl (fun k hk => hc k), ← hpart.2, sum_union hpart.1]
    have hout : ∀ k ∈ outsideNodes i j, (if k ∈ insideNodes i j then -f k else f k) = f k := by
      intro k hk
      exact if_neg (disjoint_left.mp hpart.1 hk)
    have hin : ∀ k ∈ insideNodes i j, (if k ∈ insideNodes i j then -f k else f k) = -f k := by
      intro k hk; exact if_pos hk
    rw [sum_congr rfl hout, sum_congr rfl hin, sum_neg_distrib, ← sub_eq_add_neg]
  have hidentity : C s * Polynomial.wronskian (interpolationGapPolynomial n t i)
      (interpolationGapPolynomial n t j) = -C (2 : ℝ) * Polynomial.wronskian U V := by
    have hconst := wronskian_C_mul_C_mul (1 : ℝ) s
      (interpolationGapPolynomial n t i) (interpolationGapPolynomial n t j)
    simp only [map_one, one_mul] at hconst
    rw [← hconst, hi, hj]
    simp only [Polynomial.wronskian, derivative_add, derivative_sub, map_ofNat]
    ring
  have heval := congrArg (fun p : ℝ[X] => p.eval x) hidentity
  simp only [eval_mul, eval_C, eval_neg, Polynomial.wronskian, eval_sub] at heval
  have hpos' : 0 < U.eval x * V.derivative.eval x - U.derivative.eval x * V.eval x := by
    simpa only [Polynomial.wronskian, eval_sub, eval_mul] using hpos
  change 0 < s * _
  nlinarith

end NLAlib
