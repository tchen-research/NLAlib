import NLAlib.Polynomial.FunctionApproximation.ChebyshevCoefficientBounds
import NLAlib.ForMathlib.Analysis.DyadicSeries

/-!
# Absolute convergence of Lipschitz Chebyshev series

Jackson approximation and finite Parseval bounds control each dyadic frequency block
by a geometric sequence. This proves the full Lipschitz absolute-convergence assertion
without assuming almost-everywhere differentiability.
Atlas: `chebyshev-series-convergence`.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Finset Real Set Filter
open scoped Topology

namespace NLAlib

/-- A Lipschitz interval function has absolutely summable Chebyshev coefficients.
Source: Trefethen, ATAP, Theorem 3.1(b). The proof uses the already proved sharp Jackson
polynomial approximation and finite Parseval/Cauchy--Schwarz on dyadic blocks, rather
than differentiating the Lipschitz function.
atlas: chebyshev-series-convergence (partial) -/
theorem summable_abs_chebyshevCoeff_of_lipschitzOnWith {f : ℝ → ℝ} {L : NNReal}
    (hf : LipschitzOnWith L f (Icc (-1 : ℝ) 1)) :
    Summable (fun k => |chebyshevCoeff f k|) := by
  let q : ℝ := (√(2 : ℝ))⁻¹
  have hrootpos : 0 < √(2 : ℝ) := by positivity
  have hrootgt : 1 < √(2 : ℝ) := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := (inv_lt_one₀ hrootpos).mpr hrootgt
  have hsqrtpow : ∀ j : ℕ, √((2 : ℝ) ^ j) = (√(2 : ℝ)) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]
  have hblock : ∀ j, ∑ k ∈ Ico (2 ^ j) (2 ^ (j + 1)),
      |chebyshevCoeff f (k + 1)| ≤ (Real.pi * (L : ℝ)) * q ^ j := by
    intro j
    let n : ℕ := 2 ^ j
    have hn : 0 < n := by dsimp [n]; positivity
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    obtain ⟨p, hp, hE⟩ := exists_degree_le_abs_sub_eval_le_jackson_unit hf n
    let M : ℝ := Real.pi * (L : ℝ) / (2 * n)
    have hM0 : 0 ≤ M := by dsimp [M]; positivity
    have hbound : ∀ x ∈ Icc (-1 : ℝ) 1, |f x - p.eval x| ≤ M := by
      intro x hx
      refine (hE x hx).trans ?_
      dsimp [M]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      linarith
    let s : Finset ℕ := Ico n (2 * n)
    let shift : ℕ ↪ ℕ := ⟨(fun k => k + 1), fun a b h => Nat.add_right_cancel h⟩
    have hcf : ∀ k ∈ s, chebyshevCoeff (fun x => f x - p.eval x) (k + 1) =
        chebyshevCoeff f (k + 1) := by
      intro k hk
      rw [chebyshevCoeff_sub hf.continuousOn p.continuous.continuousOn,
        chebyshevCoeff_eval_eq_zero_of_degree_lt hp (by
          have hk' : n ≤ k := (mem_Ico.mp hk).1
          omega), sub_zero]
    have hfinite := sum_abs_chebyshevCoeff_le_sqrt_card_mul
      (hf.continuousOn.sub p.continuous.continuousOn) hM0 hbound (s.map shift)
    rw [sum_map] at hfinite
    change (∑ k ∈ s, |chebyshevCoeff (fun x => f x - p.eval x) (k + 1)|) ≤
      2 * √((s.map shift).card : ℝ) * M at hfinite
    have hsum : (∑ k ∈ s, |chebyshevCoeff (fun x => f x - p.eval x) (k + 1)|) =
        ∑ k ∈ s, |chebyshevCoeff f (k + 1)| := by
      apply sum_congr rfl
      intro k hk
      rw [hcf k hk]
    rw [hsum] at hfinite
    have hcard : (s.map shift).card = n := by simp [s]; omega
    rw [hcard] at hfinite
    have hupper : 2 ^ (j + 1) = 2 * n := by dsimp [n]; rw [pow_succ]; omega
    rw [hupper]
    change (∑ k ∈ s, |chebyshevCoeff f (k + 1)|) ≤ _
    refine hfinite.trans_eq ?_
    have hncast : (n : ℝ) = (2 : ℝ) ^ j := by simp [n]
    have hroot : √(n : ℝ) = √(2 : ℝ) ^ j := by rw [hncast, hsqrtpow]
    have hden : (n : ℝ) = (√(2 : ℝ) ^ j) ^ 2 := by
      rw [← hroot, Real.sq_sqrt hnR.le]
    dsimp [M, q]
    rw [hroot, hden, inv_pow]
    field_simp
  have hs := summable_of_dyadic_block_sum_le_geometric
    (a := fun k => |chebyshevCoeff f (k + 1)|) (fun _ => abs_nonneg _)
    (C := Real.pi * (L : ℝ)) (by positivity) hq0 hq1 hblock
  exact (summable_nat_add_iff 1).mp hs

/-- Lipschitz functions have their genuine Chebyshev expansion at every point of `[-1,1]`.
Source: Trefethen, ATAP, Theorem 3.1.
atlas: chebyshev-series-convergence (partial) -/
theorem hasSum_chebyshevCoeff_mul_eval_T_of_lipschitzOnWith {f : ℝ → ℝ} {L : NNReal}
    (hf : LipschitzOnWith L f (Icc (-1 : ℝ) 1)) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun k => chebyshevCoeff f k * (T ℝ (k : ℤ)).eval x) (f x) :=
  hasSum_chebyshevCoeff_mul_eval_T hf.continuousOn (summable_abs_chebyshevCoeff_of_lipschitzOnWith hf) hx

/-- The genuine Chebyshev truncations of any Lipschitz interval function converge uniformly.
Source: Trefethen, ATAP, Theorem 3.1.
atlas: chebyshev-series-convergence -/
theorem tendstoUniformlyOn_chebyshevTrunc_of_lipschitzOnWith {f : ℝ → ℝ} {L : NNReal}
    (hf : LipschitzOnWith L f (Icc (-1 : ℝ) 1)) :
    TendstoUniformlyOn (fun n x => (chebyshevTrunc f n).eval x) f atTop (Icc (-1 : ℝ) 1) :=
  tendstoUniformlyOn_chebyshevTrunc hf.continuousOn (summable_abs_chebyshevCoeff_of_lipschitzOnWith hf)

end NLAlib
