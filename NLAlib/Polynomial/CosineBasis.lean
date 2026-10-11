import NLAlib.Polynomial.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Finite cosine expansions through the Chebyshev first-kind basis

Mathlib's actual degree-indexed Chebyshev polynomial sequence spans every finite degree
space, supplying the coefficients of the fixed Jackson convolution polynomial.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Finset Real

namespace NLAlib

/-- Every real polynomial of degree at most `n` has a finite first-kind Chebyshev expansion.
Source: Rivlin, Chebyshev Polynomials, Chapter 1; Mathlib polynomial-sequence spanning.
This is the genuine cosine-basis construction used by sharp `jackson-lipschitz`. -/
theorem exists_sum_smul_T_eq_of_degree_le {p : ℝ[X]} {n : ℕ} (hp : p.degree ≤ n) :
    ∃ c : ℕ → ℝ, (∑ j ∈ range (n + 1), c j • T ℝ (j : ℤ)) = p := by
  let S := chebyshevTsequence ℝ
  have hCoeff : ∀ i ≤ n, IsUnit (S i).leadingCoeff := by
    intro i hi
    exact isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr (S.ne_zero i))
  have hmem : p ∈ Polynomial.degreeLE ℝ n := Polynomial.mem_degreeLE.mpr hp
  rw [← S.span_degreeLE hCoeff] at hmem
  have hset : Set.Iic n = (range (n + 1) : Set ℕ) := by ext i; simp
  rw [hset] at hmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' ℝ).mp hmem
  exact ⟨c, hc⟩

/-- Evaluating the actual finite first-kind expansion gives a finite cosine series.
Source: Rivlin, Chebyshev Polynomials, Chapter 1; helper for sharp `jackson-lipschitz`. -/
theorem exists_cosine_expansion_of_degree_le {p : ℝ[X]} {n : ℕ} (hp : p.degree ≤ n) :
    ∃ c : ℕ → ℝ, ∀ t : ℝ,
      p.eval (cos t) = ∑ j ∈ range (n + 1), c j * cos ((j : ℝ) * t) := by
  obtain ⟨c, hc⟩ := exists_sum_smul_T_eq_of_degree_le hp
  refine ⟨c, fun t => ?_⟩
  rw [← hc, eval_finsetSum]
  simp only [eval_smul, smul_eq_mul, T_real_cos, Int.cast_natCast]

end NLAlib
