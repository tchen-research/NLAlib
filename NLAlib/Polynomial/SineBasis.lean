import NLAlib.Polynomial.SawtoothInterpolation
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Finite sine expansions through the Chebyshev second-kind basis

Mathlib's polynomial-sequence spanning theorem supplies the actual coefficients of
`sin(t) p(cos(t))`, with frequencies bounded by the degree of `p` plus one.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Finset Real

namespace NLAlib

/-- Chebyshev second-kind polynomials form a genuine degree-indexed polynomial sequence.
Source: Rivlin, Chebyshev Polynomials, Chapter 1; helper for sharp `jackson-lipschitz`. -/
def chebyshevUSequence : Polynomial.Sequence ℝ where
  elems' n := U ℝ (n : ℤ)
  degree_eq' n := degree_U_natCast ℝ n

/-- Every real polynomial of degree below `n` has a finite second-kind Chebyshev expansion.
Source: Rivlin, Chebyshev Polynomials, Chapter 1; Mathlib polynomial-sequence spanning.
This is the genuine sine-basis construction needed by sharp `jackson-lipschitz`. -/
theorem exists_sum_smul_U_eq_of_degree_lt {p : ℝ[X]} {n : ℕ} (hp : p.degree < n) :
    ∃ c : ℕ → ℝ, (∑ j ∈ range n, c j • U ℝ (j : ℤ)) = p := by
  let S := chebyshevUSequence
  have hCoeff : ∀ i < n, IsUnit (S i).leadingCoeff := by
    intro i hi
    exact isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr (S.ne_zero i))
  have hmem : p ∈ Polynomial.degreeLT ℝ n := Polynomial.mem_degreeLT.mpr hp
  rw [← S.span_degreeLT hCoeff] at hmem
  have hset : Set.Iio n = (range n : Set ℕ) := by ext i; simp
  rw [hset] at hmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' ℝ).mp hmem
  exact ⟨c, hc⟩

/-- A degree-bounded polynomial times `sin(t)` is a finite sine series with no frequency
above the degree cutoff.
Source: Rivlin, Chebyshev Polynomials, Chapter 1, `sin(t)U_j(cos(t))=sin((j+1)t)`;
helper for sharp `jackson-lipschitz`. -/
theorem exists_sine_expansion_of_degree_lt {p : ℝ[X]} {n : ℕ} (hp : p.degree < n) :
    ∃ c : ℕ → ℝ, ∀ t : ℝ,
      sin t * p.eval (cos t) = ∑ j ∈ range n, c j * sin (((j + 1 : ℕ) : ℝ) * t) := by
  obtain ⟨c, hc⟩ := exists_sum_smul_U_eq_of_degree_lt hp
  refine ⟨c, fun t => ?_⟩
  rw [← hc, eval_finsetSum, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [eval_smul, smul_eq_mul]
  have h := U_real_cos t (j : ℤ)
  have heq : sin t * (c j * (U ℝ (j : ℤ)).eval (cos t)) =
      c j * ((U ℝ (j : ℤ)).eval (cos t) * sin t) := by ring
  rw [heq, h]
  norm_cast

/-- The actual odd sawtooth interpolant has a finite sine expansion of degree at most `n`.
Source: operator rederivations `rt:sawtooth`; helper for sharp `jackson-lipschitz`. -/
theorem exists_sine_expansion_sawtoothApprox (n : ℕ) :
    ∃ c : ℕ → ℝ, ∀ t : ℝ,
      sawtoothApprox n t = ∑ j ∈ range n, c j * sin (((j + 1 : ℕ) : ℝ) * t) :=
  exists_sine_expansion_of_degree_lt (degree_sawtoothSineInterp_lt n)

end NLAlib
