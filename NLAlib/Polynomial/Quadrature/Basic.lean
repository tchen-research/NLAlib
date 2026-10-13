import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousMap.Algebra

/-! # Interpolatory quadrature vocabulary

The Clenshaw–Curtis rule is the integral of the actual polynomial interpolant
at the Chebyshev endpoint grid. The scalar moments are the Lebesgue Chebyshev moments.
-/
noncomputable section
namespace NLAlib

/-- The Lebesgue moment of the degree-`k` first-kind Chebyshev polynomial.
Source: Trefethen, ATAP, Theorem 19.2. -/
def chebyshevMoment (k : ℕ) : ℝ := if Even k then 2 / (1 - (k : ℝ) ^ 2) else 0

/-- The `(n+1)`-node Clenshaw–Curtis rule integrates the actual endpoint-grid interpolant.
Source: Trefethen, ATAP, Chapter 19. The usual endpoint grid is used when `n≥1`. -/
def clenshawCurtisRule (n : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, (Lagrange.interpolate (Finset.range (n + 1))
    (Polynomial.Chebyshev.node n) (f ∘ Polynomial.Chebyshev.node n)).eval x

/-- The actual Clenshaw–Curtis weight is the integral of its endpoint-grid
Lagrange cardinal polynomial. Source: Trefethen, ATAP, Chapter 19. -/
def clenshawCurtisWeight (n j : ℕ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, (Lagrange.basis (Finset.range (n + 1))
    (Polynomial.Chebyshev.node n) j).eval x

/-- The Clenshaw–Curtis rule as its finite weighted linear functional on
continuous unit-interval functions. Source: Trefethen, ATAP, Chapter 19. -/
def clenshawCurtisLinearMap (n : ℕ) :
    C(Set.Icc (-1 : ℝ) 1, ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∑ j ∈ Finset.range (n + 1), clenshawCurtisWeight n j *
    f ⟨Polynomial.Chebyshev.node n j, Polynomial.Chebyshev.node_mem_Icc⟩
  map_add' f g := by
    simp only [ContinuousMap.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- An explicit sufficient cutoff for the eventual corrected Clenshaw–Curtis BV
bound: `ν(ν+1)/2 + ceil((105/16)ν2^ν)`. The ceiling is written with exact natural
arithmetic. Source: focused reroutes, Theorem “An explicit eventual bound”. -/
def quadratureBvThreshold (ν : ℕ) : ℕ :=
  ν * (ν + 1) / 2 + (105 * ν * 2 ^ ν + 15) / 16

end NLAlib
