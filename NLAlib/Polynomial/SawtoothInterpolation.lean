import NLAlib.Polynomial.ChebyshevAliasing
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Odd trigonometric interpolation of the sawtooth

The odd interpolant is constructed as `sin(t) r(cos(t))`, where `r` is the actual Lagrange
interpolant of the divided sawtooth values at the interior canonical Chebyshev nodes.
This avoids an unproved trigonometric interpolation-existence premise in sharp Jackson.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Finset Real

namespace NLAlib

/-- The sine-divided Lagrange polynomial underlying the sharp Jackson sawtooth interpolant.
Source: operator rederivations `rt:sawtooth`; Arnold, numerical analysis, Section 1.2.
Atlas `jackson-lipschitz` (construction helper). -/
def sawtoothSineInterp (n : ℕ) : ℝ[X] :=
  Lagrange.interpolate (range n) (fun j => node (n + 1) (j + 1))
    (fun j => (Real.pi - (j + 1 : ℕ) * Real.pi / (n + 1)) / sin ((j + 1 : ℕ) * Real.pi / (n + 1)))

/-- The explicit odd trigonometric interpolant `τ_n(t)=sin(t) r_n(cos(t))`.
Source: operator rederivations `rt:sawtooth`; Arnold, numerical analysis, Section 1.2.
Atlas `jackson-lipschitz` (construction helper). -/
def sawtoothApprox (n : ℕ) (t : ℝ) : ℝ := sin t * (sawtoothSineInterp n).eval (cos t)

/-- Interior Chebyshev grid angles lie strictly between zero and Real.pi.
Source: canonical Chebyshev nodes; helper for sharp Jackson (`jackson-lipschitz`). -/
theorem sawtooth_angle_mem_Ioo {n j : ℕ} (hj : j < n) :
    ((j + 1 : ℕ) : ℝ) * Real.pi / (n + 1) ∈ Set.Ioo (0 : ℝ) Real.pi := by
  constructor
  · positivity
  · rw [div_lt_iff₀ (by positivity : (0 : ℝ) < n + 1)]
    have hjs : ((j + 1 : ℕ) : ℝ) < (n : ℝ) + 1 := by exact_mod_cast Nat.succ_lt_succ hj
    nlinarith [pi_pos]

/-- The sine at every interior interpolation angle is positive.
Source: canonical Chebyshev nodes; helper for sharp Jackson (`jackson-lipschitz`). -/
theorem sin_sawtooth_angle_pos {n j : ℕ} (hj : j < n) :
    0 < sin (((j + 1 : ℕ) : ℝ) * Real.pi / (n + 1)) :=
  sin_pos_of_pos_of_lt_pi (sawtooth_angle_mem_Ioo hj).1 (sawtooth_angle_mem_Ioo hj).2

/-- The interior nodal map of the divided-sine interpolation is injective.
Source: Mathlib `strictAntiOn_node`; helper for sharp Jackson (`jackson-lipschitz`). -/
theorem sawtooth_node_injOn (n : ℕ) :
    Set.InjOn (fun j => node (n + 1) (j + 1)) (range n : Set ℕ) := by
  intro i hi j hj hij
  have h := (strictAntiOn_node (n + 1)).injOn
    (mem_range.mpr (by have := mem_range.mp hi; omega))
    (mem_range.mpr (by have := mem_range.mp hj; omega)) hij
  omega

/-- The divided-sine interpolating polynomial has degree below `n`.
Source: Lagrange interpolation; helper for sharp Jackson (`jackson-lipschitz`). -/
theorem degree_sawtoothSineInterp_lt (n : ℕ) : (sawtoothSineInterp n).degree < n := by
  have h := Lagrange.degree_interpolate_lt
    (fun j => (Real.pi - (j + 1 : ℕ) * Real.pi / (n + 1)) / sin ((j + 1 : ℕ) * Real.pi / (n + 1)))
    (sawtooth_node_injOn n)
  simpa only [card_range, sawtoothSineInterp] using h

/-- The explicit odd trigonometric polynomial takes the sawtooth value at every positive
interior half-period grid point.
Source: operator rederivations `rt:sawtooth`; helper for sharp Jackson (`jackson-lipschitz`). -/
theorem sawtoothApprox_grid_eq {n j : ℕ} (hj : j < n) :
    sawtoothApprox n (((j + 1 : ℕ) : ℝ) * Real.pi / (n + 1)) =
      Real.pi - ((j + 1 : ℕ) : ℝ) * Real.pi / (n + 1) := by
  have h := Lagrange.eval_interpolate_at_node
    (fun j => (Real.pi - (j + 1 : ℕ) * Real.pi / (n + 1)) / sin ((j + 1 : ℕ) * Real.pi / (n + 1)))
    (sawtooth_node_injOn n) (mem_range.mpr hj)
  change (sawtoothSineInterp n).eval (node (n + 1) (j + 1)) = _ at h
  unfold sawtoothApprox
  simp only [node, Nat.cast_add, Nat.cast_one] at h ⊢
  rw [h]
  exact mul_div_cancel₀ _ (by simpa only [Nat.cast_add, Nat.cast_one] using (sin_sawtooth_angle_pos hj).ne')

/-- The zero-degree sawtooth interpolant vanishes identically.
Source: operator rederivations `rt:sawtooth`, degenerate case (`jackson-lipschitz`). -/
@[simp] theorem sawtoothApprox_zero (t : ℝ) : sawtoothApprox 0 t = 0 := by
  simp [sawtoothApprox, sawtoothSineInterp]

/-- The odd sawtooth interpolant vanishes at the origin.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
@[simp] theorem sawtoothApprox_at_zero (n : ℕ) : sawtoothApprox n 0 = 0 := by simp [sawtoothApprox]

/-- The odd sawtooth interpolant vanishes at Real.pi.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
@[simp] theorem sawtoothApprox_at_pi (n : ℕ) : sawtoothApprox n Real.pi = 0 := by simp [sawtoothApprox]

end NLAlib
