import NLAlib.Polynomial.BestApproximation.AbsoluteBernsteinLimit
import NLAlib.Polynomial.BestApproximation.AbsoluteLower

/-!
# Positivity and coarse enclosure of the Bernstein constant

The finite Fejér dual lower certificate transfers to the actual scaled minimax
limit. Source: focused polynomial Bernstein reroute, Section 2.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace NLAlib

/-- The actual Bernstein constant is bounded below by the positive finite
Fejér certificate constant `1/(18π)`.
Source: focused polynomial Bernstein reroute, positive lower enclosure.
atlas: abs-best-approx-asymptotics (partial) -/
theorem one_div_eighteen_pi_le_bernsteinConstant :
    1/(18*Real.pi) ≤ bernsteinConstant := by
  have hL : Tendsto (fun n : ℕ => (1/(18*Real.pi))*((n:ℝ)/(n+1)))
      atTop (𝓝 (1/(18*Real.pi))) := by
    simpa only [mul_one] using
      (tendsto_natCast_div_add_atTop (1:ℝ)).const_mul (1/(18*Real.pi))
  apply le_of_tendsto_of_tendsto hL tendsto_nat_mul_absoluteMinimaxError
  apply Eventually.of_forall
  intro n
  have h := mul_le_mul_of_nonneg_left
    (one_div_eighteen_pi_mul_succ_le_absoluteMinimaxError n) (Nat.cast_nonneg n)
  have heq : (1/(18*Real.pi))*((n:ℝ)/(n+1)) =
      (n:ℝ)*(1/(18*Real.pi*(n+1))) := by
    field_simp
  change (1/(18*Real.pi))*((n:ℝ)/(n+1)) ≤ (n:ℝ)*absoluteMinimaxError n
  rwa [heq]

/-- Bernstein's actual polynomial minimax limit is strictly positive.
Source: focused polynomial Bernstein reroute, existence and positivity.
atlas: abs-best-approx-asymptotics (partial) -/
theorem bernsteinConstant_pos : 0 < bernsteinConstant :=
  (div_pos zero_lt_one (mul_pos (by norm_num) Real.pi_pos)).trans_le
    one_div_eighteen_pi_le_bernsteinConstant

/-- There exists a positive constant which is the full scaled native minimax
limit for absolute value on the unit interval.
Source: focused polynomial Bernstein reroute, retained Bernstein asymptotic.
atlas: abs-best-approx-asymptotics (partial) -/
theorem exists_pos_tendsto_nat_mul_absoluteMinimaxError :
    ∃ β : ℝ, 0 < β ∧
      Tendsto (fun n : ℕ => (n:ℝ)*absoluteMinimaxError n) atTop (𝓝 β) :=
  ⟨bernsteinConstant, bernsteinConstant_pos, tendsto_nat_mul_absoluteMinimaxError⟩

/-- The retained polynomial Bernstein constant has the stated coarse enclosure.
No numerical decimal or excluded Stahl rational equivalent is claimed.
Source: focused polynomial Bernstein reroute, finite dual and comparison bounds.
atlas: abs-best-approx-asymptotics (partial) -/
theorem bernsteinConstant_mem_Icc :
    bernsteinConstant ∈ Set.Icc (1/(18*Real.pi)) (2/Real.pi) :=
  ⟨one_div_eighteen_pi_le_bernsteinConstant, bernsteinConstant_le_two_div_pi⟩

end NLAlib
