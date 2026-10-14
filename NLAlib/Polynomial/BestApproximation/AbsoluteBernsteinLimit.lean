import NLAlib.Polynomial.BestApproximation.BernsteinDegreeTransfer
import NLAlib.ForMathlib.Analysis.DegreeTransferLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Existence of the polynomial Bernstein constant

The native minimax error has a scaled limit. The proof uses the finite
degree-transfer inequality and a scalar liminf subsequence, without constructing
an entire-function limit. Source: focused polynomial Bernstein reroute, Section 2.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace NLAlib

/-- The actual Bernstein constant is the liminf of the scaled native even-degree
absolute-value minimax errors. Its full-sequence limit is proved below. -/
def bernsteinConstant : ℝ :=
  liminf (fun m : ℕ => ((2*m:ℕ):ℝ)*absoluteMinimaxError (2*m)) atTop

/-- The finite degree-transfer remainder tends to zero as the target degree
increases, for every fixed `α<1`. Its polynomial prefactor does not prevent
exponential decay. Source: focused polynomial Bernstein reroute. -/
theorem tendsto_bernsteinDegreeTransferRemainder {α : ℝ} (hα1 : α < 1) :
    Tendsto (bernsteinDegreeTransferRemainder α) atTop (𝓝 0) := by
  let c := bernsteinDegreeTransferDecay α
  let t := (1-α)/2
  let C := 12*Real.exp 1/(Real.pi*α*(Real.exp t-1))
  have hc : 0 < c := bernsteinDegreeTransferDecay_pos hα1
  have h0 : Tendsto (fun N : ℕ => Real.exp (-c*N)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.rpow_zero, one_mul] using!
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 c hc).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have h2 : Tendsto (fun N : ℕ => (N:ℝ)^2*Real.exp (-c*N)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.rpow_two] using!
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 c hc).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := (h0.add (h2.const_mul ((α*Real.cosh t)^2))).const_mul C
  simp only [mul_zero, add_zero] at h
  convert! h using 1
  funext N
  dsimp [bernsteinDegreeTransferRemainder, c, C, t]
  ring

private theorem scaled_absoluteMinimaxError_even_le (m : ℕ) :
    ((2*m:ℕ):ℝ)*absoluteMinimaxError (2*m) ≤ 2/Real.pi := by
  have h := (le_div_iff₀ (by positivity : (0:ℝ)<Real.pi*(2*m+1))).mp
    (absoluteMinimaxError_even_le m)
  apply (le_div_iff₀ Real.pi_pos).mpr
  have hp := mul_nonneg (absoluteMinimaxError_nonneg (2*m)) Real.pi_pos.le
  push_cast
  nlinarith

private theorem absoluteMinimaxError_degreeTransfer_eventually :
    ∀ α : ℝ, 0<α → α<1 → ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧
      ∀ N : ℕ, 1≤N → ∀ᶠ m : ℕ in atTop,
        (N:ℝ)*absoluteMinimaxError N ≤
          ((2*m:ℕ):ℝ)*absoluteMinimaxError (2*m)/α+r N := by
  intro α hα0 hα1
  refine ⟨bernsteinDegreeTransferRemainder α, tendsto_bernsteinDegreeTransferRemainder hα1, ?_⟩
  intro N hN
  have hm : Tendsto (fun m : ℕ => ((2*m:ℕ):ℝ)) atTop atTop := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num : (0:ℝ)<2)
  filter_upwards [hm.eventually_ge_atTop
    (2*max 1 ((α*N*Real.cosh ((1-α)/2))^2))] with m hthreshold
  exact mul_absoluteMinimaxError_le_degreeTransfer hα0 hα1 hN hthreshold

/-- The actual scaled polynomial minimax error for absolute value converges at
every integer degree to the Bernstein constant.
Source: focused polynomial Bernstein reroute, finite degree-transfer closure.
atlas: abs-best-approx-asymptotics (partial) -/
theorem tendsto_nat_mul_absoluteMinimaxError :
    Tendsto (fun n : ℕ => (n:ℝ)*absoluteMinimaxError n) atTop (𝓝 bernsteinConstant) := by
  apply tendsto_nat_mul_of_even_tendsto absoluteMinimaxError_antitone
  exact tendsto_even_sequence_of_degree_transfer
    (fun n => (n:ℝ)*absoluteMinimaxError n)
    (fun n => mul_nonneg (by positivity) (absoluteMinimaxError_nonneg _))
    scaled_absoluteMinimaxError_even_le absoluteMinimaxError_degreeTransfer_eventually

/-- The actual Bernstein constant is nonnegative.
Source: native minimax nonnegativity and the proved scaled limit. -/
theorem bernsteinConstant_nonneg : 0 ≤ bernsteinConstant :=
  le_of_tendsto_of_tendsto tendsto_const_nhds tendsto_nat_mul_absoluteMinimaxError
    (Eventually.of_forall fun n => mul_nonneg (by positivity) (absoluteMinimaxError_nonneg n))

/-- The explicit Chebyshev comparison bounds the actual Bernstein constant by
`2/π`. Source: focused polynomial Bernstein reroute, coarse finite enclosure.
atlas: abs-best-approx-asymptotics (partial) -/
theorem bernsteinConstant_le_two_div_pi : bernsteinConstant ≤ 2/Real.pi := by
  have ht : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ => by dsimp; omega) tendsto_id
  have h := tendsto_nat_mul_absoluteMinimaxError.comp ht
  exact le_of_tendsto h (Eventually.of_forall scaled_absoluteMinimaxError_even_le)

end NLAlib
