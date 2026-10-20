import NLAlib.Matrix.Spectral.PositiveTraceNorm
import NLAlib.Matrix.Norms.EntryBounds
import NLAlib.ForMathlib.MeasureTheory.MatrixIntegral
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Native matrix square expectation from a bilinear variance budget

Coordinate unit probes control every expected entry square. Their sum is
the genuine real trace of the sum of matrix square expectations, which
dominates its spectral norm. Empty matrix dimensions are included.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Matrix
open scoped MatrixOrder ComplexOrder
namespace NLAlib
variable {ι n Ω : Type*} [Fintype ι] [Fintype n] [DecidableEq n] [MeasurableSpace Ω]

open scoped Matrix.Norms.L2Operator in
/-- A common actual unit-ball bilinear second-moment budget controls the
spectral norm of the actual sum of square expectations. The dimension
factor counts all matrix entries; independence and centering are not
needed for this deterministic consequence of the marginal moments.
All integrability is derived from measurability and the actual AE bound,
and empty matrix dimensions are included. -/
theorem specNorm_sum_integral_sq_le_card_sq_mul_of_bilinear_budget
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (Z : ι → Ω → Matrix n n ℂ) (hZm : ∀ i, Measurable (Z i))
    {R v : ℝ} (hR : 0≤R)
    (hZH : ∀ i, ∀ᵐ ω ∂ν i, (Z i ω).IsHermitian)
    (hZB : ∀ i, ∀ᵐ ω ∂ν i, specNorm (Z i ω)≤R)
    (hbudget : ∀ a b : EuclideanSpace ℂ n, ‖a‖≤1 → ‖b‖≤1 →
      (∑ i, ∫ ω, ‖star a.ofLp ⬝ᵥ (Z i ω *ᵥ b.ofLp)‖^2 ∂ν i)≤v) :
    specNorm (∑ i, ∫ ω, Z i ω^2 ∂ν i) ≤ (Fintype.card n : ℝ)^2*v := by
  classical
  have hsqMeas (i : ι) : Measurable (fun ω => Z i ω^2) := by
    simpa only [pow_two] using (hZm i).matrix_mul (hZm i)
  have hiSq (i : ι) : Integrable (fun ω => Z i ω^2) (ν i) := by
    apply Integrable.of_bound (hsqMeas i).aestronglyMeasurable (R^2)
    filter_upwards [hZB i] with ω hω
    exact (norm_pow_le' (Z i ω) (by norm_num : 0<(2 : ℕ))).trans (pow_le_pow_left₀ (norm_nonneg _)
      (by simpa only [specNorm_eq_norm] using hω) 2)
  have hiEntry (i : ι) (j k : n) : Integrable (fun ω => ‖Z i ω j k‖^2) (ν i) := by
    apply Integrable.of_bound
      ((((Matrix.measurable_entry j k).comp (hZm i)).norm).pow_const 2).aestronglyMeasurable (R^2)
    filter_upwards [hZB i] with ω hω
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _) hR).mpr ((norm_apply_le_specNorm _ j k).trans hω)
  have hnonneg : 0≤∑ i, ∫ ω, Z i ω^2 ∂ν i := by
    apply Finset.sum_nonneg
    intro i _
    apply integral_nonneg_of_ae
    filter_upwards [hZH i] with ω hω
    change (Z i ω^2-(0 : Matrix n n ℂ)).PosSemidef
    simpa only [sub_zero,hω.eq,pow_two] using Matrix.posSemidef_conjTranspose_mul_self (Z i ω)
  have htrace (i : ι) : (∫ ω, Z i ω^2 ∂ν i).trace.re =
      ∑ j, ∑ k, ∫ ω, ‖Z i ω j k‖^2 ∂ν i := by
    change RCLike.re (∫ ω, Z i ω^2 ∂ν i).trace = _
    rw [Matrix.re_trace_integral (hiSq i)]
    calc
      _ = ∫ ω, frobSq (Z i ω) ∂ν i := by
        apply integral_congr_ae
        filter_upwards [hZH i] with ω hω
        simpa only [hω.eq,pow_two] using (frobSq_eq_re_trace_conjTranspose_mul_self (Z i ω)).symm
      _ = ∫ ω, ∑ j, ∑ k, ‖Z i ω j k‖^2 ∂ν i := by simp_rw [frobSq_eq_sum_norm_sq]
      _ = _ := by
        rw [integral_finsetSum Finset.univ (fun j _ =>
          integrable_finsetSum Finset.univ (fun k _ => hiEntry i j k))]
        apply Finset.sum_congr rfl
        intro j _
        exact integral_finsetSum Finset.univ (fun k _ => hiEntry i j k)
  let e (j : n) : EuclideanSpace ℂ n := EuclideanSpace.single j 1
  have heNorm (j : n) : ‖e j‖≤1 := by simp [e]
  have heval (j k : n) (A : Matrix n n ℂ) :
      star (e j).ofLp ⬝ᵥ (A *ᵥ (e k).ofLp)=A j k := by simp [e]
  have hentry (j k : n) : (∑ i, ∫ ω, ‖Z i ω j k‖^2 ∂ν i)≤v := by
    simpa only [heval] using hbudget (e j) (e k) (heNorm j) (heNorm k)
  calc
    _ ≤ (∑ i, ∫ ω, Z i ω^2 ∂ν i).trace.re := hnonneg.posSemidef.specNorm_le_re_trace
    _ = ∑ i, ∑ j, ∑ k, ∫ ω, ‖Z i ω j k‖^2 ∂ν i := by
      simp only [Matrix.trace_sum,Complex.re_sum,htrace]
    _ = ∑ j, ∑ k, ∑ i, ∫ ω, ‖Z i ω j k‖^2 ∂ν i := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ ≤ ∑ _j : n, ∑ _k : n, v :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hentry j k
    _ = _ := by simp; ring

end NLAlib
