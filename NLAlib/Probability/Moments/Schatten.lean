import NLAlib.Matrix.Norms.SchattenComparison
import NLAlib.Matrix.Norms.SchattenContinuity
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Integrability of finite Schatten moments

A finite positive-exponent Schatten norm is controlled by a fixed dimensional
constant times the spectral norm. Actual matrix Lp assumptions therefore give
genuine integrability of every requested finite Schatten moment.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NLAlib

variable {Ω 𝕜 m n : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [RCLike 𝕜]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Every fixed positive-exponent finite Schatten norm of an Lp random matrix
is itself Lp. The claim uses actual matrix Lp and derives the Schatten moment;
no moment-finiteness certificate is assumed. -/
theorem memLp_schattenNormReal {p : ℝ≥0∞} (D : Ω → Matrix m n 𝕜)
    (hD : MemLp D p μ) {q : ℝ} (hq : 0 < q) :
    MemLp (fun ω => schattenNormReal (D ω) q) p μ := by
  let c : ℝ := (Fintype.card n : ℝ) ^ (1 / q)
  refine (hD.norm.const_mul c).mono'
    ((continuous_schattenNormReal hq).comp_aestronglyMeasurable hD.aestronglyMeasurable) ?_
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (schattenNormReal_nonneg _ _)]
  calc
    schattenNormReal (D ω) q ≤ (Matrix.rank (D ω) : ℝ) ^ (1 / q) * specNorm (D ω) :=
      schattenNormReal_le_rank_rpow_mul_specNorm _ hq
    _ ≤ c * ‖D ω‖ := by
      rw [← specNorm_eq_norm]
      apply mul_le_mul_of_nonneg_right _ (specNorm_nonneg _)
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (D ω).rank_le_card_width)
        (one_div_nonneg.mpr hq.le)

open scoped Matrix.Norms.L2Operator in
/-- Finite matrix Lp at a positive natural exponent implies a genuine
integrable power of any fixed positive-exponent Schatten norm. -/
theorem integrable_schattenNormReal_pow_of_memLp
    (D : Ω → Matrix m n 𝕜) {p : ℕ} (hD : MemLp D p μ) (hp : p ≠ 0)
    {q : ℝ} (hq : 0 < q) :
    Integrable (fun ω => schattenNormReal (D ω) q ^ p) μ := by
  have h := (memLp_schattenNormReal D hD hq).integrable_norm_pow hp
  simpa only [Real.norm_eq_abs, abs_of_nonneg (schattenNormReal_nonneg _ _)] using h

end NLAlib
