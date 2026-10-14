import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Logarithmic factors in finite-order root limits
-/

noncomputable section
open Filter
open scoped Topology
namespace Real

/-- The logarithm of a positive-slope affine sequence is negligible on the
linear scale, even when finitely many initial arguments are nonpositive. -/
theorem tendsto_log_affine_nat_div_nat {A : ℝ} (hA : 0 < A) (B : ℝ) :
    Tendsto (fun n : ℕ => log (A*n+B)/(n:ℝ)) atTop (𝓝 0) := by
  have haff : Tendsto (fun n : ℕ => A*n+B) atTop atTop :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hA).atTop_add
      tendsto_const_nhds
  have h := (tendsto_pow_log_div_mul_add_atTop (1/A) (-B/A) 1
    (by positivity : (1/A:ℝ) ≠ 0)).comp haff
  convert h using 1
  funext n
  simp only [Function.comp_apply, pow_one]
  congr 1
  field_simp
  ring

/-- A logarithmic slope limit determines the positive sequence's actual real
`n`th-root limit. The order-zero value is harmless for the limit. -/
theorem tendsto_rpow_inv_nat_of_log_div_tendsto {u : ℕ → ℝ} (hu : ∀ n, 0 < u n)
    {L : ℝ} (h : Tendsto (fun n => log (u n)/(n:ℝ)) atTop (𝓝 L)) :
    Tendsto (fun n => (u n) ^ (1/(n:ℝ))) atTop (𝓝 (exp L)) := by
  have h' := continuous_exp.continuousAt.tendsto.comp h
  convert h' using 1
  funext n
  rw [rpow_def_of_pos (hu n)]
  congr 1
  ring

end Real
