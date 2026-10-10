import NLAlib.Matrix.GramSoftMin
import NLAlib.Matrix.Measurable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Measurability of the Gram resolvent calculus

The total matrix inverse, finite trace powers, and real scalar powers give
entrywise measurability of the resolvent approximation and both Gram
derivatives. Positivity is not needed for these measurable-map statements.

Atlas: `wishart-lambda-min-tail` (operator calculus helpers).
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
/-- Entries of a total inverse of an entrywise measurable real matrix map
are measurable. Source: determinant/adjugate inverse formula; atlas
`wishart-lambda-min-tail` (helper). -/
theorem measurable_inv_entry_of {A : Ω → Matrix ι ι ℝ}
    (hA : ∀ i j, Measurable fun x => A x i j) (i j : ι) :
    Measurable fun x => (A x)⁻¹ i j := by
  have harray : Measurable (fun x => fun i j => A x i j) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hA i j
  have hc : Continuous (fun M : ι → ι → ℝ => Matrix.of M) := continuous_id
  have hdet : Measurable fun x => (A x).det := hc.matrix_det.measurable.comp harray
  have hadj : Measurable fun x => (A x).adjugate i j :=
    (hc.matrix_adjugate.matrix_elem i j).measurable.comp harray
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact hdet.inv.mul hadj

omit [Fintype κ] [DecidableEq κ] in
/-- Every finite power of an entrywise measurable matrix map is entrywise
measurable. Source: finite multiplication; atlas `wishart-lambda-min-tail` (helper). -/
theorem measurable_pow_entry_of {A : Ω → Matrix ι ι ℝ}
    (hA : ∀ i j, Measurable fun x => A x i j) (n : ℕ) (i j : ι) :
    Measurable fun x => (A x ^ n) i j := by
  induction n generalizing i j with
  | zero => simpa only [pow_zero] using measurable_const
  | succ n ih =>
    simp only [pow_succ]
    exact measurable_mul_entry_of (fun a b => ih a b) hA i j

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- The trace of an entrywise measurable matrix map is measurable.
Source: finite diagonal sum; atlas `wishart-lambda-min-tail` (helper). -/
theorem measurable_trace_of_entries {A : Ω → Matrix ι ι ℝ}
    (hA : ∀ i j, Measurable fun x => A x i j) : Measurable fun x => Matrix.trace (A x) := by
  exact Finset.measurable_sum _ fun i _ => hA i i

omit [Fintype κ] [DecidableEq κ] in
/-- The resolvent minimum is measurable for an entrywise measurable matrix
map. Source: inverse/trace-power formula; atlas `wishart-lambda-min-tail` (helper). -/
theorem measurable_inversePowerSoftMin_of_entries {A : Ω → Matrix ι ι ℝ}
    (hA : ∀ i j, Measurable fun x => A x i j) (n : ℕ) :
    Measurable fun x => inversePowerSoftMin n (A x) := by
  exact (measurable_trace_of_entries (measurable_pow_entry_of (measurable_inv_entry_of hA) n)).pow_const _

omit [Fintype κ] [DecidableEq κ] in
/-- Entries of the resolvent gradient weight are measurable.
Source: inverse/trace-power formula; atlas `wishart-lambda-min-tail` (helper). -/
theorem measurable_inversePowerSoftMinWeight_entry_of {A : Ω → Matrix ι ι ℝ}
    (hA : ∀ i j, Measurable fun x => A x i j) (n : ℕ) (i j : ι) :
    Measurable fun x => inversePowerSoftMinWeight n (A x) i j := by
  have hR := measurable_inv_entry_of hA
  have hT := measurable_trace_of_entries (measurable_pow_entry_of hR n)
  exact (hT.pow_const _).mul (measurable_pow_entry_of hR (n + 1) i j)

omit [Fintype κ] [DecidableEq κ] in
/-- The first resolvent directional derivative is measurable for two
entrywise measurable matrix maps. Source: trace formula; atlas
`wishart-lambda-min-tail` (helper). -/
theorem measurable_inversePowerSoftMinFirst_of_entries {A B : Ω → Matrix ι ι ℝ}
    (hA : ∀ i j, Measurable fun x => A x i j)
    (hB : ∀ i j, Measurable fun x => B x i j) (n : ℕ) :
    Measurable fun x => inversePowerSoftMinFirst n (A x) (B x) := by
  have hR := measurable_inv_entry_of hA
  have hT := measurable_trace_of_entries (measurable_pow_entry_of hR n)
  have hU := measurable_trace_of_entries
    (measurable_mul_entry_of (measurable_pow_entry_of hR (n + 1)) hB)
  exact (hT.pow_const _).mul hU

omit [Fintype κ] [DecidableEq κ] in
/-- The second resolvent directional derivative is measurable for two
entrywise measurable matrix maps. Source: finite Hessian kernel formula;
atlas `wishart-lambda-min-tail` (helper). -/
theorem measurable_inversePowerSoftMinSecond_of_entries {A B : Ω → Matrix ι ι ℝ}
    (hA : ∀ i j, Measurable fun x => A x i j)
    (hB : ∀ i j, Measurable fun x => B x i j) (n : ℕ) :
    Measurable fun x => inversePowerSoftMinSecond n (A x) (B x) := by
  have hR := measurable_inv_entry_of hA
  have hT := measurable_trace_of_entries (measurable_pow_entry_of hR n)
  have hU := measurable_trace_of_entries
    (measurable_mul_entry_of (measurable_pow_entry_of hR (n + 1)) hB)
  have hK : Measurable fun x => inversePowerHessianKernel (A x)⁻¹ (B x) n := by
    exact Finset.measurable_sum _ fun a _ => measurable_trace_of_entries
      (measurable_mul_entry_of (measurable_mul_entry_of
        (measurable_mul_entry_of (measurable_pow_entry_of hR (n - a + 1)) hB)
        (measurable_pow_entry_of hR (a + 1))) hB)
  exact ((measurable_const.mul (hT.pow_const _)).mul (hU.pow_const 2)).sub
    ((hT.pow_const _).mul hK)

omit [DecidableEq κ] in
/-- Every entry of a regularized Gram matrix is measurable on matrix
arrays. Source: finite coordinate polynomials; atlas `wishart-lambda-min-tail` (helper). -/
theorem measurable_regularizedGram_entry (ε : ℝ) (i j : ι) :
    Measurable fun G : ι → κ → ℝ => regularizedGram ε (Matrix.of G) i j := by
  have hc : Continuous fun G : ι → κ → ℝ => regularizedGram ε (Matrix.of G) := by
    unfold regularizedGram
    fun_prop
  exact (hc.matrix_elem i j).measurable

omit [DecidableEq κ] in
/-- The resolvent regularized Gram minimum is measurable on matrix arrays.
Source: inverse/trace-power formula; atlas `wishart-lambda-min-tail` (helper). -/
theorem measurable_inversePowerSoftMin_regularizedGram (n : ℕ) (ε : ℝ) :
    Measurable fun G : ι → κ → ℝ => inversePowerSoftMin n (regularizedGram ε (Matrix.of G)) :=
  measurable_inversePowerSoftMin_of_entries (measurable_regularizedGram_entry ε) n

omit [DecidableEq κ] in
/-- Each actual Gram gradient entry is measurable on matrix arrays.
Source: finite matrix product formula; atlas `wishart-lambda-min-tail` (helper). -/
theorem measurable_gramSoftMinGradient_entry (n : ℕ) (ε : ℝ) (i : ι) (j : κ) :
    Measurable fun G : ι → κ → ℝ => gramSoftMinGradient n ε (Matrix.of G) i j := by
  have hG : ∀ i j, Measurable fun G : ι → κ → ℝ => Matrix.of G i j := fun i j => by fun_prop
  have hP : ∀ a b : ι, Measurable fun G : ι → κ → ℝ =>
      inversePowerSoftMinWeight n (regularizedGram ε (Matrix.of G)) a b :=
    measurable_inversePowerSoftMinWeight_entry_of (measurable_regularizedGram_entry ε) n
  exact measurable_const.mul (measurable_mul_entry_of hP hG i j)

set_option maxHeartbeats 800000 in
/-- Each actual second coordinate Gram derivative is measurable on matrix
arrays. Source: finite Gram Hessian formula; atlas `wishart-lambda-min-tail` (helper). -/
theorem measurable_gramSoftMinSecond_single (n : ℕ) (ε : ℝ) (i : ι) (j : κ) :
    Measurable fun G : ι → κ → ℝ => gramSoftMinSecond n ε (Matrix.of G) (Matrix.single i j 1) := by
  let E : Matrix ι κ ℝ := Matrix.single i j 1
  have hG : ∀ i j, Measurable fun G : ι → κ → ℝ => Matrix.of G i j := fun i j => by fun_prop
  have hE : ∀ i j, Measurable fun _ : ι → κ → ℝ => E i j := fun _ _ => measurable_const
  have hD : ∀ a b, Measurable fun G : ι → κ → ℝ =>
      (E * (Matrix.of G)ᵀ + Matrix.of G * Eᵀ) a b := fun a b =>
    (measurable_mul_entry_of hE (fun a b => hG b a) a b).add
      (measurable_mul_entry_of hG (fun a b => hE b a) a b)
  have hW : ∀ a b : ι, Measurable fun G : ι → κ → ℝ => regularizedGram ε (Matrix.of G) a b :=
    measurable_regularizedGram_entry ε
  have hSecond : Measurable fun G : ι → κ → ℝ =>
      inversePowerSoftMinSecond n (regularizedGram ε (Matrix.of G))
        (E * (Matrix.of G)ᵀ + Matrix.of G * Eᵀ) :=
    measurable_inversePowerSoftMinSecond_of_entries hW hD n
  have hC : ∀ a b : ι, Measurable fun _ : ι → κ → ℝ => ((2 : ℝ) • (E * Eᵀ)) a b :=
    fun _ _ => measurable_const
  have hFirst : Measurable fun G : ι → κ → ℝ =>
      inversePowerSoftMinFirst n (regularizedGram ε (Matrix.of G)) ((2 : ℝ) • (E * Eᵀ)) :=
    measurable_inversePowerSoftMinFirst_of_entries hW hC n
  exact hSecond.add hFirst

end NLAlib
