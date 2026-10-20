import NLAlib.Matrix.Functions.MultilinearTraceWords
import NLAlib.Matrix.Functions.CyclicTraceWords
import NLAlib.Matrix.Norms.SchattenMultilinearInterpolation
import NLAlib.Matrix.Norms.ComplexSchattenDuality
import NLAlib.ForMathlib.Analysis.CStarAlgebra.AggregateProducts
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Aggregate Hermitian trace-word Schatten estimates

All words and multilinear functionals are actual
finite matrix products and sums. No probability or copy-law assumptions occur.
Source: the deterministic operator endpoint in Brailovskaya–van Handel,
arXiv:2201.05142v3, Proposition 5.1, q=infinity. Supports
independent-sum-spectrum-universality (partial).
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix MatrixOrder ComplexOrder ENNReal
namespace NLAlib

open scoped Matrix.Norms.L2Operator in
/-- The actual sum of ordered alternating trace-word functionals. -/
def sumTraceWordMultilinear {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
    {k : ℕ} (Z : ι → Fin k → Matrix n n ℂ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin k => Matrix n n ℂ) ℂ :=
  ∑ i, traceWordMultilinear (Z i)

open scoped Matrix.Norms.L2Operator in
/-- Evaluating the aggregate multilinear functional gives the literal finite
sum of ordered alternating matrix trace words. -/
@[simp]
theorem sumTraceWordMultilinear_apply {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
    {k : ℕ} (Z : ι → Fin k → Matrix n n ℂ) (Y : Fin k → Matrix n n ℂ) :
    sumTraceWordMultilinear Z Y =
      ∑ i, (List.ofFn (fun l => Z i l * Y l)).prod.trace := by
  simp [sumTraceWordMultilinear, traceWordMultilinear_apply]

open scoped Matrix.Norms.L2Operator in
private theorem specNorm_sum_cyclic_trace_cut_le {ι n : Type*}
    [Fintype ι] [Fintype n] [DecidableEq n] {m : ℕ}
    (Z : ι → Fin (m + 2) → Matrix n n ℂ)
    (hHerm : ∀ i l, (Z i l).IsHermitian) {R M : ℝ} (hR : 0 ≤ R)
    (hZ : ∀ i l, specNorm (Z i l) ≤ R)
    (hMass : ∀ l, specNorm (∑ i, Z i l ^ 2) ≤ M)
    (Y : Fin (m + 2) → Matrix n n ℂ) (j : Fin (m + 2)) :
    specNorm (∑ i, Z i (finRotate (m + 2) j) * cyclicTraceWordMiddle (Z i) Y j * Z i j) ≤
      (R ^ m * ∏ l ∈ Finset.univ.erase j, specNorm (Y l)) * M := by
  let r := R ^ m * ∏ l ∈ Finset.univ.erase j, specNorm (Y l)
  have hr : 0 ≤ r := mul_nonneg (pow_nonneg hR m)
    (Finset.prod_nonneg fun l _ => specNorm_nonneg (Y l))
  have hC (i : ι) : ‖cyclicTraceWordMiddle (Z i) Y j‖ ≤ r := by
    simpa only [← specNorm_eq_norm] using specNorm_cyclicTraceWordMiddle_le (Z i) Y hR (hZ i) j
  have hA : (∑ i, Z i (finRotate (m + 2) j) * star (Z i (finRotate (m + 2) j))) =
      ∑ i, Z i (finRotate (m + 2) j) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.star_eq_conjTranspose, (hHerm i _).eq, pow_two]
  have hB : (∑ i, star (Z i j) * Z i j) = ∑ i, Z i j ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.star_eq_conjTranspose, (hHerm i j).eq, pow_two]
  have hn := CStarAlgebra.norm_sum_mul_mul_le
    (fun i => Z i (finRotate (m + 2) j))
    (fun i => cyclicTraceWordMiddle (Z i) Y j) (fun i => Z i j) hr hC
  rw [hA, hB] at hn
  simp only [← specNorm_eq_norm] at hn
  calc
    _ ≤ r / 2 * (specNorm (∑ i, Z i (finRotate (m + 2) j) ^ 2) +
        specNorm (∑ i, Z i j ^ 2)) := hn
    _ ≤ r / 2 * (M + M) := mul_le_mul_of_nonneg_left
      (add_le_add (hMass _) (hMass j)) (div_nonneg hr (by norm_num))
    _ = r * M := by ring

open scoped Matrix.Norms.L2Operator in
private theorem norm_sumTraceWordMultilinear_le_nuclear_endpoint_aux {ι n : Type*}
    [Fintype ι] [Fintype n] [DecidableEq n] {m : ℕ}
    (Z : ι → Fin (m + 2) → Matrix n n ℂ)
    (hHerm : ∀ i l, (Z i l).IsHermitian) {R M : ℝ} (hR : 0 ≤ R)
    (hZ : ∀ i l, specNorm (Z i l) ≤ R)
    (hMass : ∀ l, specNorm (∑ i, Z i l ^ 2) ≤ M)
    (Y : Fin (m + 2) → Matrix n n ℂ) (j : Fin (m + 2)) :
    ‖sumTraceWordMultilinear Z Y‖ ≤
      R ^ m * M * nuclearNorm (Y j) * ∏ l ∈ Finset.univ.erase j, specNorm (Y l) := by
  have heq : sumTraceWordMultilinear Z Y =
      ((∑ i, Z i (finRotate (m + 2) j) * cyclicTraceWordMiddle (Z i) Y j * Z i j) * Y j).trace := by
    rw [sumTraceWordMultilinear_apply, Finset.sum_mul, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun i _ => trace_alternating_word_eq_cyclic_cut (Z i) Y j
  have hN : 0 ≤ nuclearNorm (Y j) := by
    simpa only [schattenNormReal_one] using schattenNormReal_nonneg (Y j) 1
  rw [heq]
  calc
    _ ≤ specNorm (∑ i, Z i (finRotate (m + 2) j) * cyclicTraceWordMiddle (Z i) Y j * Z i j) *
        nuclearNorm (Y j) := by
      apply (norm_trace_le_nuclearNorm _).trans
      simpa only [schattenNormReal_one] using
        schattenNormReal_mul_le_specNorm_mul
          (∑ i, Z i (finRotate (m + 2) j) * cyclicTraceWordMiddle (Z i) Y j * Z i j)
          (Y j) (p := 1) zero_lt_one
    _ ≤ ((R ^ m * ∏ l ∈ Finset.univ.erase j, specNorm (Y l)) * M) * nuclearNorm (Y j) :=
      mul_le_mul_of_nonneg_right (specNorm_sum_cyclic_trace_cut_le Z hHerm hR hZ hMass Y j) hN
    _ = _ := by ring

open scoped Matrix.Norms.L2Operator in
/-- Sharp ordinary-trace nuclear endpoints for an actual finite Hermitian
word family. Each slot's realized aggregate square norm is bounded by M;
the coefficient arrays may have any relation. No dimension factor occurs. -/
theorem norm_sumTraceWordMultilinear_le_nuclear_endpoint {ι n : Type*}
    [Fintype ι] [Fintype n] [DecidableEq n] {k : ℕ} (hk : 2 ≤ k)
    (Z : ι → Fin k → Matrix n n ℂ) (hHerm : ∀ i l, (Z i l).IsHermitian)
    {R M : ℝ} (hR : 0 ≤ R) (hZ : ∀ i l, specNorm (Z i l) ≤ R)
    (hMass : ∀ l, specNorm (∑ i, Z i l ^ 2) ≤ M)
    (Y : Fin k → Matrix n n ℂ) (j : Fin k) :
    ‖sumTraceWordMultilinear Z Y‖ ≤
      R ^ (k - 2) * M * nuclearNorm (Y j) * ∏ l ∈ Finset.univ.erase j, specNorm (Y l) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  simpa only [Nat.add_sub_cancel] using
    norm_sumTraceWordMultilinear_le_nuclear_endpoint_aux Z hHerm hR hZ hMass Y j

open scoped Matrix.Norms.L2Operator in
/-- Arbitrary-k deterministic aggregate trace-word Schatten bound, including
infinity exponents, zero radius and empty matrix or summand dimensions.
Source: the q=infinity endpoint/interpolation mechanism of
Brailovskaya–van Handel, arXiv:2201.05142v3, Proposition 5.1 and Lemma 5.2. -/
theorem norm_sumTraceWordMultilinear_le_prod_schattenNorm {ι n : Type*}
    [Fintype ι] [Fintype n] [DecidableEq n] {k : ℕ} (hk : 2 ≤ k)
    (Z : ι → Fin k → Matrix n n ℂ) (hHerm : ∀ i l, (Z i l).IsHermitian)
    {R M : ℝ} (hR : 0 ≤ R) (hZ : ∀ i l, specNorm (Z i l) ≤ R)
    (hMass : ∀ l, specNorm (∑ i, Z i l ^ 2) ≤ M)
    (p : Fin k → ℝ≥0∞) (hp : ∀ l, 1 ≤ p l)
    (hsum : ∑ l, ((p l)⁻¹).toReal = 1) (Y : Fin k → Matrix n n ℂ) :
    ‖sumTraceWordMultilinear Z Y‖ ≤
      R ^ (k - 2) * M * ∏ l, schattenNorm (Y l) (p l) := by
  have hM : 0 ≤ M := by
    let j : Fin k := ⟨0, by omega⟩
    exact (specNorm_nonneg (∑ i, Z i j ^ 2)).trans (hMass j)
  exact norm_multilinear_le_prod_schattenNorm_of_endpoints (sumTraceWordMultilinear Z)
    (mul_nonneg (pow_nonneg hR _) hM)
    (fun j Y => norm_sumTraceWordMultilinear_le_nuclear_endpoint hk Z hHerm hR hZ hMass Y j)
    p hp hsum Y

end NLAlib
