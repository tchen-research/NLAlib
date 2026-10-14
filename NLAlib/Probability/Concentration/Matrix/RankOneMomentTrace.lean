import NLAlib.Matrix.Functions.RankOneWords
import NLAlib.Matrix.Functions.CFCTrace
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Directional rank-one moments and positive trace tests

A directional bound for the moments of `y yᵀ` controls every positive
semidefinite trace test with the same constant. The proof expands the
test matrix in its orthonormal eigenbasis.
-/

noncomputable section

open MeasureTheory Matrix
open scoped Matrix

namespace NLAlib

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
variable {μ : Measure Ω}

/-- Directional rank-one moment control lifts to every PSD trace test,
including integrability of the tested matrix moment. -/
theorem integrable_and_integral_trace_mul_vecMulVec_pow_succ_le
    (y : Ω → ι → ℝ) (p : ℕ) {a : ℝ}
    (hmoment : ∀ x : ι → ℝ,
      Integrable (fun ω => (y ω ⬝ᵥ y ω) ^ p * (x ⬝ᵥ y ω) ^ 2) μ ∧
      (∫ ω, (y ω ⬝ᵥ y ω) ^ p * (x ⬝ᵥ y ω) ^ 2 ∂μ) ≤ a * (x ⬝ᵥ x))
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) :
    Integrable (fun ω => (C * vecMulVec (y ω) (y ω) ^ (p + 1)).trace) μ ∧
      (∫ ω, (C * vecMulVec (y ω) (y ω) ^ (p + 1)).trace ∂μ) ≤ a * C.trace := by
  classical
  let h := hC.isHermitian
  let x (i : ι) : ι → ℝ := h.eigenvectorBasis i
  have hx (i : ι) : x i ⬝ᵥ x i = 1 := by
    simpa [x] using eigenvectorBasis_dotProduct_eigenvectorBasis h i i
  have he (ω : Ω) : (C * vecMulVec (y ω) (y ω) ^ (p + 1)).trace =
      ∑ i, h.eigenvalues i * ((y ω ⬝ᵥ y ω) ^ p * (x i ⬝ᵥ y ω) ^ 2) := by
    rw [trace_mul_vecMulVec_pow_succ]
    have hc := dotProduct_cfc_mulVec_eq_sum h id (y ω)
    rw [cfc_id ℝ C] at hc
    rw [hc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [id_eq]
    ring
  have hint (i : ι) : Integrable (fun ω => h.eigenvalues i *
      ((y ω ⬝ᵥ y ω) ^ p * (x i ⬝ᵥ y ω) ^ 2)) μ :=
    (hmoment (x i)).1.const_mul _
  constructor
  · simp_rw [he]
    exact integrable_finsetSum _ (fun i _ => hint i)
  · simp_rw [he]
    rw [integral_finsetSum _ (fun i _ => hint i)]
    simp_rw [integral_const_mul]
    calc
      _ ≤ ∑ i, h.eigenvalues i * a := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (by simpa only [hx, mul_one] using (hmoment (x i)).2)
          (hC.eigenvalues_nonneg i)
      _ = _ := by
        have ht := trace_cfc_eq_sum_eigenvalues h id
        rw [cfc_id ℝ C] at ht
        simp only [id_eq, RCLike.ofReal_real_eq_id] at ht
        rw [← Finset.sum_mul, ht]
        ring

end NLAlib
