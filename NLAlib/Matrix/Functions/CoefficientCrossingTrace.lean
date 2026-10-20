import NLAlib.Matrix.Structured.CoefficientCrossingBound
import NLAlib.Matrix.Functions.AggregateTraceWords

/-!
# Actual crossed coefficient trace words

The covariance alignment estimate gives all four nuclear/spectral endpoints
of the genuine crossed trace functional. Complex multilinear interpolation
then supplies arbitrary Schatten exponents, including infinity.
Source: arXiv:2108.06312v2, Lemma 4.5 and Proposition 4.6.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix ENNReal

namespace NLAlib

variable {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq d]

open scoped Matrix.Norms.L2Operator in
/-- The literal crossed trace-word functional with coefficient pattern
`A_i, B_j, A_i, B_j`, retaining the original order. -/
def coefficientCrossingTraceMultilinear
    (A : ι → Matrix d d ℂ) (B : κ → Matrix d d ℂ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin 4 => Matrix d d ℂ) ℂ :=
  sumTraceWordMultilinear (fun ij : ι × κ => ![A ij.1,B ij.2,A ij.1,B ij.2])

omit [DecidableEq ι] [DecidableEq κ] in
open scoped Matrix.Norms.L2Operator in
/-- Evaluation of the actual multilinear functional is the trace of the
actual crossing sum followed by its fourth matrix. -/
theorem coefficientCrossingTraceMultilinear_apply
    (A : ι → Matrix d d ℂ) (B : κ → Matrix d d ℂ)
    (Y : Fin 4 → Matrix d d ℂ) :
    coefficientCrossingTraceMultilinear A B Y =
      (coefficientCrossingSum A B (Y 0) (Y 1) (Y 2)*Y 3).trace := by
  simp [coefficientCrossingTraceMultilinear,sumTraceWordMultilinear_apply,
    coefficientCrossingSum,List.ofFn_succ,Matrix.mul_assoc,
    Fintype.sum_prod_type,Matrix.trace_sum,Finset.sum_mul]

omit [DecidableEq d] in
private theorem trace_crossing_rotate (A B U V W Z : Matrix d d ℂ) :
    (A*U*B*V*A*W*B*Z).trace = (B*V*A*W*B*Z*A*U).trace := by
  simpa only [Matrix.mul_assoc] using
    Matrix.trace_mul_comm (A*U) (B*V*A*W*B*Z)

omit [DecidableEq ι] [DecidableEq κ] in
open scoped Matrix.Norms.L2Operator in
/-- Rotating one alternating pair swaps the two actual coefficient families.
Only cyclic trace algebra is used. -/
theorem coefficientCrossingTraceMultilinear_rotate
    (A : ι → Matrix d d ℂ) (B : κ → Matrix d d ℂ)
    (Y : Fin 4 → Matrix d d ℂ) :
    coefficientCrossingTraceMultilinear A B Y =
      coefficientCrossingTraceMultilinear B A ![Y 1,Y 2,Y 3,Y 0] := by
  simp only [coefficientCrossingTraceMultilinear_apply,
    Matrix.cons_val_zero,
    coefficientCrossingSum,Finset.sum_mul,Matrix.trace_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  exact trace_crossing_rotate _ _ _ _ _ _

open scoped Matrix.Norms.L2Operator in
private theorem norm_coefficientCrossingTraceMultilinear_last_le
    (A : ι → Matrix d d ℂ) (B : κ → Matrix d d ℂ)
    (hA : ∀ i, (A i).IsHermitian) (Y : Fin 4 → Matrix d d ℂ) :
    ‖coefficientCrossingTraceMultilinear A B Y‖ ≤
      (specNorm (coefficientStack A)*specNorm (coefficientVectorization A)*
        specNorm (coefficientVectorization B)*specNorm (coefficientStack B))*
          nuclearNorm (Y 3)*(specNorm (Y 0)*specNorm (Y 1)*specNorm (Y 2)) := by
  rw [coefficientCrossingTraceMultilinear_apply]
  calc
    _ ≤ specNorm (coefficientCrossingSum A B (Y 0) (Y 1) (Y 2))*
        nuclearNorm (Y 3) := by
      apply (norm_trace_le_nuclearNorm _).trans
      simpa only [schattenNormReal_one] using
        schattenNormReal_mul_le_specNorm_mul
          (coefficientCrossingSum A B (Y 0) (Y 1) (Y 2)) (Y 3) (p := 1) zero_lt_one
    _ ≤ ((specNorm (coefficientStack A)*specNorm (coefficientVectorization A)*
        specNorm (coefficientVectorization B)*specNorm (coefficientStack B))*
        (specNorm (Y 0)*specNorm (Y 1)*specNorm (Y 2)))*nuclearNorm (Y 3) := by
      apply mul_le_mul_of_nonneg_right
        (specNorm_coefficientCrossingSum_le_stack_vectorization A B hA _ _ _)
      simpa only [schattenNormReal_one] using schattenNormReal_nonneg (Y 3) 1
    _ = _ := by ring

open scoped Matrix.Norms.L2Operator in
/-- All actual nuclear/spectral endpoints of the crossed trace functional.
No dimension factor or joint law assumption is needed. -/
theorem norm_coefficientCrossingTraceMultilinear_le_nuclear_endpoint
    (A : ι → Matrix d d ℂ) (B : κ → Matrix d d ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hB : ∀ j, (B j).IsHermitian)
    (Y : Fin 4 → Matrix d d ℂ) (j : Fin 4) :
    ‖coefficientCrossingTraceMultilinear A B Y‖ ≤
      (specNorm (coefficientStack A)*specNorm (coefficientVectorization A)*
        specNorm (coefficientVectorization B)*specNorm (coefficientStack B))*
          nuclearNorm (Y j)*∏ l ∈ Finset.univ.erase j, specNorm (Y l) := by
  let C := specNorm (coefficientStack A)*specNorm (coefficientVectorization A)*
    specNorm (coefficientVectorization B)*specNorm (coefficientStack B)
  have hswap : specNorm (coefficientStack B)*specNorm (coefficientVectorization B)*
      specNorm (coefficientVectorization A)*specNorm (coefficientStack A)=C := by
    dsimp [C]
    ring
  have h1 := norm_coefficientCrossingTraceMultilinear_last_le B A hB ![Y 1,Y 2,Y 3,Y 0]
  have h2 := norm_coefficientCrossingTraceMultilinear_last_le A B hA ![Y 2,Y 3,Y 0,Y 1]
  have h3 := norm_coefficientCrossingTraceMultilinear_last_le B A hB ![Y 3,Y 0,Y 1,Y 2]
  have h4 := norm_coefficientCrossingTraceMultilinear_last_le A B hA Y
  have hr1 := coefficientCrossingTraceMultilinear_rotate A B Y
  have hr2 := coefficientCrossingTraceMultilinear_rotate B A ![Y 1,Y 2,Y 3,Y 0]
  have hr3 := coefficientCrossingTraceMultilinear_rotate A B ![Y 2,Y 3,Y 0,Y 1]
  simp at h1 h2 h3 hr2 hr3
  fin_cases j
  · change ‖coefficientCrossingTraceMultilinear A B Y‖ ≤
      C*nuclearNorm (Y 0)*∏ l ∈ (Finset.univ : Finset (Fin 4)).erase 0, specNorm (Y l)
    have he : (Finset.univ : Finset (Fin 4)).erase 0 = {1,2,3} := by decide
    rw [he]
    rw [hr1]
    simpa [hswap,C,mul_comm,mul_left_comm,mul_assoc] using h1
  · change ‖coefficientCrossingTraceMultilinear A B Y‖ ≤
      C*nuclearNorm (Y 1)*∏ l ∈ (Finset.univ : Finset (Fin 4)).erase 1, specNorm (Y l)
    have he : (Finset.univ : Finset (Fin 4)).erase 1 = {0,2,3} := by decide
    rw [he]
    rw [hr1,hr2]
    simpa [C,mul_comm,mul_left_comm,mul_assoc] using h2
  · change ‖coefficientCrossingTraceMultilinear A B Y‖ ≤
      C*nuclearNorm (Y 2)*∏ l ∈ (Finset.univ : Finset (Fin 4)).erase 2, specNorm (Y l)
    have he : (Finset.univ : Finset (Fin 4)).erase 2 = {0,1,3} := by decide
    rw [he]
    rw [hr1,hr2,hr3]
    simpa [hswap,C,mul_comm,mul_left_comm,mul_assoc] using h3
  · change ‖coefficientCrossingTraceMultilinear A B Y‖ ≤
      C*nuclearNorm (Y 3)*∏ l ∈ (Finset.univ : Finset (Fin 4)).erase 3, specNorm (Y l)
    have he : (Finset.univ : Finset (Fin 4)).erase 3 = {0,1,2} := by decide
    rw [he]
    simpa [C,mul_assoc] using h4

open scoped Matrix.Norms.L2Operator in
/-- Genuine deterministic crossing Schatten inequality for arbitrary four
exponents, including infinity, with the actual covariance alignment scale.
Source: arXiv:2108.06312v2, Lemma 4.5 and Proposition 4.6.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem norm_coefficientCrossingTraceMultilinear_le_prod_schattenNorm
    (A : ι → Matrix d d ℂ) (B : κ → Matrix d d ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hB : ∀ j, (B j).IsHermitian)
    (p : Fin 4 → ℝ≥0∞) (hp : ∀ l, 1 ≤ p l)
    (hsum : ∑ l, ((p l)⁻¹).toReal = 1) (Y : Fin 4 → Matrix d d ℂ) :
    ‖coefficientCrossingTraceMultilinear A B Y‖ ≤
      (Real.sqrt (specNorm (coefficientVariance A))*
        Real.sqrt (specNorm (coefficientCovariance A))*
        Real.sqrt (specNorm (coefficientCovariance B))*
        Real.sqrt (specNorm (coefficientVariance B)))*
          ∏ l, schattenNorm (Y l) (p l) := by
  have hC : 0 ≤ specNorm (coefficientStack A)*specNorm (coefficientVectorization A)*
      specNorm (coefficientVectorization B)*specNorm (coefficientStack B) :=
    mul_nonneg (mul_nonneg (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _))
      (specNorm_nonneg _)) (specNorm_nonneg _)
  have h := norm_multilinear_le_prod_schattenNorm_of_endpoints
    (coefficientCrossingTraceMultilinear A B) hC
    (fun j Y => norm_coefficientCrossingTraceMultilinear_le_nuclear_endpoint A B hA hB Y j)
    p hp hsum Y
  simpa only [specNorm_coefficientStack_eq_sqrt_variance A hA,
    specNorm_coefficientStack_eq_sqrt_variance B hB,
    specNorm_coefficientVectorization_eq_sqrt_covariance] using h

end NLAlib

end
