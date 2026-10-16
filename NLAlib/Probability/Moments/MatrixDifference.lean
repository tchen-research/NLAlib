import NLAlib.ForMathlib.MeasureTheory.MatrixIntegral
import NLAlib.Matrix.Norms.SchattenThirdMoment
import NLAlib.Matrix.Norms.SchattenContinuity
import NLAlib.Matrix.Norms.TraceSpectral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Operator.Mul

/-! # Independent-copy matrix difference moments

Bounded centered matrix laws have genuine first and second Bochner moments.
Independent-copy squares are twice the centered second moment, and actual
normalized Schatten third moments are controlled by the variance matrix.
Source: bounded-summand reroute for `cauchy-transform-gaussian-universality`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Finset MeasureTheory ProbabilityTheory Filter
open scoped Matrix ComplexOrder MatrixOrder
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

open scoped Matrix.Norms.L2Operator in
/-- The actual sum of normalized third Schatten moments of independent
same-law copies of each matrix summand. The laws need not be identical.
atlas: cauchy-transform-gaussian-universality (partial)
-/
def matrixDifferenceThirdMoment {ι : Type*} [Fintype ι]
    (ν : ι → Measure (Matrix n n ℂ)) : ℝ :=
  ∑ i, ∫ p : Matrix n n ℂ × Matrix n n ℂ,
    schattenNormReal (p.1 - p.2) 3 ^ 3 / (Fintype.card n : ℝ) ∂(ν i).prod (ν i)

open scoped Matrix.Norms.L2Operator in
/-- Independent-copy normalized Schatten cubic moments are nonnegative,
for every matrix measure, without requiring an integrability assumption. -/
theorem matrixDifferenceThirdMoment_nonneg {ι : Type*} [Fintype ι]
    (ν : ι → Measure (Matrix n n ℂ)) : 0 ≤ matrixDifferenceThirdMoment ν := by
  apply Finset.sum_nonneg
  intro i _
  exact integral_nonneg (fun p => div_nonneg
    (pow_nonneg (schattenNormReal_nonneg _ _) _) (Nat.cast_nonneg _))

open scoped Matrix.Norms.L2Operator in
private theorem integrable_of_ae_norm_le {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → E} (hf : AEStronglyMeasurable f μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : Integrable f μ :=
  (MemLp.of_bound hf C hC : MemLp f 1 μ).integrable le_rfl

open scoped Matrix.Norms.L2Operator in
/-- An almost-everywhere bound on the centered spectral norm implies
integrability of the actual matrix law itself. -/
theorem integrable_id_of_ae_specNorm_centered_le
    (ν : Measure (Matrix n n ℂ)) [IsProbabilityMeasure ν] {L : ℝ}
    (hbound : ∀ᵐ S ∂ν, specNorm (S - ∫ T, T ∂ν) ≤ L) :
    Integrable (fun S : Matrix n n ℂ => S) ν := by
  have hT : Integrable (fun S : Matrix n n ℂ => S - ∫ T, T ∂ν) ν :=
    integrable_of_ae_norm_le (by fun_prop) hbound
  have hsum : Integrable (fun S : Matrix n n ℂ =>
      (S - ∫ T, T ∂ν) + ∫ T, T ∂ν) ν := hT.add (integrable_const _)
  simpa only [sub_add_cancel, id_eq] using hsum

open scoped Matrix.Norms.L2Operator in
/-- An actual centered spectral bound gives every finite or infinite norm
moment of the original matrix law, without assuming its mean exists first. -/
theorem memLp_id_of_ae_specNorm_centered_le
    (ν : Measure (Matrix n n ℂ)) [IsProbabilityMeasure ν] {L : ℝ} {p : ENNReal}
    (hbound : ∀ᵐ S ∂ν, specNorm (S - ∫ T, T ∂ν) ≤ L) :
    MemLp (fun S : Matrix n n ℂ => S) p ν := by
  have hT : MemLp (fun S : Matrix n n ℂ => S - ∫ T, T ∂ν) p ν :=
    MemLp.of_bound (by fun_prop) L hbound
  have hsum : MemLp (fun S : Matrix n n ℂ =>
      (S - ∫ T, T ∂ν) + ∫ T, T ∂ν) p ν := hT.add (memLp_const _)
  simpa only [sub_add_cancel] using hsum

open scoped Matrix.Norms.L2Operator in
/-- Every natural power of the centered actual matrix law is integrable
under its centered spectral bound, including the zeroth power. -/
theorem integrable_matrix_centered_pow_of_ae_specNorm_le
    (ν : Measure (Matrix n n ℂ)) [IsProbabilityMeasure ν] {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ᵐ S ∂ν, specNorm (S - ∫ T, T ∂ν) ≤ L) (k : ℕ) :
    Integrable (fun S : Matrix n n ℂ => (S - ∫ T, T ∂ν) ^ k) ν := by
  apply integrable_of_ae_norm_le (by fun_prop)
  filter_upwards [hbound] with S hS
  exact (norm_pow_le _ k).trans (pow_le_pow_left₀ (norm_nonneg _) hS k)

open scoped Matrix.Norms.L2Operator in
/-- Centering by the actual mean gives zero actual first moment; the required
integrability is derived from the centered spectral bound. -/
theorem integral_matrix_centered_eq_zero
    (ν : Measure (Matrix n n ℂ)) [IsProbabilityMeasure ν] {L : ℝ}
    (hbound : ∀ᵐ S ∂ν, specNorm (S - ∫ T, T ∂ν) ≤ L) :
    (∫ S : Matrix n n ℂ, (S - ∫ T, T ∂ν) ∂ν) = 0 := by
  have hi : Integrable (fun S : Matrix n n ℂ => S) ν :=
    integrable_id_of_ae_specNorm_centered_le ν hbound
  calc
    _ = (∫ S : Matrix n n ℂ, S ∂ν) - ∫ _ : Matrix n n ℂ, (∫ T, T ∂ν) ∂ν :=
      integral_sub hi (integrable_const _)
    _ = 0 := by simp

open scoped Matrix.Norms.L2Operator in
/-- Independent-copy differences obey the actual centered bound `2L`
almost everywhere on the genuine product law. -/
theorem ae_specNorm_matrix_sub_copy_le
    (ν : Measure (Matrix n n ℂ)) [IsProbabilityMeasure ν] {L : ℝ}
    (hbound : ∀ᵐ S ∂ν, specNorm (S - ∫ T, T ∂ν) ≤ L) :
    ∀ᵐ p : Matrix n n ℂ × Matrix n n ℂ ∂ν.prod ν,
      specNorm (p.1 - p.2) ≤ 2 * L := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hbound,
    Measure.quasiMeasurePreserving_snd.ae hbound] with p hp hq
  have he : p.1 - p.2 = (p.1 - ∫ T, T ∂ν) - (p.2 - ∫ T, T ∂ν) := by abel
  rw [he]
  change ‖p.1 - ∫ T, T ∂ν‖ ≤ L at hp
  change ‖p.2 - ∫ T, T ∂ν‖ ≤ L at hq
  exact (norm_sub_le _ _).trans (by linarith [hp, hq])

open scoped Matrix.Norms.L2Operator in
/-- Every independent-copy difference square is integrable under the actual
centered spectral bound. -/
theorem integrable_matrix_sub_copy_sq
    (ν : Measure (Matrix n n ℂ)) [IsProbabilityMeasure ν] {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ᵐ S ∂ν, specNorm (S - ∫ T, T ∂ν) ≤ L) :
    Integrable (fun p : Matrix n n ℂ × Matrix n n ℂ => (p.1 - p.2) ^ 2) (ν.prod ν) := by
  apply integrable_of_ae_norm_le (by fun_prop)
  filter_upwards [ae_specNorm_matrix_sub_copy_le ν hbound] with p hp
  exact (norm_pow_le _ 2).trans
    (pow_le_pow_left₀ (norm_nonneg _) hp 2)

open scoped Matrix.Norms.L2Operator in
/-- The independent-copy square is exactly twice the actual centered second
moment. Both integrability and zero centered means are derived from boundedness;
the conclusion is not an exchangeable-pair interface assumption.
atlas: cauchy-transform-gaussian-universality (partial)
-/
theorem integral_matrix_sub_copy_sq
    (ν : Measure (Matrix n n ℂ)) [IsProbabilityMeasure ν] {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ᵐ S ∂ν, specNorm (S - ∫ T, T ∂ν) ≤ L) :
    (∫ p : Matrix n n ℂ × Matrix n n ℂ, (p.1 - p.2) ^ 2 ∂ν.prod ν) =
      2 • ∫ S : Matrix n n ℂ, (S - ∫ T, T ∂ν) ^ 2 ∂ν := by
  let T : Matrix n n ℂ → Matrix n n ℂ := fun S => S - ∫ R, R ∂ν
  have hT : Integrable T ν := by
    exact integrable_of_ae_norm_le (by fun_prop) hbound
  have hT2 : Integrable (fun S => T S ^ 2) ν :=
    integrable_matrix_centered_pow_of_ae_specNorm_le ν hL hbound 2
  have hmean : (∫ S, T S ∂ν) = 0 := integral_matrix_centered_eq_zero ν hbound
  have hcross := integral_prod_bilin (ContinuousLinearMap.mul ℂ (Matrix n n ℂ)) hT hT
  have hcross' := integral_prod_bilin (ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).flip hT hT
  simp only [ContinuousLinearMap.mul_apply', hmean, mul_zero] at hcross
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply', hmean, mul_zero] at hcross'
  have hexpand (p : Matrix n n ℂ × Matrix n n ℂ) :
      (p.1 - p.2) ^ 2 = T p.1 ^ 2 - T p.1 * T p.2 - T p.2 * T p.1 + T p.2 ^ 2 := by
    dsimp [T]
    noncomm_ring
  have hrev : Integrable (fun p : Matrix n n ℂ × Matrix n n ℂ => T p.2 * T p.1) (ν.prod ν) :=
    (hT.mul_prod hT).swap
  have hfirst : Integrable (fun p : Matrix n n ℂ × Matrix n n ℂ =>
      T p.1 ^ 2 - T p.1 * T p.2) (ν.prod ν) := (hT2.comp_fst ν).sub (hT.mul_prod hT)
  have hsecond : Integrable (fun p : Matrix n n ℂ × Matrix n n ℂ =>
      T p.1 ^ 2 - T p.1 * T p.2 - T p.2 * T p.1) (ν.prod ν) := hfirst.sub hrev
  simp_rw [hexpand]
  rw [integral_add hsecond (hT2.comp_snd ν), integral_sub hfirst hrev,
    integral_sub (hT2.comp_fst ν) (hT.mul_prod hT), hcross, hcross',
    integral_fun_fst (μ := ν) (ν := ν) (fun S => T S ^ 2),
    integral_fun_snd (μ := ν) (ν := ν) (fun S => T S ^ 2)]
  simp only [probReal_univ, one_smul, sub_zero, two_smul, T]

end NLAlib
