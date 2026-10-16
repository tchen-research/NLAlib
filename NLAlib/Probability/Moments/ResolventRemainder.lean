import NLAlib.Matrix.Functions.ResolventWordBounds
import NLAlib.Matrix.Functions.ResolventMeasurability
import NLAlib.Probability.Moments.Schatten
import NLAlib.ForMathlib.Analysis.PowerInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Expected six-word resolvent remainder

The actual ordered remainder has a cubic Schatten envelope. Its integrability
and expected trace bound follow from the three actual cubic moments. No
independence hypothesis is needed for this step of Cauchy comparison.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped Matrix
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

open scoped Matrix.Norms.L2Operator in
private theorem norm_six_word_remainder_le_cubic
    (ζ : ℂ) (A B C D E F : M) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hC : C.IsHermitian) (hζ : ζ.im ≠ 0) :
    ‖normalizedTrace (D * resolventSquareSecondDifference ζ A B C D E +
        D * resolventSquareSecondDifference ζ A C C F D)‖ ≤
      |ζ.im|⁻¹^4 * (4 * (schattenNormReal D 3 ^ 3 / (Fintype.card n : ℝ)) +
        schattenNormReal E 3 ^ 3 / (Fintype.card n : ℝ) +
        schattenNormReal F 3 ^ 3 / (Fintype.card n : ℝ)) := by
  let d := schattenNormReal D 3
  let e := schattenNormReal E 3
  let f := schattenNormReal F 3
  let c := |ζ.im|⁻¹^4 / (Fintype.card n : ℝ)
  have hc : 0 ≤ c := div_nonneg (by positivity) (Nat.cast_nonneg _)
  have hd := schattenNormReal_nonneg D 3
  have he := schattenNormReal_nonneg E 3
  have hf := schattenNormReal_nonneg F 3
  have h₁ := norm_normalizedTrace_mul_resolventSquareSecondDifference_le
    ζ A B C D D E hA hB hC hζ
  have h₂ := norm_normalizedTrace_mul_resolventSquareSecondDifference_le
    ζ A C C D F D hA hC hC hζ
  have hu := mul_le_mul_of_nonneg_left (three_mul_mul_mul_le_add_cube hd hd he) hc
  have hv := mul_le_mul_of_nonneg_left (three_mul_mul_mul_le_add_cube hd hf hd) hc
  have hb₁ : ‖normalizedTrace (D * resolventSquareSecondDifference ζ A B C D E)‖ ≤
      c * (2*d^3+e^3) := h₁.trans (by convert hu using 1 <;> dsimp [c,d,e] <;> ring)
  have hb₂ : ‖normalizedTrace (D * resolventSquareSecondDifference ζ A C C F D)‖ ≤
      c * (2*d^3+f^3) := h₂.trans (by convert hv using 1 <;> dsimp [c,d,f] <;> ring)
  rw [normalizedTrace_add]
  calc
    _ ≤ ‖normalizedTrace (D * resolventSquareSecondDifference ζ A B C D E)‖ +
        ‖normalizedTrace (D * resolventSquareSecondDifference ζ A C C F D)‖ := norm_add_le _ _
    _ ≤ c * (2*d^3+e^3) + c * (2*d^3+f^3) := add_le_add hb₁ hb₂
    _ = _ := by dsimp [c,d,e,f]; ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

open scoped Matrix.Norms.L2Operator in
private theorem aemeasurable_six_word_remainder
    (ζ : ℂ) (A B C D E F : Ω → M)
    (hA : AEMeasurable A P) (hB : AEMeasurable B P) (hC : AEMeasurable C P)
    (hD : AEMeasurable D P) (hE : AEMeasurable E P) (hF : AEMeasurable F P) :
    AEMeasurable (fun ω => normalizedTrace
      (D ω * resolventSquareSecondDifference ζ (A ω) (B ω) (C ω) (D ω) (E ω) +
        D ω * resolventSquareSecondDifference ζ (A ω) (C ω) (C ω) (F ω) (D ω))) P := by
  have hRA := (measurable_matrix_resolvent ζ).comp_aemeasurable hA
  have hRB := (measurable_matrix_resolvent ζ).comp_aemeasurable hB
  have hRC := (measurable_matrix_resolvent ζ).comp_aemeasurable hC
  have htr : Measurable (normalizedTrace : M → ℂ) :=
    (continuous_const.mul continuous_id.matrix_trace).measurable
  apply htr.comp_aemeasurable
  unfold resolventSquareSecondDifference
  fun_prop

open scoped Matrix.Norms.L2Operator in
/-- The expected six-word remainder is bounded by its three actual normalized
cubic Schatten moments. Equal moments give the sharp factor six. The three
base matrices need only be almost surely Hermitian; no independence is used.
All complex product integrability follows from the cubic envelope.
Source: supplied Cauchy-transform reroute, comparison-sixwords.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem integrable_and_norm_integral_six_word_remainder_le
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (A B C D E F : Ω → M)
    (hAm : AEMeasurable A P) (hBm : AEMeasurable B P) (hCm : AEMeasurable C P)
    (hDm : AEMeasurable D P) (hEm : AEMeasurable E P) (hFm : AEMeasurable F P)
    (hA : ∀ᵐ ω ∂P, (A ω).IsHermitian)
    (hB : ∀ᵐ ω ∂P, (B ω).IsHermitian)
    (hC : ∀ᵐ ω ∂P, (C ω).IsHermitian)
    (hD3 : Integrable (fun ω => schattenNormReal (D ω) 3 ^ 3 / (Fintype.card n : ℝ)) P)
    (hE3 : Integrable (fun ω => schattenNormReal (E ω) 3 ^ 3 / (Fintype.card n : ℝ)) P)
    (hF3 : Integrable (fun ω => schattenNormReal (F ω) 3 ^ 3 / (Fintype.card n : ℝ)) P)
    (m : ℝ)
    (hmD : (∫ ω, schattenNormReal (D ω) 3 ^ 3 / (Fintype.card n : ℝ) ∂P) = m)
    (hmE : (∫ ω, schattenNormReal (E ω) 3 ^ 3 / (Fintype.card n : ℝ) ∂P) = m)
    (hmF : (∫ ω, schattenNormReal (F ω) 3 ^ 3 / (Fintype.card n : ℝ) ∂P) = m) :
    Integrable (fun ω => normalizedTrace
      (D ω * resolventSquareSecondDifference ζ (A ω) (B ω) (C ω) (D ω) (E ω) +
        D ω * resolventSquareSecondDifference ζ (A ω) (C ω) (C ω) (F ω) (D ω))) P ∧
    ‖∫ ω, normalizedTrace
      (D ω * resolventSquareSecondDifference ζ (A ω) (B ω) (C ω) (D ω) (E ω) +
        D ω * resolventSquareSecondDifference ζ (A ω) (C ω) (C ω) (F ω) (D ω)) ∂P‖ ≤
      6 * m / |ζ.im|^4 := by
  let g : Ω → ℝ := fun ω => |ζ.im|⁻¹^4 *
    (4 * (schattenNormReal (D ω) 3 ^ 3 / (Fintype.card n : ℝ)) +
      schattenNormReal (E ω) 3 ^ 3 / (Fintype.card n : ℝ) +
      schattenNormReal (F ω) 3 ^ 3 / (Fintype.card n : ℝ))
  have hg : Integrable g P := ((hD3.const_mul 4).add hE3 |>.add hF3).const_mul _
  have hbound : ∀ᵐ ω ∂P, ‖normalizedTrace
      (D ω * resolventSquareSecondDifference ζ (A ω) (B ω) (C ω) (D ω) (E ω) +
        D ω * resolventSquareSecondDifference ζ (A ω) (C ω) (C ω) (F ω) (D ω))‖ ≤ g ω := by
    filter_upwards [hA,hB,hC] with ω hA hB hC
    exact norm_six_word_remainder_le_cubic ζ _ _ _ _ _ _ hA hB hC hζ
  have hmeas := (aemeasurable_six_word_remainder ζ A B C D E F
    hAm hBm hCm hDm hEm hFm).aestronglyMeasurable
  refine ⟨hg.mono' hmeas hbound, (norm_integral_le_of_norm_le hg hbound).trans_eq ?_⟩
  have hDE : Integrable (fun ω =>
      4 * (schattenNormReal (D ω) 3 ^ 3 / (Fintype.card n : ℝ)) +
        schattenNormReal (E ω) 3 ^ 3 / (Fintype.card n : ℝ)) P :=
    (hD3.const_mul 4).add hE3
  dsimp [g]
  rw [integral_const_mul, integral_add hDE hF3,
    integral_add (hD3.const_mul 4) hE3, integral_const_mul, hmD, hmE, hmF]
  rw [div_eq_mul_inv, inv_pow]
  ring

open scoped Matrix.Norms.L2Operator in
/-- Matrix L³ assumptions discharge every cubic integrability premise of the
expected six-word estimate. The equality assumptions concern actual finite
normalized cubic moments, not formal Bochner values of nonintegrable tests.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem integrable_and_norm_integral_six_word_remainder_le_of_memLp
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (A B C D E F : Ω → M)
    (hAm : AEMeasurable A P) (hBm : AEMeasurable B P) (hCm : AEMeasurable C P)
    (hD : MemLp D 3 P) (hE : MemLp E 3 P) (hF : MemLp F 3 P)
    (hA : ∀ᵐ ω ∂P, (A ω).IsHermitian)
    (hB : ∀ᵐ ω ∂P, (B ω).IsHermitian)
    (hC : ∀ᵐ ω ∂P, (C ω).IsHermitian)
    (m : ℝ)
    (hmD : (∫ ω, schattenNormReal (D ω) 3 ^ 3 / (Fintype.card n : ℝ) ∂P) = m)
    (hmE : (∫ ω, schattenNormReal (E ω) 3 ^ 3 / (Fintype.card n : ℝ) ∂P) = m)
    (hmF : (∫ ω, schattenNormReal (F ω) 3 ^ 3 / (Fintype.card n : ℝ) ∂P) = m) :
    Integrable (fun ω => normalizedTrace
      (D ω * resolventSquareSecondDifference ζ (A ω) (B ω) (C ω) (D ω) (E ω) +
        D ω * resolventSquareSecondDifference ζ (A ω) (C ω) (C ω) (F ω) (D ω))) P ∧
    ‖∫ ω, normalizedTrace
      (D ω * resolventSquareSecondDifference ζ (A ω) (B ω) (C ω) (D ω) (E ω) +
        D ω * resolventSquareSecondDifference ζ (A ω) (C ω) (C ω) (F ω) (D ω)) ∂P‖ ≤
      6 * m / |ζ.im|^4 := by
  apply integrable_and_norm_integral_six_word_remainder_le ζ hζ A B C D E F
    hAm hBm hCm hD.aestronglyMeasurable.aemeasurable hE.aestronglyMeasurable.aemeasurable
    hF.aestronglyMeasurable.aemeasurable hA hB hC _ _ _ m hmD hmE hmF
  · exact (integrable_schattenNormReal_pow_of_memLp D (p := 3) hD (by decide) (by norm_num)).div_const _
  · exact (integrable_schattenNormReal_pow_of_memLp E (p := 3) hE (by decide) (by norm_num)).div_const _
  · exact (integrable_schattenNormReal_pow_of_memLp F (p := 3) hF (by decide) (by norm_num)).div_const _

end NLAlib
