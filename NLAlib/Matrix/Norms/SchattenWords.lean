import NLAlib.Matrix.Norms.ComplexSchattenProducts
import NLAlib.Matrix.Norms.SchattenEndpoints
import NLAlib.Matrix.Norms.TraceNuclear

/-!
# Trace bounds for three Schatten factors

Sharp complex Schatten Hölder and the ideal property bound matrix words with
three finite-third-moment factors and arbitrary bounded intervening matrices.
These deterministic estimates supply the Cauchy-transform universality remainders.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Trace Hölder for three complex Schatten-three factors, with constant one. -/
theorem norm_trace_mul_three_le_schattenNormReal_three_mul (A B C : Matrix n n ℂ) :
    ‖(A*B*C).trace‖ ≤ schattenNormReal A 3 * schattenNormReal B 3 * schattenNormReal C 3 := by
  have hp : Real.HolderTriple 3 3 (3/2) := by constructor <;> norm_num
  have hq : Real.HolderTriple (3/2) 3 1 := by constructor <;> norm_num
  calc
    _ ≤ schattenNormReal (A*B*C) 1 := by
      simpa only [schattenNormReal_one] using norm_trace_le_nuclearNorm (A*B*C)
    _ ≤ schattenNormReal (A*B) (3/2) * schattenNormReal C 3 :=
      schattenNormReal_mul_le_mul_complex (A*B) C hq
    _ ≤ _ := mul_le_mul_of_nonneg_right (schattenNormReal_mul_le_mul_complex A B hp)
      (schattenNormReal_nonneg C 3)

open scoped Matrix.Norms.L2Operator in
/-- Three third-moment factors and four bounded multipliers give a sharp
fourth-power bound for the absolute trace of their ordered product. -/
theorem norm_trace_word_le_schattenNormReal_three_mul (R₀ H₁ R₁ H₂ R₂ H₃ R₃ : Matrix n n ℂ)
    {c : ℝ} (hc : 0 ≤ c) (hR₀ : specNorm R₀ ≤ c) (hR₁ : specNorm R₁ ≤ c)
    (hR₂ : specNorm R₂ ≤ c) (hR₃ : specNorm R₃ ≤ c) :
    ‖(R₀*H₁*R₁*H₂*R₂*H₃*R₃).trace‖
      ≤ c^4 * schattenNormReal H₁ 3 * schattenNormReal H₂ 3 * schattenNormReal H₃ 3 := by
  have h₁ : schattenNormReal (R₀*H₁*R₁) 3 ≤ c^2 * schattenNormReal H₁ 3 := by
    calc
      _ ≤ schattenNormReal (R₀*H₁) 3 * specNorm R₁ :=
        schattenNormReal_mul_le_mul_specNorm (R₀*H₁) R₁ (by norm_num)
      _ ≤ (specNorm R₀ * schattenNormReal H₁ 3) * c :=
        mul_le_mul (schattenNormReal_mul_le_specNorm_mul R₀ H₁ (by norm_num))
          hR₁ (specNorm_nonneg _) (mul_nonneg (specNorm_nonneg _) (schattenNormReal_nonneg _ _))
      _ ≤ (c * schattenNormReal H₁ 3) * c := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hR₀ (schattenNormReal_nonneg _ _)) hc
      _ = _ := by ring
  have h₂ : schattenNormReal (H₂*R₂) 3 ≤ c * schattenNormReal H₂ 3 := by
    calc
      _ ≤ schattenNormReal H₂ 3 * specNorm R₂ :=
        schattenNormReal_mul_le_mul_specNorm H₂ R₂ (by norm_num)
      _ ≤ schattenNormReal H₂ 3 * c :=
        mul_le_mul_of_nonneg_left hR₂ (schattenNormReal_nonneg _ _)
      _ = _ := mul_comm _ _
  have h₃ : schattenNormReal (H₃*R₃) 3 ≤ c * schattenNormReal H₃ 3 := by
    calc
      _ ≤ schattenNormReal H₃ 3 * specNorm R₃ :=
        schattenNormReal_mul_le_mul_specNorm H₃ R₃ (by norm_num)
      _ ≤ schattenNormReal H₃ 3 * c :=
        mul_le_mul_of_nonneg_left hR₃ (schattenNormReal_nonneg _ _)
      _ = _ := mul_comm _ _
  have hprod : schattenNormReal (R₀*H₁*R₁) 3 * schattenNormReal (H₂*R₂) 3 *
      schattenNormReal (H₃*R₃) 3 ≤
      (c^2*schattenNormReal H₁ 3) * (c*schattenNormReal H₂ 3) *
      (c*schattenNormReal H₃ 3) := by
    apply mul_le_mul _ h₃ (schattenNormReal_nonneg _ _)
      (mul_nonneg (mul_nonneg (sq_nonneg _) (schattenNormReal_nonneg _ _))
        (mul_nonneg hc (schattenNormReal_nonneg _ _)))
    exact mul_le_mul h₁ h₂ (schattenNormReal_nonneg _ _)
      (mul_nonneg (sq_nonneg _) (schattenNormReal_nonneg _ _))
  have htrace := norm_trace_mul_three_le_schattenNormReal_three_mul
    (R₀*H₁*R₁) (H₂*R₂) (H₃*R₃)
  have halg : c^2 * schattenNormReal H₁ 3 * (c * schattenNormReal H₂ 3) *
      (c * schattenNormReal H₃ 3) =
      c^4 * schattenNormReal H₁ 3 * schattenNormReal H₂ 3 * schattenNormReal H₃ 3 := by ring
  have hfin := htrace.trans (hprod.trans_eq halg)
  simpa only [Matrix.mul_assoc] using hfin

open scoped Matrix.Norms.L2Operator in
/-- The normalized version of the ordered three-factor trace estimate. -/
theorem norm_normalizedTrace_word_le_schattenNormReal_three_mul
    (R₀ H₁ R₁ H₂ R₂ H₃ R₃ : Matrix n n ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hR₀ : specNorm R₀ ≤ c) (hR₁ : specNorm R₁ ≤ c)
    (hR₂ : specNorm R₂ ≤ c) (hR₃ : specNorm R₃ ≤ c) :
    ‖normalizedTrace (R₀*H₁*R₁*H₂*R₂*H₃*R₃)‖
      ≤ (c^4 * schattenNormReal H₁ 3 * schattenNormReal H₂ 3 * schattenNormReal H₃ 3)
        / (Fintype.card n : ℝ) := by
  rw [norm_normalizedTrace]
  exact div_le_div_of_nonneg_right
    (norm_trace_word_le_schattenNormReal_three_mul R₀ H₁ R₁ H₂ R₂ H₃ R₃ hc hR₀ hR₁ hR₂ hR₃)
    (Nat.cast_nonneg _)

open scoped Matrix.Norms.L2Operator in
/-- Cyclicity permits a consecutive pair of bounded factors in a three-factor
Schatten trace word, retaining the exact fourth power of the common bound. -/
theorem norm_normalizedTrace_word_pair_le_schattenNormReal_three_mul
    (H₀ R₀ R₁ H₁ R₂ H₂ R₃ : Matrix n n ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hR₀ : specNorm R₀ ≤ c) (hR₁ : specNorm R₁ ≤ c)
    (hR₂ : specNorm R₂ ≤ c) (hR₃ : specNorm R₃ ≤ c) :
    ‖normalizedTrace (H₀*R₀*R₁*H₁*R₂*H₂*R₃)‖ ≤
      (c^4 * schattenNormReal H₀ 3 * schattenNormReal H₁ 3 * schattenNormReal H₂ 3) /
        (Fintype.card n : ℝ) := by
  have he : normalizedTrace (H₀*R₀*R₁*H₁*R₂*H₂*R₃) =
      normalizedTrace (R₁*H₁*R₂*H₂*R₃*H₀*R₀) := by
    calc
      _ = normalizedTrace ((H₀*R₀)*(R₁*H₁*R₂*H₂*R₃)) :=
        congrArg normalizedTrace (by noncomm_ring)
      _ = normalizedTrace ((R₁*H₁*R₂*H₂*R₃)*(H₀*R₀)) := normalizedTrace_mul_comm _ _
      _ = _ := congrArg normalizedTrace (by noncomm_ring)
  calc
    _ = ‖normalizedTrace (R₁*H₁*R₂*H₂*R₃*H₀*R₀)‖ := congrArg norm he
    _ ≤ (c^4 * schattenNormReal H₁ 3 * schattenNormReal H₂ 3 * schattenNormReal H₀ 3) /
        (Fintype.card n : ℝ) :=
      norm_normalizedTrace_word_le_schattenNormReal_three_mul R₁ H₁ R₂ H₂ R₃ H₀ R₀
        hc hR₁ hR₂ hR₃ hR₀
    _ = _ := by ring

end NLAlib
