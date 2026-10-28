import NLAlib.Estimation.Reconstruction.NormalSpectralScaling
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Explicit constants in the normal spectral-density asymptotic error

The published radius is retained exactly. Elementary logarithmic comparisons
give a concrete universal constant for its derived order bound.
-/

noncomputable section
open Real MeasureTheory
open scoped Matrix
namespace NLAlib

private theorem normal_log_factors {M : ℕ} (hM : 2≤M) {δ : ℝ}
    (hδ : 0<δ) (hδ1 : δ<1) :
    (1/2 : ℝ)≤log M ∧ 0≤log ((M : ℝ)/δ) ∧
      log ((2*((M+1)^2-1 : ℕ) : ℝ)/δ) ≤ 5*log ((M : ℝ)/δ) ∧
      0≤log ((2*((M+1)^2-1 : ℕ) : ℝ)/δ) := by
  have hm : (2 : ℝ)≤M := by exact_mod_cast hM
  have hmp : 0<(M : ℝ) := by linarith
  have hlog : log 2≤log M := log_le_log (by norm_num) hm
  have hhalf : (1/2 : ℝ)≤log M := by linarith [log_two_gt_d9]
  have hdlog : log δ≤0 := log_nonpos hδ.le hδ1.le
  have hratio : 0≤log ((M : ℝ)/δ) := by rw [log_div hmp.ne' hδ.ne'];linarith
  have hknat : 1≤(M+1)^2 := by nlinarith
  have hk : (((M+1)^2-1 : ℕ) : ℝ)=(M : ℝ)^2+2*M := by
    rw [Nat.cast_sub hknat,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
    ring
  have hnum : (2*((M+1)^2-1 : ℕ) : ℝ)≤8*(M : ℝ)^2 := by rw [hk];nlinarith
  have hnumpos : 0<(2*((M+1)^2-1 : ℕ) : ℝ) := by rw [hk];positivity
  have hupper : log ((2*((M+1)^2-1 : ℕ) : ℝ)/δ)≤5*log ((M : ℝ)/δ) := by
    calc
      _ ≤ log (8*(M : ℝ)^2/δ) := log_le_log (div_pos hnumpos hδ)
        (div_le_div_of_nonneg_right hnum hδ.le)
      _ = 3*log 2+2*log M-log δ := by
        rw [log_div (by positivity) hδ.ne',log_mul (by norm_num) (pow_ne_zero 2 hmp.ne'),
          show (8 : ℝ)=2^3 by norm_num,log_pow,log_pow]
        norm_num
      _ ≤ _ := by rw [log_div hmp.ne' hδ.ne'];linarith
  have hlower : 0≤log ((2*((M+1)^2-1 : ℕ) : ℝ)/δ) := by
    apply log_nonneg
    apply (one_le_div hδ).mpr
    rw [hk]
    nlinarith
  exact ⟨hhalf,hratio,hupper,hlower⟩

/-- The explicit source radius has the card's dimension-enhanced order term,
with a fully specified universal constant. -/
theorem pi_mul_normalTensorMomentRadius_mul_sqrt_le {n M : ℕ}
    (hn : 1≤n) (hM : 2≤M) {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1) :
    π*normalTensorMomentRadius n M δ*sqrt (5+(π/2)*log M) ≤
      128*sqrt (log ((M : ℝ)/δ)*log M/n) := by
  obtain ⟨hlog,hlogratio,hupper,hlower⟩ := normal_log_factors hM hδ hδ1
  have hnR : (1 : ℝ)≤n := by exact_mod_cast hn
  have hnp : 0<(n : ℝ) := by linarith
  have hden : (n : ℝ)≤2*n-1 := by linarith
  have hdenpos : 0<2*(n : ℝ)-1 := by linarith
  have hsq : normalTensorMomentRadius n M δ ^ 2 =
      8/(2*(n : ℝ)-1)*log ((2*((M+1)^2-1 : ℕ) : ℝ)/δ) := by
    rw [normalTensorMomentRadius,sq_sqrt (mul_nonneg (by positivity) hlower)]
  have hradius : normalTensorMomentRadius n M δ ^ 2 ≤ 40*log ((M : ℝ)/δ)/n := by
    rw [hsq]
    calc
      _ ≤ (8/(n : ℝ))*(5*log ((M : ℝ)/δ)) :=
        mul_le_mul (div_le_div_of_nonneg_left (by norm_num) hnp hden) hupper hlower (by positivity)
      _ = _ := by ring
  have hL : 0≤5+(π/2)*log M := by positivity
  have hLbound : 5+(π/2)*log M≤12*log M := by
    have hprod := mul_le_mul_of_nonneg_right pi_lt_four.le (show 0≤log M by linarith)
    nlinarith
  have hpi : π^2≤16 := by nlinarith [pi_pos,pi_lt_four]
  let T : ℝ := log ((M : ℝ)/δ)*log M/n
  have hT : 0≤T := by dsimp [T];positivity
  have hs : (π*normalTensorMomentRadius n M δ*sqrt (5+(π/2)*log M))^2 ≤
      (128*sqrt T)^2 := by
    calc
      _ = (π^2*normalTensorMomentRadius n M δ^2)*(5+(π/2)*log M) := by
        rw [mul_pow,mul_pow,sq_sqrt hL]
      _ ≤ (16*(40*log ((M : ℝ)/δ)/n))*(12*log M) :=
        mul_le_mul (mul_le_mul hpi hradius (sq_nonneg _) (by norm_num)) hLbound hL (by positivity)
      _ = 7680*T := by dsimp [T];ring
      _ ≤ 128^2*T := mul_le_mul_of_nonneg_right (by norm_num) hT
      _ = _ := by rw [mul_pow,sq_sqrt hT]
  have hr : 0≤normalTensorMomentRadius n M δ := sqrt_nonneg _
  have hleft : 0≤π*normalTensorMomentRadius n M δ*sqrt (5+(π/2)*log M) :=
    mul_nonneg (mul_nonneg pi_pos.le hr) (sqrt_nonneg _)
  exact (sq_le_sq₀ hleft (by positivity)).mp hs

/-- The entire exact source estimate has the stated derived order bound. -/
theorem normalSpectralDensityError_le_asymptotic {n M : ℕ}
    (hn : 1≤n) (hM : 2≤M) {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1) :
    84/(M : ℝ)+π*normalTensorMomentRadius n M δ*sqrt (5+(π/2)*log M) ≤
      128*(1/(M : ℝ)+sqrt (log ((M : ℝ)/δ)*log M/n)) := by
  have hh := pi_mul_normalTensorMomentRadius_mul_sqrt_le hn hM hδ hδ1
  have hm : 0≤(M : ℝ) := Nat.cast_nonneg M
  have hbase : 84/(M : ℝ)≤128/(M : ℝ) := div_le_div_of_nonneg_right (by norm_num) hm
  simp only [div_eq_mul_inv] at hh hbase ⊢
  linarith

/-- The actual supplied-scale native query strategy obeys the derived error
bound with universal constant 128 under the same exact probability law.
atlas: normal-spectral-density-query (partial) -/
theorem measureReal_wassersteinEDistOne_normalScaledSpectralDensityProgram_asymptotic_gt_le
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℂ} (hA : A*Aᴴ=Aᴴ*A) {S : ℝ} (hS : 0<S) (hbound : specNorm A≤S)
    {M : ℕ} (hM : 2≤M) {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1) :
    (complexSphereVector n).real {b |
      ENNReal.ofReal (128*S*(1/(M : ℝ)+sqrt (log ((M : ℝ)/δ)*log M/Fintype.card n))) <
        wassersteinEDistOne (normalEmpiricalSpectralLaw hA)
          ((normalScaledSpectralDensityProgram S b M).run (matrixAdjointOracle A))} ≤ δ := by
  apply (measureReal_mono ?_).trans
    (measureReal_wassersteinEDistOne_normalScaledSpectralDensityProgram_gt_le hA hS hbound hM hδ hδ1)
  intro b hb
  change ENNReal.ofReal _ < _ at hb
  change ENNReal.ofReal _ < _
  apply lt_of_le_of_lt _ hb
  apply ENNReal.ofReal_le_ofReal
  have hh := mul_le_mul_of_nonneg_left
    (normalSpectralDensityError_le_asymptotic (n := Fintype.card n)
      (Fintype.card_pos (α := n)) hM hδ hδ1) hS.le
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hh

end NLAlib
