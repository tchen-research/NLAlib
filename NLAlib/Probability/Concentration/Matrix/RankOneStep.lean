import NLAlib.Matrix.Functions.CenteredWordBounds
import NLAlib.Probability.Concentration.Matrix.RankOneMomentTrace
import NLAlib.Probability.Concentration.Matrix.InsertionMomentExpansion
import NLAlib.Probability.Concentration.QuadraticForms.QuadraticMoments
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# One-step trace moments for centered rank-one covariance samples

Centering removes the linear coefficient. The quadratic coefficient
retains the variance and higher coefficients use the rank-one word bound.
Source: Heidary, *The Sharp Logarithmic Cost of Khatri--Rao Subspace
Embeddings*, Lemma `closed:lem:step`.
https://github.com/DiarHaidary/Results/blob/main/manuscripts/08-Khatri-Rao-Embeddings-and-Approximation/Khatri_Rao_Embeddings_and_Approximation_Focused.pdf
-/

noncomputable section

open MeasureTheory Matrix
open scoped Matrix

namespace NLAlib

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A matrix insertion word in a measurable vector has measurable trace. -/
theorem measurable_trace_insertionWord_vecMulVec_sub_one
    (y : Ω → ι → ℝ) (hy : Measurable y) (A : Matrix ι ι ℝ) (w : List Bool) :
    Measurable (fun ω => (insertionWord A (vecMulVec (y ω) (y ω) - 1) w).trace) := by
  have hyi (i : ι) : Measurable (fun ω => y ω i) := (measurable_pi_apply i).comp hy
  have hmat : ∀ (w : List Bool) (i j : ι),
      Measurable (fun ω => insertionWord A (vecMulVec (y ω) (y ω) - 1) w i j) := by
    intro w
    induction w with
    | nil => intro i j; simp only [insertionWord, List.map_nil, List.prod_nil]; fun_prop
    | cons b w ih =>
      intro i j
      cases b
      · change Measurable (fun ω => ∑ k, A i k * insertionWord A
          (vecMulVec (y ω) (y ω) - 1) w k j)
        exact Finset.measurable_sum _ fun k _ => measurable_const.mul (ih k j)
      · change Measurable (fun ω => ∑ k, (y ω i * y ω k - (1 : Matrix ι ι ℝ) i k) *
          insertionWord A (vecMulVec (y ω) (y ω) - 1) w k j)
        exact Finset.measurable_sum _ fun k _ => ((hyi i).mul (hyi k) |>.sub_const _).mul (ih k j)
  simp only [Matrix.trace, Matrix.diag]
  exact Finset.measurable_sum _ fun i _ => hmat w i i

omit [IsProbabilityMeasure μ] in
/-- A uniform bound on the positive rank-one moments bounds any centered
insertion word, with one factor of two for each expanded insertion. -/
theorem integrable_and_integral_trace_insertionWord_sub_one_le
    (y : Ω → ι → ℝ) (hy : Measurable y)
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (w : List Bool) {B : ℝ}
    (hmoment : ∀ l ≤ w.count true,
      Integrable (fun ω => (cfc (fun x : ℝ => |x| ^ w.count false) A *
        vecMulVec (y ω) (y ω) ^ l).trace) μ ∧
      (∫ ω, (cfc (fun x : ℝ => |x| ^ w.count false) A *
        vecMulVec (y ω) (y ω) ^ l).trace ∂μ) ≤
          B * (cfc (fun x : ℝ => |x| ^ w.count false) A).trace) :
    Integrable (fun ω =>
      (insertionWord A (vecMulVec (y ω) (y ω) - 1) w).trace) μ ∧
      (∫ ω, (insertionWord A (vecMulVec (y ω) (y ω) - 1) w).trace ∂μ) ≤
        2 ^ w.count true * B * (cfc (fun x : ℝ => |x| ^ w.count false) A).trace := by
  let C := cfc (fun x : ℝ => |x| ^ w.count false) A
  let f (v : ℕ × List Bool) (ω : Ω) := (C * vecMulVec (y ω) (y ω) ^ v.2.count true).trace
  have hi (v : ℕ × List Bool) (hv : v ∈ subInsertionWords w) : Integrable (f v) μ :=
    (hmoment _ (by have h := (counts_of_mem_subInsertionWords hv).2; omega)).1
  have hls : ∀ ls : List (ℕ × List Bool), (∀ v ∈ ls, v ∈ subInsertionWords w) →
      Integrable (fun ω => (ls.map fun v => f v ω).sum) μ ∧
      (∫ ω, (ls.map fun v => f v ω).sum ∂μ) ≤ (ls.length : ℝ) * (B * C.trace) := by
    intro ls
    induction ls with
    | nil => intro _; simp
    | cons v ls ih =>
      intro hmem
      have hv := hmem v (by simp)
      obtain ⟨hit, hbt⟩ := ih (fun u hu => hmem u (List.mem_cons_of_mem _ hu))
      have hiv := hi v hv
      have hb := (hmoment (v.2.count true)
        (by have h := (counts_of_mem_subInsertionWords hv).2; omega)).2
      simp only [List.map_cons, List.sum_cons]
      refine ⟨hiv.add hit, ?_⟩
      rw [integral_add hiv hit]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      change (∫ ω, f v ω ∂μ) + (∫ ω, (ls.map fun v => f v ω).sum ∂μ) ≤ _
      change (∫ ω, f v ω ∂μ) ≤ B * C.trace at hb
      linarith
  obtain ⟨hG, hbG⟩ := hls _ (fun _ h => h)
  have hpoint (ω : Ω) :
      |(insertionWord A (vecMulVec (y ω) (y ω) - 1) w).trace| ≤
        ((subInsertionWords w).map fun v => f v ω).sum :=
    abs_trace_insertionWord_vecMulVec_sub_one_le_sum hA (y ω) w
  have hW : Integrable (fun ω =>
      (insertionWord A (vecMulVec (y ω) (y ω) - 1) w).trace) μ :=
    hG.mono' (measurable_trace_insertionWord_vecMulVec_sub_one y hy A w).aestronglyMeasurable
      (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hpoint ω)
  refine ⟨hW, ?_⟩
  calc
    _ ≤ ∫ ω, ((subInsertionWords w).map fun v => f v ω).sum ∂μ :=
      integral_mono hW hG fun ω => (le_abs_self _).trans (hpoint ω)
    _ ≤ _ := by
      simpa only [length_subInsertionWords, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using hbG

omit [IsProbabilityMeasure μ] in
/-- An isotropic vector integrates a rank-one trace test to the test trace.
Source: the isotropic quadratic-form identity.
Atlas: `khatri-rao-sharp-growth`. -/
theorem integrable_and_integral_trace_mul_vecMulVec_eq
    (y : Ω → ι → ℝ) (hy : Measurable y)
    (hsecond : ∀ i j, (∫ ω, y ω i * y ω j ∂μ) = if i = j then 1 else 0)
    (C : Matrix ι ι ℝ) :
    Integrable (fun ω => (C * vecMulVec (y ω) (y ω)).trace) μ ∧
      (∫ ω, (C * vecMulVec (y ω) (y ω)).trace ∂μ) = C.trace := by
  have hm (i : ι) : AEMeasurable (fun ω => y ω i) μ :=
    ((measurable_pi_apply i).comp hy).aemeasurable
  have he (ω : Ω) : (C * vecMulVec (y ω) (y ω)).trace = quadForm C (y ω) := by
    simp only [mul_vecMulVec, trace_vecMulVec, quadForm_def, star_trivial, dotProduct_comm]
  constructor
  · simpa only [he] using integrable_quadForm_of_second_moments C hm hsecond
  · simp_rw [he]
    exact integral_quadForm_eq_trace_of_second_moments C hm hsecond

/-- Centering an isotropic rank-one covariance sample kills every linear trace test.
Source: isotropy. Atlas: `khatri-rao-sharp-growth`. -/
theorem integrable_and_integral_trace_mul_vecMulVec_sub_one_eq_zero
    (y : Ω → ι → ℝ) (hy : Measurable y)
    (hsecond : ∀ i j, (∫ ω, y ω i * y ω j ∂μ) = if i = j then 1 else 0)
    (C : Matrix ι ι ℝ) :
    Integrable (fun ω => (C * (vecMulVec (y ω) (y ω) - 1)).trace) μ ∧
      (∫ ω, (C * (vecMulVec (y ω) (y ω) - 1)).trace ∂μ) = 0 := by
  obtain ⟨hi, he⟩ := integrable_and_integral_trace_mul_vecMulVec_eq y hy hsecond C
  simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub]
  exact ⟨hi.sub (integrable_const _), by rw [integral_sub hi (integrable_const _), he]; simp⟩

/-- The variance of a centered isotropic rank-one covariance sample is bounded
by its raw second moment, retaining each positive trace test.
Source: `E(H-I)^2=E H^2-I`.
Atlas: `khatri-rao-sharp-growth`. -/
theorem integrable_and_integral_trace_mul_vecMulVec_sub_one_sq_le
    (y : Ω → ι → ℝ) (hy : Measurable y)
    (hsecond : ∀ i j, (∫ ω, y ω i * y ω j ∂μ) = if i = j then 1 else 0)
    {v : ℝ}
    (hmoment : ∀ x : ι → ℝ,
      Integrable (fun ω => (y ω ⬝ᵥ y ω) * (x ⬝ᵥ y ω) ^ 2) μ ∧
        (∫ ω, (y ω ⬝ᵥ y ω) * (x ⬝ᵥ y ω) ^ 2 ∂μ) ≤ v * (x ⬝ᵥ x))
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) :
    Integrable (fun ω => (C * (vecMulVec (y ω) (y ω) - 1) ^ 2).trace) μ ∧
      (∫ ω, (C * (vecMulVec (y ω) (y ω) - 1) ^ 2).trace ∂μ) ≤ v * C.trace := by
  obtain ⟨hi1, he1⟩ := integrable_and_integral_trace_mul_vecMulVec_eq y hy hsecond C
  have hm (x : ι → ℝ) :
      Integrable (fun ω => (y ω ⬝ᵥ y ω) ^ 1 * (x ⬝ᵥ y ω) ^ 2) μ ∧
        (∫ ω, (y ω ⬝ᵥ y ω) ^ 1 * (x ⬝ᵥ y ω) ^ 2 ∂μ) ≤ v * (x ⬝ᵥ x) := by
    simpa only [pow_one] using hmoment x
  obtain ⟨hi2, hb2⟩ := integrable_and_integral_trace_mul_vecMulVec_pow_succ_le y 1 hm C hC
  norm_num only [Nat.reduceAdd] at hi2 hb2
  have he (ω : Ω) :
      (C * (vecMulVec (y ω) (y ω) - 1) ^ 2).trace =
        (C * vecMulVec (y ω) (y ω) ^ 2).trace -
          2 * (C * vecMulVec (y ω) (y ω)).trace + C.trace := by
    have hm : C * (vecMulVec (y ω) (y ω) - 1) ^ 2 =
        C * vecMulVec (y ω) (y ω) ^ 2 - C * vecMulVec (y ω) (y ω) -
          C * vecMulVec (y ω) (y ω) + C := by noncomm_ring
    rw [hm]
    simp only [Matrix.trace_add, Matrix.trace_sub]
    ring
  constructor
  · simp_rw [he]
    exact (hi2.sub (hi1.const_mul 2)).add (integrable_const _)
  · simp_rw [he]
    have hadd := integral_add (hi2.sub (hi1.const_mul 2)) (integrable_const C.trace)
    simp only [Pi.sub_apply] at hadd
    rw [hadd, integral_sub hi2 (hi1.const_mul 2), integral_const_mul, he1]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    linarith [hC.trace_nonneg]

/-- A factorial raw rank-one moment profile bounds every centered word with
at least two insertions, with explicit centering constants `4v` and `2R`.
Source: the rank-one word expansion in Heidary, Lemma `closed:lem:step`.
Atlas: `khatri-rao-sharp-growth`. -/
theorem integrable_and_integral_trace_centered_insertionWord_le_factorial
    (y : Ω → ι → ℝ) (hy : Measurable y)
    (hsecond : ∀ i j, (∫ ω, y ω i * y ω j ∂μ) = if i = j then 1 else 0)
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (w : List Bool)
    (hw : 2 ≤ w.count true) {v R : ℝ} (hv : 2 ≤ v) (hR : 1 ≤ R)
    (hraw : ∀ l, 2 ≤ l → l ≤ w.count true → ∀ x : ι → ℝ,
      Integrable (fun ω => (y ω ⬝ᵥ y ω) ^ (l - 1) * (x ⬝ᵥ y ω) ^ 2) μ ∧
        (∫ ω, (y ω ⬝ᵥ y ω) ^ (l - 1) * (x ⬝ᵥ y ω) ^ 2 ∂μ) ≤
          ((l.factorial : ℝ) / 2) * v * R ^ (l - 2) * (x ⬝ᵥ x)) :
    Integrable (fun ω =>
      (insertionWord A (vecMulVec (y ω) (y ω) - 1) w).trace) μ ∧
      (∫ ω, (insertionWord A (vecMulVec (y ω) (y ω) - 1) w).trace ∂μ) ≤
        ((w.count true).factorial : ℝ) / 2 * (4 * v) * (2 * R) ^ (w.count true - 2) *
          (cfc (fun x : ℝ => |x| ^ w.count false) A).trace := by
  let j := w.count true
  let B : ℝ := ((j.factorial : ℝ) / 2) * v * R ^ (j - 2)
  let C := cfc (fun x : ℝ => |x| ^ w.count false) A
  have hC : C.PosSemidef := posSemidef_cfc_of_nonneg_eigenvalues hA
    (fun _ => pow_nonneg (abs_nonneg _) _)
  have hjfact : (2 : ℝ) ≤ j.factorial := by
    exact_mod_cast (show 2 ≤ j.factorial from (by simpa using Nat.factorial_le hw))
  have hB : 1 ≤ B := by
    apply one_le_mul_of_one_le_of_one_le
    · apply one_le_mul_of_one_le_of_one_le
      · linarith
      · linarith
    · exact one_le_pow₀ hR
  have hm (l : ℕ) (hl : l ≤ w.count true) :
      Integrable (fun ω => (C * vecMulVec (y ω) (y ω) ^ l).trace) μ ∧
        (∫ ω, (C * vecMulVec (y ω) (y ω) ^ l).trace ∂μ) ≤ B * C.trace := by
    by_cases hl0 : l = 0
    · subst l
      simp only [pow_zero, Matrix.mul_one]
      refine ⟨integrable_const _, ?_⟩
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      exact le_mul_of_one_le_left hC.trace_nonneg hB
    by_cases hl1 : l = 1
    · subst l
      simp only [pow_one]
      obtain ⟨hi, he⟩ := integrable_and_integral_trace_mul_vecMulVec_eq y hy hsecond C
      exact ⟨hi, he.le.trans (le_mul_of_one_le_left hC.trace_nonneg hB)⟩
    have hl2 : 2 ≤ l := by omega
    have htrace := integrable_and_integral_trace_mul_vecMulVec_pow_succ_le
      y (l - 1) (hraw l hl2 hl) C hC
    rw [show l - 1 + 1 = l by omega] at htrace
    refine ⟨htrace.1, htrace.2.trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ hC.trace_nonneg
    dsimp [B]
    have hfact : (l.factorial : ℝ) ≤ j.factorial := by exact_mod_cast Nat.factorial_le hl
    have hpow : R ^ (l - 2) ≤ R ^ (j - 2) := pow_le_pow_right₀ hR (by omega)
    gcongr
  obtain ⟨hi, hb⟩ := integrable_and_integral_trace_insertionWord_sub_one_le y hy hA w hm
  refine ⟨hi, hb.trans_eq ?_⟩
  change 2 ^ j * B * C.trace = _
  have he : (2 : ℝ) ^ j = 4 * 2 ^ (j - 2) := by
    rw [show j = (j - 2) + 2 by dsimp [j]; omega, pow_add]
    norm_num
    ring
  rw [he]
  dsimp [B, C, j]
  rw [mul_pow]
  ring

/-- Actual centered isotropic rank-one covariance samples satisfy the finite
trace-moment update used by the sharp Khatri--Rao embedding bound.
Source: Heidary, Lemma `closed:lem:step`; the explicit centering factors here
are `4v` and `2R` rather than the manuscript's optimized shift.
Atlas: `khatri-rao-sharp-growth`. -/
theorem integrable_and_integral_trace_add_centered_rankOne_pow_le
    (y : Ω → ι → ℝ) (hy : Measurable y)
    (hsecond : ∀ i j, (∫ ω, y ω i * y ω j ∂μ) = if i = j then 1 else 0)
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {p : ℕ} (hp : 1 ≤ p)
    {v R : ℝ} (hv : 2 ≤ v) (hR : 1 ≤ R)
    (hraw : ∀ l, 2 ≤ l → l ≤ 2 * p → ∀ x : ι → ℝ,
      Integrable (fun ω => (y ω ⬝ᵥ y ω) ^ (l - 1) * (x ⬝ᵥ y ω) ^ 2) μ ∧
        (∫ ω, (y ω ⬝ᵥ y ω) ^ (l - 1) * (x ⬝ᵥ y ω) ^ 2 ∂μ) ≤
          ((l.factorial : ℝ) / 2) * v * R ^ (l - 2) * (x ⬝ᵥ x)) :
    Integrable (fun ω => ((A + (vecMulVec (y ω) (y ω) - 1)) ^ (2 * p)).trace) μ ∧
      (∫ ω, ((A + (vecMulVec (y ω) (y ω) - 1)) ^ (2 * p)).trace ∂μ) ≤
        (A ^ (2 * p)).trace + ∑ k ∈ Finset.range (2 * p - 1),
          ((2 * p).choose (k + 2) : ℝ) * ((k + 2).factorial : ℝ) / 2 *
            (4 * v) * (2 * R) ^ k *
              (cfc (fun x : ℝ => |x| ^ (2 * p - (k + 2))) A).trace := by
  let X : Ω → Matrix ι ι ℝ := fun ω => vecMulVec (y ω) (y ω) - 1
  have hlin (w : List Bool) (hw : w.count true = 1) :
      Integrable (fun ω => (insertionWord A (X ω) w).trace) μ ∧
        (∫ ω, (insertionWord A (X ω) w).trace ∂μ) = 0 := by
    simp_rw [trace_insertionWord_of_count_true_eq_one A _ w hw]
    exact integrable_and_integral_trace_mul_vecMulVec_sub_one_eq_zero y hy hsecond _
  have hword (j : ℕ) (hj : j ≤ 2 * p) (w : List Bool) (hw : w ∈ insertionWords (2 * p) j)
      (hj2 : 2 ≤ j) :=
    integrable_and_integral_trace_centered_insertionWord_le_factorial y hy hsecond hA w
      (by rw [(length_and_count_of_mem_insertionWords hw).2]; exact hj2) hv hR
      (fun l hl2 hlj => hraw l hl2
        (le_trans hlj (by rw [(length_and_count_of_mem_insertionWords hw).2]; exact hj)))
  have hi (j : ℕ) (hj : j ≤ 2 * p) (w : List Bool) (hw : w ∈ insertionWords (2 * p) j) :
      Integrable (fun ω => (insertionWord A (X ω) w).trace) μ := by
    by_cases hj0 : j = 0
    · have hc : w.count true = 0 := by simpa [hj0] using (length_and_count_of_mem_insertionWords hw).2
      simp_rw [insertionWord_eq_pow_of_count_true_eq_zero A _ w hc]
      exact integrable_const _
    by_cases hj1 : j = 1
    · exact (hlin w (by simpa [hj1] using (length_and_count_of_mem_insertionWords hw).2)).1
    exact (hword j hj w hw (by omega)).1
  refine ⟨(integrable_and_integral_trace_add_pow_eq_sum_insertionWords A X (2 * p) hi).1, ?_⟩
  apply integral_trace_add_pow_le_of_centered_word_budgets A X (by omega) (4 * v) (2 * R)
    (fun n => (cfc (fun x : ℝ => |x| ^ n) A).trace) hi
  · intro w hw
    exact (hlin w (length_and_count_of_mem_insertionWords hw).2).2
  · intro j hj2 hj w hw
    have hcounts := length_and_count_of_mem_insertionWords hw
    have hc : w.count false = 2 * p - j := by
      have htotal := count_false_add_count_true_eq_length w
      omega
    simpa only [hcounts.2, hc, mul_assoc] using (hword j hj w hw hj2).2

end NLAlib
