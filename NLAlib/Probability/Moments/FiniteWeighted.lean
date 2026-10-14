import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Even moments of weighted finite sums of squares

Finite Jensen preserves a common even-moment budget under weighted sums
of squares. No independence among the summands is needed.
-/

noncomputable section

open MeasureTheory

namespace NLAlib

/-- A convex combination of squares preserves a common even-moment budget.
This is finite Jensen followed by integration, with integrability deduced
from the same pointwise domination. -/
theorem integrable_and_integral_weighted_sq_pow_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω}
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (X : ι → Ω → ℝ) (hX : ∀ i, AEMeasurable (X i) μ)
    (p : ℕ) (hXi : ∀ i, Integrable (fun ω => X i ω ^ (2 * p)) μ)
    {C : ℝ} (hmoment : ∀ i, (∫ ω, X i ω ^ (2 * p) ∂μ) ≤ C) :
    Integrable (fun ω => (∑ i, w i * X i ω ^ 2) ^ p) μ ∧
      (∫ ω, (∑ i, w i * X i ω ^ 2) ^ p ∂μ) ≤ C := by
  classical
  have hright : Integrable (fun ω => ∑ i, w i * X i ω ^ (2 * p)) μ :=
    integrable_finsetSum _ fun i _ => (hXi i).const_mul (w i)
  have hpoint (ω : Ω) :
      (∑ i, w i * X i ω ^ 2) ^ p ≤ ∑ i, w i * X i ω ^ (2 * p) := by
    simpa only [← pow_mul] using Real.pow_arith_mean_le_arith_mean_pow
      Finset.univ w (fun i => X i ω ^ 2) (fun i _ => hw i) hsum
      (fun i _ => sq_nonneg _) p
  have hleft : Integrable (fun ω => (∑ i, w i * X i ω ^ 2) ^ p) μ := by
    apply hright.mono_nonneg
      (show AEMeasurable (fun ω => (∑ i, w i * X i ω ^ 2) ^ p) μ from by
        fun_prop).aestronglyMeasurable
    · exact ae_of_all _ fun ω => pow_nonneg
        (Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)) p
    · exact ae_of_all _ hpoint
  refine ⟨hleft, ?_⟩
  calc
    (∫ ω, (∑ i, w i * X i ω ^ 2) ^ p ∂μ) ≤
        ∫ ω, ∑ i, w i * X i ω ^ (2 * p) ∂μ :=
      integral_mono hleft hright hpoint
    _ = ∑ i, w i * ∫ ω, X i ω ^ (2 * p) ∂μ := by
      rw [integral_finsetSum _ fun i _ => (hXi i).const_mul (w i)]
      simp only [integral_const_mul]
    _ ≤ ∑ i, w i * C := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hmoment i) (hw i)
    _ = C := by rw [← Finset.sum_mul, hsum, one_mul]

/-- A finite Euclidean sum of scalar variables with a common even-moment
budget is bounded by the squared coefficient norm to the matching power.
The scalar variables may be arbitrarily dependent. -/
theorem integrable_and_integral_sum_mul_sq_pow_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω}
    (c : ι → ℝ) (X : ι → Ω → ℝ) (hX : ∀ i, AEMeasurable (X i) μ)
    {p : ℕ} (hp : 0 < p) (hXi : ∀ i, Integrable (fun ω => X i ω ^ (2 * p)) μ)
    {C : ℝ} (hmoment : ∀ i, (∫ ω, X i ω ^ (2 * p) ∂μ) ≤ C) :
    Integrable (fun ω => (∑ i, (c i * X i ω) ^ 2) ^ p) μ ∧
      (∫ ω, (∑ i, (c i * X i ω) ^ 2) ^ p ∂μ) ≤ C * (∑ i, c i ^ 2) ^ p := by
  classical
  let s : ℝ := ∑ i, c i ^ 2
  have hs : 0 ≤ s := Finset.sum_nonneg fun i _ => sq_nonneg _
  by_cases hs0 : s = 0
  · have hc (i : ι) : c i = 0 := by
      have hi : c i ^ 2 ≤ s := Finset.single_le_sum (fun j _ => sq_nonneg (c j))
        (Finset.mem_univ i)
      nlinarith [sq_nonneg (c i)]
    simp [hc, ne_of_gt hp]
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  let w : ι → ℝ := fun i => c i ^ 2 / s
  have hw (i : ι) : 0 ≤ w i := div_nonneg (sq_nonneg _) hs
  have hw1 : ∑ i, w i = 1 := by
    dsimp [w]
    rw [← Finset.sum_div]
    exact div_self hs0
  have h := integrable_and_integral_weighted_sq_pow_le w hw hw1 X hX p hXi hmoment
  have hpoint (ω : Ω) : (∑ i, (c i * X i ω) ^ 2) ^ p =
      s ^ p * (∑ i, w i * X i ω ^ 2) ^ p := by
    rw [← mul_pow]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [w]
    field_simp
  refine ⟨?_, ?_⟩
  · simpa only [← hpoint] using h.1.const_mul (s ^ p)
  · calc
      (∫ ω, (∑ i, (c i * X i ω) ^ 2) ^ p ∂μ) =
          s ^ p * ∫ ω, (∑ i, w i * X i ω ^ 2) ^ p ∂μ := by
            simp_rw [hpoint]
            rw [integral_const_mul]
      _ ≤ s ^ p * C := mul_le_mul_of_nonneg_left h.2 (pow_nonneg hs _)
      _ = C * (∑ i, c i ^ 2) ^ p := mul_comm _ _

end NLAlib
