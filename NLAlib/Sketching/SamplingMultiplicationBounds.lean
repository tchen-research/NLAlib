import NLAlib.Sketching.SamplingMultiplication

/-!
# Approximate column-row probabilities for sampled multiplication

Probability domination by `β w_i/W` yields the manuscript's exact
`1/(βc)` mean-square bound for the literal algorithm. Source: `sa:amm-theorem`.
Atlas: `amm-sampling`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Matrix Matrix.Norms.Frobenius NNReal
namespace NLAlib

/-- Approximate column-row sampling probabilities give the exact complex
mean-square upper bound. Zero-mass support is derived from domination;
the estimator is the actual rescaled sampled column/row product.
Source: operator re-derivation `sa:amm-theorem`, approximate-law variant.
atlas: amm-sampling -/
theorem integral_frobenius_sampled_mul_sub_sq_le_of_probability_domination
    {m n t : Type*} [Fintype m] [Fintype n] [Fintype t]
    [MeasurableSpace n] [MeasurableSingletonClass n]
    (A : Matrix m n ℂ) (B : Matrix n t ℂ)
    (p : n → ℝ≥0) (hp : ∑ i, p i = 1)
    (hW : 0 < ∑ i, columnRowWeight A B i) {β : ℝ} (hβ : 0 < β)
    (hdom : ∀ i, β * columnRowWeight A B i / ∑ j, columnRowWeight A B j ≤ p i)
    {c : ℕ} (hc : 0 < c) :
    (∫ ω : Fin c → n, ‖sampledColumnMatrix A p ω * sampledRowMatrix B p ω - A * B‖ ^ 2
      ∂Measure.pi (fun _ => finiteSamplingLaw p hp)) ≤
      ‖A‖ ^ 2 * ‖B‖ ^ 2 / (β * c) := by
  classical
  let W := ∑ i, columnRowWeight A B i
  have hsupp : ∀ i, p i = 0 → Matrix.vecMulVec (fun a => A a i) (fun b => B i b) = 0 := by
    intro i hi
    apply vecMulVec_eq_zero_of_columnRowWeight_eq_zero A B i
    have hh := hdom i
    rw [hi, NNReal.coe_zero, div_le_iff₀ hW, zero_mul] at hh
    have hw := columnRowWeight_nonneg A B i
    nlinarith
  have hterm (i : n) : columnRowWeight A B i ^ 2 / p i ≤ (W / β) * columnRowWeight A B i := by
    by_cases hi : (p i : ℝ) = 0
    · rw [hi, div_zero]
      exact mul_nonneg (div_nonneg hW.le hβ.le) (columnRowWeight_nonneg A B i)
    · have hip : 0 < (p i : ℝ) := lt_of_le_of_ne (p i).coe_nonneg (Ne.symm hi)
      rw [show (W / β) * columnRowWeight A B i = W * columnRowWeight A B i / β by ring,
        div_le_div_iff₀ hip hβ]
      have hh := hdom i
      rw [div_le_iff₀ hW] at hh
      have hm := mul_le_mul_of_nonneg_right hh (columnRowWeight_nonneg A B i)
      dsimp only [W]
      nlinarith
  have hmoment : (∑ i, ((∑ a, ‖A a i‖ ^ 2) * ∑ b, ‖B i b‖ ^ 2) / p i) ≤ W ^ 2 / β := by
    simp_rw [← columnRowWeight_sq]
    calc
      _ ≤ ∑ i, (W / β) * columnRowWeight A B i := Finset.sum_le_sum (fun i _ => hterm i)
      _ = _ := by rw [← Finset.mul_sum]; change (W / β) * W = W ^ 2 / β; ring
  rw [integral_frobenius_sampled_mul_sub_sq A B p hp hsupp hc, one_div_mul_eq_div]
  calc
    _ ≤ (W ^ 2 / β) / (c : ℝ) := div_le_div_of_nonneg_right
      ((sub_le_self _ (sq_nonneg _)).trans hmoment) (Nat.cast_nonneg c)
    _ ≤ (‖A‖ ^ 2 * ‖B‖ ^ 2 / β) / (c : ℝ) :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (sum_columnRowWeight_sq_le A B) hβ.le)
        (Nat.cast_nonneg c)
    _ = _ := by ring

/-- The approximate-law multiplication bound for literal real sampled
columns and rows, stated with the existing real `frobSq` definition.
Source: `sa:amm-theorem`; atlas `amm-sampling`. -/
theorem integral_frobSq_sampled_mul_sub_le_of_probability_domination
    {m n t : Type*} [Fintype m] [Fintype n] [Fintype t]
    [MeasurableSpace n] [MeasurableSingletonClass n]
    (A : Matrix m n ℝ) (B : Matrix n t ℝ)
    (p : n → ℝ≥0) (hp : ∑ i, p i = 1)
    (hW : 0 < ∑ i, columnRowWeight A B i) {β : ℝ} (hβ : 0 < β)
    (hdom : ∀ i, β * columnRowWeight A B i / ∑ j, columnRowWeight A B j ≤ p i)
    {c : ℕ} (hc : 0 < c) :
    (∫ ω : Fin c → n,
      frobSq (sampledColumnMatrixReal A p ω * sampledRowMatrixReal B p ω - A * B)
      ∂Measure.pi (fun _ => finiteSamplingLaw p hp)) ≤ frobSq A * frobSq B / (β * c) := by
  have hw : columnRowWeight (A.map Complex.ofReal) (B.map Complex.ofReal) =
      columnRowWeight A B := by
    funext i
    simp [columnRowWeight, Matrix.map_apply]
  have h := integral_frobenius_sampled_mul_sub_sq_le_of_probability_domination
    (A.map Complex.ofReal) (B.map Complex.ofReal) p hp (by rwa [hw]) hβ
    (by simpa only [hw] using hdom) hc
  simp only [sampledColumnMatrix_map_ofReal, sampledRowMatrix_map_ofReal] at h
  have hmap : ∀ X : Matrix m (Fin c) ℝ, ∀ Y : Matrix (Fin c) t ℝ,
      X.map Complex.ofReal * Y.map Complex.ofReal - A.map Complex.ofReal * B.map Complex.ofReal =
        (X * Y - A * B).map Complex.ofReal := by
    intro X Y
    ext a b
    simp [Matrix.mul_apply, Matrix.map_apply, Complex.ofReal_sum]
  simpa only [hmap, frobenius_norm_sq_map_ofReal_eq_frobSq] using h

end NLAlib
