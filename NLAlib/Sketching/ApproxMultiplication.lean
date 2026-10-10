import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.LinearAlgebra.Matrix.DotProduct
import NLAlib.Matrix.Norms

/-!
# Approximate matrix multiplication from the JL moment property

If a random sketch `S` satisfies the **JL second-moment property** with parameter `ε`,
`E (‖Sx‖² − ‖x‖²)² ≤ ε² ‖x‖⁴` for every `x`, then for all fixed `A`, `B`

  `E ‖AᵀSᵀSB − AᵀB‖_F² ≤ ε² ‖A‖_F² ‖B‖_F²`

(`lintegral_frobSq_transpose_mul_sketch_sub_le`), with constant `1`.

Proof: entry `(i, j)` of the error is `⟨Saᵢ, Sbⱼ⟩ − ⟨aᵢ, bⱼ⟩` (`aᵢ`, `bⱼ` the columns). After
rescaling `u = c aᵢ`, `v = c⁻¹ bⱼ` so that `‖u‖² = ‖v‖² = ‖aᵢ‖‖bⱼ‖`, polarization writes it as
`Z(p) − Z(q)` with `Z(x) = ‖Sx‖² − ‖x‖²`, `p = (u + v)/2`, `q = (u − v)/2`. Minkowski in `L²`
(`lintegral_ofReal_sq_sub_le`) gives `‖Z(p) − Z(q)‖_{L²} ≤ ε(‖p‖² + ‖q‖²) = ε‖aᵢ‖‖bⱼ‖`; sum over
`i, j`. Everything is stated with lower Lebesgue integrals, so no integrability hypothesis is
needed.

Source: Woodruff 2014, Thm 2.8 (the `ℓ = 2` case of the JL moment property; Kane–Nelson 2014);
Sarlós 2006, Lem 6. Atlas: `amm-ose` (depends on no other result; the Gaussian instance of the
moment property is `gaussian-amm`).
-/

noncomputable section

open MeasureTheory
open scoped Matrix ENNReal

namespace NLAlib

/-- **Minkowski in `L²`, squared lower-integral form.** If `∫⁻ X² ≤ a²` and `∫⁻ Y² ≤ b²` with
`a, b ≥ 0` (written with `ENNReal.ofReal`), then `∫⁻ (X − Y)² ≤ (a + b)²`. Proof: the pointwise
bound `(X − Y)² ≤ (1 + b/a)X² + (1 + a/b)Y²` for `a, b > 0`, and the a.e.-zero cases.
Standard (Minkowski's inequality); atlas `amm-ose` (helper; belongs in
`ForMathlib/MeasureTheory/Integral.lean`). -/
theorem lintegral_ofReal_sq_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {X Y : α → ℝ} (hX : Measurable X) (hY : Measurable Y) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hXa : ∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂μ ≤ ENNReal.ofReal (a ^ 2))
    (hYb : ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂μ ≤ ENNReal.ofReal (b ^ 2)) :
    ∫⁻ ω, ENNReal.ofReal ((X ω - Y ω) ^ 2) ∂μ ≤ ENNReal.ofReal ((a + b) ^ 2) := by
  -- If one of the bounds is `0`, that variable vanishes a.e.
  have hzero : ∀ {Z : α → ℝ}, Measurable Z →
      ∫⁻ ω, ENNReal.ofReal (Z ω ^ 2) ∂μ ≤ ENNReal.ofReal (0 ^ 2) → Z =ᵐ[μ] 0 := by
    intro Z hZ h
    rw [show ((0 : ℝ) ^ 2) = 0 by ring, ENNReal.ofReal_zero, nonpos_iff_eq_zero,
      lintegral_eq_zero_iff (hZ.pow_const 2).ennreal_ofReal] at h
    filter_upwards [h] with ω hω
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hω ⊢
    nlinarith [sq_nonneg (Z ω)]
  rcases ha.eq_or_lt with ha0 | hapos
  · subst ha0
    have hX0 := hzero hX hXa
    calc ∫⁻ ω, ENNReal.ofReal ((X ω - Y ω) ^ 2) ∂μ = ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hX0] with ω hω
          simp only [Pi.zero_apply] at hω
          rw [hω]; ring_nf
      _ ≤ _ := by rw [zero_add]; exact hYb
  rcases hb.eq_or_lt with hb0 | hbpos
  · subst hb0
    have hY0 := hzero hY hYb
    calc ∫⁻ ω, ENNReal.ofReal ((X ω - Y ω) ^ 2) ∂μ = ∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hY0] with ω hω
          simp only [Pi.zero_apply] at hω
          rw [hω]; ring_nf
      _ ≤ _ := by rw [add_zero]; exact hXa
  -- Both bounds positive.
  set c₁ := 1 + b / a with hc₁
  set c₂ := 1 + a / b with hc₂
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hpt : ∀ ω, ENNReal.ofReal ((X ω - Y ω) ^ 2) ≤
      ENNReal.ofReal c₁ * ENNReal.ofReal (X ω ^ 2) +
        ENNReal.ofReal c₂ * ENNReal.ofReal (Y ω ^ 2) := by
    intro ω
    rw [← ENNReal.ofReal_mul hc₁0, ← ENNReal.ofReal_mul hc₂0,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have key : c₁ * X ω ^ 2 + c₂ * Y ω ^ 2 - (X ω - Y ω) ^ 2 =
        (b * X ω + a * Y ω) ^ 2 / (a * b) := by
      rw [hc₁, hc₂]; field_simp; ring
    have : 0 ≤ (b * X ω + a * Y ω) ^ 2 / (a * b) := by positivity
    linarith
  have hmX : Measurable fun ω => ENNReal.ofReal (X ω ^ 2) :=
    ENNReal.measurable_ofReal.comp (hX.pow_const 2)
  have hmY : Measurable fun ω => ENNReal.ofReal (Y ω ^ 2) :=
    ENNReal.measurable_ofReal.comp (hY.pow_const 2)
  calc ∫⁻ ω, ENNReal.ofReal ((X ω - Y ω) ^ 2) ∂μ
      ≤ ∫⁻ ω, (ENNReal.ofReal c₁ * ENNReal.ofReal (X ω ^ 2) +
          ENNReal.ofReal c₂ * ENNReal.ofReal (Y ω ^ 2)) ∂μ := lintegral_mono hpt
    _ = ENNReal.ofReal c₁ * ∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂μ +
          ENNReal.ofReal c₂ * ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂μ := by
        rw [lintegral_add_left (hmX.const_mul _), lintegral_const_mul _ hmX,
          lintegral_const_mul _ hmY]
    _ ≤ ENNReal.ofReal c₁ * ENNReal.ofReal (a ^ 2) + ENNReal.ofReal c₂ * ENNReal.ofReal (b ^ 2) :=
        by gcongr
    _ = ENNReal.ofReal ((a + b) ^ 2) := by
        rw [← ENNReal.ofReal_mul hc₁0, ← ENNReal.ofReal_mul hc₂0,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        rw [hc₁, hc₂]; field_simp; ring

section Sketch

variable {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} {k n : Type*} [Fintype k]
  [Fintype n]

omit [Fintype k] in
private theorem measurable_mulVec_dotProduct [Fintype k] {S : Ωs → Matrix k n ℝ}
    (hS : ∀ i j, Measurable fun ω => S ω i j) (u v : n → ℝ) :
    Measurable fun ω => (S ω *ᵥ u) ⬝ᵥ (S ω *ᵥ v) := by
  simp only [dotProduct, Matrix.mulVec]
  refine Finset.measurable_sum _ fun i _ => Measurable.mul ?_ ?_ <;>
    exact Finset.measurable_sum _ fun j _ => (hS i j).mul measurable_const

/-- Polarization for a sketch: with `Z(x) = ‖Sx‖² − ‖x‖²`, `p = (u + v)/2`, `q = (u − v)/2`,
`Z(p) − Z(q) = ⟨Su, Sv⟩ − ⟨u, v⟩`. Atlas `amm-ose` (helper). -/
theorem sub_eq_mulVec_dotProduct_sub_of_polarization (S : Matrix k n ℝ) (u v : n → ℝ) :
    ((S *ᵥ ((1 / 2 : ℝ) • (u + v))) ⬝ᵥ (S *ᵥ ((1 / 2 : ℝ) • (u + v))) -
        ((1 / 2 : ℝ) • (u + v)) ⬝ᵥ ((1 / 2 : ℝ) • (u + v))) -
      ((S *ᵥ ((1 / 2 : ℝ) • (u - v))) ⬝ᵥ (S *ᵥ ((1 / 2 : ℝ) • (u - v))) -
        ((1 / 2 : ℝ) • (u - v)) ⬝ᵥ ((1 / 2 : ℝ) • (u - v))) =
      (S *ᵥ u) ⬝ᵥ (S *ᵥ v) - u ⬝ᵥ v := by
  simp only [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_sub, smul_dotProduct,
    dotProduct_smul, add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub,
    smul_eq_mul, dotProduct_comm v u, dotProduct_comm (S *ᵥ v) (S *ᵥ u)]
  ring

/-- **Entrywise AMM bound.** Under the JL second-moment property with parameter `ε ≥ 0`, for
fixed vectors `a`, `b`, `E(⟨Sa, Sb⟩ − ⟨a, b⟩)² ≤ ε² ‖a‖² ‖b‖²`. Woodruff 2014, proof of
Thm 2.8; Kane–Nelson 2014. Atlas `amm-ose`. -/
theorem lintegral_mulVec_dotProduct_sub_sq_le {S : Ωs → Matrix k n ℝ}
    (hS : ∀ i j, Measurable fun ω => S ω i j) {ε : ℝ} (hε : 0 ≤ ε)
    (hmom : ∀ x : n → ℝ, ∫⁻ ω, ENNReal.ofReal (((S ω *ᵥ x) ⬝ᵥ (S ω *ᵥ x) - x ⬝ᵥ x) ^ 2) ∂μ
      ≤ ENNReal.ofReal (ε ^ 2 * (x ⬝ᵥ x) ^ 2))
    (a b : n → ℝ) :
    ∫⁻ ω, ENNReal.ofReal (((S ω *ᵥ a) ⬝ᵥ (S ω *ᵥ b) - a ⬝ᵥ b) ^ 2) ∂μ
      ≤ ENNReal.ofReal (ε ^ 2 * (a ⬝ᵥ a) * (b ⬝ᵥ b)) := by
  have haa := dotProduct_self_nonneg a
  have hbb := dotProduct_self_nonneg b
  -- Degenerate cases.
  by_cases ha0 : a ⬝ᵥ a = 0
  · have : a = 0 := dotProduct_self_eq_zero.mp ha0
    subst this
    simp
  by_cases hb0 : b ⬝ᵥ b = 0
  · have : b = 0 := dotProduct_self_eq_zero.mp hb0
    subst this
    simp
  have hapos : 0 < a ⬝ᵥ a := lt_of_le_of_ne haa (Ne.symm ha0)
  have hbpos : 0 < b ⬝ᵥ b := lt_of_le_of_ne hbb (Ne.symm hb0)
  set na := Real.sqrt (a ⬝ᵥ a) with hna
  set nb := Real.sqrt (b ⬝ᵥ b) with hnb
  have hna0 : 0 < na := Real.sqrt_pos.2 hapos
  have hnb0 : 0 < nb := Real.sqrt_pos.2 hbpos
  have hna2 : na ^ 2 = a ⬝ᵥ a := Real.sq_sqrt haa
  have hnb2 : nb ^ 2 = b ⬝ᵥ b := Real.sq_sqrt hbb
  set c := Real.sqrt (nb / na) with hc
  have hc0 : 0 < c := Real.sqrt_pos.2 (div_pos hnb0 hna0)
  have hc2 : c ^ 2 = nb / na := Real.sq_sqrt (div_pos hnb0 hna0).le
  set u := c • a with hu
  set v := c⁻¹ • b with hv
  set p := (1 / 2 : ℝ) • (u + v) with hp
  set q := (1 / 2 : ℝ) • (u - v) with hq
  set Z : (n → ℝ) → Ωs → ℝ := fun x ω => (S ω *ᵥ x) ⬝ᵥ (S ω *ᵥ x) - x ⬝ᵥ x with hZ
  have hZm : ∀ x, Measurable (Z x) := fun x =>
    (measurable_mulVec_dotProduct hS x x).sub measurable_const
  have hdiff : ∀ ω, Z p ω - Z q ω = (S ω *ᵥ a) ⬝ᵥ (S ω *ᵥ b) - a ⬝ᵥ b := by
    intro ω
    simp only [hZ, hp, hq]
    rw [sub_eq_mulVec_dotProduct_sub_of_polarization, hu, hv, Matrix.mulVec_smul,
      Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_assoc,
      mul_inv_cancel₀ hc0.ne', one_mul, one_mul]
  have hpq : p ⬝ᵥ p + q ⬝ᵥ q = na * nb := by
    have huu : u ⬝ᵥ u = na * nb := by
      rw [hu, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq,
        hc2, ← hna2]
      field_simp
    have hvv : v ⬝ᵥ v = na * nb := by
      rw [hv, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
        ← sq, inv_pow, hc2, ← hnb2]
      field_simp
    simp only [hp, hq, smul_dotProduct, dotProduct_smul, add_dotProduct, dotProduct_add,
      sub_dotProduct, dotProduct_sub, smul_eq_mul, dotProduct_comm v u]
    rw [huu, hvv]; ring
  have hp0 := dotProduct_self_nonneg p
  have hq0 := dotProduct_self_nonneg q
  have hmp : ∫⁻ ω, ENNReal.ofReal (Z p ω ^ 2) ∂μ ≤ ENNReal.ofReal ((ε * (p ⬝ᵥ p)) ^ 2) := by
    rw [mul_pow]; exact hmom p
  have hmq : ∫⁻ ω, ENNReal.ofReal (Z q ω ^ 2) ∂μ ≤ ENNReal.ofReal ((ε * (q ⬝ᵥ q)) ^ 2) := by
    rw [mul_pow]; exact hmom q
  have h := lintegral_ofReal_sq_sub_le (hZm p) (hZm q) (mul_nonneg hε hp0) (mul_nonneg hε hq0)
    hmp hmq
  simp only [hdiff] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  rw [← mul_add, hpq, ← hna2, ← hnb2]
  ring

/-- **Approximate matrix multiplication from the JL moment property.** If the random sketch
`S` (entrywise measurable) satisfies `E (‖Sx‖² − ‖x‖²)² ≤ ε² ‖x‖⁴` for every `x`, with `ε ≥ 0`,
then for fixed `A ∈ ℝ^{n×d₁}`, `B ∈ ℝ^{n×d₂}`,
`E ‖AᵀSᵀSB − AᵀB‖_F² ≤ ε² ‖A‖_F² ‖B‖_F²`.

Woodruff 2014, Thm 2.8 (the `ℓ = 2` case of the `(ε, δ, ℓ)`-JL moment property; Kane–Nelson
2014); Sarlós 2006, Lem 6. Atlas `amm-ose`. Deviations: stated with lower Lebesgue integrals
(no integrability hypothesis); the hypothesis is the second-moment property itself, not a tail
bound; constant `1`. -/
theorem lintegral_frobSq_transpose_mul_sketch_sub_le {d₁ d₂ : Type*} [Fintype d₁]
    [Fintype d₂] (S : Ωs → Matrix k n ℝ) (hS : ∀ i j, Measurable fun ω => S ω i j) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hmom : ∀ x : n → ℝ, ∫⁻ ω, ENNReal.ofReal (((S ω *ᵥ x) ⬝ᵥ (S ω *ᵥ x) - x ⬝ᵥ x) ^ 2) ∂μ
      ≤ ENNReal.ofReal (ε ^ 2 * (x ⬝ᵥ x) ^ 2))
    (A : Matrix n d₁ ℝ) (B : Matrix n d₂ ℝ) :
    ∫⁻ ω, ENNReal.ofReal (frobSq (Aᵀ * (S ω)ᵀ * S ω * B - Aᵀ * B)) ∂μ
      ≤ ENNReal.ofReal (ε ^ 2 * frobSq A * frobSq B) := by
  have hentry : ∀ ω i j, (Aᵀ * (S ω)ᵀ * S ω * B - Aᵀ * B) i j =
      (S ω *ᵥ (fun l => A l i)) ⬝ᵥ (S ω *ᵥ (fun l => B l j)) -
        (fun l => A l i) ⬝ᵥ (fun l => B l j) := by
    intro ω i j
    have h : Aᵀ * (S ω)ᵀ * S ω * B = (S ω * A)ᵀ * (S ω * B) := by
      rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    rw [Matrix.sub_apply, h]
    rfl
  have hfrob : ∀ ω, ENNReal.ofReal (frobSq (Aᵀ * (S ω)ᵀ * S ω * B - Aᵀ * B)) =
      ∑ i, ∑ j, ENNReal.ofReal (((S ω *ᵥ (fun l => A l i)) ⬝ᵥ (S ω *ᵥ (fun l => B l j)) -
        (fun l => A l i) ⬝ᵥ (fun l => B l j)) ^ 2) := by
    intro ω
    rw [frobSq_eq_sum_sq]
    simp_rw [hentry ω]
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun j _ => sq_nonneg _]
  have hm : ∀ i j, Measurable fun ω =>
      ENNReal.ofReal (((S ω *ᵥ (fun l => A l i)) ⬝ᵥ (S ω *ᵥ (fun l => B l j)) -
        (fun l => A l i) ⬝ᵥ (fun l => B l j)) ^ 2) := fun i j =>
    ENNReal.measurable_ofReal.comp
      (((measurable_mulVec_dotProduct hS _ _).sub measurable_const).pow_const 2)
  simp_rw [hfrob]
  rw [lintegral_finsetSum _ fun i _ => Finset.measurable_sum _ fun j _ => hm i j]
  have hA : frobSq A = ∑ i, (fun l => A l i) ⬝ᵥ (fun l => A l i) := by
    rw [frobSq_eq_sum_sq, Finset.sum_comm]; simp [dotProduct, sq]
  have hB : frobSq B = ∑ j, (fun l => B l j) ⬝ᵥ (fun l => B l j) := by
    rw [frobSq_eq_sum_sq, Finset.sum_comm]; simp [dotProduct, sq]
  set a : d₁ → ℝ := fun i => (fun l => A l i) ⬝ᵥ (fun l => A l i) with ha
  set b : d₂ → ℝ := fun j => (fun l => B l j) ⬝ᵥ (fun l => B l j) with hb
  have ha0 : ∀ i, 0 ≤ a i := fun i => dotProduct_self_nonneg _
  have hb0 : ∀ j, 0 ≤ b j := fun j => dotProduct_self_nonneg _
  have hsum : ε ^ 2 * frobSq A * frobSq B = ∑ i, ∑ j, ε ^ 2 * a i * b j := by
    rw [hA, hB, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum, ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (sq_nonneg ε) (ha0 i)) (hb0 j)]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [lintegral_finsetSum _ fun j _ => hm i j, ENNReal.ofReal_sum_of_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (sq_nonneg ε) (ha0 i)) (hb0 j)]
  exact Finset.sum_le_sum fun j _ => lintegral_mulVec_dotProduct_sub_sq_le hS hε hmom _ _

end Sketch

end NLAlib
