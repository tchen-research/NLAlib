import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import NLAlib.Gaussian.Basic
import NLAlib.Gaussian.LinearImage
import NLAlib.Gaussian.Extreme.ChiSquare
import NLAlib.ForMathlib.Analysis.Real
import NLAlib.Sketching.Basic

/-!
# The Johnson–Lindenstrauss lemma for a Gaussian sketch

`S = k^{-1/2} G` with `G` a `k × n` standard Gaussian matrix (`NLAlib.gaussianMatrix k n`,
matrix view `Matrix.of G`). Squared norms are written `v ⬝ᵥ v`.

* `jl_distributional`: for fixed `x`,
  `P[|‖Sx‖² − ‖x‖²| > ε‖x‖²] ≤ 2 exp(−k(ε²/4 − ε³/6))` (Dasgupta–Gupta 2003, Lem 2.2), from the
  law of `G x` (`gaussianMatrix_map_mulVec_of_dotProduct_self_eq_one`) and the sharp chi-square
  tails (`measure_le_sum_sq_le_gaussianReal`, `measure_sum_sq_le_one_sub_mul_le_gaussianReal`).
* `jl_lemma`: union bound over all ordered pairs of a finite family `p : Fin N → Fin n → ℝ`,
  failure probability `≤ N² · 2 exp(−k(ε²/4 − ε³/6))` (Dasgupta–Gupta 2003, Thm 2.1).
* `jl_lemma_prob_le_of_log_le`: failure probability `≤ δ` once
  `k ≥ (ε²/4 − ε³/6)⁻¹ log(2N²/δ)`.
* `jl_lemma_prob_le_half`, `jl_lemma_exists`: with `k ≥ 48 log N / ε²` (`N ≥ 2`), failure
  probability `≤ 1/2`, hence a linear map `ℝⁿ → ℝᵏ` preserving all pairwise squared distances
  to within `1 ± ε` exists.

Arithmetic helpers: `sq_div_four_sub_pow_three_div_six_pos` (the exponent `ε²/4 − ε³/6` is
positive on `(0, 1)`) and `sq_mul_two_mul_exp_neg_mul_le_of_inv_mul_log_le`.

Atlas: `jl-distributional`, `jl-lemma`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- **Distributional Johnson–Lindenstrauss lemma** for the Gaussian sketch: for
`S = k^{-1/2} G` with `G` standard Gaussian `k × n`, any fixed `x : ℝⁿ` and `0 < ε < 1`,
`P[|‖Sx‖² − ‖x‖²| > ε‖x‖²] ≤ 2 exp(−k(ε²/4 − ε³/6))`.

Dasgupta–Gupta 2003, Lem 2.2 (stated there for the projection of a random unit vector; the
Gaussian-sketch form is Woodruff 2014 §2.1). Atlas: `jl-distributional`; uses
`gaussian-matrix-mulVec-law`, `chi-square-upper-tail`, `chi-square-lower-tail`.

Proof: with `u = x/‖x‖`, `‖Sx‖² = (‖x‖²/k) ‖Gu‖²` and `Gu` is a standard Gaussian vector, so the
event lies in `{χ²_k ≥ (1+ε)k} ∪ {χ²_k ≤ (1−ε)k}`. The Chernoff tails and
`log(1+ε) ≤ ε − ε²/2 + ε³/3`, `log(1−ε) ≤ −ε − ε²/2` bound each part by `exp(−k(ε²/4 − ε³/6))`.
Degenerate cases: for `x = 0` the event is empty; for `k = 0` the bound is `2`. -/
theorem jl_distributional (k n : ℕ) (x : Fin n → ℝ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    gaussianMatrix k n {G |
      |((1 / Real.sqrt k) • Matrix.of G) *ᵥ x ⬝ᵥ ((1 / Real.sqrt k) • Matrix.of G) *ᵥ x
        - x ⬝ᵥ x| > ε * (x ⬝ᵥ x)}
      ≤ ENNReal.ofReal (2 * Real.exp (-(k : ℝ) * (ε ^ 2 / 4 - ε ^ 3 / 6))) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    simp only [CharP.cast_eq_zero, neg_zero, zero_mul, Real.exp_zero]
    norm_num
  by_cases hx0 : x ⬝ᵥ x = 0
  · have hx : x = 0 := dotProduct_self_eq_zero.mp hx0
    subst hx
    simp
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : 0 < x ⬝ᵥ x := lt_of_le_of_ne (dotProduct_self_star_nonneg x) (Ne.symm hx0)
  set r := Real.sqrt (x ⬝ᵥ x) with hr_def
  have hr : 0 < r := Real.sqrt_pos.2 hpos
  set u := r⁻¹ • x with hu_def
  have hu : u ⬝ᵥ u = 1 := by
    rw [hu_def, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      ← sq, inv_pow, hr_def, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hx0]
  have hxu : x = r • u := by rw [hu_def, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  -- `‖Sx‖² = (‖x‖² / k) ‖G u‖²`
  have hid : ∀ G : Fin k → Fin n → ℝ,
      ((1 / Real.sqrt k) • Matrix.of G) *ᵥ x ⬝ᵥ ((1 / Real.sqrt k) • Matrix.of G) *ᵥ x
        = (x ⬝ᵥ x) / k * ∑ i, (Matrix.of G *ᵥ u) i ^ 2 := by
    intro G
    have hsq : (1 / Real.sqrt k) ^ 2 = 1 / k := by
      rw [div_pow, Real.sq_sqrt hkpos.le, one_pow]
    have hr2 : r ^ 2 = x ⬝ᵥ x := Real.sq_sqrt hpos.le
    conv_lhs => rw [hxu]
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq, mul_pow, hsq, hr2]
    simp only [dotProduct, ← sq]
    ring
  set f : (Fin k → Fin n → ℝ) → (Fin k → ℝ) := fun G => Matrix.of G *ᵥ u with hf_def
  have hf : Measurable f := by
    refine measurable_pi_lambda _ fun i => ?_
    simp only [hf_def, Matrix.mulVec, dotProduct, Matrix.of_apply]
    fun_prop
  set B₁ : Set (Fin k → ℝ) := {y | (1 + ε) * k ≤ ∑ i, y i ^ 2} with hB₁_def
  set B₂ : Set (Fin k → ℝ) := {y | ∑ i, y i ^ 2 ≤ (1 - ε) * k} with hB₂_def
  have hB₁ : MeasurableSet B₁ := measurableSet_le measurable_const (by fun_prop)
  have hB₂ : MeasurableSet B₂ := measurableSet_le (by fun_prop) measurable_const
  have hsub : {G : Fin k → Fin n → ℝ |
      |((1 / Real.sqrt k) • Matrix.of G) *ᵥ x ⬝ᵥ ((1 / Real.sqrt k) • Matrix.of G) *ᵥ x
        - x ⬝ᵥ x| > ε * (x ⬝ᵥ x)} ⊆ f ⁻¹' (B₁ ∪ B₂) := by
    intro G hG
    simp only [Set.mem_ofPred_eq, hid] at hG
    set s := ∑ i, (Matrix.of G *ᵥ u) i ^ 2 with hs_def
    simp only [Set.mem_preimage, Set.mem_union, hB₁_def, hB₂_def, Set.mem_ofPred_eq, hf_def,
      ← hs_def]
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have habs : |s - k| < ε * k := by rw [abs_lt]; constructor <;> linarith
    have heq : (x ⬝ᵥ x) / k * s - x ⬝ᵥ x = (x ⬝ᵥ x) / k * (s - k) := by
      field_simp
    rw [heq, abs_mul, abs_of_pos (by positivity : 0 < (x ⬝ᵥ x) / k)] at hG
    have : (x ⬝ᵥ x) / k * |s - k| < (x ⬝ᵥ x) / k * (ε * k) :=
      mul_lt_mul_of_pos_left habs (by positivity)
    have h3 : (x ⬝ᵥ x) / k * (ε * k) = ε * (x ⬝ᵥ x) := by field_simp
    linarith
  set c := ε ^ 2 / 4 - ε ^ 3 / 6 with hc_def
  have hlaw := gaussianMatrix_map_mulVec_of_dotProduct_self_eq_one (k := k) u hu
  have h₁ : (Measure.pi fun _ : Fin k => gaussianReal 0 1) B₁
      ≤ ENNReal.ofReal (Real.exp (-(k : ℝ) * c)) := by
    refine (measure_le_sum_sq_le_gaussianReal hε0.le).trans
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
    have hlog := log_one_add_le_sub_sq_div_two_add_pow_three_div_three hε0.le
    have : (k : ℝ) / 2 * (2 * c) ≤ (k : ℝ) / 2 * (ε - Real.log (1 + ε)) :=
      mul_le_mul_of_nonneg_left (by rw [hc_def]; linarith) (by positivity)
    linarith
  have h₂ : (Measure.pi fun _ : Fin k => gaussianReal 0 1) B₂
      ≤ ENNReal.ofReal (Real.exp (-(k : ℝ) * c)) := by
    refine (measure_sum_sq_le_one_sub_mul_le_gaussianReal hε0.le hε1).trans
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
    have hlog := log_one_sub_le_neg_sub_sq_div_two hε0.le hε1
    have hε3 : 0 ≤ ε ^ 3 := by positivity
    have hc : c ≤ ε ^ 2 / 4 := by rw [hc_def]; linarith
    have : (k : ℝ) / 2 * (ε + Real.log (1 - ε)) ≤ (k : ℝ) / 2 * (-(ε ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  calc _ ≤ gaussianMatrix k n (f ⁻¹' (B₁ ∪ B₂)) := measure_mono hsub
    _ = (Measure.pi fun _ : Fin k => gaussianReal 0 1) (B₁ ∪ B₂) := by
        rw [← Measure.map_apply hf (hB₁.union hB₂), hf_def, hlaw]
    _ ≤ (Measure.pi fun _ : Fin k => gaussianReal 0 1) B₁
          + (Measure.pi fun _ : Fin k => gaussianReal 0 1) B₂ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(k : ℝ) * c)) + ENNReal.ofReal (Real.exp (-(k : ℝ) * c)) :=
        add_le_add h₁ h₂
    _ = ENNReal.ofReal (2 * Real.exp (-(k : ℝ) * c)) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, two_mul]

/-- Johnson–Lindenstrauss lemma, union-bound form (Dasgupta–Gupta 2003, Thm 2.1): for a finite
family `p : Fin N → ℝⁿ`, the probability that the Gaussian sketch `S = k^{-1/2} G` distorts some
pairwise squared distance `‖p i − p j‖²` by more than a factor `1 ± ε` is at most
`N² · 2 exp(−k(ε²/4 − ε³/6))`.

Deviation: the union is taken over all `N²` ordered pairs (not the `N(N−1)/2` unordered ones),
which costs a constant factor `2` in the bound. No measurability hypothesis is needed (the union
bound holds for the outer measure).

Atlas: `jl-lemma`; uses `jl-distributional`. -/
theorem jl_lemma (k n N : ℕ) (p : Fin N → Fin n → ℝ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    gaussianMatrix k n {G | ∃ i j, i ≠ j ∧
      |((1 / Real.sqrt k) • Matrix.of G) *ᵥ (p i - p j) ⬝ᵥ
          ((1 / Real.sqrt k) • Matrix.of G) *ᵥ (p i - p j)
        - (p i - p j) ⬝ᵥ (p i - p j)| > ε * ((p i - p j) ⬝ᵥ (p i - p j))}
      ≤ ENNReal.ofReal ((N : ℝ) ^ 2 * 2 * Real.exp (-(k : ℝ) * (ε ^ 2 / 4 - ε ^ 3 / 6))) := by
  set b := 2 * Real.exp (-(k : ℝ) * (ε ^ 2 / 4 - ε ^ 3 / 6)) with hb
  let bad : Fin N → Fin N → Set (Fin k → Fin n → ℝ) := fun i j => {G |
      |((1 / Real.sqrt k) • Matrix.of G) *ᵥ (p i - p j) ⬝ᵥ
          ((1 / Real.sqrt k) • Matrix.of G) *ᵥ (p i - p j)
        - (p i - p j) ⬝ᵥ (p i - p j)| > ε * ((p i - p j) ⬝ᵥ (p i - p j))}
  have hsub : {G | ∃ i j, i ≠ j ∧
      |((1 / Real.sqrt k) • Matrix.of G) *ᵥ (p i - p j) ⬝ᵥ
          ((1 / Real.sqrt k) • Matrix.of G) *ᵥ (p i - p j)
        - (p i - p j) ⬝ᵥ (p i - p j)| > ε * ((p i - p j) ⬝ᵥ (p i - p j))}
      ⊆ ⋃ i, ⋃ j, bad i j := by
    rintro G ⟨i, j, -, hG⟩
    exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, hG⟩⟩
  calc _ ≤ gaussianMatrix k n (⋃ i, ⋃ j, bad i j) := measure_mono hsub
    _ ≤ ∑ i, gaussianMatrix k n (⋃ j, bad i j) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ i : Fin N, ∑ j : Fin N, gaussianMatrix k n (bad i j) :=
        Finset.sum_le_sum fun i _ => measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin N, ∑ _j : Fin N, ENNReal.ofReal b :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          jl_distributional k n (p i - p j) hε0 hε1
    _ = ENNReal.ofReal ((N : ℝ) ^ 2 * b) := by
        have hN : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
        rw [ENNReal.ofReal_mul hN, ENNReal.ofReal_pow (Nat.cast_nonneg N),
          ENNReal.ofReal_natCast]
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sq,
          mul_assoc]
    _ = _ := by rw [hb, mul_assoc]

/-- `ε²/4 − ε³/6 > 0` for `0 < ε < 1`: the exponent of the Johnson–Lindenstrauss tail
(Dasgupta–Gupta 2003, Lem 2.2) is positive. Helper for `jl-lemma`. -/
theorem sq_div_four_sub_pow_three_div_six_pos {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    0 < ε ^ 2 / 4 - ε ^ 3 / 6 := by
  have h : ε ^ 2 / 4 - ε ^ 3 / 6 = ε ^ 2 * (3 - 2 * ε) / 12 := by ring
  rw [h]; have : 0 < ε ^ 2 := by positivity
  apply div_pos _ (by norm_num); nlinarith

/-- Arithmetic step of the JL lemma: `N² · 2 exp(−k c) ≤ δ` as soon as `k ≥ c⁻¹ log(2N²/δ)`.
Helper for `jl-lemma`. -/
theorem sq_mul_two_mul_exp_neg_mul_le_of_inv_mul_log_le {N : ℕ} {k c δ : ℝ} (hc : 0 < c)
    (hδ : 0 < δ) (hk : c⁻¹ * Real.log (2 * (N : ℝ) ^ 2 / δ) ≤ k) :
    (N : ℝ) ^ 2 * 2 * Real.exp (-k * c) ≤ δ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [hδ.le]
  have hA : 0 < 2 * (N : ℝ) ^ 2 / δ := by positivity
  have hlog : Real.log (2 * (N : ℝ) ^ 2 / δ) ≤ k * c := by
    have := mul_le_mul_of_nonneg_right hk hc.le
    rwa [mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc.ne', mul_one] at this
  have hexp : Real.exp (-k * c) ≤ δ / (2 * (N : ℝ) ^ 2) := by
    calc Real.exp (-k * c) ≤ Real.exp (-Real.log (2 * (N : ℝ) ^ 2 / δ)) := by
          apply Real.exp_le_exp.2; linarith
      _ = δ / (2 * (N : ℝ) ^ 2) := by
          rw [Real.exp_neg, Real.exp_log hA, inv_div]
  have hpos : (0 : ℝ) < 2 * (N : ℝ) ^ 2 := by positivity
  calc (N : ℝ) ^ 2 * 2 * Real.exp (-k * c) = (2 * (N : ℝ) ^ 2) * Real.exp (-k * c) := by ring
    _ ≤ (2 * (N : ℝ) ^ 2) * (δ / (2 * (N : ℝ) ^ 2)) := by gcongr
    _ = δ := by field_simp

/-- Johnson–Lindenstrauss lemma with explicit dimension (Dasgupta–Gupta 2003, Thm 2.1): if
`0 < ε < 1`, `0 < δ` and `k ≥ (ε²/4 − ε³/6)⁻¹ log(2N²/δ)`, then with probability at least
`1 − δ` the Gaussian sketch `S = k^{-1/2} G` preserves all pairwise squared distances of
`p : Fin N → ℝⁿ` to within `1 ± ε`.

Deviation: Dasgupta–Gupta take `k ≥ 4 (ε²/2 − ε³/3)⁻¹ log N`, aiming at success probability
`1/N`; we state the general-`δ` form with the constant coming from the ordered-pair union bound
in `jl_lemma`.

Atlas: `jl-lemma`; uses `jl-distributional`. -/
theorem jl_lemma_prob_le_of_log_le (k n N : ℕ) (p : Fin N → Fin n → ℝ) {ε δ : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) (hδ : 0 < δ)
    (hk : (ε ^ 2 / 4 - ε ^ 3 / 6)⁻¹ * Real.log (2 * (N : ℝ) ^ 2 / δ) ≤ k) :
    gaussianMatrix k n {G | ∃ i j, i ≠ j ∧
      |((1 / Real.sqrt k) • Matrix.of G) *ᵥ (p i - p j) ⬝ᵥ
          ((1 / Real.sqrt k) • Matrix.of G) *ᵥ (p i - p j)
        - (p i - p j) ⬝ᵥ (p i - p j)| > ε * ((p i - p j) ⬝ᵥ (p i - p j))}
      ≤ ENNReal.ofReal δ :=
  (jl_lemma k n N p hε0 hε1).trans <| ENNReal.ofReal_le_ofReal <|
    sq_mul_two_mul_exp_neg_mul_le_of_inv_mul_log_le
      (sq_div_four_sub_pow_three_div_six_pos hε0 hε1) hδ hk

/-- Johnson–Lindenstrauss lemma, `O(ε⁻² log N)` form (Dasgupta–Gupta 2003, Thm 2.1): for
`N ≥ 2` points, `0 < ε < 1` and `k ≥ 48 log N / ε²`, the Gaussian sketch `S = k^{-1/2} G`
distorts some pairwise squared distance by more than `1 ± ε` with probability at most `1/2`.

Deviation: the explicit constant `48` (from `(ε²/4 − ε³/6)⁻¹ ≤ 12/ε²` and
`log(4N²) ≤ 4 log N` for `N ≥ 2`) is not optimised; Dasgupta–Gupta's constant is `4·(1/2 − ε/3)⁻¹`
at failure probability `1 − 1/N`.

Atlas: `jl-lemma`; uses `jl-distributional`. -/
theorem jl_lemma_prob_le_half (k n N : ℕ) (p : Fin N → Fin n → ℝ) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) (hN : 2 ≤ N) (hk : 48 * Real.log N / ε ^ 2 ≤ k) :
    gaussianMatrix k n {G | ∃ i j, i ≠ j ∧
      |((1 / Real.sqrt k) • Matrix.of G) *ᵥ (p i - p j) ⬝ᵥ
          ((1 / Real.sqrt k) • Matrix.of G) *ᵥ (p i - p j)
        - (p i - p j) ⬝ᵥ (p i - p j)| > ε * ((p i - p j) ⬝ᵥ (p i - p j))}
      ≤ ENNReal.ofReal (1 / 2) := by
  apply jl_lemma_prob_le_of_log_le k n N p hε0 hε1 (by norm_num)
  have hc := sq_div_four_sub_pow_three_div_six_pos hε0 hε1
  have hε2 : 0 < ε ^ 2 := by positivity
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN'
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- `log (2 N² / (1/2)) = log 4 + 2 log N ≤ 4 log N`
  have hL : Real.log (2 * (N : ℝ) ^ 2 / (1 / 2)) ≤ 4 * Real.log N := by
    have hNpos : (0 : ℝ) < N := by linarith
    have : 2 * (N : ℝ) ^ 2 / (1 / 2) = 2 * 2 * (N : ℝ) ^ 2 := by ring
    rw [this, Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num)
      (by norm_num), Real.log_pow]
    push_cast; linarith
  -- `(ε²/4 − ε³/6)⁻¹ ≤ 12 / ε²`
  have hci : (ε ^ 2 / 4 - ε ^ 3 / 6)⁻¹ ≤ 12 / ε ^ 2 := by
    rw [inv_le_comm₀ hc (by positivity), inv_div]
    have : ε ^ 3 = ε ^ 2 * ε := by ring
    rw [this]
    nlinarith [mul_pos hε2 (sub_pos.2 hε1)]
  have hlogN0 : 0 ≤ Real.log N := hlog2.le.trans hlogN
  calc (ε ^ 2 / 4 - ε ^ 3 / 6)⁻¹ * Real.log (2 * (N : ℝ) ^ 2 / (1 / 2))
      ≤ (12 / ε ^ 2) * (4 * Real.log N) := by
        apply mul_le_mul hci hL _ (by positivity)
        apply Real.log_nonneg
        have : (1 : ℝ) ≤ N ^ 2 := by nlinarith
        rw [le_div_iff₀ (by norm_num)]; nlinarith
    _ = 48 * Real.log N / ε ^ 2 := by field_simp; ring
    _ ≤ k := hk

/-- Johnson–Lindenstrauss lemma, existence form (Johnson–Lindenstrauss 1984; Dasgupta–Gupta
2003, Thm 2.1): any `N ≥ 2` points of `ℝⁿ` admit a linear map `S : ℝⁿ → ℝᵏ` with
`k ≥ 48 log N / ε²` that preserves every pairwise squared distance to within `1 ± ε`.

Atlas: `jl-lemma`; uses `jl-distributional`. -/
theorem jl_lemma_exists (k n N : ℕ) (p : Fin N → Fin n → ℝ) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) (hN : 2 ≤ N) (hk : 48 * Real.log N / ε ^ 2 ≤ k) :
    ∃ S : Matrix (Fin k) (Fin n) ℝ, ∀ i j,
      (1 - ε) * ((p i - p j) ⬝ᵥ (p i - p j)) ≤ S *ᵥ (p i - p j) ⬝ᵥ S *ᵥ (p i - p j) ∧
      S *ᵥ (p i - p j) ⬝ᵥ S *ᵥ (p i - p j) ≤ (1 + ε) * ((p i - p j) ⬝ᵥ (p i - p j)) := by
  by_contra hcon
  push Not at hcon
  have hall : {G : Fin k → Fin n → ℝ | ∃ i j, i ≠ j ∧
      |((1 / Real.sqrt k) • Matrix.of G) *ᵥ (p i - p j) ⬝ᵥ
          ((1 / Real.sqrt k) • Matrix.of G) *ᵥ (p i - p j)
        - (p i - p j) ⬝ᵥ (p i - p j)| > ε * ((p i - p j) ⬝ᵥ (p i - p j))} = Set.univ := by
    refine Set.eq_univ_of_forall fun G => ?_
    obtain ⟨i, j, hij⟩ := hcon ((1 / Real.sqrt k) • Matrix.of G)
    refine ⟨i, j, ?_, ?_⟩
    · rintro rfl
      simp at hij
    · rw [gt_iff_lt, lt_abs]
      by_cases h : (1 - ε) * ((p i - p j) ⬝ᵥ (p i - p j)) ≤
          ((1 / Real.sqrt k) • Matrix.of G) *ᵥ (p i - p j) ⬝ᵥ
            ((1 / Real.sqrt k) • Matrix.of G) *ᵥ (p i - p j)
      · left; have := hij h; linarith
      · right; push Not at h; linarith
  have h := jl_lemma_prob_le_half k n N p hε0 hε1 hN hk
  rw [hall, measure_univ] at h
  have : (1 : ENNReal) ≤ ENNReal.ofReal (1 / 2) := h
  rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by norm_num)] at this
  norm_num at this

end NLAlib
