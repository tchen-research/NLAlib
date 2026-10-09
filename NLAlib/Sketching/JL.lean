import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import NLAlib.Gaussian.Basic
import NLAlib.Sketching.Basic

/-!
# The Johnson–Lindenstrauss lemma for a Gaussian sketch

`S = k^{-1/2} G` with `G` a `k × n` standard Gaussian matrix (`NLAlib.gaussianMatrix k n`,
matrix view `Matrix.of G`). Squared norms are written `v ⬝ᵥ v`.

* `jl_distributional` (SCAFFOLD): for fixed `x`,
  `P[|‖Sx‖² − ‖x‖²| > ε‖x‖²] ≤ 2 exp(−k(ε²/4 − ε³/6))` (Dasgupta–Gupta 2003, Lem 2.2).
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

/-- SCAFFOLD: jl-distributional.

Distributional Johnson–Lindenstrauss lemma for the Gaussian sketch (Dasgupta–Gupta 2003,
Lem 2.2; Woodruff 2014 §2.1): for `S = k^{-1/2} G` with `G` standard Gaussian `k × n`, any fixed
`x : ℝⁿ` and `0 < ε < 1`,
`P[|‖Sx‖² − ‖x‖²| > ε‖x‖²] ≤ 2 exp(−k(ε²/4 − ε³/6))`.

Deferred: the proof needs rotation invariance of the Gaussian matrix (`‖Gx‖² / ‖x‖²` is
`χ²_k`) and the two Chernoff tails of the chi-square law (atlas `rotation-invariance`,
`chi-square-upper-tail`, `chi-square-lower-tail`), none of which is yet in the library. -/
theorem jl_distributional (k n : ℕ) (x : Fin n → ℝ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    gaussianMatrix k n {G |
      |((1 / Real.sqrt k) • Matrix.of G) *ᵥ x ⬝ᵥ ((1 / Real.sqrt k) • Matrix.of G) *ᵥ x
        - x ⬝ᵥ x| > ε * (x ⬝ᵥ x)}
      ≤ ENNReal.ofReal (2 * Real.exp (-(k : ℝ) * (ε ^ 2 / 4 - ε ^ 3 / 6))) := by
  sorry

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
