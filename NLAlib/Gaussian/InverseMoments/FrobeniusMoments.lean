/-
Ported from the Prove2me workspace (Gaussian Random Matrices series, solutions
`Sol_GaussianMatrix_inverse_wishart_frobenius_moment`,
`Sol_GaussianMatrix_pinv_frobenius_fourth_moment`, `Sol_GaussianMatrix_pinv_frobenius_tail`).
-/
import NLAlib.Gaussian.InverseMoments.OffDiagonal

/-!
# Frobenius moments and tail of the inverse Wishart matrix and the pseudoinverse

For an `r × k` standard Gaussian matrix `G` with pseudoinverse `G† = pinvR G = Gᵀ (G Gᵀ)⁻¹`:

* `integrable_and_integral_frobSq_inv_self_mul_transpose_gaussianMatrix`:
  `E‖(G Gᵀ)⁻¹‖_F² = r(k-1)/((k-r)(k-r-1)(k-r-3))` for `r + 4 ≤ k`
  (atlas `inverse-wishart-frob-moment`);
* `integrable_and_integral_frobSq_pinvR_sq_gaussianMatrix`:
  `E‖G†‖_F⁴ = (r²(k-r) - 2r(r-1))/((k-r)(k-r-1)(k-r-3))` for `r + 4 ≤ k`
  (Tropp–Webber 2023, Lemma B.2; atlas `pinv-frob-fourth-moment`);
* `gaussianMatrix_lt_frobSq_pinvR_le`: `P[‖G†‖_F² > 12 r t/(k-r)] ≤ 4 t^{-(k-r)/2}` for
  `t ≥ 1`, `r + 4 ≤ k` (HMT 2011, Thm A.6 / Prop 10.4; atlas `pinv-frob-tail`).

All three are proved (no scaffold). Proof source: Prove2me workspace, Gaussian Random Matrices
series; the workspace's `inv_chi_square_Lq_bound` is
`NLAlib.integrable_and_integral_rpow_inv_sum_sq_gaussianReal_lt` (atlas
`chi-square-neg-moment`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- Counting diagonal and off-diagonal terms of an `r × r` double sum. -/
private lemma sum_sum_ite_eq_mul_add {r : ℕ} (a b : ℝ) :
    (∑ i : Fin r, ∑ j : Fin r, if i = j then a else b) = r * a + ((r : ℝ) * r - r) * b := by
  have : ∀ i : Fin r, (∑ j : Fin r, if i = j then a else b) = a + ((r : ℝ) - 1) * b := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    rw [if_pos rfl, Finset.sum_congr rfl
        (fun j hj => if_neg (Ne.symm (Finset.ne_of_mem_erase hj))),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos r with h | h
    · exact (Fin.elim0 (h ▸ i))
    · rw [Nat.cast_sub (by omega)]; push_cast; ring
  simp_rw [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **Frobenius moment of the inverse Wishart matrix.** For an `r × k` standard Gaussian matrix
`G` with `r + 4 ≤ k`, `‖(G Gᵀ)⁻¹‖_F²` is integrable and
`E‖(G Gᵀ)⁻¹‖_F² = r(k-1)/((k-r)(k-r-1)(k-r-3))`.

Tropp–Webber 2023, proof of Lemma B.2 (second moments of the inverse Wishart matrix). Atlas:
`inverse-wishart-frob-moment`. Proof: sum of the diagonal
(`integrable_and_integral_inv_self_mul_transpose_apply_self_sq_gaussianMatrix`) and
off-diagonal (`integrable_and_integral_inv_self_mul_transpose_apply_sq_gaussianMatrix`) second
moments, which use atlas `inverse-wishart-mean` and `chi-square-neg-moment`. Ported from
Prove2me solution `GaussianMatrix.inverse_wishart_frobenius_moment`.
atlas: inverse-wishart-frob-moment -/
theorem integrable_and_integral_frobSq_inv_self_mul_transpose_gaussianMatrix {r k : ℕ}
    (hrk : r + 4 ≤ k) :
    Integrable (fun G : Fin r → Fin k → ℝ => frobSq (Matrix.of G * (Matrix.of G)ᵀ)⁻¹)
      (gaussianMatrix r k) ∧
    ∫ G, frobSq (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ∂(gaussianMatrix r k)
      = (r : ℝ) * ((k : ℝ) - 1)
          / (((k : ℝ) - r) * ((k : ℝ) - r - 1) * ((k : ℝ) - r - 3)) := by
  set M : (Fin r → Fin k → ℝ) → Matrix (Fin r) (Fin r) ℝ :=
    fun G => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ with hM
  have hfun : (fun G : Fin r → Fin k → ℝ => frobSq (Matrix.of G * (Matrix.of G)ᵀ)⁻¹)
      = fun G => ∑ i, ∑ j, M G i j ^ 2 := by
    funext G; rw [frobSq_eq_sum_sq]
  have hterm : ∀ i j : Fin r, Integrable (fun G => M G i j ^ 2) (gaussianMatrix r k) ∧
      ∫ G, M G i j ^ 2 ∂(gaussianMatrix r k)
        = if i = j then 1 / (((k : ℝ) - r - 1) * ((k : ℝ) - r - 3))
          else 1 / (((k : ℝ) - r) * ((k : ℝ) - r - 1) * ((k : ℝ) - r - 3)) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      exact integrable_and_integral_inv_self_mul_transpose_apply_self_sq_gaussianMatrix hrk i
    · rw [if_neg hij]
      exact integrable_and_integral_inv_self_mul_transpose_apply_sq_gaussianMatrix hrk i j hij
  rw [hfun]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hterm i j).1, ?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hterm i j).1]
  simp_rw [integral_finsetSum _ fun j _ => (hterm _ j).1, fun i j => (hterm i j).2]
  rw [sum_sum_ite_eq_mul_add]
  have hx : (4 : ℝ) ≤ (k : ℝ) - r := by
    have : ((r + 4 : ℕ) : ℝ) ≤ k := by exact_mod_cast hrk
    push_cast at this; linarith
  have h1 : (k : ℝ) - r ≠ 0 := by linarith
  have h2 : (k : ℝ) - r - 1 ≠ 0 := by linarith
  have h3 : (k : ℝ) - r - 3 ≠ 0 := by linarith
  field_simp
  ring

/-- **Fourth Frobenius moment of the Gaussian pseudoinverse.** For an `r × k` standard Gaussian
matrix `G` with `r + 4 ≤ k`, `‖G†‖_F⁴` is integrable and
`E‖G†‖_F⁴ = (r²(k-r) - 2r(r-1))/((k-r)(k-r-1)(k-r-3))`, with `G† = pinvR G`.

Tropp–Webber 2023, Lemma B.2. Atlas: `pinv-frob-fourth-moment`. Proof: `‖G†‖_F² = tr (G Gᵀ)⁻¹`
(`frobSq_pinvR_eq_trace_inv`, atlas `pseudoinverse`), so `‖G†‖_F⁴ = ∑ᵢⱼ Nᵢᵢ Nⱼⱼ`; the diagonal
terms are `integrable_and_integral_inv_self_mul_transpose_apply_self_sq_gaussianMatrix` and the
mixed ones
`integrable_and_integral_inv_self_mul_transpose_apply_self_mul_apply_self_gaussianMatrix`
(atlas `inverse-wishart-mean`, `chi-square-neg-moment`, `rotation-invariance`). Ported from
Prove2me solution `GaussianMatrix.pinv_frobenius_fourth_moment`.
atlas: pinv-frob-fourth-moment -/
theorem integrable_and_integral_frobSq_pinvR_sq_gaussianMatrix {r k : ℕ} (hrk : r + 4 ≤ k) :
    Integrable (fun G : Fin r → Fin k → ℝ => frobSq (pinvR (Matrix.of G)) ^ 2)
      (gaussianMatrix r k) ∧
    ∫ G, frobSq (pinvR (Matrix.of G)) ^ 2 ∂(gaussianMatrix r k)
      = ((r : ℝ) ^ 2 * ((k : ℝ) - r) - 2 * r * ((r : ℝ) - 1))
          / (((k : ℝ) - r) * ((k : ℝ) - r - 1) * ((k : ℝ) - r - 3)) := by
  set M : (Fin r → Fin k → ℝ) → Matrix (Fin r) (Fin r) ℝ :=
    fun G => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ with hM
  have hfun : (fun G : Fin r → Fin k → ℝ => frobSq (pinvR (Matrix.of G)) ^ 2)
      = fun G => ∑ i, ∑ j, M G i i * M G j j := by
    funext G
    rw [frobSq_pinvR_eq_trace_inv, Matrix.trace, sq, Finset.sum_mul_sum]
    rfl
  have hterm : ∀ i j : Fin r, Integrable (fun G => M G i i * M G j j) (gaussianMatrix r k) ∧
      ∫ G, M G i i * M G j j ∂(gaussianMatrix r k)
        = if i = j then 1 / (((k : ℝ) - r - 1) * ((k : ℝ) - r - 3))
          else ((k : ℝ) - r - 2) / (((k : ℝ) - r) * ((k : ℝ) - r - 1) * ((k : ℝ) - r - 3)) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      obtain ⟨h1, h2⟩ :=
        integrable_and_integral_inv_self_mul_transpose_apply_self_sq_gaussianMatrix hrk i
      simp only [if_true, hM]
      simp only [← sq]
      exact ⟨h1, h2⟩
    · rw [if_neg hij]
      exact integrable_and_integral_inv_self_mul_transpose_apply_self_mul_apply_self_gaussianMatrix
        hrk i j hij
  rw [hfun]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hterm i j).1, ?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hterm i j).1]
  simp_rw [integral_finsetSum _ fun j _ => (hterm _ j).1, fun i j => (hterm i j).2]
  rw [sum_sum_ite_eq_mul_add]
  have hx : (4 : ℝ) ≤ (k : ℝ) - r := by
    have : ((r + 4 : ℕ) : ℝ) ≤ k := by exact_mod_cast hrk
    push_cast at this; linarith
  have h1 : (k : ℝ) - r ≠ 0 := by linarith
  have h2 : (k : ℝ) - r - 1 ≠ 0 := by linarith
  have h3 : (k : ℝ) - r - 3 ≠ 0 := by linarith
  field_simp
  ring

/-- HMT Lemma A.10 (endpoint case) in `eLpNorm` form: `‖1/χ²_d‖_{L^q} ≤ 3/d` for
`q = (d-1)/2`. -/
private lemma eLpNorm_inv_sum_sq_le {d : ℕ} (hd : 5 ≤ d) :
    eLpNorm (fun x : Fin d → ℝ => (∑ j, x j ^ 2)⁻¹) (ENNReal.ofReal (((d : ℝ) - 1) / 2))
      (Measure.pi fun _ : Fin d => gaussianReal 0 1) ≤ ENNReal.ofReal (3 / d) := by
  have hd' : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have hq : 0 < ((d : ℝ) - 1) / 2 := by linarith
  obtain ⟨hint, hlt⟩ := integrable_and_integral_rpow_inv_sum_sq_gaussianReal_lt hd
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq.le]
  have hnn : ∀ x : Fin d → ℝ, 0 ≤ (∑ j, x j ^ 2)⁻¹ :=
    fun x => inv_nonneg.mpr (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have h1 : ∀ x : Fin d → ℝ, ‖(∑ j, x j ^ 2)⁻¹‖ₑ ^ (((d : ℝ) - 1) / 2)
      = ENNReal.ofReal (((∑ j, x j ^ 2)⁻¹) ^ (((d : ℝ) - 1) / 2)) := by
    intro x
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hnn x),
      ENNReal.ofReal_rpow_of_nonneg (hnn x) hq.le]
  simp_rw [h1]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hnn x) _)]
  have hI : 0 ≤ ∫ x, ((∑ j, x j ^ 2)⁻¹) ^ (((d : ℝ) - 1) / 2)
      ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) :=
    integral_nonneg fun x => Real.rpow_nonneg (hnn x) _
  rw [ENNReal.ofReal_rpow_of_nonneg hI (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h3 : (0 : ℝ) ≤ 3 / d := by positivity
  calc _ ≤ ((3 / (d : ℝ)) ^ (((d : ℝ) - 1) / 2)) ^ (1 / (((d : ℝ) - 1) / 2)) :=
        Real.rpow_le_rpow hI hlt.le (by positivity)
    _ = 3 / d := by
        rw [← Real.rpow_mul h3, mul_one_div_cancel hq.ne', Real.rpow_one]

/-- **Tail bound for the Frobenius norm of the Gaussian pseudoinverse.** For an `r × k`
standard Gaussian matrix `G` with `r + 4 ≤ k` and `t ≥ 1`,
`P[‖G†‖_F² > 12 r t/(k-r)] ≤ 4 t^{-(k-r)/2}`, with `G† = pinvR G`.

HMT 2011, Thm A.6 (used in Prop 10.4; HMT state it as `P[‖Ω₁†‖_F ≥ √(12k/p) t] ≤ 4 t^{-p}`
with `Ω₁` of size `k × (k+p)`, the same bound after `t ↦ √t`). Atlas: `pinv-frob-tail`.
Proof: each diagonal entry of `(G Gᵀ)⁻¹` is `1/χ²_{k-r+1}`
(`gaussianMatrix_map_inv_self_mul_transpose_apply_self`), whose `L^{(k-r)/2}` norm is at most
`3/(k-r+1)` (`integrable_and_integral_rpow_inv_sum_sq_gaussianReal_lt`, atlas
`chi-square-neg-moment`); Minkowski's inequality bounds `‖tr (G Gᵀ)⁻¹‖_{L^q}` and Markov's
inequality gives the tail. Ported from Prove2me solution `GaussianMatrix.pinv_frobenius_tail`.
atlas: pinv-frob-tail -/
theorem gaussianMatrix_lt_frobSq_pinvR_le {r k : ℕ} (hrk : r + 4 ≤ k) (t : ℝ) (ht : 1 ≤ t) :
    (gaussianMatrix r k) {G | 12 * (r : ℝ) / ((k : ℝ) - r) * t < frobSq (pinvR (Matrix.of G))}
      ≤ ENNReal.ofReal (4 * t ^ (-(((k : ℝ) - r) / 2))) := by
  have hrk' : (r : ℝ) + 4 ≤ k := by exact_mod_cast hrk
  have hp : (4 : ℝ) ≤ (k : ℝ) - r := by linarith
  have hq : (2 : ℝ) ≤ ((k : ℝ) - r) / 2 := by linarith
  have hq0 : (0 : ℝ) < ((k : ℝ) - r) / 2 := by linarith
  have ht0 : (0 : ℝ) < t := by linarith
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · subst hr0
    have : {G : Fin 0 → Fin k → ℝ | 12 * ((0 : ℕ) : ℝ) / ((k : ℝ) - (0 : ℕ)) * t
        < frobSq (pinvR (Matrix.of G))} = ∅ := by
      ext G; simp [frobSq, frobInner]
    rw [this, measure_empty]
    exact zero_le
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast hrpos
  set μ := gaussianMatrix r k with hμ
  set Q : ENNReal := ENNReal.ofReal (((k : ℝ) - r) / 2) with hQ
  have hQ0 : Q ≠ 0 := by simpa [hQ] using hq0
  have hQtop : Q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hQ1 : 1 ≤ Q := by rw [hQ]; exact ENNReal.one_le_ofReal.mpr (by linarith)
  have hQr : Q.toReal = ((k : ℝ) - r) / 2 := ENNReal.toReal_ofReal hq0.le
  set D : Fin r → (Fin r → Fin k → ℝ) → ℝ :=
    fun i G => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i with hD
  have hDm : ∀ i, Measurable (D i) := fun i => measurable_inv_self_mul_transpose_apply i i
  have hZ : ∀ G : Fin r → Fin k → ℝ, frobSq (pinvR (Matrix.of G)) = (∑ i, D i) G := by
    intro G
    rw [frobSq_pinvR_eq_trace_inv, Finset.sum_apply]
    rfl
  have hdcast : ((k - r + 1 : ℕ) : ℝ) = (k : ℝ) - r + 1 := by
    rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_one]
  have hDi : ∀ i, eLpNorm (D i) Q μ ≤ ENNReal.ofReal (3 / ((k : ℝ) - r + 1)) := by
    intro i
    have hlaw := gaussianMatrix_map_inv_self_mul_transpose_apply_self (by omega : r ≤ k) i
    have e1 : eLpNorm (D i) Q μ = eLpNorm id Q (Measure.map (D i) μ) := by
      rw [eLpNorm_map_measure aestronglyMeasurable_id (hDm i).aemeasurable]; rfl
    have hS : Measurable (fun x : Fin (k - r + 1) → ℝ => (∑ j, x j ^ 2)⁻¹) := by fun_prop
    rw [e1, hD, hlaw, eLpNorm_map_measure aestronglyMeasurable_id hS.aemeasurable]
    have := eLpNorm_inv_sum_sq_le (d := k - r + 1) (by omega)
    rw [hdcast, show (k : ℝ) - r + 1 - 1 = (k : ℝ) - r by ring] at this
    exact this
  have hmink : eLpNorm (∑ i, D i) Q μ ≤ ENNReal.ofReal (r * (3 / ((k : ℝ) - r + 1))) := by
    refine (eLpNorm_sum_le (fun i _ => (hDm i).aestronglyMeasurable) hQ1).trans ?_
    calc ∑ i, eLpNorm (D i) Q μ ≤ ∑ _i : Fin r, ENNReal.ofReal (3 / ((k : ℝ) - r + 1)) :=
          Finset.sum_le_sum fun i _ => hDi i
      _ = ENNReal.ofReal (r * (3 / ((k : ℝ) - r + 1))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  set a : ℝ := 12 * (r : ℝ) / ((k : ℝ) - r) * t with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have hsub : {G : Fin r → Fin k → ℝ | a < frobSq (pinvR (Matrix.of G))}
      ⊆ {G | ENNReal.ofReal a ≤ ‖(∑ i, D i) G‖ₑ} := by
    intro G hG
    simp only [Set.mem_ofPred_eq] at hG ⊢
    rw [hZ] at hG
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hG.le.trans (le_abs_self _))
  have hSm : Measurable (∑ i, D i) := by
    have := Finset.measurable_sum (Finset.univ : Finset (Fin r)) fun i _ => hDm i
    simpa only [← Finset.sum_apply] using this
  have hmarkov := meas_ge_le_mul_pow_eLpNorm_enorm μ hQ0 hQtop hSm.aestronglyMeasurable
    (ε := ENNReal.ofReal a) (by simpa using ha0) (fun h => absurd h ENNReal.ofReal_ne_top)
  rw [hQr] at hmarkov
  have hc : (0 : ℝ) ≤ r * (3 / ((k : ℝ) - r + 1)) := by positivity
  calc μ {G | a < frobSq (pinvR (Matrix.of G))}
      ≤ μ {G | ENNReal.ofReal a ≤ ‖(∑ i, D i) G‖ₑ} := measure_mono hsub
    _ ≤ (ENNReal.ofReal a)⁻¹ ^ (((k : ℝ) - r) / 2) *
          eLpNorm (∑ i, D i) Q μ ^ (((k : ℝ) - r) / 2) := hmarkov
    _ ≤ (ENNReal.ofReal a)⁻¹ ^ (((k : ℝ) - r) / 2) *
          ENNReal.ofReal (r * (3 / ((k : ℝ) - r + 1))) ^ (((k : ℝ) - r) / 2) := by
        gcongr
    _ = ENNReal.ofReal ((a⁻¹ * (r * (3 / ((k : ℝ) - r + 1)))) ^ (((k : ℝ) - r) / 2)) := by
        rw [← ENNReal.ofReal_inv_of_pos ha0, ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le,
          ENNReal.ofReal_rpow_of_nonneg hc hq0.le, ← ENNReal.ofReal_mul (by positivity),
          Real.mul_rpow (by positivity) hc]
    _ ≤ ENNReal.ofReal (4 * t ^ (-(((k : ℝ) - r) / 2))) := by
        apply ENNReal.ofReal_le_ofReal
        have hp0 : (0 : ℝ) < (k : ℝ) - r := by linarith
        have hx : a⁻¹ * (r * (3 / ((k : ℝ) - r + 1))) ≤ t⁻¹ := by
          rw [ha]
          have hr0 : (0 : ℝ) < r := by linarith
          rw [show (12 * (r : ℝ) / ((k : ℝ) - r) * t)⁻¹ * (r * (3 / ((k : ℝ) - r + 1)))
              = ((k : ℝ) - r) / (4 * ((k : ℝ) - r + 1)) * t⁻¹ by field_simp; ring]
          have : ((k : ℝ) - r) / (4 * ((k : ℝ) - r + 1)) ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith
          have hti : 0 < t⁻¹ := inv_pos.mpr ht0
          nlinarith
        calc (a⁻¹ * (r * (3 / ((k : ℝ) - r + 1)))) ^ (((k : ℝ) - r) / 2)
            ≤ t⁻¹ ^ (((k : ℝ) - r) / 2) := Real.rpow_le_rpow (by positivity) hx hq0.le
          _ = t ^ (-(((k : ℝ) - r) / 2)) := by rw [Real.inv_rpow ht0.le, Real.rpow_neg ht0.le]
          _ ≤ 4 * t ^ (-(((k : ℝ) - r) / 2)) := by
              have : 0 ≤ t ^ (-(((k : ℝ) - r) / 2)) := Real.rpow_nonneg ht0.le _
              linarith

end NLAlib
