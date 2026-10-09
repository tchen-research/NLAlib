import NLAlib.Matrix.Spectral
import NLAlib.Gaussian.Comparison.Slepian
import NLAlib.Gaussian.Extreme.LinearForms

/-!
# Second moment of the spectral norm of a Gaussian sandwich

For fixed matrices `S` (`a × p`) and `T` (`m × n`) and a `p × m` standard Gaussian matrix `Γ`
(Tropp–Webber 2023, Lemma B.1; Gordon 1985):

* `integral_specNorm_sq_mul_gaussianMatrix_mul_le`:
  `𝔼 ‖S Γ T‖₂² ≤ (‖S‖₂ ‖T‖_F + ‖S‖_F ‖T‖₂)²`;
* `integrable_and_integral_specNorm_sq_mul_gaussianMatrix_mul_le`: the same with integrability of
  `‖S Γ T‖₂²`.

Proof: `‖S Γ T‖₂ = max_{u,v} ⟨Sᵀu ⊗ T v, Γ⟩` over unit vectors; discretise by finite `ε`-nets,
compare the process `X_{u,v} = ⟨Sᵀu ⊗ Tv, Γ⟩ + γ d_{u,v}` (an extra independent normal `γ`
equalises the variances) with `Y_{u,v} = ‖T v‖⟨g, Sᵀu⟩ + ‖Sᵀu‖⟨h, T v⟩` by Slepian's
inequality, convert the tail comparison into a comparison of second moments of the positive part
of the maximum by the layer-cake formula, bound `𝔼 max Y²` by Minkowski's inequality, and let
`ε → 0`.

Ported from the Prove2me solutions `GaussianMatrix.spectral_second_moment_bound` and
`GaussianMatrix.spectral_second_moment`.

Atlas: `spectral-second-moment`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-! ### The matrix process `X` on `(G, γ)` -/

/-- Joint law of an independent pair `(G, γ)`: Gaussian matrix and standard normal scalar. -/
private noncomputable abbrev ssbP (p m : ℕ) : Measure ((Fin p → Fin m → ℝ) × ℝ) :=
  (gaussianMatrix p m).prod (gaussianReal 0 1)

/-- `X_{c,d}(G, γ) = ∑ᵢⱼ cᵢⱼ Gᵢⱼ + d γ`. -/
private noncomputable def ssbX {p m : ℕ} (c : Fin p → Fin m → ℝ) (d : ℝ)
    (ω : (Fin p → Fin m → ℝ) × ℝ) : ℝ := linForm c ω.1 + d * ω.2

private theorem ssb_hasGaussianLaw_X {ι : Type*} [Fintype ι] {p m : ℕ} (c : ι → Fin p → Fin m → ℝ)
    (d : ι → ℝ) : HasGaussianLaw (fun ω t => ssbX (c t) (d t) ω) (ssbP p m) := by
  have h0 : HasGaussianLaw (fun ω : (Fin p → Fin m → ℝ) × ℝ => ω) (ssbP p m) := by
    have : IsGaussian (ssbP p m) := inferInstance
    exact ⟨by rw [Measure.map_id']; exact this⟩
  set L : ((Fin p → Fin m → ℝ) × ℝ) →L[ℝ] (ι → ℝ) :=
    (linFormCLM c).comp (ContinuousLinearMap.fst ℝ _ _) +
      (ContinuousLinearMap.pi fun t => d t • ContinuousLinearMap.snd ℝ (Fin p → Fin m → ℝ) ℝ)
  have h := h0.map_fun L
  have e : (fun ω t => ssbX (c t) (d t) ω) = fun ω => L ω := by
    funext ω t
    simp [L, ssbX, linFormCLM, linForm]
  rw [e]; exact h

private theorem ssb_memLp_fst {p m : ℕ} (c : Fin p → Fin m → ℝ) :
    MemLp (fun ω : (Fin p → Fin m → ℝ) × ℝ => linForm c ω.1) 2 (ssbP p m) :=
  (memLp_linForm_gaussianMatrix c).comp_measurePreserving measurePreserving_fst

private theorem ssb_memLp_snd (p m : ℕ) :
    MemLp (fun ω : (Fin p → Fin m → ℝ) × ℝ => ω.2) 2 (ssbP p m) :=
  (memLp_id_gaussianReal' 2 (by simp)).comp_measurePreserving measurePreserving_snd

private theorem ssb_memLp_X {p m : ℕ} (c : Fin p → Fin m → ℝ) (d : ℝ) :
    MemLp (ssbX c d) 2 (ssbP p m) :=
  (ssb_memLp_fst c).add ((ssb_memLp_snd p m).const_mul d)

private theorem ssb_continuous_X {p m : ℕ} (c : Fin p → Fin m → ℝ) (d : ℝ) : Continuous (ssbX c d) := by
  unfold ssbX linForm; fun_prop

private theorem ssb_integral_X {p m : ℕ} (c : Fin p → Fin m → ℝ) (d : ℝ) :
    ∫ ω, ssbX c d ω ∂(ssbP p m) = 0 := by
  unfold ssbX
  rw [integral_add ((ssb_memLp_fst c).integrable (by simp))
    (((ssb_memLp_snd p m).integrable (by simp)).const_mul d), integral_const_mul]
  rw [integral_fun_fst (fun G => linForm c G), integral_fun_snd (fun x : ℝ => x)]
  simp [integral_linForm_gaussianMatrix, integral_id_gaussianReal]

private theorem ssb_X_sub {p m : ℕ} (c c' : Fin p → Fin m → ℝ) (d d' : ℝ) (ω : (Fin p → Fin m → ℝ) × ℝ) :
    ssbX c d ω - ssbX c' d' ω = ssbX (c - c') (d - d') ω := by
  unfold ssbX
  rw [← linForm_sub_linForm]; ring

private theorem ssb_integral_X_sq {p m : ℕ} (c : Fin p → Fin m → ℝ) (d : ℝ) :
    ∫ ω, ssbX c d ω ^ 2 ∂(ssbP p m) = ∑ i, ∑ j, c i j ^ 2 + d ^ 2 := by
  have hexp : ∀ ω : (Fin p → Fin m → ℝ) × ℝ, ssbX c d ω ^ 2 =
      linForm c ω.1 ^ 2 + 2 * d * (linForm c ω.1 * ω.2) + d ^ 2 * ω.2 ^ 2 := by
    intro ω; unfold ssbX; ring
  simp_rw [hexp]
  have i1 := (ssb_memLp_fst c).integrable_sq
  have i2 : Integrable (fun ω : (Fin p → Fin m → ℝ) × ℝ => 2 * d * (linForm c ω.1 * ω.2))
      (ssbP p m) := ((ssb_memLp_fst c).integrable_mul (ssb_memLp_snd p m)).const_mul (2 * d)
  have i3 := (ssb_memLp_snd p m).integrable_sq.const_mul (d ^ 2)
  rw [integral_add (f := fun ω => linForm c ω.1 ^ 2 + 2 * d * (linForm c ω.1 * ω.2)) (i1.add i2) i3,
    integral_add i1 i2, integral_const_mul, integral_const_mul]
  rw [integral_fun_fst (fun G => linForm c G ^ 2), integral_fun_snd (fun x : ℝ => x ^ 2)]
  have hprod := integral_prod_mul (μ := gaussianMatrix p m) (ν := gaussianReal 0 1)
    (fun G => linForm c G) (fun x : ℝ => x)
  rw [hprod, integral_linForm_sq_gaussianMatrix]
  have h1 : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
    have h := variance_eq_sub (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp))
    rw [variance_id_gaussianReal] at h
    simp [integral_id_gaussianReal] at h
    exact h.symm
  simp [h1, integral_linForm_gaussianMatrix]


/-! ### Positive part of a finite maximum, Fubini–Jensen step, layer cake -/

private theorem ssb_sup_sq_le_sum {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    max (⨆ t, f t) 0 ^ 2 ≤ ∑ t, f t ^ 2 := by
  obtain ⟨t0, ht0⟩ := exists_eq_ciSup_of_finite (f := f)
  rw [← ht0]
  have h : max (f t0) 0 ^ 2 ≤ f t0 ^ 2 := by
    rcases le_total (f t0) 0 with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg (f t0)]
    · rw [max_eq_left h]
  exact h.trans (Finset.single_le_sum (f := fun t => f t ^ 2) (fun t _ => sq_nonneg _)
    (Finset.mem_univ t0))

private theorem ssb_integrable_supsq {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype ι]
    [Nonempty ι] (f : ι → Ω → ℝ) (hf : ∀ t, MemLp (f t) 2 μ) (hm : ∀ t, Measurable (f t)) :
    Integrable (fun ω => max (⨆ t, f t ω) 0 ^ 2) μ := by
  refine Integrable.mono' (integrable_finsetSum Finset.univ fun t _ => (hf t).integrable_sq)
    (((Measurable.iSup hm).max measurable_const).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact ssb_sup_sq_le_sum (fun t => f t ω)

/-- Averaging out an independent scalar Gaussian can only increase `(max ·)₊²`:
`(maxₜ Bₜ)₊² ≤ 𝔼_γ (maxₜ (Bₜ + dₜ γ))₊²`. (Jensen's inequality in elementary form.) -/
private theorem ssb_gamma_jensen {ι : Type*} [Fintype ι] [Nonempty ι] (B d : ι → ℝ)
    (hint : Integrable (fun γ : ℝ => max (⨆ t, B t + d t * γ) 0 ^ 2) (gaussianReal 0 1)) :
    max (⨆ t, B t) 0 ^ 2 ≤ ∫ γ, max (⨆ t, B t + d t * γ) 0 ^ 2 ∂(gaussianReal 0 1) := by
  obtain ⟨t0, ht0⟩ := exists_eq_ciSup_of_finite (f := B)
  rw [← ht0]
  rcases le_total (B t0) 0 with hb | hb
  · rw [max_eq_right hb]
    have : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [this]
    exact integral_nonneg fun γ => sq_nonneg _
  · rw [max_eq_left hb]
    have hpt : ∀ γ : ℝ, B t0 ^ 2 + 2 * B t0 * d t0 * γ ≤ max (⨆ t, B t + d t * γ) 0 ^ 2 := by
      intro γ
      have h1 : B t0 + d t0 * γ ≤ max (⨆ t, B t + d t * γ) 0 :=
        (le_ciSup (f := fun t => B t + d t * γ) (Set.finite_range _).bddAbove t0).trans
          (le_max_left _ _)
      nlinarith [sq_nonneg (max (⨆ t, B t + d t * γ) 0 - B t0), mul_le_mul_of_nonneg_left h1 hb]
    have hid : Integrable (fun γ : ℝ => γ) (gaussianReal 0 1) :=
      (memLp_id_gaussianReal' 2 (by simp)).integrable (by simp)
    have hlin : Integrable (fun γ : ℝ => B t0 ^ 2 + 2 * B t0 * d t0 * γ) (gaussianReal 0 1) :=
      (integrable_const _).add (hid.const_mul _)
    calc B t0 ^ 2 = ∫ γ, (B t0 ^ 2 + 2 * B t0 * d t0 * γ) ∂(gaussianReal 0 1) := by
          rw [integral_add (integrable_const _) (hid.const_mul _), integral_const,
            integral_const_mul, integral_id_gaussianReal]
          simp
      _ ≤ _ := integral_mono hlin hint hpt

/-- Fubini + Jensen: `𝔼_G (maxₜ Bₜ(G))₊² ≤ 𝔼_{G,γ} (maxₜ Xₜ(G,γ))₊²`. -/
private theorem ssb_fubini {ι : Type*} [Fintype ι] [Nonempty ι] {p m : ℕ} (c : ι → Fin p → Fin m → ℝ)
    (d : ι → ℝ) :
    ∫ G, max (⨆ t, linForm (c t) G) 0 ^ 2 ∂(gaussianMatrix p m)
      ≤ ∫ ω, max (⨆ t, ssbX (c t) (d t) ω) 0 ^ 2 ∂(ssbP p m) := by
  have hint := ssb_integrable_supsq (μ := ssbP p m) (fun t => ssbX (c t) (d t))
    (fun t => ssb_memLp_X _ _) (fun t => (ssb_continuous_X _ _).measurable)
  rw [integral_prod _ hint]
  have hL := ssb_integrable_supsq (μ := gaussianMatrix p m) (fun t => linForm (c t))
    (fun t => memLp_linForm_gaussianMatrix _) (fun t => (continuous_linForm _).measurable)
  refine integral_mono_ae hL hint.integral_prod_left ?_
  filter_upwards [hint.prod_right_ae] with G hG
  exact ssb_gamma_jensen (fun t => linForm (c t) G) d hG

private theorem ssb_layercake_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (h : Ω → ℝ)
    (hh : Measurable h) :
    ∫⁻ ω, ENNReal.ofReal (max (h ω) 0 ^ 2) ∂μ
      = ∫⁻ t in Set.Ioi 0, μ {ω | t < h ω} * ENNReal.ofReal (2 * t) := by
  have := lintegral_comp_eq_lintegral_meas_lt_mul μ (f := fun ω => max (h ω) 0)
    (Filter.Eventually.of_forall fun ω => le_max_right _ _) (hh.max measurable_const).aemeasurable
    (g := fun t => 2 * t) (fun t _ => (continuous_const.mul continuous_id).intervalIntegrable _ _)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => by
      simp only [Set.mem_Ioi] at ht; linarith))
  have e1 : ∀ x : ℝ, ∫ t in (0 : ℝ)..x, 2 * t = x ^ 2 := by
    intro x
    rw [intervalIntegral.integral_const_mul, integral_id]; ring
  simp only [e1] at this
  rw [this]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [Set.mem_Ioi] at ht
  congr 2
  ext ω
  simp only [Set.mem_ofPred_eq, lt_max_iff]
  constructor
  · rintro (h1 | h1)
    · exact h1
    · exact absurd h1 (not_lt.2 ht.le)
  · exact fun h1 => Or.inl h1

/-- Layer cake: a tail comparison `P(f > t) ≤ Q(g > t)` for `t > 0` gives
`𝔼 f₊² ≤ 𝔼 g₊²`. -/
private theorem ssb_layercake_sq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω') (f : Ω → ℝ) (g : Ω' → ℝ) (hf : Measurable f)
    (hg : Measurable g) (hfi : Integrable (fun ω => max (f ω) 0 ^ 2) P)
    (hgi : Integrable (fun ω => max (g ω) 0 ^ 2) Q)
    (htail : ∀ t : ℝ, 0 < t → P {ω | t < f ω} ≤ Q {ω | t < g ω}) :
    ∫ ω, max (f ω) 0 ^ 2 ∂P ≤ ∫ ω, max (g ω) 0 ^ 2 ∂Q := by
  rw [← ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => sq_nonneg _),
    ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall fun _ => sq_nonneg _),
    ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall fun _ => sq_nonneg _),
    ssb_layercake_eq P f hf, ssb_layercake_eq Q g hg]
  refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
  exact mul_le_mul_left (htail t ht) _


/-! ### The Tropp–Webber comparison processes -/

/-- Euclidean norm of a coordinate vector. -/
private noncomputable def ssbN {κ : Type*} [Fintype κ] (x : κ → ℝ) : ℝ := Real.sqrt (∑ k, x k ^ 2)

private theorem ssbN_nonneg {κ : Type*} [Fintype κ] (x : κ → ℝ) : 0 ≤ ssbN x := Real.sqrt_nonneg _

private theorem ssbN_sq {κ : Type*} [Fintype κ] (x : κ → ℝ) : ∑ k, x k ^ 2 = ssbN x ^ 2 :=
  (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm

private theorem ssb_inner_le {κ : Type*} [Fintype κ] (x x' : κ → ℝ) : ∑ k, x k * x' k ≤ ssbN x * ssbN x' :=
  Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- The coefficient comparison behind Tropp–Webber's covariance identity
`𝔼 XX' - 𝔼 YY' = (‖x‖‖x'‖ - ⟨x,x'⟩)(‖y‖‖y'‖ - ⟨y,y'⟩) ≥ 0`, in increment form. -/
private theorem ssb_coeff_cmp {p m : ℕ} (x x' : Fin p → ℝ) (y y' : Fin m → ℝ) :
    ∑ k, ∑ l, (x k * y l - x' k * y' l) ^ 2 + (ssbN x * ssbN y - ssbN x' * ssbN y') ^ 2
      ≤ ∑ k, (ssbN y * x k - ssbN y' * x' k) ^ 2 + ∑ l, (ssbN x * y l - ssbN x' * y' l) ^ 2 := by
  have hα := ssb_inner_le x x'
  have hβ := ssb_inner_le y y'
  have hL : ∑ k, ∑ l, (x k * y l - x' k * y' l) ^ 2
      = (∑ k, x k ^ 2) * (∑ l, y l ^ 2) - 2 * ((∑ k, x k * x' k) * (∑ l, y l * y' l))
        + (∑ k, x' k ^ 2) * (∑ l, y' l ^ 2) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hR1 : ∑ k, (ssbN y * x k - ssbN y' * x' k) ^ 2
      = ssbN y ^ 2 * (∑ k, x k ^ 2) - 2 * (ssbN y * ssbN y') * (∑ k, x k * x' k)
        + ssbN y' ^ 2 * (∑ k, x' k ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hR2 : ∑ l, (ssbN x * y l - ssbN x' * y' l) ^ 2
      = ssbN x ^ 2 * (∑ l, y l ^ 2) - 2 * (ssbN x * ssbN x') * (∑ l, y l * y' l)
        + ssbN x' ^ 2 * (∑ l, y' l ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hL, hR1, hR2, ssbN_sq x, ssbN_sq x', ssbN_sq y, ssbN_sq y']
  nlinarith [mul_nonneg (sub_nonneg.2 hα) (sub_nonneg.2 hβ)]

private theorem ssb_append_sq {p m : ℕ} (u : Fin p → ℝ) (w : Fin m → ℝ) :
    ∑ _i : Fin 1, ∑ k : Fin (p + m), Fin.append u w k ^ 2 = ∑ k, u k ^ 2 + ∑ l, w l ^ 2 := by
  rw [Fin.sum_univ_one, Fin.sum_univ_add]
  simp

private theorem ssb_append_sub_sq {p m : ℕ} (u u' : Fin p → ℝ) (w w' : Fin m → ℝ) :
    ∑ _i : Fin 1, ∑ k : Fin (p + m), (Fin.append u w k - Fin.append u' w' k) ^ 2
      = ∑ k, (u k - u' k) ^ 2 + ∑ l, (w l - w' l) ^ 2 := by
  rw [Fin.sum_univ_one, Fin.sum_univ_add]
  simp

/-- Coefficients of the comparison process
`Yₜ = ‖yₜ‖ ⟨g, xₜ⟩ + ‖xₜ‖ ⟨h, yₜ⟩`, realized on one Gaussian row `(g, h) ∈ ℝ^{p+m}`. -/
private noncomputable def ssbYc {ι : Type*} {p m : ℕ} (x : ι → Fin p → ℝ) (y : ι → Fin m → ℝ) (t : ι) :
    Fin 1 → Fin (p + m) → ℝ :=
  fun _ k => Fin.append (fun k => ssbN (y t) * x t k) (fun l => ssbN (x t) * y t l) k

/-- The Gaussian comparison (Tropp–Webber, proof of Lemma B.1, via Slepian's inequality):
`𝔼_G (maxₜ ⟨xₜ, G yₜ⟩)₊² ≤ 𝔼 (maxₜ Yₜ)₊²`. -/
private theorem ssb_main_cmp {ι : Type*} [Fintype ι] [Nonempty ι] {p m : ℕ} (x : ι → Fin p → ℝ)
    (y : ι → Fin m → ℝ) :
    ∫ G, max (⨆ t, linForm (fun k l => x t k * y t l) G) 0 ^ 2 ∂(gaussianMatrix p m)
      ≤ ∫ H, max (⨆ t, linForm (ssbYc x y t) H) 0 ^ 2 ∂(gaussianMatrix 1 (p + m)) := by
  set c : ι → Fin p → Fin m → ℝ := fun t k l => x t k * y t l with hc
  set d : ι → ℝ := fun t => ssbN (x t) * ssbN (y t) with hd
  refine (ssb_fubini c d).trans ?_
  have hvar : ∀ t, ∫ ω, ssbX (c t) (d t) ω ^ 2 ∂(ssbP p m)
      = ∫ H, linForm (ssbYc x y t) H ^ 2 ∂(gaussianMatrix 1 (p + m)) := by
    intro t
    rw [ssb_integral_X_sq, integral_linForm_sq_gaussianMatrix]
    simp only [ssbYc, hc, hd]
    rw [ssb_append_sq]
    have e1 : ∑ k, ∑ l, (x t k * y t l) ^ 2 = (∑ k, x t k ^ 2) * ∑ l, y t l ^ 2 := by
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    have e2 : ∑ k, (ssbN (y t) * x t k) ^ 2 = ssbN (y t) ^ 2 * ∑ k, x t k ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    have e3 : ∑ l, (ssbN (x t) * y t l) ^ 2 = ssbN (x t) ^ 2 * ∑ l, y t l ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
    rw [e1, e2, e3, ssbN_sq (x t), ssbN_sq (y t)]
    ring
  have hinc : ∀ s t, ∫ ω, (ssbX (c s) (d s) ω - ssbX (c t) (d t) ω) ^ 2 ∂(ssbP p m)
      ≤ ∫ H, (linForm (ssbYc x y s) H - linForm (ssbYc x y t) H) ^ 2
          ∂(gaussianMatrix 1 (p + m)) := by
    intro s t
    simp_rw [ssb_X_sub, linForm_sub_linForm]
    rw [ssb_integral_X_sq, integral_linForm_sq_gaussianMatrix]
    simp only [ssbYc, hc, hd, Pi.sub_apply]
    rw [ssb_append_sub_sq]
    exact ssb_coeff_cmp (x s) (x t) (y s) (y t)
  have hS := slepian_inequality (fun t => ssbX (c t) (d t)) (fun t => linForm (ssbYc x y t))
    (ssb_hasGaussianLaw_X c d) (hasGaussianLaw_linForm_gaussianMatrix _) (fun t => ssb_integral_X _ _)
    (fun t => integral_linForm_gaussianMatrix _) hvar hinc
  refine ssb_layercake_sq _ _ _ _ (Measurable.iSup fun t => (ssb_continuous_X _ _).measurable)
    (Measurable.iSup fun t => (continuous_linForm _).measurable)
    (ssb_integrable_supsq _ (fun t => ssb_memLp_X _ _) fun t => (ssb_continuous_X _ _).measurable)
    (ssb_integrable_supsq _ (fun t => memLp_linForm_gaussianMatrix _) fun t => (continuous_linForm _).measurable)
    fun τ _ => hS τ


/-! ### Deterministic matrix facts -/

private theorem ssb_sandwich_entry {a p m n : ℕ} (S : Matrix (Fin a) (Fin p) ℝ) (T : Matrix (Fin m) (Fin n) ℝ)
    (G : Fin p → Fin m → ℝ) (u : Fin a → ℝ) (v : Fin n → ℝ) :
    ∑ i, ∑ j, u i * (S * Matrix.of G * T) i j * v j
      = ∑ k, ∑ l, ((∑ i, u i * S i k) * (∑ j, T l j * v j)) * G k l := by
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    ({ toFun := fun x => (x.2.2.2, (x.2.2.1, (x.2.1, x.1)))
       invFun := fun x => (x.2.2.2, (x.2.2.1, (x.2.1, x.1)))
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl } : Fin a × Fin n × Fin m × Fin p ≃ Fin p × Fin m × Fin n × Fin a)
    _ _ fun x => ?_
  simp only [Equiv.coe_fn_mk]
  ring

open scoped Matrix.Norms.L2Operator in
private theorem ssb_norm_vecMul_le {a p : ℕ} (S : Matrix (Fin a) (Fin p) ℝ) (u : EuclideanSpace ℝ (Fin a))
    (hu : ‖u‖ = 1) : Real.sqrt (∑ k, (∑ i, u i * S i k) ^ 2) ≤ specNorm S := by
  have h := Matrix.l2_opNorm_mulVec Sᵀ u
  rw [hu, mul_one, ← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.l2_opNorm_conjTranspose] at h
  refine le_of_eq_of_le ?_ h
  rw [EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]

open scoped Matrix.Norms.L2Operator in
private theorem ssb_norm_mulVec_le {m n : ℕ} (T : Matrix (Fin m) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n))
    (hv : ‖v‖ = 1) : Real.sqrt (∑ l, (∑ j, T l j * v j) ^ 2) ≤ specNorm T := by
  have h := Matrix.l2_opNorm_mulVec T v
  rw [hv, mul_one] at h
  refine le_of_eq_of_le ?_ h
  rw [EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [Matrix.mulVec, dotProduct]

/-- `⟨x, g⟩ ≤ ‖S g‖` for `x = Sᵀ u`, `‖u‖ = 1`. -/
private theorem ssb_vecMul_inner_le {a p : ℕ} (S : Matrix (Fin a) (Fin p) ℝ) (u : EuclideanSpace ℝ (Fin a))
    (hu : ‖u‖ = 1) (g : Fin p → ℝ) :
    ∑ k, (∑ i, u i * S i k) * g k ≤ Real.sqrt (∑ i, (∑ k, S i k * g k) ^ 2) := by
  have e : ∑ k, (∑ i, u i * S i k) * g k = ∑ i, u i * (∑ k, S i k * g k) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  rw [e]
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => u i) (fun i => ∑ k, S i k * g k)
  rw [← norm_eq_sqrt_sum_sq, hu, one_mul] at h
  exact h

/-- `⟨y, h⟩ ≤ ‖Tᵀ h‖` for `y = T v`, `‖v‖ = 1`. -/
private theorem ssb_mulVec_inner_le {m n : ℕ} (T : Matrix (Fin m) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n))
    (hv : ‖v‖ = 1) (h : Fin m → ℝ) :
    ∑ l, (∑ j, T l j * v j) * h l ≤ Real.sqrt (∑ j, (∑ l, T l j * h l) ^ 2) := by
  have e : ∑ l, (∑ j, T l j * v j) * h l = ∑ j, v j * (∑ l, T l j * h l) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  rw [e]
  have h' := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun j => v j) (fun j => ∑ l, T l j * h l)
  rw [← norm_eq_sqrt_sum_sq, hv, one_mul] at h'
  exact h'

/-! ### Bounding the comparison process -/

/-- Minkowski in `L²` for nonnegative functions. -/
private theorem ssb_minkowski {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (a b : Ω → ℝ)
    (ha0 : ∀ ω, 0 ≤ a ω) (hb0 : ∀ ω, 0 ≤ b ω) (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    ∫ ω, (a ω + b ω) ^ 2 ∂μ
      ≤ (Real.sqrt (∫ ω, a ω ^ 2 ∂μ) + Real.sqrt (∫ ω, b ω ^ 2 ∂μ)) ^ 2 := by
  have hab : ∫ ω, a ω * b ω ∂μ
      ≤ Real.sqrt (∫ ω, a ω ^ 2 ∂μ) * Real.sqrt (∫ ω, b ω ^ 2 ∂μ) := by
    have h2 : ENNReal.ofReal 2 = 2 := by simp
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall ha0) (Filter.Eventually.of_forall hb0)
      (by rw [h2]; exact ha) (by rw [h2]; exact hb)
    simp only [Real.rpow_two] at h
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    exact h
  have hexp : ∀ ω, (a ω + b ω) ^ 2 = a ω ^ 2 + 2 * (a ω * b ω) + b ω ^ 2 := fun ω => by ring
  simp_rw [hexp]
  have i1 := ha.integrable_sq
  have i2 : Integrable (fun ω => 2 * (a ω * b ω)) μ := (ha.integrable_mul hb).const_mul 2
  have i3 := hb.integrable_sq
  rw [integral_add (f := fun ω => a ω ^ 2 + 2 * (a ω * b ω)) (i1.add i2) i3, integral_add i1 i2,
    integral_const_mul]
  have hA := Real.sq_sqrt (integral_nonneg fun ω => sq_nonneg (a ω) : 0 ≤ ∫ ω, a ω ^ 2 ∂μ)
  have hB := Real.sq_sqrt (integral_nonneg fun ω => sq_nonneg (b ω) : 0 ≤ ∫ ω, b ω ^ 2 ∂μ)
  nlinarith [hab]

private theorem ssb_lin_left {p m : ℕ} (w : Fin p → ℝ) (H : Fin 1 → Fin (p + m) → ℝ) :
    ∑ k, w k * H 0 (Fin.castAdd m k) = linForm (fun _ k => Fin.append w (0 : Fin m → ℝ) k) H := by
  unfold linForm; rw [Fin.sum_univ_one, Fin.sum_univ_add]; simp

private theorem ssb_lin_right {p m : ℕ} (w : Fin m → ℝ) (H : Fin 1 → Fin (p + m) → ℝ) :
    ∑ l, w l * H 0 (Fin.natAdd p l) = linForm (fun _ k => Fin.append (0 : Fin p → ℝ) w k) H := by
  unfold linForm; rw [Fin.sum_univ_one, Fin.sum_univ_add]; simp

/-- `𝔼 ∑ᵢ (∑ₖ Wᵢₖ gₖ)² = ‖W‖_F²` for the first block `g` of a Gaussian row. -/
private theorem ssb_integral_left_sq {r p m : ℕ} (W : Fin r → Fin p → ℝ) :
    Integrable (fun H : Fin 1 → Fin (p + m) → ℝ => ∑ i, (∑ k, W i k * H 0 (Fin.castAdd m k)) ^ 2)
      (gaussianMatrix 1 (p + m)) ∧
    ∫ H, ∑ i, (∑ k, W i k * H 0 (Fin.castAdd m k)) ^ 2 ∂(gaussianMatrix 1 (p + m))
      = ∑ i, ∑ k, W i k ^ 2 := by
  simp_rw [ssb_lin_left]
  have hi : ∀ i, Integrable (fun H : Fin 1 → Fin (p + m) → ℝ =>
      linForm (fun _ k => Fin.append (W i) (0 : Fin m → ℝ) k) H ^ 2) (gaussianMatrix 1 (p + m)) :=
    fun i => (memLp_linForm_gaussianMatrix _).integrable_sq
  refine ⟨integrable_finsetSum _ fun i _ => hi i, ?_⟩
  rw [integral_finsetSum _ fun i _ => hi i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_linForm_sq_gaussianMatrix, ssb_append_sq]
  simp

private theorem ssb_integral_right_sq {r p m : ℕ} (W : Fin r → Fin m → ℝ) :
    Integrable (fun H : Fin 1 → Fin (p + m) → ℝ => ∑ i, (∑ l, W i l * H 0 (Fin.natAdd p l)) ^ 2)
      (gaussianMatrix 1 (p + m)) ∧
    ∫ H, ∑ i, (∑ l, W i l * H 0 (Fin.natAdd p l)) ^ 2 ∂(gaussianMatrix 1 (p + m))
      = ∑ i, ∑ l, W i l ^ 2 := by
  simp_rw [ssb_lin_right]
  have hi : ∀ i, Integrable (fun H : Fin 1 → Fin (p + m) → ℝ =>
      linForm (fun _ k => Fin.append (0 : Fin p → ℝ) (W i) k) H ^ 2) (gaussianMatrix 1 (p + m)) :=
    fun i => (memLp_linForm_gaussianMatrix _).integrable_sq
  refine ⟨integrable_finsetSum _ fun i _ => hi i, ?_⟩
  rw [integral_finsetSum _ fun i _ => hi i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_linForm_sq_gaussianMatrix, ssb_append_sq]
  simp

/-- `√Q` has a finite second moment when `Q ≥ 0` is integrable. -/
private theorem ssb_memLp_sqrt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (Q : Ω → ℝ)
    (hQ0 : ∀ ω, 0 ≤ Q ω) (hQ : Integrable Q μ) (hm : Measurable Q) (c : ℝ) :
    MemLp (fun ω => c * Real.sqrt (Q ω)) 2 μ := by
  refine MemLp.const_mul ?_ c
  refine (memLp_two_iff_integrable_sq (hm.sqrt.aestronglyMeasurable)).2 ?_
  exact hQ.congr (Filter.Eventually.of_forall fun ω => (Real.sq_sqrt (hQ0 ω)).symm)

/-- The bound on the comparison process: if `‖xₜ‖ ≤ α`, `‖yₜ‖ ≤ β`, `⟨xₜ, g⟩ ≤ ‖S g‖` and
`⟨yₜ, h⟩ ≤ ‖Tᵀ h‖`, then `𝔼 (maxₜ Yₜ)₊² ≤ (β‖S‖_F + α‖T‖_F)²`. -/
private theorem ssb_Y_bound {ι : Type*} [Fintype ι] [Nonempty ι] {a p m n : ℕ}
    (S : Matrix (Fin a) (Fin p) ℝ) (T : Matrix (Fin m) (Fin n) ℝ) (x : ι → Fin p → ℝ)
    (y : ι → Fin m → ℝ) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hx : ∀ t, ssbN (x t) ≤ α) (hy : ∀ t, ssbN (y t) ≤ β)
    (hxg : ∀ t (g : Fin p → ℝ), ∑ k, x t k * g k ≤ Real.sqrt (∑ i, (∑ k, S i k * g k) ^ 2))
    (hyh : ∀ t (h : Fin m → ℝ), ∑ l, y t l * h l ≤ Real.sqrt (∑ j, (∑ l, T l j * h l) ^ 2)) :
    ∫ H, max (⨆ t, linForm (ssbYc x y t) H) 0 ^ 2 ∂(gaussianMatrix 1 (p + m))
      ≤ (β * frobNorm S + α * frobNorm T) ^ 2 := by
  set Q1 : (Fin 1 → Fin (p + m) → ℝ) → ℝ :=
    fun H => ∑ i, (∑ k, S i k * H 0 (Fin.castAdd m k)) ^ 2 with hQ1
  set Q2 : (Fin 1 → Fin (p + m) → ℝ) → ℝ :=
    fun H => ∑ j, (∑ l, (fun j l => T l j) j l * H 0 (Fin.natAdd p l)) ^ 2 with hQ2
  have hQ10 : ∀ H, 0 ≤ Q1 H := fun H => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hQ20 : ∀ H, 0 ≤ Q2 H := fun H => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hQ1m : Measurable Q1 := by rw [hQ1]; fun_prop
  have hQ2m : Measurable Q2 := by rw [hQ2]; fun_prop
  obtain ⟨hQ1i, hQ1e⟩ := ssb_integral_left_sq (m := m) S
  obtain ⟨hQ2i, hQ2e⟩ := ssb_integral_right_sq (p := p) (fun j l => T l j)
  have hYle : ∀ H t, linForm (ssbYc x y t) H
      ≤ β * Real.sqrt (Q1 H) + α * Real.sqrt (Q2 H) := by
    intro H t
    have e : linForm (ssbYc x y t) H
        = ssbN (y t) * (∑ k, x t k * H 0 (Fin.castAdd m k))
          + ssbN (x t) * (∑ l, y t l * H 0 (Fin.natAdd p l)) := by
      unfold linForm ssbYc
      rw [Fin.sum_univ_one, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, Finset.mul_sum]
      congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    have h1 := hxg t (fun k => H 0 (Fin.castAdd m k))
    have h2 := hyh t (fun l => H 0 (Fin.natAdd p l))
    have r1 : 0 ≤ Real.sqrt (Q1 H) := Real.sqrt_nonneg _
    have r2 : 0 ≤ Real.sqrt (Q2 H) := Real.sqrt_nonneg _
    have n1 := ssbN_nonneg (y t)
    have n2 := ssbN_nonneg (x t)
    have k1 : ssbN (y t) * (∑ k, x t k * H 0 (Fin.castAdd m k)) ≤ β * Real.sqrt (Q1 H) :=
      (mul_le_mul_of_nonneg_left h1 n1).trans (mul_le_mul_of_nonneg_right (hy t) r1)
    have k2 : ssbN (x t) * (∑ l, y t l * H 0 (Fin.natAdd p l)) ≤ α * Real.sqrt (Q2 H) :=
      (mul_le_mul_of_nonneg_left h2 n2).trans (mul_le_mul_of_nonneg_right (hx t) r2)
    linarith
  have hW0 : ∀ H, 0 ≤ β * Real.sqrt (Q1 H) + α * Real.sqrt (Q2 H) := fun H =>
    add_nonneg (mul_nonneg hβ (Real.sqrt_nonneg _)) (mul_nonneg hα (Real.sqrt_nonneg _))
  have hm1 := ssb_memLp_sqrt Q1 hQ10 hQ1i hQ1m β
  have hm2 := ssb_memLp_sqrt Q2 hQ20 hQ2i hQ2m α
  have hpt : ∀ H, max (⨆ t, linForm (ssbYc x y t) H) 0 ^ 2
      ≤ (β * Real.sqrt (Q1 H) + α * Real.sqrt (Q2 H)) ^ 2 := by
    intro H
    refine pow_le_pow_left₀ (le_max_right _ _) (max_le (ciSup_le fun t => hYle H t) (hW0 H)) 2
  have hint := ssb_integrable_supsq (μ := gaussianMatrix 1 (p + m))
    (fun t => linForm (ssbYc x y t)) (fun t => memLp_linForm_gaussianMatrix _)
    (fun t => (continuous_linForm _).measurable)
  refine (integral_mono hint (hm1.add hm2).integrable_sq hpt).trans ?_
  refine (ssb_minkowski _ _ _ (fun H => mul_nonneg hβ (Real.sqrt_nonneg _))
    (fun H => mul_nonneg hα (Real.sqrt_nonneg _)) hm1 hm2).trans (le_of_eq ?_)
  have s1 : ∫ H, (β * Real.sqrt (Q1 H)) ^ 2 ∂(gaussianMatrix 1 (p + m)) = β ^ 2 * frobSq S := by
    simp_rw [mul_pow, Real.sq_sqrt (hQ10 _)]
    rw [integral_const_mul, frobSq_eq_sum_sq]
    congr 1
  have s2 : ∫ H, (α * Real.sqrt (Q2 H)) ^ 2 ∂(gaussianMatrix 1 (p + m)) = α ^ 2 * frobSq T := by
    simp_rw [mul_pow, Real.sq_sqrt (hQ20 _)]
    rw [integral_const_mul]
    congr 1
    rw [hQ2e, frobSq_eq_sum_sq, Finset.sum_comm]
  rw [s1, s2, Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hβ,
    Real.sqrt_sq hα]
  rfl


/-! ### Assembly -/

/-- The bound at a fixed net scale `ε`: `(1 - 2ε)² 𝔼‖SGT‖² ≤ (‖S‖‖T‖_F + ‖S‖_F‖T‖)²`. -/
private theorem ssb_scaled_bound {a p m n : ℕ} (S : Matrix (Fin a) (Fin p) ℝ) (T : Matrix (Fin m) (Fin n) ℝ)
    (ha : 0 < a) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    (1 - 2 * ε) ^ 2 * ∫ G, specNorm (S * Matrix.of G * T) ^ 2 ∂(gaussianMatrix p m)
      ≤ (specNorm S * frobNorm T + frobNorm S * specNorm T) ^ 2 := by
  -- finite `ε`-nets of the two unit spheres
  obtain ⟨Fu, hFuS, hFufin, hFucov⟩ := Metric.finite_approx_of_totallyBounded
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).totallyBounded ε hε
  obtain ⟨Fv, hFvS, hFvfin, hFvcov⟩ := Metric.finite_approx_of_totallyBounded
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin a)) 1).totallyBounded ε hε
  set I := hFufin.toFinset ×ˢ hFvfin.toFinset with hIdef
  have hI1 : ∀ t ∈ I, ‖t.1‖ = 1 := by
    intro t ht
    rw [hIdef, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at ht
    simpa using hFuS ht.1
  have hI2 : ∀ t ∈ I, ‖t.2‖ = 1 := by
    intro t ht
    rw [hIdef, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at ht
    simpa using hFvS ht.2
  have hcov : ∀ (u : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin a)), ‖u‖ = 1 →
      ‖v‖ = 1 → ∃ t ∈ I, ‖u - t.1‖ ≤ ε ∧ ‖v - t.2‖ ≤ ε := by
    intro u v hu hv
    have hu' : u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by simpa using hu
    have hv' : v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin a)) 1 := by simpa using hv
    obtain ⟨y, hy, hyu⟩ := Set.mem_iUnion₂.1 (hFucov hu')
    obtain ⟨z, hz, hzv⟩ := Set.mem_iUnion₂.1 (hFvcov hv')
    refine ⟨(y, z), ?_, ?_, ?_⟩
    · rw [hIdef, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      exact ⟨hy, hz⟩
    · rw [Metric.mem_ball, dist_eq_norm] at hyu; exact hyu.le
    · rw [Metric.mem_ball, dist_eq_norm] at hzv; exact hzv.le
  have hne : Nonempty I := by
    obtain ⟨t, ht, -⟩ := hcov (EuclideanSpace.single (⟨0, hn⟩ : Fin n) 1)
      (EuclideanSpace.single (⟨0, ha⟩ : Fin a) 1) (by simp) (by simp)
    exact ⟨⟨t, ht⟩⟩
  -- the vectors `xₜ = Sᵀ uₜ` and `yₜ = T vₜ`
  set x : I → Fin p → ℝ := fun t k => ∑ i, t.1.2 i * S i k with hx
  set y : I → Fin m → ℝ := fun t l => ∑ j, T l j * t.1.1 j with hy
  have hspec : Integrable (fun G : Fin p → Fin m → ℝ => specNorm (S * Matrix.of G * T) ^ 2)
      (gaussianMatrix p m) :=
    (integrable_and_integrable_sq_of_abs_sub_le_mul_frobNorm (fun G : Fin p → Fin m → ℝ => specNorm (S * Matrix.of G * T))
      (specNorm S * specNorm T) (mul_nonneg (specNorm_nonneg S) (specNorm_nonneg T))
      (abs_specNorm_mul_of_mul_sub_le S T)).2
  have hL := ssb_integrable_supsq (μ := gaussianMatrix p m)
    (fun t => linForm (fun k l => x t k * y t l)) (fun t => memLp_linForm_gaussianMatrix _)
    (fun t => (continuous_linForm _).measurable)
  have step1 : ∀ G : Fin p → Fin m → ℝ, (1 - 2 * ε) ^ 2 * specNorm (S * Matrix.of G * T) ^ 2
      ≤ max (⨆ t, linForm (fun k l => x t k * y t l) G) 0 ^ 2 := by
    intro G
    have hnet := one_sub_two_mul_mul_specNorm_le_iSup (S * Matrix.of G * T) ε hε.le I hI2 hcov
    have e : (⨆ t : I, ∑ i, ∑ j, t.1.2 i * (S * Matrix.of G * T) i j * t.1.1 j)
        = ⨆ t, linForm (fun k l => x t k * y t l) G := by
      congr 1
      funext t
      exact ssb_sandwich_entry S T G (fun i => t.1.2 i) (fun j => t.1.1 j)
    rw [e] at hnet
    have h0 : 0 ≤ (1 - 2 * ε) * specNorm (S * Matrix.of G * T) :=
      mul_nonneg (by linarith) (specNorm_nonneg _)
    calc (1 - 2 * ε) ^ 2 * specNorm (S * Matrix.of G * T) ^ 2
        = ((1 - 2 * ε) * specNorm (S * Matrix.of G * T)) ^ 2 := by ring
      _ ≤ _ := pow_le_pow_left₀ h0 (hnet.trans (le_max_left _ _)) 2
  calc (1 - 2 * ε) ^ 2 * ∫ G, specNorm (S * Matrix.of G * T) ^ 2 ∂(gaussianMatrix p m)
      = ∫ G, (1 - 2 * ε) ^ 2 * specNorm (S * Matrix.of G * T) ^ 2 ∂(gaussianMatrix p m) :=
        (integral_const_mul _ _).symm
    _ ≤ ∫ G, max (⨆ t, linForm (fun k l => x t k * y t l) G) 0 ^ 2 ∂(gaussianMatrix p m) :=
        integral_mono (hspec.const_mul _) hL step1
    _ ≤ ∫ H, max (⨆ t, linForm (ssbYc x y t) H) 0 ^ 2 ∂(gaussianMatrix 1 (p + m)) :=
        ssb_main_cmp x y
    _ ≤ (specNorm T * frobNorm S + specNorm S * frobNorm T) ^ 2 :=
        ssb_Y_bound S T x y (specNorm S) (specNorm T) (specNorm_nonneg S)
          (specNorm_nonneg T)
          (fun t => ssb_norm_vecMul_le S t.1.2 (hI2 _ t.2))
          (fun t => ssb_norm_mulVec_le T t.1.1 (hI1 _ t.2))
          (fun t g => ssb_vecMul_inner_le S t.1.2 (hI2 _ t.2) g)
          (fun t h => ssb_mulVec_inner_le T t.1.1 (hI1 _ t.2) h)
    _ = (specNorm S * frobNorm T + frobNorm S * specNorm T) ^ 2 := by ring


/-- **Second moment of a Gaussian sandwich.** For `S : a × p`, `T : m × n` and a `p × m`
standard Gaussian matrix `Γ`, `𝔼 ‖S Γ T‖₂² ≤ (‖S‖₂ ‖T‖_F + ‖S‖_F ‖T‖₂)²`. Source: Tropp–Webber
2023, Lemma B.1 (via Gordon's comparison); the first-moment version is Chevet's inequality (HMT
2011, Prop. A.2). Atlas: `spectral-second-moment`. Ported from Prove2me solution
`GaussianMatrix.spectral_second_moment_bound`. -/
theorem integral_specNorm_sq_mul_gaussianMatrix_mul_le {a p m n : ℕ} (S : Matrix (Fin a) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin n) ℝ) :
    ∫ G, specNorm (S * Matrix.of G * T) ^ 2 ∂(gaussianMatrix p m)
      ≤ (specNorm S * frobNorm T + frobNorm S * specNorm T) ^ 2 := by
  have hC : 0 ≤ (specNorm S * frobNorm T + frobNorm S * specNorm T) ^ 2 := sq_nonneg _
  have hzero : (∀ G : Fin p → Fin m → ℝ, specNorm (S * Matrix.of G * T) = 0) →
      ∫ G, specNorm (S * Matrix.of G * T) ^ 2 ∂(gaussianMatrix p m)
        ≤ (specNorm S * frobNorm T + frobNorm S * specNorm T) ^ 2 := by
    intro h0
    have : ∫ G, specNorm (S * Matrix.of G * T) ^ 2 ∂(gaussianMatrix p m) = 0 := by simp [h0]
    rw [this]; exact hC
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    exact hzero fun G => by rw [Subsingleton.elim (S * Matrix.of G * T) 0, specNorm_zero]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact hzero fun G => by rw [Subsingleton.elim (S * Matrix.of G * T) 0, specNorm_zero]
  set E := ∫ G, specNorm (S * Matrix.of G * T) ^ 2 ∂(gaussianMatrix p m) with hE
  set C := (specNorm S * frobNorm T + frobNorm S * specNorm T) ^ 2 with hCdef
  have hE0 : 0 ≤ E := integral_nonneg fun G => sq_nonneg _
  by_contra hcon
  have hlt : C < E := not_le.1 hcon
  have hEpos : 0 < E := lt_of_le_of_lt hC hlt
  have hε : 0 < (E - C) / (8 * E) := div_pos (by linarith) (by linarith)
  have hε2 : (E - C) / (8 * E) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h := ssb_scaled_bound S T ha hn ((E - C) / (8 * E)) hε hε2
  rw [← hE, ← hCdef] at h
  have h1 : (1 - 4 * ((E - C) / (8 * E))) * E ≤ (1 - 2 * ((E - C) / (8 * E))) ^ 2 * E :=
    mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg ((E - C) / (8 * E))]) hE0
  have h2 : (1 - 4 * ((E - C) / (8 * E))) * E = (E + C) / 2 := by
    field_simp; ring
  linarith

/-- **Second moment of a Gaussian sandwich, with integrability.** For `S : a × p`, `T : m × n`
and a `p × m` standard Gaussian matrix `Γ`, `‖S Γ T‖₂²` is integrable and
`𝔼 ‖S Γ T‖₂² ≤ (‖S‖₂ ‖T‖_F + ‖S‖_F ‖T‖₂)²`, i.e.
`(𝔼 ‖S Γ T‖₂²)^{1/2} ≤ ‖S‖₂ ‖T‖_F + ‖S‖_F ‖T‖₂`. Source: Tropp–Webber 2023, Lemma B.1.
Atlas: `spectral-second-moment`. Ported from Prove2me solution
`GaussianMatrix.spectral_second_moment`. -/
theorem integrable_and_integral_specNorm_sq_mul_gaussianMatrix_mul_le {a p m n : ℕ}
    (S : Matrix (Fin a) (Fin p) ℝ) (T : Matrix (Fin m) (Fin n) ℝ) :
    Integrable (fun G : Fin p → Fin m → ℝ => specNorm (S * Matrix.of G * T) ^ 2)
      (gaussianMatrix p m) ∧
    ∫ G, specNorm (S * Matrix.of G * T) ^ 2 ∂(gaussianMatrix p m)
      ≤ (specNorm S * frobNorm T + frobNorm S * specNorm T) ^ 2 := by
  refine ⟨(integrable_and_integrable_sq_of_abs_sub_le_mul_frobNorm
    (fun G : Fin p → Fin m → ℝ => specNorm (S * Matrix.of G * T))
    (specNorm S * specNorm T) (mul_nonneg (specNorm_nonneg S) (specNorm_nonneg T))
    (abs_specNorm_mul_of_mul_sub_le S T)).2, integral_specNorm_sq_mul_gaussianMatrix_mul_le S T⟩

end NLAlib
