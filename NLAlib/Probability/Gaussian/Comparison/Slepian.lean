import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Probability.CDF
import Mathlib.Topology.UniformSpace.Uniformizable
import NLAlib.Probability.Gaussian.Comparison.Interpolation
/-!
# Slepian's inequality

For centred Gaussian processes `X, Y` on a finite index set with equal variances
`𝔼 Xₜ² = 𝔼 Yₜ²` and dominated increments `𝔼 (Xₛ - Xₜ)² ≤ 𝔼 (Yₛ - Yₜ)²`, the maximum of `X` is
stochastically dominated by the maximum of `Y`:

* `slepian_inequality`: `P(τ < maxₜ Xₜ) ≤ Q(τ < maxₜ Yₜ)` for every `τ`
  (Slepian 1962; Vershynin 2018, Thm 7.2.1).

Proof by Gaussian interpolation (Chatterjee's proof, as in Vershynin 2018, §7.2): with the smooth
product functional `F(x) = ∏ₜ φ(xₜ)` (`φ ≥ 0` nonincreasing, a smoothed indicator of
`(-∞, τ]`), whose off-diagonal Hessian entries are nonnegative, `θ ↦ 𝔼 F(cos θ X + sin θ Y)` is
nonincreasing on `[0, π/2]` by Gaussian integration by parts (equal variances kill the diagonal
terms); then `Q(max Y ≤ τ) ≤ 𝔼 F_δ(Y) ≤ 𝔼 F_δ(X) ≤ P(max X ≤ τ + δ)` and `δ ↓ 0` by right
continuity of the distribution function of `max X`.

Ported from the Prove2me solution `GaussianMatrix.slepian_tail_comparison`.

Atlas: `slepian`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

section ProdFun

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "PR" j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j

/-- `F(x) = ∏ₜ φ(xₜ)`, a smooth surrogate of the indicator of `{max x ≤ τ}`. -/
private noncomputable def slF (φ : ℝ → ℝ) (x : ι → ℝ) : ℝ := ∏ t, φ (x t)

/-- the partial derivative `∂ᵢF` -/
private noncomputable def slG (φ φ' : ℝ → ℝ) (i : ι) (x : ι → ℝ) : ℝ :=
  φ' (x i) * ∏ t ∈ Finset.univ.erase i, φ (x t)

/-- the second partial derivative `∂ⱼ∂ᵢF` -/
private noncomputable def slH (φ φ' φ'' : ℝ → ℝ) (i j : ι) (x : ι → ℝ) : ℝ :=
  if j = i then φ'' (x i) * ∏ t ∈ Finset.univ.erase i, φ (x t)
  else φ' (x i) * (φ' (x j) * ∏ t ∈ (Finset.univ.erase i).erase j, φ (x t))

omit [DecidableEq ι] in
private theorem sl_coord_hasFDerivAt (φ φ' : ℝ → ℝ) (hφ : ∀ u, HasDerivAt φ (φ' u) u) (t : ι)
    (x : ι → ℝ) : HasFDerivAt (fun y : ι → ℝ => φ (y t)) (φ' (x t) • PR t) x := by
  have h1 : HasDerivAt φ (φ' (x t)) ((PR t) x) := hφ (x t)
  exact h1.comp_hasFDerivAt x (PR t).hasFDerivAt

private theorem slF_hasFDerivAt (φ φ' : ℝ → ℝ) (hφ : ∀ u, HasDerivAt φ (φ' u) u) (x : ι → ℝ) :
    HasFDerivAt (slF φ) (∑ i, slG φ φ' i x • PR i) x := by
  have h := HasFDerivAt.finsetProd (u := Finset.univ)
    (fun t _ => sl_coord_hasFDerivAt φ φ' hφ t x)
  refine h.congr_fderiv ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, slG, mul_comm]

private theorem slG_hasFDerivAt (φ φ' φ'' : ℝ → ℝ) (hφ : ∀ u, HasDerivAt φ (φ' u) u)
    (hφ' : ∀ u, HasDerivAt φ' (φ'' u) u) (i : ι) (x : ι → ℝ) :
    HasFDerivAt (slG φ φ' i) (∑ j, slH φ φ' φ'' i j x • PR j) x := by
  have h1 := sl_coord_hasFDerivAt φ' φ'' hφ' i x
  have h2 := HasFDerivAt.finsetProd (u := Finset.univ.erase i)
    (fun t _ => sl_coord_hasFDerivAt φ φ' hφ t x)
  have h := h1.mul h2
  refine h.congr_fderiv ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [slH, if_true]
  have e : ∑ j ∈ Finset.univ.erase i, slH φ φ' φ'' i j x • (PR j)
      = ∑ j ∈ Finset.univ.erase i,
        (φ' (x i) * (φ' (x j) * ∏ t ∈ (Finset.univ.erase i).erase j, φ (x t))) • (PR j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [slH, if_neg (Finset.ne_of_mem_erase hj)]
  simp only [slH] at e
  rw [e, add_comm, Finset.smul_sum]
  simp only [smul_smul]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [mul_comm]
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    ring

variable {φ φ' φ'' : ℝ → ℝ}

omit [Fintype ι] [DecidableEq ι] in
private theorem sl_prod_bounds (h0 : ∀ u, 0 ≤ φ u) (h1 : ∀ u, φ u ≤ 1) (s : Finset ι) (x : ι → ℝ) :
    0 ≤ ∏ t ∈ s, φ (x t) ∧ ∏ t ∈ s, φ (x t) ≤ 1 :=
  ⟨Finset.prod_nonneg fun _ _ => h0 _, Finset.prod_le_one (fun _ _ => h0 _) (fun _ _ => h1 _)⟩

omit [DecidableEq ι] in
private theorem slF_nonneg (h0 : ∀ u, 0 ≤ φ u) (h1 : ∀ u, φ u ≤ 1) (x : ι → ℝ) : 0 ≤ slF φ x :=
  (sl_prod_bounds h0 h1 _ x).1

omit [DecidableEq ι] in
private theorem slF_le_one (h0 : ∀ u, 0 ≤ φ u) (h1 : ∀ u, φ u ≤ 1) (x : ι → ℝ) : slF φ x ≤ 1 :=
  (sl_prod_bounds h0 h1 _ x).2

private theorem slG_abs_le (h0 : ∀ u, 0 ≤ φ u) (h1 : ∀ u, φ u ≤ 1) {C : ℝ} (hC1 : ∀ u, |φ' u| ≤ C)
    (i : ι) (x : ι → ℝ) : |slG φ φ' i x| ≤ C := by
  obtain ⟨p0, p1⟩ := sl_prod_bounds h0 h1 (Finset.univ.erase i) x
  rw [slG, abs_mul, abs_of_nonneg p0]
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC1 0)
  calc |φ' (x i)| * _ ≤ C * 1 := mul_le_mul (hC1 _) p1 p0 hC0
    _ = C := mul_one C

private theorem slH_abs_le (h0 : ∀ u, 0 ≤ φ u) (h1 : ∀ u, φ u ≤ 1) {C : ℝ} (hC1 : ∀ u, |φ' u| ≤ C)
    (hC2 : ∀ u, |φ'' u| ≤ C) (i j : ι) (x : ι → ℝ) : |slH φ φ' φ'' i j x| ≤ C + C * C := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC1 0)
  unfold slH
  split_ifs with hij
  · obtain ⟨p0, p1⟩ := sl_prod_bounds h0 h1 (Finset.univ.erase i) x
    rw [abs_mul, abs_of_nonneg p0]
    have := mul_le_mul (hC2 (x i)) p1 p0 hC0
    nlinarith
  · obtain ⟨p0, p1⟩ := sl_prod_bounds h0 h1 ((Finset.univ.erase i).erase j) x
    rw [abs_mul, abs_mul, abs_of_nonneg p0]
    have a1 := hC1 (x i)
    have a2 := hC1 (x j)
    have b1 := abs_nonneg (φ' (x i))
    have b2 := abs_nonneg (φ' (x j))
    have : |φ' (x j)| * ∏ t ∈ (Finset.univ.erase i).erase j, φ (x t) ≤ C :=
      (mul_le_mul a2 p1 p0 hC0).trans (le_of_eq (mul_one C))
    have h3 : 0 ≤ |φ' (x j)| * ∏ t ∈ (Finset.univ.erase i).erase j, φ (x t) :=
      mul_nonneg b2 p0
    have := mul_le_mul a1 this h3 hC0
    nlinarith

private theorem slH_nonneg_of_ne (h0 : ∀ u, 0 ≤ φ u) (hd : ∀ u, φ' u ≤ 0) {i j : ι} (hij : j ≠ i)
    (x : ι → ℝ) : 0 ≤ slH φ φ' φ'' i j x := by
  rw [slH, if_neg hij]
  have p0 : 0 ≤ ∏ t ∈ (Finset.univ.erase i).erase j, φ (x t) := Finset.prod_nonneg fun _ _ => h0 _
  have := mul_nonpos_of_nonpos_of_nonneg (hd (x j)) p0
  exact mul_nonneg_of_nonpos_of_nonpos (hd (x i)) this

private theorem slH_continuous (hφc : Continuous φ) (hφ'c : Continuous φ') (hφ''c : Continuous φ'')
    (i j : ι) : Continuous (slH (ι := ι) φ φ' φ'' i j) := by
  unfold slH
  split_ifs
  · exact (hφ''c.comp (continuous_apply i)).mul
      (continuous_finsetProd _ fun t _ => hφc.comp (continuous_apply t))
  · exact (hφ'c.comp (continuous_apply i)).mul ((hφ'c.comp (continuous_apply j)).mul
      (continuous_finsetProd _ fun t _ => hφc.comp (continuous_apply t)))

end ProdFun


section Compare

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω] {P : Measure Ω}

/-- Slepian's comparison for the smooth product functional `∏ₜ φ(xₜ)`, `φ` nonincreasing:
on one space with `(X, Y)` jointly Gaussian, centered, with vanishing cross-moments, equal
variances and dominated increments, `𝔼 F(Y) ≤ 𝔼 F(X)`. This is
`integral_le_integral_of_covariance_hessian_nonneg` with `X, Y` swapped. -/
private theorem sl_compare (X Y : ι → Ω → ℝ)
    (hXY : HasGaussianLaw (fun ω => (fun t => X t ω, fun t => Y t ω)) P)
    (hX0 : ∀ t, ∫ ω, X t ω ∂P = 0) (hY0 : ∀ t, ∫ ω, Y t ω ∂P = 0)
    (hcross : ∀ s t, ∫ ω, X s ω * Y t ω ∂P = 0)
    (hvar : ∀ t, ∫ ω, X t ω * X t ω ∂P = ∫ ω, Y t ω * Y t ω ∂P)
    (hinc : ∀ s t, ∫ ω, (X s ω - X t ω) ^ 2 ∂P ≤ ∫ ω, (Y s ω - Y t ω) ^ 2 ∂P)
    (φ φ' φ'' : ℝ → ℝ) (hφ : ∀ u, HasDerivAt φ (φ' u) u)
    (hφ' : ∀ u, HasDerivAt φ' (φ'' u) u) (hφ''c : Continuous φ'')
    (h0 : ∀ u, 0 ≤ φ u) (h1 : ∀ u, φ u ≤ 1) (hd : ∀ u, φ' u ≤ 0)
    (C : ℝ) (hC1 : ∀ u, |φ' u| ≤ C) (hC2 : ∀ u, |φ'' u| ≤ C) :
    ∫ ω, slF φ (fun t => Y t ω) ∂P ≤ ∫ ω, slF φ (fun t => X t ω) ∂P := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC1 0)
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun u => (hφ u).continuousAt
  have hφ'c : Continuous φ' := continuous_iff_continuousAt.2 fun u => (hφ' u).continuousAt
  have hXm : ∀ t, MemLp (X t) 2 P := fun t => (hXY.fst.eval t).memLp_two
  have hYm : ∀ t, MemLp (Y t) 2 P := fun t => (hXY.snd.eval t).memLp_two
  -- equal variances and dominated increments: `𝔼 YᵢYⱼ ≤ 𝔼 XᵢXⱼ`
  have hΔo : ∀ i j, ∫ ω, Y i ω * Y j ω ∂P - ∫ ω, X i ω * X j ω ∂P ≤ 0 := by
    intro i j
    have h := hinc i j
    rw [integral_sub_sq_eq X hXm i j, integral_sub_sq_eq Y hYm i j] at h
    have ea : ∫ ω, X j ω * X i ω ∂P = ∫ ω, X i ω * X j ω ∂P := by
      congr 1; ext ω; ring
    have eb : ∫ ω, Y j ω * Y i ω ∂P = ∫ ω, Y i ω * Y j ω ∂P := by
      congr 1; ext ω; ring
    rw [ea, eb, hvar i, hvar j] at h
    linarith
  have hYX : HasGaussianLaw (fun ω => (fun t => Y t ω, fun t => X t ω)) P := by
    simpa using hXY.map_fun ((ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)).prod
      (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)))
  have hKC : C ≤ C + C * C := by nlinarith
  refine integral_le_integral_of_covariance_hessian_nonneg Y X hYX hY0 hX0
    (fun s t => by simpa only [mul_comm] using hcross t s) (slF φ) (slG φ φ') (slH φ φ' φ'')
    (slF_hasFDerivAt φ φ' hφ) (slG_hasFDerivAt φ φ' φ'' hφ hφ') (slH_continuous hφc hφ'c hφ''c)
    (C + C * C) (fun i x => (slG_abs_le h0 h1 hC1 i x).trans hKC) (slH_abs_le h0 h1 hC1 hC2)
    1 (fun x => ?_) (fun x => ?_)
  · rw [abs_of_nonneg (slF_nonneg h0 h1 x)]
    have := slF_le_one h0 h1 x
    have : 0 ≤ ∑ t, |x t| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  · refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    by_cases hij : j = i
    · rw [hij, hvar i, sub_self, zero_mul]
    · exact mul_nonneg (by linarith [hΔo i j]) (slH_nonneg_of_ne h0 hd hij x)

end Compare


section Cutoff

private theorem sl_deriv_zero_of_const {f : ℝ → ℝ} {c x : ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hx : x ∈ U)
    (hf : ∀ y ∈ U, f y = c) : deriv f x = 0 ∧ deriv (deriv f) x = 0 := by
  have h1 : ∀ y ∈ U, deriv f y = 0 := fun y hy => by
    have : f =ᶠ[nhds y] fun _ => c := Filter.eventually_of_mem (hU.mem_nhds hy) hf
    rw [this.deriv_eq]; exact deriv_const _ _
  refine ⟨h1 x hx, ?_⟩
  have : deriv f =ᶠ[nhds x] fun _ => (0 : ℝ) := Filter.eventually_of_mem (hU.mem_nhds hx) h1
  rw [this.deriv_eq]; exact deriv_const _ _

private theorem sl_sT_deriv_zero {x : ℝ} (hx : x ∉ Set.Icc (0 : ℝ) 1) :
    deriv Real.smoothTransition x = 0 ∧ deriv (deriv Real.smoothTransition) x = 0 := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with hx | hx
  · exact sl_deriv_zero_of_const isOpen_Iio hx
      (fun y hy => Real.smoothTransition.zero_of_nonpos (le_of_lt hy))
  · exact sl_deriv_zero_of_const isOpen_Ioi hx
      (fun y hy => Real.smoothTransition.one_of_one_le (le_of_lt hy))

private theorem sl_sT_props :
    (∀ x, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x) ∧
    (∀ x, HasDerivAt (deriv Real.smoothTransition)
      (deriv (deriv Real.smoothTransition) x) x) ∧
    Continuous (deriv (deriv Real.smoothTransition)) ∧
    (∀ x, 0 ≤ deriv Real.smoothTransition x) ∧
    ∃ C, (∀ x, |deriv Real.smoothTransition x| ≤ C) ∧
      (∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition := Real.smoothTransition.contDiff
  have hc1 : ContDiff ℝ (⊤ : ℕ∞) (deriv Real.smoothTransition) := by
    simpa using hc.iterate_deriv 1
  have hc2 : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv Real.smoothTransition)) := by
    have := hc.iterate_deriv 2
    simpa [Function.iterate_succ] using this
  have hd0 := hc.differentiable (by simp)
  have hd1 := hc1.differentiable (by simp)
  refine ⟨fun x => (hd0 x).hasDerivAt, fun x => (hd1 x).hasDerivAt, hc2.continuous,
    fun x => Real.smoothTransition.monotone.deriv_nonneg, ?_⟩
  have s1 : HasCompactSupport (deriv Real.smoothTransition) :=
    HasCompactSupport.intro isCompact_Icc fun x hx => (sl_sT_deriv_zero hx).1
  have s2 : HasCompactSupport (deriv (deriv Real.smoothTransition)) :=
    HasCompactSupport.intro isCompact_Icc fun x hx => (sl_sT_deriv_zero hx).2
  obtain ⟨C1, hC1⟩ := hc1.continuous.bounded_above_of_compact_support s1
  obtain ⟨C2, hC2⟩ := hc2.continuous.bounded_above_of_compact_support s2
  refine ⟨max C1 C2, fun x => ?_, fun x => ?_⟩
  · exact (hC1 x).trans (le_max_left _ _)
  · exact (hC2 x).trans (le_max_right _ _)

/-- the cutoff `φ_δ(u) = s((τ + δ - u)/δ)`: `1` on `(-∞, τ]`, `0` on `[τ + δ, ∞)` -/
private noncomputable def slφ (τ δ u : ℝ) : ℝ := Real.smoothTransition ((τ + δ - u) / δ)
private noncomputable def slφ1 (τ δ u : ℝ) : ℝ :=
  -(1 / δ) * deriv Real.smoothTransition ((τ + δ - u) / δ)
private noncomputable def slφ2 (τ δ u : ℝ) : ℝ :=
  (1 / δ) ^ 2 * deriv (deriv Real.smoothTransition) ((τ + δ - u) / δ)

private theorem sl_cutoff (τ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (∀ u, HasDerivAt (slφ τ δ) (slφ1 τ δ u) u) ∧
    (∀ u, HasDerivAt (slφ1 τ δ) (slφ2 τ δ u) u) ∧
    Continuous (slφ2 τ δ) ∧
    (∀ u, 0 ≤ slφ τ δ u) ∧ (∀ u, slφ τ δ u ≤ 1) ∧ (∀ u, slφ1 τ δ u ≤ 0) ∧
    (∀ u, u ≤ τ → slφ τ δ u = 1) ∧ (∀ u, τ + δ ≤ u → slφ τ δ u = 0) ∧
    ∃ C, (∀ u, |slφ1 τ δ u| ≤ C) ∧ (∀ u, |slφ2 τ δ u| ≤ C) := by
  obtain ⟨d0, d1, c2, pos, C, hC1, hC2⟩ := sl_sT_props
  have ha : ∀ u, HasDerivAt (fun u => (τ + δ - u) / δ) (-1 / δ) u := fun u => by
    simpa using ((hasDerivAt_id u).const_sub (τ + δ)).div_const δ
  refine ⟨fun u => ?_, fun u => ?_, ?_, fun u => Real.smoothTransition.nonneg _,
    fun u => Real.smoothTransition.le_one _, fun u => ?_, fun u hu => ?_, fun u hu => ?_,
    ⟨(1 / δ + (1 / δ) ^ 2) * C, fun u => ?_, fun u => ?_⟩⟩
  · have := (d0 ((τ + δ - u) / δ)).comp u (ha u)
    refine this.congr_deriv ?_
    simp only [slφ1]; ring
  · have := ((d1 ((τ + δ - u) / δ)).comp u (ha u)).const_mul (-(1 / δ))
    refine this.congr_deriv ?_
    simp only [slφ2]; ring
  · unfold slφ2; fun_prop
  · simp only [slφ1]
    have := pos ((τ + δ - u) / δ)
    have : 0 < 1 / δ := by positivity
    nlinarith
  · simp only [slφ]
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ hδ]; linarith
  · simp only [slφ]
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  · have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC1 0)
    simp only [slφ1, abs_mul, abs_neg, abs_of_pos (one_div_pos.2 hδ)]
    have := mul_le_mul_of_nonneg_left (hC1 ((τ + δ - u) / δ)) (one_div_pos.2 hδ).le
    nlinarith [sq_nonneg (1 / δ)]
  · have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC1 0)
    simp only [slφ2, abs_mul, abs_pow, abs_of_pos (one_div_pos.2 hδ)]
    have := mul_le_mul_of_nonneg_left (hC2 ((τ + δ - u) / δ)) (sq_nonneg (1 / δ))
    nlinarith [one_div_pos.2 hδ]

end Cutoff


section Main

/-- **Slepian's inequality.** Let `X` (on `(Ω, P)`) and `Y` (on `(Ω', Q)`) be centred Gaussian
processes indexed by a finite set, with equal variances `𝔼 Xₜ² = 𝔼 Yₜ²` and dominated
increments `𝔼 (Xₛ - Xₜ)² ≤ 𝔼 (Yₛ - Yₜ)²`. Then for every `τ`,
`P(τ < maxₜ Xₜ) ≤ Q(τ < maxₜ Yₜ)`.
Source: Slepian 1962; Vershynin 2018, Thm 7.2.1. Atlas: `slepian`. Ported from Prove2me solution
`GaussianMatrix.slepian_tail_comparison`.
atlas: slepian -/
theorem slepian_inequality {ι Ω Ω' : Type*} [Fintype ι] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'} (X : ι → Ω → ℝ) (Y : ι → Ω' → ℝ)
    (hX : HasGaussianLaw (fun ω t => X t ω) P) (hY : HasGaussianLaw (fun ω t => Y t ω) Q)
    (hX0 : ∀ t, ∫ ω, X t ω ∂P = 0) (hY0 : ∀ t, ∫ ω, Y t ω ∂Q = 0)
    (hvar : ∀ t, ∫ ω, X t ω ^ 2 ∂P = ∫ ω, Y t ω ^ 2 ∂Q)
    (hinc : ∀ s t, ∫ ω, (X s ω - X t ω) ^ 2 ∂P ≤ ∫ ω, (Y s ω - Y t ω) ^ 2 ∂Q) (τ : ℝ) :
    P {ω | τ < ⨆ t, X t ω} ≤ Q {ω | τ < ⨆ t, Y t ω} := by
  have hP := hX.isProbabilityMeasure
  have hQ := hY.isProbabilityMeasure
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [Real.iSup_of_isEmpty]
    by_cases h : τ < 0 <;> simp [h]
  classical
  set μX := P.map (fun ω t => X t ω) with hμX
  set μY := Q.map (fun ω t => Y t ω) with hμY
  have : IsGaussian μX := hX.isGaussian_map
  have : IsGaussian μY := hY.isGaussian_map
  have : IsProbabilityMeasure μX := Measure.isProbabilityMeasure_map hX.aemeasurable
  have : IsProbabilityMeasure μY := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hsup : Measurable (fun x : ι → ℝ => ⨆ t, x t) :=
    Measurable.iSup fun t => measurable_pi_apply t
  set S : Set (ι → ℝ) := {x | τ < ⨆ t, x t} with hSdef
  have hS : MeasurableSet S := measurableSet_lt measurable_const hsup
  have eX : P {ω | τ < ⨆ t, X t ω} = μX S :=
    (Measure.map_apply_of_aemeasurable hX.aemeasurable hS).symm
  have eY : Q {ω | τ < ⨆ t, Y t ω} = μY S :=
    (Measure.map_apply_of_aemeasurable hY.aemeasurable hS).symm
  rw [eX, eY]
  set T : ℝ → Set (ι → ℝ) := fun a => {x | ⨆ t, x t ≤ a} with hTdef
  have hT : ∀ a, MeasurableSet (T a) := fun a => measurableSet_le hsup measurable_const
  have hmemT : ∀ a x, x ∈ T a ↔ ∀ t, x t ≤ a := fun a x =>
    ciSup_le_iff (Set.finite_range x).bddAbove
  -- one product space
  set μ := μX.prod μY with hμ
  have hlaw : HasGaussianLaw (fun p : (ι → ℝ) × (ι → ℝ) => (fun t => p.1 t, fun t => p.2 t)) μ :=
    IsGaussian.hasGaussianLaw_id
  have hfst : ∀ f : (ι → ℝ) → ℝ, Measurable f → ∫ p, f p.1 ∂μ = ∫ x, f x ∂μX := by
    intro f hf
    have h1 : ∫ p, f p.1 ∂μ = ∫ x, f x ∂(μ.map Prod.fst) :=
      (integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable).symm
    rw [h1, hμ, Measure.map_fst_prod, measure_univ, one_smul]
  have hsnd : ∀ f : (ι → ℝ) → ℝ, Measurable f → ∫ p, f p.2 ∂μ = ∫ x, f x ∂μY := by
    intro f hf
    have h1 : ∫ p, f p.2 ∂μ = ∫ x, f x ∂(μ.map Prod.snd) :=
      (integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable).symm
    rw [h1, hμ, Measure.map_snd_prod, measure_univ, one_smul]
  have hXf : ∀ f : (ι → ℝ) → ℝ, Measurable f →
      ∫ p, f p.1 ∂μ = ∫ ω, f (fun t => X t ω) ∂P := fun f hf => by
    rw [hfst f hf, hμX, integral_map hX.aemeasurable hf.aestronglyMeasurable]
  have hYf : ∀ f : (ι → ℝ) → ℝ, Measurable f →
      ∫ p, f p.2 ∂μ = ∫ ω, f (fun t => Y t ω) ∂Q := fun f hf => by
    rw [hsnd f hf, hμY, integral_map hY.aemeasurable hf.aestronglyMeasurable]
  have hX0' : ∀ t, ∫ p, p.1 t ∂μ = 0 := fun t => by
    rw [hXf (fun x => x t) (measurable_pi_apply t)]; exact hX0 t
  have hY0' : ∀ t, ∫ p, p.2 t ∂μ = 0 := fun t => by
    rw [hYf (fun x => x t) (measurable_pi_apply t)]; exact hY0 t
  have hcross : ∀ s t, ∫ p, p.1 s * p.2 t ∂μ = 0 := by
    intro s t
    rw [hμ, integral_prod_mul (fun x : ι → ℝ => x s) (fun y : ι → ℝ => y t)]
    have : ∫ x, x s ∂μX = 0 := by
      rw [hμX, integral_map hX.aemeasurable (measurable_pi_apply s).aestronglyMeasurable]
      exact hX0 s
    rw [this, zero_mul]
  have hvar' : ∀ t, ∫ p, p.1 t * p.1 t ∂μ = ∫ p, p.2 t * p.2 t ∂μ := by
    intro t
    rw [hXf (fun x => x t * x t) (by fun_prop), hYf (fun x => x t * x t) (by fun_prop)]
    simpa only [sq] using hvar t
  have hinc' : ∀ s t, ∫ p, (p.1 s - p.1 t) ^ 2 ∂μ ≤ ∫ p, (p.2 s - p.2 t) ^ 2 ∂μ := by
    intro s t
    rw [hXf (fun x => (x s - x t) ^ 2) (by fun_prop),
      hYf (fun x => (x s - x t) ^ 2) (by fun_prop)]
    exact hinc s t
  -- smoothed comparison
  have key : ∀ δ : ℝ, 0 < δ → μY.real (T τ) ≤ μX.real (T (τ + δ)) := by
    intro δ hδ
    obtain ⟨d0, d1, c2, p0, p1, pd, pτ, pτδ, C, hC1, hC2⟩ := sl_cutoff τ hδ
    have hc := sl_compare (P := μ) (fun t p => p.1 t) (fun t p => p.2 t) hlaw hX0' hY0'
      hcross hvar' hinc' (slφ τ δ) (slφ1 τ δ) (slφ2 τ δ) d0 d1 c2 p0 p1 pd C hC1 hC2
    have hFc : Continuous (slF (ι := ι) (slφ τ δ)) :=
      continuous_iff_continuousAt.2 fun x =>
        (slF_hasFDerivAt (slφ τ δ) (slφ1 τ δ) d0 x).continuousAt
    rw [hfst _ hFc.measurable, hsnd _ hFc.measurable] at hc
    have hFint : ∀ ν : Measure (ι → ℝ), IsFiniteMeasure ν → Integrable (slF (slφ τ δ)) ν :=
      fun ν _ => Integrable.mono' (integrable_const 1) hFc.aestronglyMeasurable
        (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (slF_nonneg p0 p1 _)]; exact slF_le_one p0 p1 _)
    have hlow : μY.real (T τ) ≤ ∫ x, slF (slφ τ δ) x ∂μY := by
      rw [← integral_indicator_one (hT τ)]
      refine integral_mono ((integrable_const 1).indicator (hT τ)) (hFint μY inferInstance)
        fun x => ?_
      by_cases hx : x ∈ T τ
      · rw [Set.indicator_of_mem hx, Pi.one_apply]
        have : slF (slφ τ δ) x = 1 :=
          Finset.prod_eq_one fun t _ => pτ (x t) ((hmemT τ x).1 hx t)
        rw [this]
      · rw [Set.indicator_of_notMem hx]; exact slF_nonneg p0 p1 _
    have hup : ∫ x, slF (slφ τ δ) x ∂μX ≤ μX.real (T (τ + δ)) := by
      rw [← integral_indicator_one (hT (τ + δ))]
      refine integral_mono (hFint μX inferInstance)
        ((integrable_const 1).indicator (hT (τ + δ))) fun x => ?_
      by_cases hx : x ∈ T (τ + δ)
      · rw [Set.indicator_of_mem hx, Pi.one_apply]; exact slF_le_one p0 p1 _
      · rw [Set.indicator_of_notMem hx]
        have : ¬ ∀ t, x t ≤ τ + δ := fun h => hx ((hmemT _ x).2 h)
        push Not at this
        obtain ⟨t, ht⟩ := this
        have : slF (slφ τ δ) x = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ t) (pτδ (x t) ht.le)
        rw [this]
    linarith
  -- right-continuity of the distribution function of `max X`
  set ν := μX.map (fun x : ι → ℝ => ⨆ t, x t) with hν
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hsup.aemeasurable
  have hνT : ∀ a, μX.real (T a) = cdf ν a := by
    intro a
    rw [cdf_eq_real, measureReal_def, measureReal_def, hν,
      Measure.map_apply hsup measurableSet_Iic]
    rfl
  have hlim : Filter.Tendsto (cdf ν) (nhdsWithin τ (Set.Ioi τ)) (nhds (cdf ν τ)) :=
    ((cdf ν).right_continuous τ).mono Set.Ioi_subset_Ici_self
  have hreal : μY.real (T τ) ≤ μX.real (T τ) := by
    rw [hνT]
    refine ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun a ha => ?_)
    have := key (a - τ) (sub_pos.2 ha)
    rw [hνT, add_sub_cancel] at this
    exact this
  have hle : μY (T τ) ≤ μX (T τ) := by
    rw [← ofReal_measureReal (μ := μY), ← ofReal_measureReal (μ := μX)]
    exact ENNReal.ofReal_le_ofReal hreal
  have hSc : S = (T τ)ᶜ := by
    ext x; simp [hSdef, hTdef, not_le]
  rw [hSc, prob_compl_eq_one_sub (hT τ), prob_compl_eq_one_sub (hT τ)]
  exact tsub_le_tsub_left hle 1

end Main
end NLAlib
