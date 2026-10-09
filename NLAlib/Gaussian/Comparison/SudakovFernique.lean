import NLAlib.Gaussian.Concentration.IntegrationByParts
import NLAlib.Gaussian.Comparison.Interpolation

/-!
# The Sudakov–Fernique inequality

For centred Gaussian processes `X, Y` on a finite index set with dominated increments
`𝔼 (Xₛ - Xₜ)² ≤ 𝔼 (Yₛ - Yₜ)²` (no assumption on the variances),

* `sudakov_fernique_inequality`: `𝔼 maxₜ Xₜ ≤ 𝔼 maxₜ Yₜ`
  (Sudakov 1971, Fernique 1975; Vershynin 2018, Thm 7.2.11).

Proof by Gaussian interpolation (Chatterjee 2005; Vershynin 2018, §7.2): realise independent
copies of `X` and `Y` on the product of their laws; for the soft-max
`F_β(x) = β⁻¹ log ∑ₜ exp(β xₜ)`, whose Hessian is `β (diag p - p pᵀ)` with `p` the softmax
weights, `θ ↦ 𝔼 F_β(cos θ X + sin θ Y)` has nonnegative derivative on `[0, π/2]` by Gaussian
integration by parts; since `max x ≤ F_β(x) ≤ max x + log |ι| / β`, let `β → ∞`.

Ported from the Prove2me solution `GaussianMatrix.sudakov_fernique`.

Atlas: `sudakov-fernique`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

section Softmax
variable {ι : Type*} [Fintype ι]

private noncomputable def sfS (β : ℝ) (x : ι → ℝ) : ℝ := ∑ t, Real.exp (β * x t)
private noncomputable def sfF (β : ℝ) (x : ι → ℝ) : ℝ := Real.log (sfS β x) / β
private noncomputable def sfp (β : ℝ) (i : ι) (x : ι → ℝ) : ℝ := Real.exp (β * x i) / sfS β x

local notation "PR" j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j

private theorem sfS_pos [Nonempty ι] (β : ℝ) (x : ι → ℝ) : 0 < sfS β x :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

private theorem sfp_nonneg (β : ℝ) (i : ι) (x : ι → ℝ) : 0 ≤ sfp β i x :=
  div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)

private theorem sfp_sum [Nonempty ι] (β : ℝ) (x : ι → ℝ) : ∑ i, sfp β i x = 1 := by
  simp only [sfp, ← Finset.sum_div]
  exact div_self (sfS_pos β x).ne'

private theorem sfp_le_one [Nonempty ι] (β : ℝ) (i : ι) (x : ι → ℝ) : sfp β i x ≤ 1 := by
  rw [← sfp_sum β x]
  exact Finset.single_le_sum (fun j _ => sfp_nonneg β j x) (Finset.mem_univ i)

private theorem sfS_hasFDerivAt (β : ℝ) (x : ι → ℝ) :
    HasFDerivAt (sfS β) (∑ t, (β * Real.exp (β * x t)) • PR t) x := by
  have : ∀ t ∈ (Finset.univ : Finset ι), HasFDerivAt (fun y : ι → ℝ => Real.exp (β * y t))
      ((β * Real.exp (β * x t)) • PR t) x := by
    intro t _
    have h := (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) t).hasFDerivAt
      (x := x)).const_mul β).exp
    exact h.congr_fderiv (by rw [smul_smul, mul_comm]; rfl)
  have h := HasFDerivAt.sum this
  have e : (sfS β : (ι → ℝ) → ℝ) = ∑ t, fun y : ι → ℝ => Real.exp (β * y t) := by
    funext y; simp [sfS]
  rw [e]; exact h

private theorem sfF_hasFDerivAt [Nonempty ι] (β : ℝ) (hβ : β ≠ 0) (x : ι → ℝ) :
    HasFDerivAt (sfF β) (∑ i, sfp β i x • PR i) x := by
  have h := ((sfS_hasFDerivAt β x).log (sfS_pos β x).ne').mul_const β⁻¹
  have e : (sfF β : (ι → ℝ) → ℝ) = fun y => Real.log (sfS β y) * β⁻¹ := by
    funext y; simp [sfF, div_eq_mul_inv]
  rw [e]
  refine h.congr_fderiv ?_
  ext v
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, Finset.mul_sum, sfp]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

/-- the Hessian coefficient of the softmax -/
private noncomputable def sfH [DecidableEq ι] (β : ℝ) (i j : ι) (x : ι → ℝ) : ℝ :=
  β * ((if i = j then sfp β i x else 0) - sfp β i x * sfp β j x)

private theorem sfp_hasFDerivAt [Nonempty ι] [DecidableEq ι] (β : ℝ) (i : ι) (x : ι → ℝ) :
    HasFDerivAt (sfp β i) (∑ j, sfH β i j x • PR j) x := by
  have h1 : HasFDerivAt (fun y : ι → ℝ => Real.exp (β * y i))
      ((β * Real.exp (β * x i)) • PR i) x := by
    have h := (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).hasFDerivAt
      (x := x)).const_mul β).exp
    exact h.congr_fderiv (by rw [smul_smul, mul_comm]; rfl)
  have h2 := (hasDerivAt_inv (sfS_pos β x).ne').comp_hasFDerivAt x (sfS_hasFDerivAt β x)
  have h := h1.mul h2
  have e : (sfp β i : (ι → ℝ) → ℝ) = fun y => Real.exp (β * y i) * ((fun z => z⁻¹) ∘ sfS β) y := by
    funext y; simp [sfp, div_eq_mul_inv]
  rw [e]
  refine h.congr_fderiv ?_
  ext v
  have hS := (sfS_pos β x).ne'
  set S := sfS β x with hSdef
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, sfH, sfp,
    add_apply, Function.comp_apply]
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, ← hSdef]
  have e2 : ∑ j, β * (Real.exp (β * x i) / S * (Real.exp (β * x j) / S)) * v j
      = Real.exp (β * x i) * (S ^ 2)⁻¹ * ∑ t, β * Real.exp (β * x t) * v t := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  rw [e2]
  field_simp
  ring


private theorem sfF_ge_max [Nonempty ι] {β : ℝ} (hβ : 0 < β) (x : ι → ℝ) :
    (⨆ t, x t) ≤ sfF β x := by
  obtain ⟨t0, ht0⟩ := exists_eq_ciSup_of_finite (f := x)
  rw [← ht0, sfF, le_div_iff₀ hβ]
  have h1 : Real.exp (β * x t0) ≤ sfS β x :=
    Finset.single_le_sum (f := fun t => Real.exp (β * x t)) (fun t _ => (Real.exp_pos _).le)
      (Finset.mem_univ t0)
  have h2 := Real.log_le_log (Real.exp_pos _) h1
  rw [Real.log_exp] at h2
  linarith

private theorem sfF_le_max [Nonempty ι] {β : ℝ} (hβ : 0 < β) (x : ι → ℝ) :
    sfF β x ≤ (⨆ t, x t) + Real.log (Fintype.card ι) / β := by
  set M := ⨆ t, x t
  have hb : BddAbove (Set.range x) := (Set.finite_range _).bddAbove
  have h1 : sfS β x ≤ (Fintype.card ι : ℝ) * Real.exp (β * M) := by
    have : sfS β x ≤ ∑ _t : ι, Real.exp (β * M) :=
      Finset.sum_le_sum fun t _ => Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_left (le_ciSup hb t) hβ.le)
    simpa using this
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h2 := Real.log_le_log (sfS_pos β x) h1
  rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp] at h2
  rw [sfF, div_le_iff₀ hβ, add_mul, div_mul_cancel₀ _ hβ.ne']
  linarith

private theorem abs_iSup_le_sum [Nonempty ι] (x : ι → ℝ) : |⨆ t, x t| ≤ ∑ t, |x t| := by
  obtain ⟨t0, ht0⟩ := exists_eq_ciSup_of_finite (f := x)
  rw [← ht0]
  exact Finset.single_le_sum (f := fun t => |x t|) (fun t _ => abs_nonneg _) (Finset.mem_univ t0)

private theorem abs_sfF_le [Nonempty ι] {β : ℝ} (hβ : 0 < β) (x : ι → ℝ) :
    |sfF β x| ≤ ∑ t, |x t| + Real.log (Fintype.card ι) / β := by
  have h1 := sfF_ge_max hβ x
  have h2 := sfF_le_max hβ x
  have h3 := abs_iSup_le_sum x
  have hc : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h4 : 0 ≤ Real.log (Fintype.card ι) / β := div_nonneg (Real.log_nonneg hc) hβ.le
  rw [abs_le] at h3 ⊢
  constructor <;> linarith [h3.1, h3.2]

end Softmax


section Core

private theorem sf_quad_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ)
    (hs : ∑ i, p i = 1)
    (hp : ∀ i, 0 ≤ p i) (Δ : ι → ι → ℝ) (h : ∀ i j, 0 ≤ Δ i i + Δ j j - Δ i j - Δ j i) :
    0 ≤ ∑ i, ∑ j, Δ i j * ((if i = j then p i else 0) - p i * p j) := by
  have e1 : ∀ i, ∑ j, Δ i j * ((if i = j then p i else 0) - p i * p j)
      = ∑ j, p i * p j * (Δ i i - Δ i j) := by
    intro i
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    have : ∑ j, p i * p j * Δ i i = Δ i i * p i := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, hs]; ring
    rw [this]
    congr 1
    refine Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e1]
  have e2 : ∑ i, ∑ j, p i * p j * (Δ i i - Δ i j) = ∑ i, ∑ j, p i * p j * (Δ j j - Δ j i) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h3 : 0 ≤ ∑ i, ∑ j, p i * p j * (Δ i i + Δ j j - Δ i j - Δ j i) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hp i) (hp j)) (h i j)
  have e3 : ∑ i, ∑ j, p i * p j * (Δ i i + Δ j j - Δ i j - Δ j i)
      = ∑ i, ∑ j, p i * p j * (Δ i i - Δ i j) + ∑ i, ∑ j, p i * p j * (Δ j j - Δ j i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [e3, ← e2] at h3
  linarith

private theorem sfF_continuous {ι : Type*} [Fintype ι] [Nonempty ι] {β : ℝ} (hβ : β ≠ 0) :
    Continuous (sfF (ι := ι) β) :=
  continuous_iff_continuousAt.2 fun x => (sfF_hasFDerivAt β hβ x).continuousAt

private theorem sfp_continuous {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] (β : ℝ)
    (i : ι) :
    Continuous (sfp (ι := ι) β i) :=
  continuous_iff_continuousAt.2 fun x => (sfp_hasFDerivAt β i x).continuousAt

private theorem sfH_continuous {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] (β : ℝ)
    (i j : ι) :
    Continuous (sfH (ι := ι) β i j) := by
  unfold sfH
  by_cases h : i = j
  · simp only [h, if_true]
    exact continuous_const.mul ((sfp_continuous β j).sub
      ((sfp_continuous β j).mul (sfp_continuous β j)))
  · simp only [h, if_false]
    exact continuous_const.mul (continuous_const.sub
      ((sfp_continuous β i).mul (sfp_continuous β j)))

private theorem sfH_abs_le {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] {β : ℝ} (hβ : 0 < β)
    (i j : ι) (x : ι → ℝ) : |sfH β i j x| ≤ 1 + 2 * β := by
  unfold sfH
  have h1 := sfp_nonneg β i x
  have h2 := sfp_le_one β i x
  have h3 := sfp_nonneg β j x
  have h4 := sfp_le_one β j x
  have h5 : 0 ≤ sfp β i x * sfp β j x := mul_nonneg h1 h3
  have h6 : sfp β i x * sfp β j x ≤ 1 := mul_le_one₀ h2 h3 h4
  rw [abs_mul, abs_of_pos hβ]
  have : |(if i = j then sfp β i x else 0) - sfp β i x * sfp β j x| ≤ 2 := by
    rw [abs_le]
    split_ifs <;> constructor <;> linarith
  nlinarith

end Core



section Interp2

variable {ι Ω : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] [MeasurableSpace Ω]
  {P : Measure Ω}

private theorem sf_softmax_compare (X Y : ι → Ω → ℝ)
    (hXY : HasGaussianLaw (fun ω => (fun t => X t ω, fun t => Y t ω)) P)
    (hX0 : ∀ t, ∫ ω, X t ω ∂P = 0) (hY0 : ∀ t, ∫ ω, Y t ω ∂P = 0)
    (hcross : ∀ s t, ∫ ω, X s ω * Y t ω ∂P = 0)
    (hinc : ∀ s t, ∫ ω, (X s ω - X t ω) ^ 2 ∂P ≤ ∫ ω, (Y s ω - Y t ω) ^ 2 ∂P)
    {β : ℝ} (hβ : 0 < β) :
    ∫ ω, sfF β (fun t => X t ω) ∂P ≤ ∫ ω, sfF β (fun t => Y t ω) ∂P := by
  have hP := hXY.isProbabilityMeasure
  have hXm : ∀ t, MemLp (X t) 2 P := fun t => (hXY.fst.eval t).memLp_two
  have hYm : ∀ t, MemLp (Y t) 2 P := fun t => (hXY.snd.eval t).memLp_two
  have hXi : ∀ t, Integrable (X t) P := fun t => (hXm t).integrable one_le_two
  have hYi : ∀ t, Integrable (Y t) P := fun t => (hYm t).integrable one_le_two
  have hXae : ∀ t, AEMeasurable (X t) P := fun t => (hXm t).aestronglyMeasurable.aemeasurable
  have hYae : ∀ t, AEMeasurable (Y t) P := fun t => (hYm t).aestronglyMeasurable.aemeasurable
  set Z : ℝ → Ω → ι → ℝ := fun θ ω t => Real.cos θ * X t ω + Real.sin θ * Y t ω with hZ
  set D : ℝ → Ω → ι → ℝ := fun θ ω t => -Real.sin θ * X t ω + Real.cos θ * Y t ω with hD
  set B : Ω → ℝ := fun ω => ∑ t, (|X t ω| + |Y t ω|) with hBdef
  have hB : Integrable B P :=
    integrable_finsetSum _ fun t _ => (hXi t).abs.add (hYi t).abs
  have hZb : ∀ θ ω t, |Z θ ω t| ≤ |X t ω| + |Y t ω| := by
    intro θ ω t
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    gcongr
    · exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one θ))
    · exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one θ))
  have hDb : ∀ θ ω t, |D θ ω t| ≤ |X t ω| + |Y t ω| := by
    intro θ ω t
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_neg]
    gcongr
    · exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one θ))
    · exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one θ))
  have hZae : ∀ θ, AEMeasurable (Z θ) P := fun θ =>
    aemeasurable_pi_lambda _ fun t => ((hXae t).const_mul _).add ((hYae t).const_mul _)
  have hDae : ∀ θ t, AEMeasurable (fun ω => D θ ω t) P := fun θ t =>
    ((hXae t).const_mul _).add ((hYae t).const_mul _)
  set Lc := Real.log (Fintype.card ι) / β with hLc
  set Φ : ℝ → ℝ := fun θ => ∫ ω, sfF β (Z θ ω) ∂P with hΦ
  set F' : ℝ → Ω → ℝ := fun θ ω => ∑ i, sfp β i (Z θ ω) * D θ ω i with hF'
  have hderiv : ∀ θ0, HasDerivAt Φ (∫ ω, F' θ0 ω ∂P) θ0 := by
    intro θ0
    have hFm : ∀ θ, AEStronglyMeasurable (fun ω => sfF β (Z θ ω)) P := fun θ =>
      ((sfF_continuous hβ.ne').measurable.comp_aemeasurable (hZae θ)).aestronglyMeasurable
    have hFint : Integrable (fun ω => sfF β (Z θ0 ω)) P := by
      refine Integrable.mono' (hB.add (integrable_const Lc)) (hFm θ0)
        (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs]
      refine (abs_sfF_le hβ _).trans ?_
      simp only [Pi.add_apply, hBdef]
      gcongr with t
      exact hZb θ0 ω t
    have hF'm : AEStronglyMeasurable (F' θ0) P := by
      refine (Finset.aemeasurable_fun_sum _ fun i _ => ?_).aestronglyMeasurable
      exact ((sfp_continuous β i).measurable.comp_aemeasurable (hZae θ0)).mul (hDae θ0 i)
    have hbound : ∀ θ ω, ‖F' θ ω‖ ≤ B ω := by
      intro θ ω
      rw [Real.norm_eq_abs, hF', hBdef]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul, abs_of_nonneg (sfp_nonneg β i _)]
      calc sfp β i (Z θ ω) * |D θ ω i| ≤ 1 * |D θ ω i| :=
            mul_le_mul_of_nonneg_right (sfp_le_one β i _) (abs_nonneg _)
        _ ≤ |X i ω| + |Y i ω| := by rw [one_mul]; exact hDb θ ω i
    have hdiff : ∀ ω θ, HasDerivAt (fun θ => sfF β (Z θ ω)) (F' θ ω) θ := by
      intro ω θ
      have hZd : HasDerivAt (fun θ => Z θ ω) (D θ ω) θ := by
        rw [hasDerivAt_pi]
        intro t
        exact ((Real.hasDerivAt_cos θ).mul_const (X t ω)).add
          ((Real.hasDerivAt_sin θ).mul_const (Y t ω))
      have := (sfF_hasFDerivAt β hβ.ne' (Z θ ω)).comp_hasDerivAt θ hZd
      refine this.congr_deriv ?_
      simp [hF']
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P)
      (F := fun θ ω => sfF β (Z θ ω)) (F' := F') (x₀ := θ0) (bound := B) (s := Set.univ)
      Filter.univ_mem (Filter.Eventually.of_forall hFm) hFint hF'm
      (ae_of_all _ fun ω θ _ => hbound θ ω) hB (ae_of_all _ fun ω θ _ => hdiff ω θ)).2
  -- the increment condition in covariance form
  set Δ : ι → ι → ℝ := fun i j => ∫ ω, Y i ω * Y j ω ∂P - ∫ ω, X i ω * X j ω ∂P with hΔdef
  have hΔ : ∀ i j, 0 ≤ Δ i i + Δ j j - Δ i j - Δ j i := by
    intro i j
    have h1 := hinc i j
    rw [integral_sub_sq_eq X hXm i j, integral_sub_sq_eq Y hYm i j] at h1
    simp only [hΔdef]
    linarith
  have hHi : ∀ θ i j, Integrable (fun ω => sfH β i j (Z θ ω)) P := fun θ i j =>
    Integrable.mono' (integrable_const (1 + 2 * β))
      ((sfH_continuous β i j).measurable.comp_aemeasurable (hZae θ)).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact sfH_abs_le hβ i j _)
  have hnonneg : ∀ θ, 0 ≤ Real.sin θ * Real.cos θ → 0 ≤ ∫ ω, F' θ ω ∂P := by
    intro θ hsc
    have hUV : ∀ i, HasGaussianLaw (fun ω => (D θ ω i, fun j => Z θ ω j)) P := by
      intro i
      set L : (ι → ℝ) × (ι → ℝ) →L[ℝ] ℝ × (ι → ℝ) :=
        ((-Real.sin θ) • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).comp
            (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ))) +
          Real.cos θ • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).comp
            (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)))).prod
        (Real.cos θ • ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ) +
          Real.sin θ • ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)) with hL
      have := hXY.map_fun L
      have heq : (fun ω => (D θ ω i, fun j => Z θ ω j))
          = fun ω => L (fun t => X t ω, fun t => Y t ω) := by
        funext ω
        simp only [hL, hD, hZ]
        ext j <;> simp
      rw [heq]; exact this
    have hU0 : ∀ i, ∫ ω, D θ ω i ∂P = 0 := by
      intro i
      simp only [hD]
      rw [integral_add ((hXi i).const_mul _) ((hYi i).const_mul _), integral_const_mul,
        integral_const_mul, hX0, hY0]; ring
    have hIBP : ∀ i, ∫ ω, D θ ω i * sfp β i (Z θ ω) ∂P
        = ∑ j, (Real.sin θ * Real.cos θ * Δ i j) * ∫ ω, sfH β i j (Z θ ω) ∂P := by
      intro i
      have h := integral_mul_eq_sum_covariance_mul_integral (fun ω => D θ ω i)
        (fun j ω => Z θ ω j) (hUV i)
        (hU0 i) (sfp β i) (sfH β i) (fun x => sfp_hasFDerivAt β i x)
        (fun j => sfH_continuous β i j) (1 + 2 * β)
        (fun x => by
          rw [abs_of_nonneg (sfp_nonneg β i x)]
          linarith [sfp_le_one β i x])
        (fun j x => sfH_abs_le hβ i j x)
      refine h.trans (Finset.sum_congr rfl fun j _ => ?_)
      congr 1
      exact covariance_rotation_eq X Y hXY hX0 hY0 hcross θ i j
    have hDp : ∀ i, Integrable (fun ω => D θ ω i * sfp β i (Z θ ω)) P := by
      intro i
      refine Integrable.mono' (((hXi i).abs.add (hYi i).abs)) (((hDae θ i).mul
        ((sfp_continuous β i).measurable.comp_aemeasurable (hZae θ))).aestronglyMeasurable)
        (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sfp_nonneg β i _)]
      calc |D θ ω i| * sfp β i (Z θ ω) ≤ |D θ ω i| * 1 :=
            mul_le_mul_of_nonneg_left (sfp_le_one β i _) (abs_nonneg _)
        _ ≤ |X i ω| + |Y i ω| := by rw [mul_one]; exact hDb θ ω i
    have e1 : ∫ ω, F' θ ω ∂P = ∑ i, ∫ ω, D θ ω i * sfp β i (Z θ ω) ∂P := by
      simp only [hF']
      rw [integral_finsetSum _ (fun i _ => by simpa only [mul_comm] using hDp i)]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1; ext ω; ring
    have e2 : ∑ i, ∑ j, (Real.sin θ * Real.cos θ * Δ i j) * ∫ ω, sfH β i j (Z θ ω) ∂P
        = ∫ ω, ∑ i, ∑ j, (Real.sin θ * Real.cos θ * Δ i j) * sfH β i j (Z θ ω) ∂P := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
        (hHi θ i j).const_mul _)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ (fun j _ => (hHi θ i j).const_mul _)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul]
    rw [e1]
    simp_rw [hIBP]
    rw [e2]
    refine integral_nonneg fun ω => ?_
    have e3 : ∑ i, ∑ j, (Real.sin θ * Real.cos θ * Δ i j) * sfH β i j (Z θ ω)
        = (Real.sin θ * Real.cos θ * β) * ∑ i, ∑ j, Δ i j *
          ((if i = j then sfp β i (Z θ ω) else 0) - sfp β i (Z θ ω) * sfp β j (Z θ ω)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold sfH; ring
    rw [e3]
    exact mul_nonneg (mul_nonneg hsc hβ.le) (sf_quad_nonneg (fun i => sfp β i (Z θ ω))
      (sfp_sum β _) (fun i => sfp_nonneg β i _) Δ hΔ)
  -- monotonicity of Φ on [0, π/2]
  have hcont : Continuous Φ := continuous_iff_continuousAt.2 fun θ => (hderiv θ).continuousAt
  have hmono : MonotoneOn Φ (Set.Icc 0 (Real.pi / 2)) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (Real.pi / 2))
      hcont.continuousOn (fun θ _ => (hderiv θ).hasDerivWithinAt) (fun θ hθ => ?_)
    rw [interior_Icc] at hθ
    refine hnonneg θ (mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2,
      Real.pi_pos])) (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.le⟩))
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h := hmono ⟨le_refl 0, hpi⟩ ⟨hpi, le_refl _⟩ hpi
  have h0 : Φ 0 = ∫ ω, sfF β (fun t => X t ω) ∂P := by simp [hΦ, hZ]
  have h1 : Φ (Real.pi / 2) = ∫ ω, sfF β (fun t => Y t ω) ∂P := by simp [hΦ, hZ]
  rw [← h0, ← h1]; exact h

end Interp2


section Main

/-- **Sudakov–Fernique inequality.** Let `X` (on `(Ω, P)`) and `Y` (on `(Ω', Q)`) be centred
Gaussian processes indexed by a finite set with dominated increments
`𝔼 (Xₛ - Xₜ)² ≤ 𝔼 (Yₛ - Yₜ)²`. Then `𝔼 maxₜ Xₜ ≤ 𝔼 maxₜ Yₜ`.
Source: Sudakov 1971, Fernique 1975; Vershynin 2018, Thm 7.2.11. Atlas: `sudakov-fernique`.
Ported from Prove2me solution `GaussianMatrix.sudakov_fernique`. -/
theorem sudakov_fernique_inequality {ι Ω Ω' : Type*} [Fintype ι] [MeasurableSpace Ω]
    [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} (X : ι → Ω → ℝ) (Y : ι → Ω' → ℝ)
    (hX : HasGaussianLaw (fun ω t => X t ω) P) (hY : HasGaussianLaw (fun ω t => Y t ω) Q)
    (hX0 : ∀ t, ∫ ω, X t ω ∂P = 0) (hY0 : ∀ t, ∫ ω, Y t ω ∂Q = 0)
    (hinc : ∀ s t, ∫ ω, (X s ω - X t ω) ^ 2 ∂P ≤ ∫ ω, (Y s ω - Y t ω) ^ 2 ∂Q) :
    ∫ ω, (⨆ t, X t ω) ∂P ≤ ∫ ω, (⨆ t, Y t ω) ∂Q := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  classical
  have hP := hX.isProbabilityMeasure
  have hQ := hY.isProbabilityMeasure
  set μX := P.map (fun ω t => X t ω) with hμX
  set μY := Q.map (fun ω t => Y t ω) with hμY
  have : IsGaussian μX := hX.isGaussian_map
  have : IsGaussian μY := hY.isGaussian_map
  set μ := μX.prod μY with hμ
  have hlaw : HasGaussianLaw (fun p : (ι → ℝ) × (ι → ℝ) => (fun t => p.1 t, fun t => p.2 t)) μ :=
    IsGaussian.hasGaussianLaw_id
  have hfst : ∀ f : (ι → ℝ) → ℝ, Measurable f →
      ∫ p, f p.1 ∂μ = ∫ ω, f (fun t => X t ω) ∂P := by
    intro f hf
    have h1 : ∫ p, f p.1 ∂μ = ∫ x, f x ∂(μ.map Prod.fst) :=
      (integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable).symm
    rw [h1, hμ, Measure.map_fst_prod, measure_univ, one_smul, hμX,
      integral_map hX.aemeasurable hf.aestronglyMeasurable]
  have hsnd : ∀ f : (ι → ℝ) → ℝ, Measurable f →
      ∫ p, f p.2 ∂μ = ∫ ω, f (fun t => Y t ω) ∂Q := by
    intro f hf
    have h1 : ∫ p, f p.2 ∂μ = ∫ x, f x ∂(μ.map Prod.snd) :=
      (integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable).symm
    rw [h1, hμ, Measure.map_snd_prod, measure_univ, one_smul, hμY,
      integral_map hY.aemeasurable hf.aestronglyMeasurable]
  have hX0' : ∀ t, ∫ p, p.1 t ∂μ = 0 := fun t => by
    rw [hfst (fun x => x t) (measurable_pi_apply t)]; exact hX0 t
  have hY0' : ∀ t, ∫ p, p.2 t ∂μ = 0 := fun t => by
    rw [hsnd (fun x => x t) (measurable_pi_apply t)]; exact hY0 t
  have hcross : ∀ s t, ∫ p, p.1 s * p.2 t ∂μ = 0 := by
    intro s t
    rw [hμ, integral_prod_mul (fun x : ι → ℝ => x s) (fun y : ι → ℝ => y t)]
    have : ∫ x, x s ∂μX = 0 := by
      rw [hμX, integral_map hX.aemeasurable (measurable_pi_apply s).aestronglyMeasurable]
      exact hX0 s
    rw [this, zero_mul]
  have hinc' : ∀ s t, ∫ p, (p.1 s - p.1 t) ^ 2 ∂μ ≤ ∫ p, (p.2 s - p.2 t) ^ 2 ∂μ := by
    intro s t
    rw [hfst (fun x => (x s - x t) ^ 2) (by fun_prop),
      hsnd (fun x => (x s - x t) ^ 2) (by fun_prop)]
    exact hinc s t
  have hXi : ∀ t, Integrable (X t) P := fun t => (hX.eval t).integrable
  have hYi : ∀ t, Integrable (Y t) Q := fun t => (hY.eval t).integrable
  have hsup : Measurable (fun x : ι → ℝ => ⨆ t, x t) :=
    Measurable.iSup fun t => measurable_pi_apply t
  have hIX : Integrable (fun ω => ⨆ t, X t ω) P :=
    integrable_comp_of_abs_le_sum_abs X hXi _ hsup hX.aemeasurable 0
      (fun x => by rw [add_zero]; exact abs_iSup_le_sum x)
  have hIY : Integrable (fun ω => ⨆ t, Y t ω) Q :=
    integrable_comp_of_abs_le_sum_abs Y hYi _ hsup hY.aemeasurable 0
      (fun x => by rw [add_zero]; exact abs_iSup_le_sum x)
  have key : ∀ β : ℝ, 0 < β → ∫ ω, (⨆ t, X t ω) ∂P
      ≤ ∫ ω, (⨆ t, Y t ω) ∂Q + Real.log (Fintype.card ι) / β := by
    intro β hβ
    have hc := sf_softmax_compare (P := μ) (fun t p => p.1 t) (fun t p => p.2 t) hlaw hX0' hY0'
      hcross hinc' hβ
    rw [hfst (sfF β) (sfF_continuous hβ.ne').measurable,
      hsnd (sfF β) (sfF_continuous hβ.ne').measurable] at hc
    have hFX : Integrable (fun ω => sfF β (fun t => X t ω)) P :=
      integrable_comp_of_abs_le_sum_abs X hXi _ (sfF_continuous hβ.ne').measurable hX.aemeasurable _
        (abs_sfF_le hβ)
    have hFY : Integrable (fun ω => sfF β (fun t => Y t ω)) Q :=
      integrable_comp_of_abs_le_sum_abs Y hYi _ (sfF_continuous hβ.ne').measurable hY.aemeasurable _
        (abs_sfF_le hβ)
    have h1 : ∫ ω, (⨆ t, X t ω) ∂P ≤ ∫ ω, sfF β (fun t => X t ω) ∂P :=
      integral_mono hIX hFX fun ω => sfF_ge_max hβ _
    have h2 : ∫ ω, sfF β (fun t => Y t ω) ∂Q
        ≤ ∫ ω, ((⨆ t, Y t ω) + Real.log (Fintype.card ι) / β) ∂Q :=
      integral_mono hFY (hIY.add (integrable_const _)) fun ω => sfF_le_max hβ _
    rw [integral_add hIY (integrable_const _), integral_const, probReal_univ, one_smul] at h2
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set Lg := Real.log (Fintype.card ι)
  have hLg : 0 ≤ Lg := Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  have hβ : 0 < (Lg + 1) / ε := div_pos (by linarith) hε
  refine (key _ hβ).trans ?_
  gcongr
  rw [div_div_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith

end Main

end NLAlib
