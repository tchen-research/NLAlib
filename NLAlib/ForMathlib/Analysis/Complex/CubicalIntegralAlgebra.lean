import NLAlib.ForMathlib.Analysis.Complex.CubicalCauchy
import NLAlib.ForMathlib.MeasureTheory.CurveIntegralFubini

/-! # Finite contour algebra and compact-support interchange

Algebraic operations on scalar forms and interchange with a finite compactly
supported measure for an actual finite chain of native C1 paths.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Finset MeasureTheory
open scoped unitInterval
namespace Complex

/-- Actual contour integration depends only on the integrand values along
its active continuous edges. -/
theorem cubicalCurveIntegral_congr {Ω : Set ℂ} (Γ : Cubical.OneChain Ω)
    {g h : ℂ → ℂ} (he : ∀ γ ∈ Γ.support, ∀ r, g (γ r : ℂ) = h (γ r : ℂ)) :
    cubicalCurveIntegral g Γ = cubicalCurveIntegral h Γ := by
  unfold cubicalCurveIntegral
  simp only [Finsupp.linearCombination_apply, Finsupp.sum]
  apply sum_congr rfl
  intro γ hγ
  congr 1
  rw [curveIntegral_def, curveIntegral_def]
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r ∈ Icc (0 : ℝ) 1 := by simpa only [Set.uIcc_of_le zero_le_one] using hr
  simp only [curveIntegralFun_def, (cubicalPath γ).extend_apply hr']
  rw [show g ((cubicalPath γ) ⟨r, hr'⟩) = h ((cubicalPath γ) ⟨r, hr'⟩) from he γ hγ ⟨r, hr'⟩]

/-- Scalar multiplication of the integrand commutes with actual finite
contour integration, even without a regularity assumption. -/
theorem cubicalCurveIntegral_const_mul {Ω : Set ℂ}
    (Γ : Cubical.OneChain Ω) (c : ℂ) (g : ℂ → ℂ) :
    cubicalCurveIntegral (fun z => c * g z) Γ = c * cubicalCurveIntegral g Γ := by
  have hpath (γ : C(I, Ω)) :
      curveIntegral (fun z => (c * g z) • ContinuousLinearMap.id ℂ ℂ) (cubicalPath γ) =
        c * curveIntegral (fun z => g z • ContinuousLinearMap.id ℂ ℂ) (cubicalPath γ) := by
    have he : (fun z => (c * g z) • ContinuousLinearMap.id ℂ ℂ) =
        fun z => c • (g z • ContinuousLinearMap.id ℂ ℂ) := by
      funext z
      exact mul_smul c (g z) (ContinuousLinearMap.id ℂ ℂ)
    rw [he, curveIntegral_fun_smul]
    rfl
  unfold cubicalCurveIntegral
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, hpath, mul_sum]
  apply sum_congr rfl
  intro γ _
  simp only [zsmul_eq_mul]
  ring

/-- Subtraction of scalar integrands commutes with actual finite contour
integration whenever the two forms are integrable on every active edge. -/
theorem cubicalCurveIntegral_sub {Ω : Set ℂ} (Γ : Cubical.OneChain Ω)
    (g h : ℂ → ℂ)
    (hg : ∀ γ ∈ Γ.support, CurveIntegrable
      (fun z => g z • ContinuousLinearMap.id ℂ ℂ) (cubicalPath γ))
    (hh : ∀ γ ∈ Γ.support, CurveIntegrable
      (fun z => h z • ContinuousLinearMap.id ℂ ℂ) (cubicalPath γ)) :
    cubicalCurveIntegral (fun z => g z - h z) Γ =
      cubicalCurveIntegral g Γ - cubicalCurveIntegral h Γ := by
  unfold cubicalCurveIntegral
  simp only [Finsupp.linearCombination_apply, Finsupp.sum]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro γ hγ
  have he : (fun z => (g z - h z) • ContinuousLinearMap.id ℂ ℂ) =
      fun z => g z • ContinuousLinearMap.id ℂ ℂ - h z • ContinuousLinearMap.id ℂ ℂ := by
    funext z
    exact sub_smul (g z) (h z) (ContinuousLinearMap.id ℂ ℂ)
  rw [he, curveIntegral_fun_sub (hg γ hγ) (hh γ hγ)]
  exact smul_sub (Γ γ) _ _

/-- Finite sums of integrable scalar forms commute with actual finite
contour integration. -/
theorem cubicalCurveIntegral_sum {Ω : Set ℂ} {ι : Type*} [Fintype ι]
    (Γ : Cubical.OneChain Ω) (g : ι → ℂ → ℂ)
    (hg : ∀ γ ∈ Γ.support, ∀ i, CurveIntegrable
      (fun z => g i z • ContinuousLinearMap.id ℂ ℂ) (cubicalPath γ)) :
    cubicalCurveIntegral (fun z => ∑ i, g i z) Γ = ∑ i, cubicalCurveIntegral (g i) Γ := by
  have hpath (γ : C(I, Ω)) (hγ : γ ∈ Γ.support) :
      curveIntegral (fun z => (∑ i, g i z) • ContinuousLinearMap.id ℂ ℂ) (cubicalPath γ) =
        ∑ i, curveIntegral (fun z => g i z • ContinuousLinearMap.id ℂ ℂ) (cubicalPath γ) := by
    have he : curveIntegralFun
        (fun z => (∑ i, g i z) • ContinuousLinearMap.id ℂ ℂ) (cubicalPath γ) =
        fun r => ∑ i, curveIntegralFun
          (fun z => g i z • ContinuousLinearMap.id ℂ ℂ) (cubicalPath γ) r := by
      funext r
      simp only [curveIntegralFun_def, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, sum_mul]
    simp only [curveIntegral_def]
    rw [he, intervalIntegral.integral_finsetSum (fun i _ => hg γ hγ i)]
  unfold cubicalCurveIntegral
  simp only [Finsupp.linearCombination_apply, Finsupp.sum]
  calc
    _ = ∑ γ ∈ Γ.support, ∑ i, Γ γ • curveIntegral
        (fun z => g i z • ContinuousLinearMap.id ℂ ℂ) (cubicalPath γ) := by
      apply sum_congr rfl
      intro γ hγ
      rw [hpath γ hγ, smul_sum]
    _ = _ := sum_comm

/-- The actual Cauchy-kernel cycle integral is integrable against the finite
measure's compact support. Every active edge is disjoint from that support. -/
theorem integrable_cubicalCurveIntegral_div_sub {Ω : Set ℂ}
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) (Γ : Cubical.OneChain Ω)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    (hoff : ∀ γ ∈ Γ.support, ∀ r, ∀ x ∈ Icc a b, (γ r : ℂ) ≠ (x : ℂ))
    {f : ℂ → ℂ} (hf : ContinuousOn f Ω) :
    Integrable (fun x : ℝ => cubicalCurveIntegral (fun z => f z / (z - (x : ℂ))) Γ) μ := by
  unfold cubicalCurveIntegral
  simp only [Finsupp.linearCombination_apply, Finsupp.sum]
  apply integrable_finsetSum
  intro γ hγ
  apply Integrable.smul
  apply integrable_curveIntegral_div_sub_of_contDiffOn hs (cubicalPath γ) (hΓ γ hγ)
  · intro t ht x hx
    rw [(cubicalPath γ).extend_apply ht]
    exact hoff γ hγ ⟨t, ht⟩ x hx
  · exact hf.mono (by rintro z ⟨r, rfl⟩; exact (γ r).property)

/-- Compact-support Fubini for an actual finite C1 contour cycle. Joint
integrability is established separately on each active edge. -/
theorem integral_cubicalCurveIntegral_div_sub {Ω : Set ℂ}
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) (Γ : Cubical.OneChain Ω)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    (hoff : ∀ γ ∈ Γ.support, ∀ r, ∀ x ∈ Icc a b, (γ r : ℂ) ≠ (x : ℂ))
    {f : ℂ → ℂ} (hf : ContinuousOn f Ω) :
    (∫ x : ℝ, cubicalCurveIntegral (fun z => f z / (z - (x : ℂ))) Γ ∂μ) =
      cubicalCurveIntegral (fun z => f z * (∫ x : ℝ, (z - (x : ℂ))⁻¹ ∂μ)) Γ := by
  have hInt (γ : C(I, Ω)) (hγ : γ ∈ Γ.support) :=
    integrable_curveIntegral_div_sub_of_contDiffOn hs (cubicalPath γ) (hΓ γ hγ)
      (fun t ht x hx => by rw [(cubicalPath γ).extend_apply ht]; exact hoff γ hγ ⟨t, ht⟩ x hx)
      (hf.mono (by rintro z ⟨r, rfl⟩; exact (γ r).property))
  unfold cubicalCurveIntegral
  simp only [Finsupp.linearCombination_apply, Finsupp.sum]
  rw [integral_finsetSum (f := fun (γ : C(I, Ω)) (x : ℝ) => Γ γ • curveIntegral
    (fun z => (f z / (z - (x : ℂ))) • ContinuousLinearMap.id ℂ ℂ) (cubicalPath γ)) _
    (fun γ hγ => (hInt γ hγ).smul (Γ γ))]
  apply sum_congr rfl
  intro γ hγ
  rw [(hInt γ hγ).integral_smul]
  rw [(curveIntegrable_and_integral_curveIntegral_div_sub hs (cubicalPath γ) (hΓ γ hγ)
    (fun t ht x hx => by rw [(cubicalPath γ).extend_apply ht]; exact hoff γ hγ ⟨t, ht⟩ x hx)
    (hf.mono (by rintro z ⟨r, rfl⟩; exact (γ r).property))).2]

end Complex
