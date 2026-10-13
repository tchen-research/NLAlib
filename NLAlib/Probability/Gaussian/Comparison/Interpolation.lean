import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import NLAlib.Probability.Gaussian.Calculus.IntegrationByParts
/-!
# Gaussian interpolation: second-moment bookkeeping

Small facts shared by the interpolation proofs of the Gaussian comparison inequalities
(`NLAlib.Probability.Gaussian.Comparison.Slepian`, `SudakovFernique`, `GordonMinimax`). Along the path
`Z(θ) = cos θ X + sin θ Y` between two independent centred Gaussian vectors, the derivative
process is `Z'(θ) = -sin θ X + cos θ Y`, and

* `covariance_rotation_eq`: `Cov(Z'(θ)ᵢ, Z(θ)ⱼ) = sin θ cos θ (𝔼 YᵢYⱼ - 𝔼 XᵢXⱼ)`;
* `integral_sub_sq_eq`: `𝔼 (Xᵢ - Xⱼ)² = 𝔼 XᵢXᵢ + 𝔼 XⱼXⱼ - 𝔼 XᵢXⱼ - 𝔼 XⱼXᵢ`;
* `integral_le_integral_of_covariance_hessian_nonneg`: the interpolation principle itself: for a
  `C²` test function `F` with bounded gradient and Hessian `H`, `𝔼 F(X) ≤ 𝔼 F(Y)` whenever
  `∑ᵢⱼ (𝔼 YᵢYⱼ - 𝔼 XᵢXⱼ) Hᵢⱼ(x) ≥ 0` for all `x` (Kahane 1986; Vershynin 2018, §7.2). Slepian,
  Sudakov–Fernique and Gordon all apply it to their smooth surrogate of the maximum.

The integrability criterion `integrable_comp_of_abs_le_sum_abs` (`g(X)` is integrable when
`|g x| ≤ ∑ₜ |xₜ| + K`) is in `NLAlib.ForMathlib.MeasureTheory.Integral`.

Gaussian integration by parts itself is `NLAlib.integral_mul_eq_sum_covariance_mul_integral`
(`NLAlib.Probability.Gaussian.Calculus.IntegrationByParts`).

Atlas: helpers of `slepian`, `sudakov-fernique`, `gordon-minimax`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace NLAlib

section Interp

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω}

/-- Covariance of the derivative process `Z'(θ) = -sin θ X + cos θ Y` with the interpolated
process `Z(θ) = cos θ X + sin θ Y`, for jointly Gaussian centred `X, Y` with vanishing cross
moments: `Cov(Z'(θ)ᵢ, Z(θ)ⱼ) = sin θ cos θ (𝔼 YᵢYⱼ - 𝔼 XᵢXⱼ)`. Standard step of the
interpolation proofs (Vershynin 2018, proof of Thm 7.2.1). Atlas: helper of `slepian`,
`sudakov-fernique`, `gordon-minimax`. -/
theorem covariance_rotation_eq (X Y : ι → Ω → ℝ)
    (hXY : HasGaussianLaw (fun ω => (fun t => X t ω, fun t => Y t ω)) P)
    (hX0 : ∀ t, ∫ ω, X t ω ∂P = 0) (hY0 : ∀ t, ∫ ω, Y t ω ∂P = 0)
    (hcross : ∀ s t, ∫ ω, X s ω * Y t ω ∂P = 0) (θ : ℝ) (i j : ι) :
    cov[fun ω => -Real.sin θ * X i ω + Real.cos θ * Y i ω,
      fun ω => Real.cos θ * X j ω + Real.sin θ * Y j ω; P]
      = Real.sin θ * Real.cos θ *
        (∫ ω, Y i ω * Y j ω ∂P - ∫ ω, X i ω * X j ω ∂P) := by
  have hP := hXY.isProbabilityMeasure
  have hXm : ∀ t, MemLp (X t) 2 P := fun t => (hXY.fst.eval t).memLp_two
  have hYm : ∀ t, MemLp (Y t) 2 P := fun t => (hXY.snd.eval t).memLp_two
  set s := Real.sin θ
  set c := Real.cos θ
  have hD : MemLp (fun ω => -s * X i ω + c * Y i ω) 2 P :=
    ((hXm i).const_mul _).add ((hYm i).const_mul _)
  have hZ : MemLp (fun ω => c * X j ω + s * Y j ω) 2 P :=
    ((hXm j).const_mul _).add ((hYm j).const_mul _)
  rw [covariance_eq_sub hD hZ]
  have hint : ∀ t, Integrable (X t) P := fun t => (hXm t).integrable one_le_two
  have hintY : ∀ t, Integrable (Y t) P := fun t => (hYm t).integrable one_le_two
  have hD0 : ∫ ω, -s * X i ω + c * Y i ω ∂P = 0 := by
    rw [integral_add ((hint i).const_mul _) ((hintY i).const_mul _), integral_const_mul,
      integral_const_mul, hX0, hY0]; ring
  rw [hD0, zero_mul, sub_zero]
  simp only [Pi.mul_apply]
  have e : (fun ω => (-s * X i ω + c * Y i ω) * (c * X j ω + s * Y j ω))
      = fun ω => (-s * c) * (X i ω * X j ω) + (-s ^ 2) * (X i ω * Y j ω)
        + c ^ 2 * (X j ω * Y i ω) + (c * s) * (Y i ω * Y j ω) := by
    funext ω; ring
  have i1 : Integrable (fun ω => X i ω * X j ω) P := (hXm i).integrable_mul (hXm j)
  have i2 : Integrable (fun ω => X i ω * Y j ω) P := (hXm i).integrable_mul (hYm j)
  have i3 : Integrable (fun ω => X j ω * Y i ω) P := (hXm j).integrable_mul (hYm i)
  have i4 : Integrable (fun ω => Y i ω * Y j ω) P := (hYm i).integrable_mul (hYm j)
  rw [e, integral_add (((i1.const_mul _).fun_add (i2.const_mul _)).fun_add (i3.const_mul _))
    (i4.const_mul _), integral_add ((i1.const_mul _).fun_add (i2.const_mul _)) (i3.const_mul _),
    integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, hcross, hcross]
  ring

omit [Fintype ι] in
/-- Expansion of the squared increment: `𝔼 (Xᵢ - Xⱼ)² = 𝔼 XᵢXᵢ + 𝔼 XⱼXⱼ - 𝔼 XᵢXⱼ - 𝔼 XⱼXᵢ` for
square-integrable `X`. Atlas: helper of `slepian`, `sudakov-fernique`, `gordon-minimax`. -/
theorem integral_sub_sq_eq (X : ι → Ω → ℝ) (hXm : ∀ t, MemLp (X t) 2 P) (i j : ι) :
    ∫ ω, (X i ω - X j ω) ^ 2 ∂P = ∫ ω, X i ω * X i ω ∂P + ∫ ω, X j ω * X j ω ∂P
      - ∫ ω, X i ω * X j ω ∂P - ∫ ω, X j ω * X i ω ∂P := by
  have i1 : Integrable (fun ω => X i ω * X i ω) P := (hXm i).integrable_mul (hXm i)
  have i2 : Integrable (fun ω => X j ω * X j ω) P := (hXm j).integrable_mul (hXm j)
  have i3 : Integrable (fun ω => X i ω * X j ω) P := (hXm i).integrable_mul (hXm j)
  have i4 : Integrable (fun ω => X j ω * X i ω) P := (hXm j).integrable_mul (hXm i)
  have e : (fun ω => (X i ω - X j ω) ^ 2) = fun ω => X i ω * X i ω + X j ω * X j ω
      - X i ω * X j ω - X j ω * X i ω := by funext ω; ring
  rw [e, integral_sub ((i1.fun_add i2).sub' i3) i4, integral_sub (i1.fun_add i2) i3,
    integral_add i1 i2]

end Interp

section GenInterp

/-- **Gaussian interpolation** for a general smooth test function. Let `X, Y` be jointly Gaussian
centred vectors on one probability space with vanishing cross moments `𝔼 XₛYₜ = 0`, and let
`F : ℝ^ι → ℝ` have gradient `g` and Hessian `H`, with `g, H` bounded, `H` continuous and
`|F x| ≤ ∑ₜ |xₜ| + K`. If `∑ᵢⱼ (𝔼 YᵢYⱼ - 𝔼 XᵢXⱼ) Hᵢⱼ(x) ≥ 0` for all `x`, then
`𝔼 F(X) ≤ 𝔼 F(Y)`. Source: Kahane 1986; Vershynin 2018, §7.2 (proof of Thm 7.2.1). Atlas: helper
of `gordon-minimax`.
atlas: gordon-minimax -/
theorem integral_le_integral_of_covariance_hessian_nonneg {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] {P : Measure Ω}
    (X Y : ι → Ω → ℝ)
    (hXY : HasGaussianLaw (fun ω => (fun t => X t ω, fun t => Y t ω)) P)
    (hX0 : ∀ t, ∫ ω, X t ω ∂P = 0) (hY0 : ∀ t, ∫ ω, Y t ω ∂P = 0)
    (hcross : ∀ s t, ∫ ω, X s ω * Y t ω ∂P = 0)
    (F : (ι → ℝ) → ℝ) (g : ι → (ι → ℝ) → ℝ) (H : ι → ι → (ι → ℝ) → ℝ)
    (hF : ∀ x, HasFDerivAt F
      (∑ i, g i x • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i) x)
    (hg : ∀ i x, HasFDerivAt (g i)
      (∑ j, H i j x • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j) x)
    (hHc : ∀ i j, Continuous (H i j))
    (C : ℝ) (hgb : ∀ i x, |g i x| ≤ C) (hHb : ∀ i j x, |H i j x| ≤ C)
    (K : ℝ) (hFb : ∀ x, |F x| ≤ ∑ t, |x t| + K)
    (hpos : ∀ x, 0 ≤ ∑ i, ∑ j,
      (∫ ω, Y i ω * Y j ω ∂P - ∫ ω, X i ω * X j ω ∂P) * H i j x) :
    ∫ ω, F (fun t => X t ω) ∂P ≤ ∫ ω, F (fun t => Y t ω) ∂P := by
  have hP := hXY.isProbabilityMeasure
  have hXm : ∀ t, MemLp (X t) 2 P := fun t => (hXY.fst.eval t).memLp_two
  have hYm : ∀ t, MemLp (Y t) 2 P := fun t => (hXY.snd.eval t).memLp_two
  have hXi : ∀ t, Integrable (X t) P := fun t => (hXm t).integrable one_le_two
  have hYi : ∀ t, Integrable (Y t) P := fun t => (hYm t).integrable one_le_two
  have hXae : ∀ t, AEMeasurable (X t) P := fun t => (hXm t).aestronglyMeasurable.aemeasurable
  have hYae : ∀ t, AEMeasurable (Y t) P := fun t => (hYm t).aestronglyMeasurable.aemeasurable
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x => (hF x).continuousAt
  have hgc : ∀ i, Continuous (g i) := fun i =>
    continuous_iff_continuousAt.2 fun x => (hg i x).continuousAt
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
  set Φ : ℝ → ℝ := fun θ => ∫ ω, F (Z θ ω) ∂P with hΦ
  set F' : ℝ → Ω → ℝ := fun θ ω => ∑ i, g i (Z θ ω) * D θ ω i with hF'
  have hgD : ∀ θ ω i, |g i (Z θ ω) * D θ ω i| ≤ C * (|X i ω| + |Y i ω|) := by
    intro θ ω i
    rw [abs_mul]
    have hC : 0 ≤ C := (abs_nonneg _).trans (hgb i (Z θ ω))
    exact mul_le_mul (hgb i _) (hDb θ ω i) (abs_nonneg _) hC
  have hderiv : ∀ θ0, HasDerivAt Φ (∫ ω, F' θ0 ω ∂P) θ0 := by
    intro θ0
    have hFm : ∀ θ, AEStronglyMeasurable (fun ω => F (Z θ ω)) P := fun θ =>
      (hFc.measurable.comp_aemeasurable (hZae θ)).aestronglyMeasurable
    have hFint : Integrable (fun ω => F (Z θ0 ω)) P := by
      refine Integrable.mono' (hB.add (integrable_const K)) (hFm θ0)
        (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs]
      refine (hFb _).trans ?_
      simp only [Pi.add_apply, hBdef]
      gcongr with t
      exact hZb θ0 ω t
    have hF'm : AEStronglyMeasurable (F' θ0) P := by
      refine (Finset.aemeasurable_fun_sum _ fun i _ => ?_).aestronglyMeasurable
      exact ((hgc i).measurable.comp_aemeasurable (hZae θ0)).mul (hDae θ0 i)
    have hbound : ∀ θ ω, ‖F' θ ω‖ ≤ C * B ω := by
      intro θ ω
      rw [Real.norm_eq_abs, hF', hBdef, Finset.mul_sum]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hgD θ ω i)
    have hdiff : ∀ ω θ, HasDerivAt (fun θ => F (Z θ ω)) (F' θ ω) θ := by
      intro ω θ
      have hZd : HasDerivAt (fun θ => Z θ ω) (D θ ω) θ := by
        rw [hasDerivAt_pi]
        intro t
        exact ((Real.hasDerivAt_cos θ).mul_const (X t ω)).add
          ((Real.hasDerivAt_sin θ).mul_const (Y t ω))
      have := (hF (Z θ ω)).comp_hasDerivAt θ hZd
      refine this.congr_deriv ?_
      simp [hF']
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P)
      (F := fun θ ω => F (Z θ ω)) (F' := F') (x₀ := θ0) (bound := fun ω => C * B ω)
      (s := Set.univ)
      Filter.univ_mem (Filter.Eventually.of_forall hFm) hFint hF'm
      (ae_of_all _ fun ω θ _ => hbound θ ω) (hB.const_mul C)
      (ae_of_all _ fun ω θ _ => hdiff ω θ)).2
  set Δ : ι → ι → ℝ := fun i j => ∫ ω, Y i ω * Y j ω ∂P - ∫ ω, X i ω * X j ω ∂P with hΔdef
  have hHi : ∀ θ i j, Integrable (fun ω => H i j (Z θ ω)) P := fun θ i j =>
    Integrable.mono' (integrable_const C)
      ((hHc i j).measurable.comp_aemeasurable (hZae θ)).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hHb i j _)
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
    have hIBP : ∀ i, ∫ ω, D θ ω i * g i (Z θ ω) ∂P
        = ∑ j, (Real.sin θ * Real.cos θ * Δ i j) * ∫ ω, H i j (Z θ ω) ∂P := by
      intro i
      have h := integral_mul_eq_sum_covariance_mul_integral (fun ω => D θ ω i)
        (fun j ω => Z θ ω j) (hUV i)
        (hU0 i) (g i) (H i) (fun x => hg i x) (fun j => hHc i j) C (hgb i) (hHb i)
      refine h.trans (Finset.sum_congr rfl fun j _ => ?_)
      congr 1
      exact covariance_rotation_eq X Y hXY hX0 hY0 hcross θ i j
    have hDp : ∀ i, Integrable (fun ω => D θ ω i * g i (Z θ ω)) P := by
      intro i
      refine Integrable.mono' (((hXi i).abs.add (hYi i).abs).const_mul C) (((hDae θ i).mul
        ((hgc i).measurable.comp_aemeasurable (hZae θ))).aestronglyMeasurable)
        (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, mul_comm]
      exact hgD θ ω i
    have e1 : ∫ ω, F' θ ω ∂P = ∑ i, ∫ ω, D θ ω i * g i (Z θ ω) ∂P := by
      simp only [hF']
      rw [integral_finsetSum _ (fun i _ => by simpa only [mul_comm] using hDp i)]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1; ext ω; ring
    have e2 : ∑ i, ∑ j, (Real.sin θ * Real.cos θ * Δ i j) * ∫ ω, H i j (Z θ ω) ∂P
        = ∫ ω, ∑ i, ∑ j, (Real.sin θ * Real.cos θ * Δ i j) * H i j (Z θ ω) ∂P := by
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
    have e3 : ∑ i, ∑ j, (Real.sin θ * Real.cos θ * Δ i j) * H i j (Z θ ω)
        = (Real.sin θ * Real.cos θ) * ∑ i, ∑ j, Δ i j * H i j (Z θ ω) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e3]
    exact mul_nonneg hsc (hpos _)
  have hcont : Continuous Φ := continuous_iff_continuousAt.2 fun θ => (hderiv θ).continuousAt
  have hmono : MonotoneOn Φ (Set.Icc 0 (Real.pi / 2)) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (Real.pi / 2))
      hcont.continuousOn (fun θ _ => (hderiv θ).hasDerivWithinAt) (fun θ hθ => ?_)
    rw [interior_Icc] at hθ
    refine hnonneg θ (mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2,
      Real.pi_pos])) (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.le⟩))
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h := hmono ⟨le_refl 0, hpi⟩ ⟨hpi, le_refl _⟩ hpi
  have h0 : Φ 0 = ∫ ω, F (fun t => X t ω) ∂P := by simp [hΦ, hZ]
  have h1 : Φ (Real.pi / 2) = ∫ ω, F (fun t => Y t ω) ∂P := by simp [hΦ, hZ]
  rw [← h0, ← h1]; exact h

end GenInterp

end NLAlib
