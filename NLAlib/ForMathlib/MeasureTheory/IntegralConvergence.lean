import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# One-sided integral convergence

Uniformly lower-bounded integrable functions with nonnegative pointwise limits
cannot have a negative limit of their integrals. The proof applies dominated
convergence only to negative parts, so the pointwise limit need not be integrable.
Source: the Fatou step in operator rederivations, Section 5;
atlas wishart-lambda-min-tail.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace NLAlib

/-- The limit of integrals of a uniformly lower-bounded sequence is nonnegative
when almost every point has a nonnegative pointwise limit. No integrability of
those pointwise limits is assumed. Source: the one-sided Fatou argument in
operator rederivations, Section 5; atlas wishart-lambda-min-tail (helper). -/
theorem nonneg_of_tendsto_integral_of_uniform_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (R : ℕ → Ω → ℝ) (hRi : ∀ n, Integrable (R n) μ)
    (C : ℝ) (hC : 0 ≤ C) (hRlower : ∀ n, ∀ᵐ x ∂μ, -C ≤ R n x)
    (hRlim : ∀ᵐ x ∂μ, ∃ L : ℝ, 0 ≤ L ∧
      Tendsto (fun n => R n x) atTop (𝓝 L))
    (L : ℝ) (hIlim : Tendsto (fun n => ∫ x, R n x ∂μ) atTop (𝓝 L)) :
    0 ≤ L := by
  let N : ℕ → Ω → ℝ := fun n x => min (R n x) 0
  have hNi (n : ℕ) : Integrable (N n) μ := by
    exact (hRi n).inf (integrable_const (0 : ℝ))
  have hNbound (n : ℕ) : ∀ᵐ x ∂μ, ‖N n x‖ ≤ C := by
    filter_upwards [hRlower n] with x hx
    rw [Real.norm_eq_abs, abs_of_nonpos (min_le_right (R n x) 0)]
    have hh : -C ≤ min (R n x) 0 := le_min hx (by linarith)
    linarith
  have hNlim : ∀ᵐ x ∂μ, Tendsto (fun n => N n x) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hRlim] with x hx
    obtain ⟨l, hl, hxl⟩ := hx
    simpa only [N, min_eq_right hl] using hxl.min (tendsto_const_nhds (x := (0 : ℝ)))
  have hINlim : Tendsto (fun n => ∫ x, N n x ∂μ) atTop (𝓝 (0 : ℝ)) := by
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
      (fun _ => C) (fun n => (hNi n).aestronglyMeasurable) (integrable_const C) hNbound hNlim
  apply le_of_tendsto_of_tendsto hINlim hIlim
  exact Eventually.of_forall fun n => integral_mono (hNi n) (hRi n)
    (fun x => min_le_left (R n x) 0)

/-- A shifted integration identity has a nonnegative weak limit when its second
derivative term has a uniform upper bound and a limiting upper bound by the shift.
The left-hand side uses ordinary domination; the right-hand side uses only the
one-sided negative-part argument. In particular its pointwise limit need not be
integrable. Source: operator rederivations, Section 5;
atlas wishart-lambda-min-tail (helper). -/
theorem integral_nonneg_of_shift_identity_limit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F A B C : ℕ → Ω → ℝ) (Y A' B' C' : Ω → ℝ)
    (ψ ψ' : ℝ → ℝ) (hψ : Continuous ψ) (hψ' : Continuous ψ')
    (b K P : ℝ) (hP : 0 ≤ P) (hψ0 : ∀ t, 0 ≤ ψ t) (hψP : ∀ t, ψ t ≤ P)
    (hLi : ∀ n, Integrable
      (fun x => ψ' (F n x) * A n x + (b - B n x) * ψ (F n x)) μ)
    (hRi : ∀ n, Integrable (fun x => (b - C n x) * ψ (F n x)) μ)
    (hidentity : ∀ n,
      (∫ x, ψ' (F n x) * A n x + (b - B n x) * ψ (F n x) ∂μ) =
      ∫ x, (b - C n x) * ψ (F n x) ∂μ)
    (hupper : ∀ n, ∀ᵐ x ∂μ, C n x ≤ K)
    (hF : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (Y x)))
    (hA : ∀ᵐ x ∂μ, Tendsto (fun n => A n x) atTop (𝓝 (A' x)))
    (hB : ∀ᵐ x ∂μ, Tendsto (fun n => B n x) atTop (𝓝 (B' x)))
    (hC : ∀ᵐ x ∂μ, Tendsto (fun n => C n x) atTop (𝓝 (C' x)))
    (hC' : ∀ᵐ x ∂μ, C' x ≤ b)
    (bound : Ω → ℝ) (hboundi : Integrable bound μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ,
      ‖ψ' (F n x) * A n x + (b - B n x) * ψ (F n x)‖ ≤ bound x) :
    0 ≤ ∫ x, ψ' (Y x) * A' x + (b - B' x) * ψ (Y x) ∂μ := by
  let L : ℕ → Ω → ℝ := fun n x =>
    ψ' (F n x) * A n x + (b - B n x) * ψ (F n x)
  let R : ℕ → Ω → ℝ := fun n x => (b - C n x) * ψ (F n x)
  have hLlim : ∀ᵐ x ∂μ, Tendsto (fun n => L n x) atTop
      (𝓝 (ψ' (Y x) * A' x + (b - B' x) * ψ (Y x))) := by
    filter_upwards [hF, hA, hB] with x hxF hxA hxB
    exact (((hψ'.continuousAt.tendsto.comp hxF).mul hxA).add
      ((tendsto_const_nhds.sub hxB).mul (hψ.continuousAt.tendsto.comp hxF)))
  have hILlim := tendsto_integral_of_dominated_convergence bound
    (fun n => (hLi n).aestronglyMeasurable) hboundi hbound hLlim
  have hRlim : ∀ᵐ x ∂μ, ∃ l : ℝ, 0 ≤ l ∧
      Tendsto (fun n => R n x) atTop (𝓝 l) := by
    filter_upwards [hF, hC, hC'] with x hxF hxC hxC'
    refine ⟨(b - C' x) * ψ (Y x), mul_nonneg (sub_nonneg.mpr hxC') (hψ0 _), ?_⟩
    exact (tendsto_const_nhds.sub hxC).mul (hψ.continuousAt.tendsto.comp hxF)
  let M : ℝ := (|b| + |K|) * P
  have hM : 0 ≤ M := mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hP
  have hRlower : ∀ n, ∀ᵐ x ∂μ, -M ≤ R n x := by
    intro n
    filter_upwards [hupper n] with x hx
    have hh : -(|b| + |K|) ≤ b - C n x := by
      linarith [neg_abs_le b, le_abs_self K]
    have hmul :
        -(|b| + |K|) * P ≤ (b - C n x) * ψ (F n x) :=
      (mul_le_mul_of_nonpos_left (hψP _) (by
        linarith [abs_nonneg b, abs_nonneg K])).trans
        (mul_le_mul_of_nonneg_right hh (hψ0 _))
    simpa only [M, R, neg_mul] using hmul
  apply nonneg_of_tendsto_integral_of_uniform_lower_bound μ R hRi M hM hRlower hRlim
  simpa only [L, hidentity] using hILlim

/-- Positive translations in the scalar test can be removed by dominated
convergence. This handles the second regularization limit after a fixed positive
Gram shift: the test sees the shifted minimum while the derivative aggregates
see the unshifted minimum. Source: operator rederivations, Section 5;
atlas wishart-lambda-min-tail (helper). -/
theorem integral_nonneg_of_positive_translates
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X A B : Ω → ℝ) (ψ ψ' : ℝ → ℝ) (hψ : Continuous ψ) (hψ' : Continuous ψ')
    (b : ℝ)
    (hmeas : ∀ ε : ℝ, 0 < ε → AEStronglyMeasurable
      (fun x => ψ' (X x + ε) * A x + (b - B x) * ψ (X x + ε)) μ)
    (bound : Ω → ℝ) (hboundi : Integrable bound μ)
    (hbound : ∀ ε : ℝ, 0 < ε → ∀ᵐ x ∂μ,
      ‖ψ' (X x + ε) * A x + (b - B x) * ψ (X x + ε)‖ ≤ bound x)
    (hweak : ∀ ε : ℝ, 0 < ε →
      0 ≤ ∫ x, ψ' (X x + ε) * A x + (b - B x) * ψ (X x + ε) ∂μ) :
    0 ≤ ∫ x, ψ' (X x) * A x + (b - B x) * ψ (X x) ∂μ := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : ∀ᵐ x ∂μ, Tendsto
      (fun n => ψ' (X x + ε n) * A x + (b - B x) * ψ (X x + ε n)) atTop
      (𝓝 (ψ' (X x) * A x + (b - B x) * ψ (X x))) := by
    filter_upwards with x
    have hx : Tendsto (fun n => X x + ε n) atTop (𝓝 (X x)) := by
      simpa only [add_zero] using tendsto_const_nhds.add hεlim
    exact ((hψ'.continuousAt.tendsto.comp hx).mul tendsto_const_nhds).add
      (tendsto_const_nhds.mul (hψ.continuousAt.tendsto.comp hx))
  have hi := tendsto_integral_of_dominated_convergence bound
    (fun n => hmeas (ε n) (hε n)) hboundi (fun n => hbound (ε n) (hε n)) hlim
  exact ge_of_tendsto hi (Eventually.of_forall fun n => hweak (ε n) (hε n))

end NLAlib
