import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.Complex.Exponential

/-!
# From Orlicz exponential moments to centered moment-generating bounds

A centered variable with `E exp((X/K)^2) ≤ 2` has a sub-Gaussian MGF with variance proxy
`9 K²`. A centered variable with `E exp(|X|/K) ≤ 2` has the local bound
`E exp(tX) ≤ exp(16 K² t²)` for `|t| ≤ 1/(2K)`.

The input bounds are nonnegative lower Lebesgue integrals. Their finiteness proves all
integrability needed below, so divergent Bochner integrals cannot satisfy the assumptions
through their default value zero. The constants are explicit and deliberately unoptimized.
Vershynin 2018, Propositions 2.5.2 and 2.7.1; atlas `subgaussian-def`, `bernstein-scalar`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NLAlib

/-- A global first-order exponential remainder bound. Used to recover the quadratic MGF
behavior of a centered variable from an Orlicz exponential moment.
Atlas `subgaussian-def`, `bernstein-scalar` (analytic helper). -/
theorem exp_le_one_add_add_sq_mul_exp_abs (x : ℝ) :
    Real.exp x ≤ 1 + x + x ^ 2 * Real.exp |x| := by
  have he : 1 ≤ Real.exp |x| := Real.one_le_exp (abs_nonneg x)
  by_cases hsmall : |x| ≤ 1
  · have hrem := Real.abs_exp_sub_one_sub_id_le hsmall
    have hupper : Real.exp x ≤ 1 + x + x ^ 2 := by
      linarith [(le_abs_self (Real.exp x - 1 - x)).trans hrem]
    have hmul : x ^ 2 ≤ x ^ 2 * Real.exp |x| := by
      simpa using mul_le_mul_of_nonneg_left he (sq_nonneg x)
    linarith
  · by_cases hx : 0 ≤ x
    · have hx1 : 1 ≤ x := by simpa [abs_of_nonneg hx] using (not_le.mp hsmall).le
      rw [abs_of_nonneg hx]
      have hsq : 1 ≤ x ^ 2 := by nlinarith
      have hmul : Real.exp x ≤ x ^ 2 * Real.exp x := by
        simpa using mul_le_mul_of_nonneg_right hsq (Real.exp_pos x).le
      linarith
    · have hx0 : x ≤ 0 := (not_le.mp hx).le
      have hx1 : x ≤ -1 := by
        have h := (not_le.mp hsmall).le
        rw [abs_of_nonpos hx0] at h
        linarith
      have hex : Real.exp x ≤ 1 := by simpa using Real.exp_le_exp.mpr hx0
      have hsq : -x ≤ x ^ 2 := by nlinarith
      have hmul : x ^ 2 ≤ x ^ 2 * Real.exp |x| := by
        simpa using mul_le_mul_of_nonneg_left he (sq_nonneg x)
      linarith

private theorem quadratic_remainder_le_exp_sq (u y : ℝ) :
    (u * y) ^ 2 * Real.exp |u * y| ≤
      2 * u ^ 2 * Real.exp (u ^ 2 / 2) * Real.exp (y ^ 2) := by
  have hYoung : |u * y| ≤ u ^ 2 / 2 + y ^ 2 / 2 := by
    rw [abs_mul]
    nlinarith [sq_abs u, sq_abs y, sq_nonneg (|u| - |y|)]
  have hy : y ^ 2 ≤ 2 * Real.exp (y ^ 2 / 2) := by
    nlinarith [Real.add_one_le_exp (y ^ 2 / 2)]
  have he : Real.exp |u * y| ≤ Real.exp (u ^ 2 / 2 + y ^ 2 / 2) :=
    Real.exp_le_exp.mpr hYoung
  calc
    (u * y) ^ 2 * Real.exp |u * y| = u ^ 2 * (y ^ 2 * Real.exp |u * y|) := by ring
    _ ≤ u ^ 2 * ((2 * Real.exp (y ^ 2 / 2)) *
        Real.exp (u ^ 2 / 2 + y ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hy he (Real.exp_pos _).le (by positivity)) (sq_nonneg u)
    _ = 2 * u ^ 2 * Real.exp (u ^ 2 / 2) * Real.exp (y ^ 2) := by
      rw [Real.exp_add]
      have hs : Real.exp (y ^ 2 / 2) * Real.exp (y ^ 2 / 2) = Real.exp (y ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        u ^ 2 * (2 * Real.exp (y ^ 2 / 2) *
            (Real.exp (u ^ 2 / 2) * Real.exp (y ^ 2 / 2))) =
          2 * u ^ 2 * Real.exp (u ^ 2 / 2) *
            (Real.exp (y ^ 2 / 2) * Real.exp (y ^ 2 / 2)) := by ring
        _ = _ := by rw [hs]

private theorem quadratic_remainder_le_exp_abs (u y : ℝ) (hu : |u| ≤ 1 / 2) :
    (u * y) ^ 2 * Real.exp |u * y| ≤ 8 * u ^ 2 * Real.exp |y| := by
  have hlin : |u * y| ≤ |y| / 2 := by
    rw [abs_mul]
    nlinarith [mul_le_mul_of_nonneg_right hu (abs_nonneg y)]
  have hy : y ^ 2 ≤ 8 * Real.exp (|y| / 2) := by
    have hp := Real.pow_div_factorial_le_exp (|y| / 2) (by positivity) 2
    norm_num at hp
    nlinarith [sq_abs y]
  have he : Real.exp |u * y| ≤ Real.exp (|y| / 2) := Real.exp_le_exp.mpr hlin
  calc
    (u * y) ^ 2 * Real.exp |u * y| = u ^ 2 * (y ^ 2 * Real.exp |u * y|) := by ring
    _ ≤ u ^ 2 * ((8 * Real.exp (|y| / 2)) * Real.exp (|y| / 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hy he (Real.exp_pos _).le (by positivity)) (sq_nonneg u)
    _ = 8 * u ^ 2 * Real.exp |y| := by
      have hs : Real.exp (|y| / 2) * Real.exp (|y| / 2) = Real.exp |y| := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        u ^ 2 * (8 * Real.exp (|y| / 2) * Real.exp (|y| / 2)) =
          8 * u ^ 2 * (Real.exp (|y| / 2) * Real.exp (|y| / 2)) := by ring
        _ = _ := by rw [hs]

private theorem integrable_and_integral_le_two_of_lintegral_le {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} {F : Ω → ℝ}
    (hF : AEMeasurable F μ) (hpos : ∀ ω, 0 ≤ F ω)
    (hbound : ∫⁻ ω, ENNReal.ofReal (F ω) ∂μ ≤ 2) :
    Integrable F μ ∧ (∫ ω, F ω ∂μ) ≤ 2 := by
  have hnonneg : 0 ≤ᵐ[μ] F := Filter.Eventually.of_forall hpos
  have hfi : Integrable F μ := ⟨hF.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal hnonneg).2 (hbound.trans_lt (by norm_num))⟩
  refine ⟨hfi, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 2)).1
  rw [ofReal_integral_eq_lintegral_ofReal hfi hnonneg]
  simpa using hbound

private theorem mgf_le_of_remainder_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X F : Ω → ℝ}
    (hX : AEMeasurable X μ) (hXi : Integrable X μ) (hmean : ∫ ω, X ω ∂μ = 0)
    (hFi : Integrable F μ) (hFb : ∫ ω, F ω ∂μ ≤ 2)
    (t c : ℝ) (hc : 0 ≤ c)
    (hrem : ∀ ω, Real.exp (t * X ω) ≤ 1 + t * X ω + c * F ω) :
    Integrable (fun ω => Real.exp (t * X ω)) μ ∧ mgf X μ t ≤ 1 + 2 * c := by
  have hright := ((integrable_const (1 : ℝ)).add (hXi.const_mul t)).add (hFi.const_mul c)
  have hexp : Integrable (fun ω => Real.exp (t * X ω)) μ :=
    hright.mono_nonneg (by fun_prop)
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)
      (Filter.Eventually.of_forall hrem)
  refine ⟨hexp, ?_⟩
  have hb := integral_mono hexp hright hrem
  simp only [Pi.add_apply] at hb
  rw [integral_add (f := fun ω => 1 + t * X ω) (g := fun ω => c * F ω)
      ((integrable_const (1 : ℝ)).add (hXi.const_mul t)) (hFi.const_mul c),
    integral_add (f := fun _ : Ω => (1 : ℝ)) (g := fun ω => t * X ω)
      (integrable_const (1 : ℝ)) (hXi.const_mul t),
    integral_const_mul, integral_const_mul, hmean] at hb
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    smul_eq_mul, mul_one,
    mul_zero, add_zero] at hb
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left hFb hc])

/-- **Orlicz square-exponential bound implies a centered sub-Gaussian MGF.** If `K>0`,
`EX=0` and the nonnegative expectation of `exp((X/K)²)` is at most two, then every
exponential tilt is integrable and `E exp(tX) ≤ exp(9K²t²/2)`, for all real `t`.
Vershynin 2018, Proposition 2.5.2; atlas `subgaussian-def` (Orlicz-to-MGF bridge). -/
theorem hasSubgaussianMGF_of_lintegral_exp_sq_le_two {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : AEMeasurable X μ) (K : ℝ) (hK : 0 < K)
    (hmean : ∫ ω, X ω ∂μ = 0)
    (hpsi : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / K) ^ 2)) ∂μ ≤ 2) :
    HasSubgaussianMGF X ⟨9 * K ^ 2, by positivity⟩ μ := by
  obtain ⟨hFi, hFb⟩ := integrable_and_integral_le_two_of_lintegral_le
    (F := fun ω => Real.exp ((X ω / K) ^ 2)) (by fun_prop)
    (fun _ => (Real.exp_pos _).le) hpsi
  have hXi : Integrable X μ := by
    apply (hFi.const_mul K).mono' hX.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs]
    have hy : |X ω / K| ≤ Real.exp ((X ω / K) ^ 2) := by
      have h1 : |X ω / K| ≤ 1 + (X ω / K) ^ 2 := by
        nlinarith [sq_abs (X ω / K), sq_nonneg (|X ω / K| - 1 / 2)]
      linarith [Real.add_one_le_exp ((X ω / K) ^ 2)]
    rw [abs_div, abs_of_pos hK] at hy
    simpa only [mul_comm] using (div_le_iff₀ hK).mp hy
  have hbound : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ ∧
      mgf X μ t ≤ Real.exp (9 * K ^ 2 * t ^ 2 / 2) := by
    intro t
    let u := t * K
    have hrem : ∀ ω, Real.exp (t * X ω) ≤
        1 + t * X ω + (2 * u ^ 2 * Real.exp (u ^ 2 / 2)) *
          Real.exp ((X ω / K) ^ 2) := by
      intro ω
      have hid : t * X ω = u * (X ω / K) := by dsimp [u]; field_simp
      have h1 := exp_le_one_add_add_sq_mul_exp_abs (t * X ω)
      have h2 := quadratic_remainder_le_exp_sq u (X ω / K)
      rw [← hid] at h2
      linarith
    obtain ⟨hexp, hb⟩ := mgf_le_of_remainder_bound hX hXi hmean hFi hFb t
      (2 * u ^ 2 * Real.exp (u ^ 2 / 2)) (by positivity) hrem
    refine ⟨hexp, hb.trans ?_⟩
    have he : 1 ≤ Real.exp (u ^ 2 / 2) := Real.one_le_exp (by positivity)
    have hex : 1 + 4 * u ^ 2 ≤ Real.exp (4 * u ^ 2) := by
      linarith [Real.add_one_le_exp (4 * u ^ 2)]
    calc
      1 + 2 * (2 * u ^ 2 * Real.exp (u ^ 2 / 2)) ≤
          Real.exp (u ^ 2 / 2) * (1 + 4 * u ^ 2) := by nlinarith
      _ ≤ Real.exp (u ^ 2 / 2) * Real.exp (4 * u ^ 2) :=
        mul_le_mul_of_nonneg_left hex (Real.exp_pos _).le
      _ = Real.exp (9 * K ^ 2 * t ^ 2 / 2) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [u]
        ring
  exact ⟨fun t => (hbound t).1, fun t => (hbound t).2⟩

/-- **Orlicz absolute-exponential bound implies a centered local MGF bound.** If `K>0`,
`EX=0` and the nonnegative expectation of `exp(|X|/K)` is at most two, then `X` and
every tilt in `|t|≤1/(2K)` are integrable, and `E exp(tX)≤exp(16K²t²)` there.
Vershynin 2018, Proposition 2.7.1; atlas `bernstein-scalar` (Orlicz-to-local-MGF bridge). -/
theorem integrable_and_local_mgf_le_of_lintegral_exp_abs_le_two {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : AEMeasurable X μ) (K : ℝ) (hK : 0 < K)
    (hmean : ∫ ω, X ω ∂μ = 0)
    (hpsi : ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / K)) ∂μ ≤ 2) :
    Integrable X μ ∧ ∀ t : ℝ, |t| ≤ 1 / (2 * K) →
      Integrable (fun ω => Real.exp (t * X ω)) μ ∧
        mgf X μ t ≤ Real.exp (16 * K ^ 2 * t ^ 2) := by
  obtain ⟨hFi, hFb⟩ := integrable_and_integral_le_two_of_lintegral_le
    (F := fun ω => Real.exp (|X ω| / K)) (by fun_prop)
    (fun _ => (Real.exp_pos _).le) hpsi
  have hXi : Integrable X μ := by
    apply (hFi.const_mul K).mono' hX.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs]
    have hy : |X ω| / K ≤ Real.exp (|X ω| / K) := by
      linarith [Real.add_one_le_exp (|X ω| / K)]
    simpa only [mul_comm] using (div_le_iff₀ hK).mp hy
  refine ⟨hXi, ?_⟩
  intro t ht
  let u := t * K
  have hu : |u| ≤ 1 / 2 := by
    have ht' := (le_div_iff₀ (by positivity : 0 < 2 * K)).mp ht
    dsimp [u]
    rw [abs_mul, abs_of_pos hK]
    nlinarith
  have hrem : ∀ ω, Real.exp (t * X ω) ≤
      1 + t * X ω + (8 * u ^ 2) * Real.exp (|X ω| / K) := by
    intro ω
    have hid : t * X ω = u * (X ω / K) := by dsimp [u]; field_simp
    have h1 := exp_le_one_add_add_sq_mul_exp_abs (t * X ω)
    have h2 := quadratic_remainder_le_exp_abs u (X ω / K) hu
    rw [abs_div, abs_of_pos hK] at h2
    rw [← hid] at h2
    linarith
  obtain ⟨hexp, hb⟩ := mgf_le_of_remainder_bound hX hXi hmean hFi hFb t
    (8 * u ^ 2) (by positivity) hrem
  refine ⟨hexp, hb.trans ?_⟩
  have hh := Real.add_one_le_exp (16 * u ^ 2)
  have heq : 16 * u ^ 2 = 16 * K ^ 2 * t ^ 2 := by dsimp [u]; ring
  rw [heq] at hh
  nlinarith

end NLAlib
