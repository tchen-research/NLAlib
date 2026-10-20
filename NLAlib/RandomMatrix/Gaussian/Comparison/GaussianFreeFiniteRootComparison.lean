import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteMomentPath
import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteMomentDerivativeBound
import NLAlib.ForMathlib.Analysis.RpowComparison

/-! # Actual finite-ensemble rooted Gaussian moment comparison -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix Kronecker
namespace NLAlib
variable {ι n d : Type*} [Fintype ι] [Fintype n] [Fintype d]
  [DecidableEq ι] [DecidableEq n] [DecidableEq d]
local notation "J" => GaussianFreeFiniteCoordinate ι n
local notation "E" => J → ℝ

open scoped Matrix.Norms.L2Operator in
/-- The actual finite-ensemble endpoint Gram moment roots differ by the source variance-times-covariance error, uniformly in ensemble size and the full deterministic mean. Continuity, strict positivity and the derivative bound are derived from the actual model; empty dimensions are handled separately.
Source: arXiv:2108.06312v2, Theorem 6.2 and Lemma 6.3.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem abs_integral_gaussianFreeFinite_resolventEvenMoment_rpow_sub_le
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) {p : ℕ} (hp : 0 < p) :
    let F := fun q : ℝ => ∫ x : E, resolventEvenMoment
      (gaussianFreeFiniteInterpolation A₀ A q x) ζ p ∂gaussianVector J
    |F 1 ^ (1 / ((2 * p : ℕ) : ℝ)) - F 0 ^ (1 / ((2 * p : ℕ) : ℝ))| ≤
      ((2 * p + 1) * (2 * p + 2) ^ 2 : ℕ) *
        (specNorm (coefficientVariance A) * specNorm (coefficientCovariance A)) *
        (|ζ.im|⁻¹) ^ 5 := by
  dsimp only
  let F := fun q : ℝ => ∫ x : E, resolventEvenMoment
    (gaussianFreeFiniteInterpolation A₀ A q x) ζ p ∂gaussianVector J
  let V : ℝ := specNorm (coefficientVariance A) * specNorm (coefficientCovariance A)
  let B : ℝ := ((2 * p + 1) * (2 * p + 2) ^ 2 : ℕ) * V * (|ζ.im|⁻¹) ^ 5
  have hV : 0 ≤ V := mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  change |F 1 ^ (1 / ((2 * p : ℕ) : ℝ)) - F 0 ^ (1 / ((2 * p : ℕ) : ℝ))| ≤ B
  cases isEmpty_or_nonempty (d × n) with
  | inl hdn =>
    have hFzero (q : ℝ) : F q = 0 := by
      dsimp only [F]
      simp [resolventEvenMoment, normalizedTrace]
    rw [hFzero, hFzero, sub_self, abs_zero]
    exact hB
  | inr hdn =>
    let : Nonempty d := hdn.map Prod.fst
    let : Nonempty n := hdn.map Prod.snd
    let s : ℝ := 1 / ((2 * p : ℕ) : ℝ)
    let C : ℝ := ((2 * p : ℕ) : ℝ) * B
    have hk : (0 : ℝ) < ((2 * p : ℕ) : ℝ) := by positivity
    have hs : 0 ≤ s := by dsimp only [s]; positivity
    have hα : (((2 * p - 1 : ℕ) : ℝ) / ((2 * p : ℕ) : ℝ)) = 1 - s := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * p)]
      dsimp only [s]
      push_cast
      field_simp [hk.ne']
    have hFc : Continuous F :=
      continuous_integral_gaussianFreeFinite_resolventEvenMoment A₀ hA₀ A hA ζ hζ hp
    have hFpos (q : ℝ) : 0 < F q :=
      integral_gaussianFreeFinite_resolventEvenMoment_pos A₀ hA₀ A hA q ζ hζ hp
    have hD (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
        HasDerivAt F (deriv F q) q ∧ |deriv F q| ≤ C * F q ^ (1 - s) := by
      obtain ⟨D, hd, hb⟩ := exists_hasDerivAt_integral_gaussianFreeFinite_mixed_resolvent_norm_le
        (n := n) A₀ hA₀ A hA ζ hζ hp hq.1 hq.2
      have hdR : HasDerivAt F D.re q := by
        have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt q hd
        have he : F = fun t => (∫ x : E, normalizedTrace
            (resolvent (gaussianFreeFiniteInterpolation A₀ A t x) ζ ^ p *
              resolvent (gaussianFreeFiniteInterpolation A₀ A t x) (star ζ) ^ p)
            ∂gaussianVector J).re := by
          funext t
          exact integral_gaussianFreeFinite_resolventEvenMoment_eq_re A₀ hA₀ A hA t ζ hζ p
        rw [he]
        exact hr
      refine ⟨hdR.congr_deriv hdR.deriv.symm, ?_⟩
      rw [hdR.deriv]
      refine (Complex.abs_re_le_norm D).trans (hb.trans_eq ?_)
      rw [hα]
      dsimp only [C, B, V, F]
      push_cast
      ring
    have he := Real.abs_rpow_sub_rpow_le_of_hasDerivAt_bound
      (f := F) (f' := deriv F) (a := 0) (b := 1) (s := s) (K := C)
      (by norm_num) hs hFc.continuousOn (fun q _ => hFpos q)
      (fun q hq => (hD q hq).1) (fun q hq => (hD q hq).2)
    have hCB : (s * C) * (1 - 0) = B := by
      dsimp only [s, C]
      field_simp [hk.ne']
      ring
    simpa only [s, hCB] using he

end NLAlib
