import NLAlib.Probability.Free.WordMatrixPolynomialComposition
import NLAlib.ForMathlib.MeasureTheory.CStarSpectralMoments
import NLAlib.ForMathlib.MeasureTheory.LpUniformApproximation
import NLAlib.Polynomial.FunctionApproximation.ResolventModulus
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Actual amplified word-resolvent ultracontractivity

Jackson approximation of the scalar inverse-distance function, the actual
spectral probability measure of the normalized amplified vacuum, and the
proved word-polynomial degree estimate give the source's nonuniform
resolvent bound. The matrix and its rooted Gram moment are the actual native
operators throughout; no moment-comparison or approximation certificate is
assumed.

Source: arXiv:2406.11453v2, Theorem 4.2.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory
open scoped Classical ComplexOrder ContinuousFunctionalCalculus

namespace NLAlib

variable {D ι : Type*} [Fintype D] [DecidableEq D] [Fintype ι]
local notation "W" => WordHilbertSpace ι
local notation "M" => CStarMatrix D D (W →L[ℂ] W)

omit [Fintype ι] in
private theorem realWordResolventCFC : IsometricContinuousFunctionalCalculus ℝ M IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus (A := M)

attribute [local instance] realWordResolventCFC

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The native nonreal resolvent of an actual self-adjoint matrix word
polynomial of degree at most `k` satisfies the source nonuniform rooted
vacuum-moment bound. The approximation error retains the actual `‖T‖`.

Source: Theorem 4.2 of arXiv:2406.11453v2.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem norm_resolvent_le_wordMatrixVacuum_evenMoment_rpow
    (k q r : ℕ) (hq : 0 < q) (hr : 0 < r) (T : M) (hself : IsSelfAdjoint T)
    (hT : ∀ i j, T i j ∈ wordWickDegreeSpan (ι := ι) k)
    {z : ℂ} (hz : 0 < z.im) :
    ‖resolvent T z‖ ≤
      (Fintype.card D : ℝ) ^ (3 / (4 * q : ℝ)) *
        (2 * q * r * k + 1 : ℝ) ^ (3 / (4 * q : ℝ)) *
          (((wordMatrixVacuumExpectation (D := D) (ι := ι)
            ((star (resolvent T z) * resolvent T z) ^ (2 * q))).re) ^
              (1 / (4 * q : ℝ)) + 12 * ‖T‖ / ((r : ℝ) * z.im ^ 2)) := by
  cases isEmpty_or_nonempty D with
  | inl hD =>
    have hzero : resolvent T z = 0 := by ext i; exact (hD.false i).elim
    have hcard : Fintype.card D = 0 := Fintype.card_eq_zero_iff.mpr hD
    have he : (3 : ℝ) / (4 * q) ≠ 0 := by
      have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
      positivity
    simp only [hzero, norm_zero, hcard, Nat.cast_zero, Real.zero_rpow he, zero_mul,
      le_refl]
  | inr hD =>
    let : Nonempty D := hD
    let φ := wordMatrixVacuumPositiveMap (D := D) (ι := ι)
    have hφ : φ 1 = 1 := wordMatrixVacuumExpectation_one
    let hprob : IsProbabilityMeasure (positiveSpectrumMeasure φ hself) :=
      isProbabilityMeasure_positiveSpectrumMeasure φ hφ hself
    let f : ℝ → ℝ := fun x => ‖(z - (x : ℂ))⁻¹‖
    let δ : ℝ := 6 * ‖T‖ / ((r : ℝ) * z.im ^ 2)
    have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
    have hf : Continuous f := by
      apply Continuous.norm
      apply (continuous_const.sub Complex.continuous_ofReal).inv₀
      intro x hx
      have heq : z = (x : ℂ) := sub_eq_zero.mp hx
      have : z.im = 0 := by rw [heq]; rfl
      exact hz.ne' this
    obtain ⟨Q, hQ, happ⟩ := exists_degree_le_resolvent_modulus_approximation
      hz ‖T‖ (norm_nonneg _) r hr
    have hinterval (x : spectrum ℝ T) : (x : ℝ) ∈ Set.Icc (-‖T‖) ‖T‖ := by
      have hone : ‖(1 : M)‖ ≤ 1 := by
        have h := CStarRing.norm_star_mul_self (x := (1 : M))
        simp only [star_one, one_mul] at h
        nlinarith [norm_nonneg (1 : M)]
      have hb : |(x : ℝ)| ≤ ‖T‖ := by
        have hb : |(x : ℝ)| ≤ ‖T‖ * ‖(1 : M)‖ := by
          simpa only [Real.norm_eq_abs] using spectrum.norm_le_norm_mul_of_mem x.property
        exact hb.trans
          (mul_le_of_le_one_right (norm_nonneg T) hone)
      exact abs_le.mp hb
    have happrox (x : spectrum ℝ T) : |Q.eval (x : ℝ) - f x| ≤ δ := by
      simpa only [abs_sub_comm] using happ x (hinterval x)
    have hmem : MemLp (fun x : spectrum ℝ T => f x) (4 * q : ENNReal)
        (positiveSpectrumMeasure φ hself) :=
      (hf.comp continuous_subtype_val).memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hp : (1 : ENNReal) ≤ 4 * q := by exact_mod_cast (show 1 ≤ 4 * q by omega)
    have hLp : lpNorm (fun x : spectrum ℝ T => Q.eval (x : ℝ)) (4 * q : ENNReal)
        (positiveSpectrumMeasure φ hself) ≤
        lpNorm (fun x : spectrum ℝ T => f x) (4 * q : ENNReal)
          (positiveSpectrumMeasure φ hself) + δ :=
      lpNorm_le_add_of_uniform_approximation hmem hp
        (by exact ENNReal.mul_ne_top (by simp) (by simp)) hδ happrox
    have hnormdiff : ‖cfc f T - Polynomial.aeval T Q‖ ≤ δ := by
      rw [← cfc_polynomial Q T hself, ← cfc_sub f (fun x => Q.eval x) T
        hf.continuousOn Q.continuous.continuousOn]
      apply norm_cfc_le hδ
      intro x hx
      simpa only [Real.norm_eq_abs, abs_sub_comm] using happrox ⟨x, hx⟩
    have hnorm : ‖resolvent T z‖ ≤ ‖Polynomial.aeval T Q‖ + δ := by
      rw [← hself.norm_cfc_resolvent_modulus hz.ne']
      calc
        _ ≤ ‖Polynomial.aeval T Q‖ + ‖cfc f T - Polynomial.aeval T Q‖ :=
          norm_le_norm_add_norm_sub' _ _
        _ ≤ _ := add_le_add le_rfl hnormdiff
    have hdegree := aeval_entries_mem_wordWickDegreeSpan (D := D) (ι := ι) hT Q
      (Polynomial.natDegree_le_of_degree_le hQ)
    have hpoly := norm_le_wordMatrixVacuum_evenMoment_rpow (D := D) (ι := ι) (r * k) q hq
      (Polynomial.aeval T Q) hdegree
    have hpolyLp : lpNorm (fun x : spectrum ℝ T => Q.eval (x : ℝ)) (4 * q : ENNReal)
        (positiveSpectrumMeasure φ hself) =
          ((φ ((star (Polynomial.aeval T Q) * Polynomial.aeval T Q) ^ (2 * q))).re) ^
            ((4 * q : ℝ)⁻¹) := by
      have hQeq : cfc (fun x : ℝ => Q.eval x) T = Polynomial.aeval T Q :=
        cfc_polynomial Q T hself
      calc
        _ = ((φ ((star (cfc Q.eval T) * cfc Q.eval T) ^ (2 * q))).re) ^
            ((4 * q : ℝ)⁻¹) :=
          lpNorm_positiveSpectrumMeasure_eq_gramMoment φ hself
            Q.eval Q.continuous.continuousOn q hq
        _ = _ := by rw [hQeq]
    have hresLp : lpNorm (fun x : spectrum ℝ T => f x) (4 * q : ENNReal)
        (positiveSpectrumMeasure φ hself) =
          ((φ ((star (resolvent T z) * resolvent T z) ^ (2 * q))).re) ^
            ((4 * q : ℝ)⁻¹) :=
      lpNorm_positiveSpectrumMeasure_resolvent_modulus φ hself hz.ne' q hq
    let C : ℝ := (Fintype.card D : ℝ) ^ (3 / (4 * q : ℝ)) *
      (2 * q * r * k + 1 : ℝ) ^ (3 / (4 * q : ℝ))
    have hCzero : 0 ≤ C := by dsimp only [C]; positivity
    have hCone : 1 ≤ C := by
      dsimp only [C]
      apply one_le_mul_of_one_le_of_one_le
      · apply Real.one_le_rpow
        · exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos (α := D)))
        · positivity
      · apply Real.one_le_rpow
        · have hn : 0 ≤ (2 * q * r * k : ℝ) := by positivity
          linarith
        · positivity
    have hpoly' : ‖Polynomial.aeval T Q‖ ≤
        C * lpNorm (fun x : spectrum ℝ T => Q.eval (x : ℝ)) (4 * q : ENNReal)
          (positiveSpectrumMeasure φ hself) := by
      rw [hpolyLp]
      simpa only [C, φ, wordMatrixVacuumPositiveMap_apply,
        one_div, Nat.cast_mul, ← mul_assoc] using hpoly
    have hbound : ‖resolvent T z‖ ≤
        C * (lpNorm (fun x : spectrum ℝ T => f x) (4 * q : ENNReal)
          (positiveSpectrumMeasure φ hself) + 2 * δ) := by
      have ha := (hnorm.trans (add_le_add hpoly' le_rfl)).trans
        (add_le_add (mul_le_mul_of_nonneg_left hLp hCzero) le_rfl)
      have hb : δ ≤ C * δ := by nlinarith
      nlinarith
    rw [hresLp] at hbound
    convert hbound using 1
    simp only [C, δ, φ, wordMatrixVacuumPositiveMap_apply, one_div]
    ring

end NLAlib

end
