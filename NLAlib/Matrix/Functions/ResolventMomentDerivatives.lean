import NLAlib.Matrix.Functions.ResolventWordDerivatives
import NLAlib.Matrix.Functions.ResolventMoments

/-!
# The actual third derivative of the normalized even resolvent moment

The Gram moment is identified with its actual mixed
resolvent trace on the whole Hermitian real coordinate space. The word
derivative theorem derives the third derivative from inverse differentiation
and the native noncommutative product rule. No derivative identity or word
estimate is supplied as a premise.

Source: Brailovskaya–van Handel, arXiv:2201.05142v3, Lemma 6.9.
These are deterministic prerequisites for the
`independent-sum-spectrum-universality` card.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "E" => ((n × n) ⊕ (n × n)) → ℝ
local notation "L" => (hermitianMatrixFromRealCoordinates : E →L[ℝ] M)

/-- The literal `p` resolvents followed by `p` conjugate-shift resolvents,
represented as ordered inverse blocks with identity coefficients. -/
def mixedResolventWord (ζ : ℂ) (p : ℕ) : Fin (p + p) → ℂ × M :=
  Fin.append (fun _ : Fin p => (ζ, 1)) (fun _ : Fin p => (star ζ, 1))

/-- The block word is the actual mixed native resolvent product. -/
theorem hermitianCoordinateResolventWord_mixed (A : M) (ζ : ℂ) (p : ℕ) (y : E) :
    hermitianCoordinateResolventWord A (mixedResolventWord ζ p) y =
      resolvent (A + L y) ζ ^ p * resolvent (A + L y) (star ζ) ^ p := by
  simp [hermitianCoordinateResolventWord, mixedResolventWord, List.ofFn_fin_append,
    List.ofFn_const, List.prod_replicate, hermitianCoordinateResolvent]

omit [Fintype n] in
/-- Both shifts in the actual mixed word are nonreal. -/
theorem im_ne_zero_mixedResolventWord (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ) :
    ∀ i, ((mixedResolventWord (n := n) ζ p) i).1.im ≠ 0 := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [mixedResolventWord, Fin.append_left] using hζ
  · simpa only [mixedResolventWord, Fin.append_right, Complex.star_def,
      Complex.conj_im] using neg_ne_zero.mpr hζ

/-- The genuine complex mixed resolvent trace is smooth everywhere in the
real Hermitian coordinate space. -/
theorem contDiff_normalizedTrace_mixed_resolvent_coordinate
    (A : M) (hA : A.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ)
    {r : WithTop ℕ∞} :
    ContDiff ℝ r (fun y : E => normalizedTrace
      (resolvent (A + L y) ζ ^ p * resolvent (A + L y) (star ζ) ^ p)) := by
  let T : M →L[ℝ] ℂ :=
    (normalizedTraceLinearMap : M →ₗ[ℂ] ℂ).toContinuousLinearMap.restrictScalars ℝ
  have hc := T.contDiff.comp (contDiff_hermitianCoordinateResolventWord A hA
    (mixedResolventWord ζ p) (im_ne_zero_mixedResolventWord ζ hζ p) (r := r))
  simpa only [T, Function.comp_def, ContinuousLinearMap.coe_restrictScalars',
    LinearMap.coe_toContinuousLinearMap', normalizedTraceLinearMap_apply,
    hermitianCoordinateResolventWord_mixed] using! hc

/-- The genuine real Gram moment is globally smooth on Hermitian real
coordinates, with zero moment order and empty dimensions included. -/
theorem contDiff_resolventEvenMoment_coordinate
    (A : M) (hA : A.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ)
    {r : WithTop ℕ∞} :
    ContDiff ℝ r (fun y : E => resolventEvenMoment (A + L y) ζ p) := by
  have hc := Complex.reCLM.contDiff.comp
    (contDiff_normalizedTrace_mixed_resolvent_coordinate A hA ζ hζ p (r := r))
  have heq : (fun y : E => resolventEvenMoment (A + L y) ζ p) =
      fun y : E => (normalizedTrace
        (resolvent (A + L y) ζ ^ p * resolvent (A + L y) (star ζ) ^ p)).re := by
    funext y
    exact resolventEvenMoment_eq_re_normalizedTrace_mul_pow
      (hA.add (isHermitian_hermitianMatrixFromRealCoordinates y)) ζ p
  rw [heq]
  exact hc

/-- The third real Fréchet derivative of the actual complex mixed normalized
trace is the literal finite three-insertion word sum, with no missing
normalization or scalar multiplicity. -/
theorem iteratedFDeriv_three_normalizedTrace_mixed_resolvent_coordinate_apply
    (A : M) (hA : A.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ)
    (y : E) (h : Fin 3 → E) :
    iteratedFDeriv ℝ 3 (fun x : E => normalizedTrace
      (resolvent (A + L x) ζ ^ p * resolvent (A + L x) (star ζ) ^ p)) y h =
      ∑ i : Fin (p + p), ∑ j : Fin (p + p + 1), ∑ k : Fin (p + p + 2),
        normalizedTrace (hermitianCoordinateResolventWord A
          (resolventWordInsert
            (resolventWordInsert
              (resolventWordInsert (mixedResolventWord ζ p) i (L (h 2))) j (L (h 1)))
                k (L (h 0))) y) := by
  let T : M →L[ℝ] ℂ :=
    (normalizedTraceLinearMap : M →ₗ[ℂ] ℂ).toContinuousLinearMap.restrictScalars ℝ
  have he := iteratedFDeriv_three_comp_hermitianCoordinateResolventWord_apply
    T A hA (mixedResolventWord ζ p) (im_ne_zero_mixedResolventWord ζ hζ p) y h
  simpa only [T, ContinuousLinearMap.coe_restrictScalars',
    LinearMap.coe_toContinuousLinearMap', normalizedTraceLinearMap_apply,
    hermitianCoordinateResolventWord_mixed] using! he

/-- The actual third real Fréchet derivative of the positive normalized Gram
moment is the real part of the exact ordered inverse/insertion sum. -/
theorem iteratedFDeriv_three_resolventEvenMoment_coordinate_apply
    (A : M) (hA : A.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ)
    (y : E) (h : Fin 3 → E) :
    iteratedFDeriv ℝ 3 (fun x : E => resolventEvenMoment (A + L x) ζ p) y h =
      ∑ i : Fin (p + p), ∑ j : Fin (p + p + 1), ∑ k : Fin (p + p + 2),
        (normalizedTrace (hermitianCoordinateResolventWord A
          (resolventWordInsert
            (resolventWordInsert
              (resolventWordInsert (mixedResolventWord ζ p) i (L (h 2))) j (L (h 1)))
                k (L (h 0))) y)).re := by
  let T : M →L[ℝ] ℝ := Complex.reCLM.comp
    ((normalizedTraceLinearMap : M →ₗ[ℂ] ℂ).toContinuousLinearMap.restrictScalars ℝ)
  have he := iteratedFDeriv_three_comp_hermitianCoordinateResolventWord_apply
    T A hA (mixedResolventWord ζ p) (im_ne_zero_mixedResolventWord ζ hζ p) y h
  have heq : (fun x : E => resolventEvenMoment (A + L x) ζ p) =
      fun x : E => T (hermitianCoordinateResolventWord A (mixedResolventWord ζ p) x) := by
    funext x
    rw [resolventEvenMoment_eq_re_normalizedTrace_mul_pow
      (hA.add (isHermitian_hermitianMatrixFromRealCoordinates x)),
      hermitianCoordinateResolventWord_mixed]
    rfl
  rw [heq]
  simpa only [T, ContinuousLinearMap.comp_apply, Complex.reCLM_apply,
    ContinuousLinearMap.coe_restrictScalars', LinearMap.coe_toContinuousLinearMap',
    normalizedTraceLinearMap_apply] using! he

/-- Exact rising-factor number of terms in the actual third moment derivative. -/
theorem card_third_resolventEvenMoment_insertions (p : ℕ) :
    Fintype.card (Fin (p + p) × Fin (p + p + 1) × Fin (p + p + 2)) =
      (2 * p) * (2 * p + 1) * (2 * p + 2) := by
  simpa only [two_mul] using card_third_resolvent_word_insertions (p + p)

end NLAlib
