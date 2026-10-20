import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Algebra.Ring.Parity
import NLAlib.Probability.Gaussian.Basic.StandardGaussian
import NLAlib.Probability.Gaussian.Moments.NaturalMoments
import NLAlib.ForMathlib.MeasureTheory.PolynomialIntegrability

/-!
# Independent-entry moment domination

Let `X e : Ω → ℝ` for `e : E` (with `E` finite) be independent real random
variables on a probability space `(Ω, μ)`. Suppose each `X e` is **symmetric**
(`X e` and `-X e` are identically distributed), every positive even power is
integrable, and its integral is at most the standard Gaussian even moment:

```
∫ (X e)^(2p) ∂μ ≤ gaussianEvenMoment p      for p ≥ 1
```

Then:

* every natural power `(X e)^p` is integrable (for `p = 0` by finiteness of
  the measure; for lower powers from the even powers via `MemLp`);
* odd moments vanish by symmetry;
* every natural moment is nonnegative and is at most the matching standard
  Gaussian moment;
* for every `k : E → ℕ` the monomial product `∏ e, (X e)^(k e)` is integrable
  and `∫ ∏ (X e)^(k e) ≤ ∫ ∏ g_e^(k e)` where `g` is a standard Gaussian
  vector (the comparison holds after the actual independence factorization:
  both sides factor into products of scalar moments);
* for any finite index type `τ`, nonnegative coefficients `c : τ → ℝ`, and
  exponents `k : τ → E → ℕ`, the same comparison holds for the weighted sum
  `∑ t, c t * ∏ e, (X e)^(k t e)`.

The empty families (`E = ∅`, `τ = ∅`), exponent zero, and independent
**non-identically-distributed** entries are all included: the only cross-entry
request is independence, and each entry only needs its own symmetry and even
moment domination.

The proof uses Mathlib's `iIndepFun.integral_fun_prod_comp` to factor actual
probability-law integrals, together with the Gaussian moment formula
`integral_pow_two_mul_gaussianReal`. Nonnegative deterministic entry weights
can be absorbed into the polynomial coefficients.

This is a scalar polynomial comparison supporting
`independent-entry-gaussian-extremum` and `independent-entry-small-deviation`.
The matrix Gram expansion, smaller iid comparator, and eventwise tail bound
are separate steps.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

namespace NLAlib

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Finite even moments imply integrability of every natural power on a finite
measure space. Symmetry supplies measurability; lower powers are integrable by
monotonicity of `MemLp` exponents. -/
private lemma integrable_pow_of_symm_even [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hsym : IdentDistrib X (fun w => -X w) μ μ)
    (h2 : ∀ p, 0 < p → Integrable (fun w => X w ^ (2 * p)) μ)
    (p : ℕ) :
    Integrable (fun w => X w ^ p) μ := by
  rcases p with _ | p
  · simp
  · have hmeas : AEStronglyMeasurable X μ := hsym.aemeasurable_fst.aestronglyMeasurable
    have h2norm : Integrable (fun w => ‖X w‖ ^ (2 * (p + 1))) μ := by
      have hn := (integrable_norm_iff (hmeas.pow (2 * (p + 1)))).2
        (h2 (p + 1) (by omega))
      refine hn.congr ?_
      filter_upwards with w
      rw [Real.norm_eq_abs, Real.norm_eq_abs, (even_two_mul (p + 1)).pow_abs]
      exact abs_of_nonneg ((even_two_mul (p + 1)).pow_nonneg (X w))
    have hlow : Integrable (fun w => ‖X w‖ ^ (p + 1)) μ :=
      integrable_norm_pow_of_le hmeas (by omega) h2norm
    have hnormres : Integrable (fun w => ‖X w ^ (p + 1)‖) μ := by
      simpa [norm_pow] using hlow
    exact (integrable_norm_iff (hmeas.pow (p + 1))).1 hnormres

/-- Odd moments of a symmetric variable vanish. -/
private lemma integral_pow_eq_zero_of_odd_of_symm {X : Ω → ℝ}
    (hsym : IdentDistrib X (fun w => -X w) μ μ)
    {p : ℕ} (hp : Odd p)
    (_hint : Integrable (fun w => X w ^ p) μ) :
    ∫ w, X w ^ p ∂μ = 0 := by
  have hcomp := hsym.comp (continuous_pow p).measurable
  have heq := hcomp.integral_eq
  have heq' : (∫ x, X x ^ p ∂μ) = ∫ x, (-X x) ^ p ∂μ := by
    simpa only [Function.comp_def] using heq
  have hneg : (fun x => (-X x) ^ p) = fun x => -X x ^ p := by
    funext x
    exact Odd.neg_pow hp (X x)
  rw [hneg, integral_neg] at heq'
  linarith

/-- Symmetric variables with even moments dominated by the Gaussian even moments
have every natural moment nonnegative and at most the matching standard Gaussian
moment. -/
theorem integral_pow_nonneg_and_le_gaussianReal [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hsym : IdentDistrib X (fun w => -X w) μ μ)
    (h2 : ∀ p, 0 < p →
      Integrable (fun w => X w ^ (2 * p)) μ ∧
        ∫ w, X w ^ (2 * p) ∂μ ≤ gaussianEvenMoment p)
    (p : ℕ) :
    0 ≤ ∫ w, X w ^ p ∂μ ∧ ∫ w, X w ^ p ∂μ ≤ ∫ z, z ^ p ∂(gaussianReal 0 1) := by
  have hint := integrable_pow_of_symm_even hsym (fun p hp => (h2 p hp).1) p
  constructor
  · rcases Nat.even_or_odd' p with ⟨q, rfl | rfl⟩
    · exact integral_nonneg (f := fun w => X w ^ (2 * q)) fun w =>
        (even_two_mul q).pow_nonneg (X w)
    · rw [integral_pow_eq_zero_of_odd_of_symm hsym ⟨q, rfl⟩ hint]
  · rcases Nat.even_or_odd' p with ⟨q, rfl | rfl⟩
    · by_cases hq : q = 0
      · subst q
        have hx : (∫ w, X w ^ (2 * 0) ∂μ) = 1 := by
          simp
        have hz : (∫ z, z ^ (2 * 0) ∂(gaussianReal 0 1)) = 1 := by
          simp
        rw [hx, hz]
      · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
        have hG : ∫ z, z ^ (2 * q) ∂(gaussianReal 0 1) = gaussianEvenMoment q :=
          integral_pow_two_mul_gaussianReal q
        rw [hG]
        exact (h2 q hqpos).2
    · have hX0 : ∫ w, X w ^ (2 * q + 1) ∂μ = 0 :=
        integral_pow_eq_zero_of_odd_of_symm hsym ⟨q, rfl⟩ hint
      have hG0 : ∫ z, z ^ (2 * q + 1) ∂(gaussianReal 0 1) = 0 := by
        have h : ∫ z, z ^ (2 * q + 1) ∂(gaussianReal 0 1) =
            ∫ z, (-z) ^ (2 * q + 1) ∂(gaussianReal 0 1) := by
          conv_lhs => rw [← neg_zero, ← gaussianReal_map_neg (μ := 0) (v := 1)]
          rw [integral_map (by fun_prop) (by fun_prop)]
        have h2' : ∫ z, (-z) ^ (2 * q + 1) ∂(gaussianReal 0 1) =
            -∫ z, z ^ (2 * q + 1) ∂(gaussianReal 0 1) := by
          rw [← integral_neg]
          congr 1
          ext z
          rw [Odd.neg_pow ⟨q, rfl⟩]
        linarith
      rw [hX0, hG0]

/-- A symmetric variable whose even moments are finite has finite natural moments. -/
private theorem hasFiniteNatMoments_of_symm_even [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hsym : IdentDistrib X (fun w => -X w) μ μ)
    (h2 : ∀ p, 0 < p → Integrable (fun w => X w ^ (2 * p)) μ) :
    HasFiniteNatMoments X μ := fun p => integrable_pow_of_symm_even hsym h2 p

variable {E : Type*} [Fintype E] {X : E → Ω → ℝ}

/-- A coordinate of the standard Gaussian vector has finite natural moments. -/
lemma hasFiniteNatMoments_eval_gaussianVector (e : E) :
    HasFiniteNatMoments (fun x : E → ℝ => x e) (gaussianVector E) := by
  intro p
  have hlaw := hasLaw_eval_gaussianVector e
  have h := integrable_pow_gaussianReal p
  rw [← hlaw.map_eq] at h
  exact (integrable_map_measure (continuous_pow p).aestronglyMeasurable
    hlaw.aemeasurable).1 h

/-- Monomial products of symmetric entries with finite even moments are
integrable. Independence and moment bounds are unnecessary for integrability. -/
private theorem integrable_prod_pow_of_symm_even [IsFiniteMeasure μ]
    (hsym : ∀ e, IdentDistrib (X e) (fun w => -X e w) μ μ)
    (h2 : ∀ e p, 0 < p → Integrable (fun w => (X e w) ^ (2 * p)) μ)
    (k : E → ℕ) :
    Integrable (fun w => ∏ e, (X e w) ^ (k e)) μ := by
  have hf : ∀ e ∈ (Finset.univ : Finset E),
      HasFiniteNatMoments (fun w => (X e w) ^ (k e)) μ := fun e _ =>
    (hasFiniteNatMoments_of_symm_even (hsym e) (h2 e)).pow (k e)
  exact (HasFiniteNatMoments.prod (Finset.univ) hf).integrable

/-- Monomial products of standard Gaussian vector coordinates are integrable. -/
theorem integrable_prod_pow_gaussianVector (k : E → ℕ) :
    Integrable (fun x : E → ℝ => ∏ e, x e ^ (k e)) (gaussianVector E) := by
  have hf : ∀ e ∈ (Finset.univ : Finset E),
      HasFiniteNatMoments (fun x : E → ℝ => x e ^ (k e)) (gaussianVector E) := fun e _ =>
    (hasFiniteNatMoments_eval_gaussianVector e).pow (k e)
  exact (HasFiniteNatMoments.prod (Finset.univ) hf).integrable

variable {τ : Type*} (c : τ → ℝ) (k : τ → E → ℕ)

/-- Scalar multiples of these monomial products are integrable. -/
private theorem integrable_mul_prod_pow [IsFiniteMeasure μ]
    (hsym : ∀ e, IdentDistrib (X e) (fun w => -X e w) μ μ)
    (h2 : ∀ e p, 0 < p → Integrable (fun w => (X e w) ^ (2 * p)) μ)
    (t : τ) :
    Integrable (fun w => c t * ∏ e, (X e w) ^ (k t e)) μ :=
  (integrable_prod_pow_of_symm_even hsym h2 (k t)).const_mul (c t)

/-- Scalar multiples of Gaussian monomial products are integrable. -/
private theorem integrable_mul_prod_pow_gaussianVector (t : τ) :
    Integrable (fun x : E → ℝ => c t * ∏ e, x e ^ (k t e)) (gaussianVector E) :=
  (integrable_prod_pow_gaussianVector (k t)).const_mul (c t)

variable [Fintype τ]

/-- **Independent-entry moment domination, monomial form**: for independent
symmetric entries whose even moments are dominated by the Gaussian even moments,
the integral of every monomial product is at most the matching standard Gaussian
vector monomial moment. The comparison is obtained after factoring both sides
into products of scalar moments by independence; it is not eventwise stochastic
domination. -/
theorem integral_prod_pow_le_integral_prod_pow_gaussianVector [IsProbabilityMeasure μ]
    (hX : iIndepFun X μ)
    (hsym : ∀ e, IdentDistrib (X e) (fun w => -X e w) μ μ)
    (h2 : ∀ e p, 0 < p →
      Integrable (fun w => (X e w) ^ (2 * p)) μ ∧
        ∫ w, (X e w) ^ (2 * p) ∂μ ≤ gaussianEvenMoment p)
    (k : E → ℕ) :
    ∫ w, ∏ e, (X e w) ^ (k e) ∂μ ≤
      ∫ x : E → ℝ, ∏ e, x e ^ (k e) ∂(gaussianVector E) := by
  have hmom : ∀ e, 0 ≤ ∫ w, (X e w) ^ (k e) ∂μ ∧
      ∫ w, (X e w) ^ (k e) ∂μ ≤ ∫ z, z ^ (k e) ∂(gaussianReal 0 1) := fun e =>
    integral_pow_nonneg_and_le_gaussianReal (hsym e) (h2 e) (k e)
  calc
    ∫ w, ∏ e, (X e w) ^ (k e) ∂μ = ∏ e, ∫ w, (X e w) ^ (k e) ∂μ := by
      exact hX.integral_fun_prod_comp (fun e => (hsym e).aemeasurable_fst)
        (fun e => (continuous_pow (k e)).aestronglyMeasurable)
    _ ≤ ∏ e, ∫ x, x e ^ (k e) ∂(gaussianVector E) := by
      refine Finset.prod_le_prod (s := Finset.univ) ?_ ?_
      · intro e he
        exact (hmom e).1
      · intro e he
        have hfac : ∫ x, x e ^ (k e) ∂(gaussianVector E) =
            ∫ z, z ^ (k e) ∂(gaussianReal 0 1) :=
          (hasLaw_eval_gaussianVector e).integral_comp
            (f := fun z : ℝ => z ^ (k e)) (by fun_prop)
        rw [hfac]
        exact (hmom e).2
    _ = ∫ x, ∏ e, x e ^ (k e) ∂(gaussianVector E) := by
      symm
      exact (iIndepFun_eval_gaussianVector E).integral_fun_prod_comp
        (fun e => (measurable_pi_apply e).aemeasurable)
        (fun e => (continuous_pow (k e)).aestronglyMeasurable)

/-- **Independent-entry moment domination, weighted-sum form**: with nonnegative
weights the moment comparison extends from monomial products to finite weighted
sums of monomial products (at the level of integrals, not eventwise). -/
theorem integral_sum_mul_prod_pow_le_integral_sum_mul_prod_pow_gaussianVector
    [IsProbabilityMeasure μ]
    (hX : iIndepFun X μ)
    (hsym : ∀ e, IdentDistrib (X e) (fun w => -X e w) μ μ)
    (h2 : ∀ e p, 0 < p →
      Integrable (fun w => (X e w) ^ (2 * p)) μ ∧
        ∫ w, (X e w) ^ (2 * p) ∂μ ≤ gaussianEvenMoment p)
    (hc : ∀ t, 0 ≤ c t) :
    ∫ w, ∑ t, c t * ∏ e, (X e w) ^ (k t e) ∂μ ≤
      ∫ x : E → ℝ, ∑ t, c t * ∏ e, x e ^ (k t e) ∂(gaussianVector E) := by
  classical
  have hXint : ∀ t ∈ (Finset.univ : Finset τ),
      Integrable (fun w => c t * ∏ e, (X e w) ^ (k t e)) μ := fun t _ =>
    integrable_mul_prod_pow c k hsym (fun e p hp => (h2 e p hp).1) t
  have hGint : ∀ t ∈ (Finset.univ : Finset τ),
      Integrable (fun x : E → ℝ => c t * ∏ e, x e ^ (k t e)) (gaussianVector E) := fun t _ =>
    integrable_mul_prod_pow_gaussianVector c k t
  calc
    ∫ w, ∑ t, c t * ∏ e, (X e w) ^ (k t e) ∂μ =
        ∑ t, c t * ∫ w, ∏ e, (X e w) ^ (k t e) ∂μ := by
      rw [integral_finsetSum (s := Finset.univ)
        (f := fun t w => c t * ∏ e, (X e w) ^ (k t e)) hXint]
      simp_rw [integral_const_mul]
    _ ≤ ∑ t, c t * ∫ x, ∏ e, x e ^ (k t e) ∂(gaussianVector E) := by
      refine Finset.sum_le_sum (fun t ht => ?_)
      exact mul_le_mul_of_nonneg_left
        (integral_prod_pow_le_integral_prod_pow_gaussianVector hX hsym h2 (k t)) (hc t)
    _ = ∫ x, ∑ t, c t * ∏ e, x e ^ (k t e) ∂(gaussianVector E) := by
      have hsum_eq :
          ∫ x, ∑ t, c t * ∏ e, x e ^ (k t e) ∂(gaussianVector E) =
            ∑ t, ∫ x, c t * ∏ e, x e ^ (k t e) ∂(gaussianVector E) :=
        integral_finsetSum (s := Finset.univ)
          (f := fun t (y : E → ℝ) => c t * ∏ e, y e ^ (k t e)) hGint
      rw [hsum_eq]
      apply Finset.sum_congr rfl
      intro t ht
      rw [integral_const_mul]

end NLAlib
