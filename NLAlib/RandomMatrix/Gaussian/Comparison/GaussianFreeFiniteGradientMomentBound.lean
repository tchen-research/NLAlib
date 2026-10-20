import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteArcCrossingBounds

/-! # Actual native gradient contraction moment estimate

The two genuine coordinate derivatives are expanded into positive inverse
arcs, estimated by the genuine crossing bound, and integrated using the
actual Gaussian marginals. No gradient or moment comparison is assumed.
Source: arXiv:2108.06312v2, Lemma 6.3.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Kronecker ComplexOrder MatrixOrder
namespace NLAlib
variable {ι n d : Type*} [Fintype ι] [Fintype n] [Fintype d]
  [DecidableEq ι] [DecidableEq n] [DecidableEq d]
local notation "K" => GaussianFreeFiniteCoordinate ι n
local notation "E" => K → ℝ
local notation "M" => Matrix (d × n) (d × n) ℂ

open scoped Matrix.Norms.L2Operator in
/-- The actual coordinate-gradient sandwich contraction of two native
mixed arcs has the original covariance budget and the exact count of
positive derivative splits. Both actual coordinate maps have their genuine
standard Gaussian marginals; no independence between them is required. -/
theorem norm_integral_nativeMixedArc_gradient_sandwich_le
    {κ : Type*} [Fintype κ] [DecidableEq κ] (C : κ → M)
    (hC : ∀ k, (C k).IsHermitian)
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hVC : specNorm (coefficientVariance C) ≤ specNorm (coefficientVariance A))
    (hWC : specNorm (coefficientCovariance C) ≤ specNorm (coefficientCovariance A))
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (a b c e : ℕ) {m : ℕ} (hm : 0 < m)
    (hL : a + b + c + e + 2 = 2 * m)
    (Y Z : E × E → E)
    (hY : MeasurePreserving Y ((gaussianVector K).prod (gaussianVector K)) (gaussianVector K))
    (hZ : MeasurePreserving Z ((gaussianVector K).prod (gaussianVector K)) (gaussianVector K)) :
    ‖∫ w : E × E, ∑ k : K, ∑ i : κ, normalizedSandwichTraceBilinear (C i)
      (fderiv ℝ (gaussianFreeFiniteMixedArc A₀ A q ζ a b) (Y w) (Pi.single k 1))
      (fderiv ℝ (gaussianFreeFiniteMixedArc A₀ A q ζ c e) (Z w) (Pi.single k 1))
        ∂(gaussianVector K).prod (gaussianVector K)‖ ≤
      ((a + b : ℕ) : ℝ) * ((c + e : ℕ) : ℝ) *
        (specNorm (coefficientVariance A) * specNorm (coefficientCovariance A)) *
        ∫ x : E, resolventEvenMoment (gaussianFreeFiniteInterpolation A₀ A q x) ζ m
          ∂gaussianVector K := by
  let μ := gaussianVector K
  let f : E → ℝ := fun x => resolventEvenMoment (gaussianFreeFiniteInterpolation A₀ A q x) ζ m
  let v : ℝ := specNorm (coefficientVariance A) * specNorm (coefficientCovariance A)
  let Y₄ : Fin 4 → E × E → E := ![Y, Y, Z, Z]
  let a₄ := mixedResolventCrossingFirstPowers a b c e
  let b₄ := mixedResolventCrossingSecondPowers a b c e
  let wgt : Fin (a + b) → Fin (c + e) → Fin 4 → ℝ :=
    fun l r j => ((a₄ l r j + b₄ l r j : ℕ) : ℝ) / (2 * m : ℕ)
  let U : Fin (a + b) → Fin (c + e) → E × E → ℝ :=
    fun l r w => v * ∑ j, wgt l r j * f (Y₄ j w)
  have hY₄ (j : Fin 4) : MeasurePreserving (Y₄ j) (μ.prod μ) μ := by
    fin_cases j <;> first | exact hY | exact hZ
  have hfi : Integrable f μ :=
    integrable_gaussianFreeFinite_resolventEvenMoment A₀ hA₀ A hA q ζ hζ hm
  have hi (j : Fin 4) : Integrable (fun w : E × E => f (Y₄ j w)) (μ.prod μ) :=
    (hY₄ j).integrable_comp_of_integrable hfi
  have he (j : Fin 4) : (∫ w : E × E, f (Y₄ j w) ∂μ.prod μ) = ∫ x, f x ∂μ :=
    (hY₄ j).hasLaw.integral_comp hfi.aestronglyMeasurable
  have hU (l : Fin (a + b)) (r : Fin (c + e)) : Integrable (U l r) (μ.prod μ) :=
    (integrable_finsetSum _ fun j _ => (hi j).const_mul (wgt l r j)).const_mul v
  have hwgt (l : Fin (a + b)) (r : Fin (c + e)) : ∑ j, wgt l r j = 1 := by
    have hs := (mixedResolventCrossingPowers_lengths a b c e l r).2.trans hL
    dsimp only [wgt, a₄, b₄]
    rw [← Finset.sum_div, show
        (∑ j : Fin 4, ((mixedResolventCrossingFirstPowers a b c e l r j +
          mixedResolventCrossingSecondPowers a b c e l r j : ℕ) : ℝ)) = (2 * m : ℕ) by
            exact_mod_cast hs,
      div_self (by positivity : ((2 * m : ℕ) : ℝ) ≠ 0)]
  have hUint (l : Fin (a + b)) (r : Fin (c + e)) :
      (∫ w : E × E, U l r w ∂μ.prod μ) = v * ∫ x, f x ∂μ := by
    dsimp only [U]
    rw [integral_const_mul, integral_finsetSum _ fun j _ => (hi j).const_mul (wgt l r j)]
    simp only [integral_const_mul, he, ← Finset.sum_mul, hwgt, one_mul]
  have hcross (l : Fin (a + b)) (r : Fin (c + e)) (w : E × E) :
      ‖(Fintype.card (d × n) : ℂ)⁻¹ * coefficientCrossingTraceMultilinear C
        (gaussianFreeFiniteCoefficient A q)
        (fun j => gaussianFreeFiniteMixedArc A₀ A q ζ (a₄ l r j) (b₄ l r j) (Y₄ j w))‖ ≤
        U l r w := by
    obtain ⟨harc, hlen⟩ := mixedResolventCrossingPowers_lengths a b c e l r
    have h := norm_nativeMixedArc_crossing_le_original_parameters C hC A₀ hA₀ A hA hq hq1
      hVC hWC ζ (a₄ l r) (b₄ l r) (hlen.trans hL) (by omega) harc (fun j => Y₄ j w)
    have hmom (j : Fin 4) : (normalizedTrace (CFC.abs (resolvent
        (gaussianFreeFiniteInterpolation A₀ A q (Y₄ j w)) ζ) ^ (2 * m))).re = f (Y₄ j w) := by
      simpa only [RCLike.re_eq_complex_re, resolventEvenMoment, f] using
        re_normalizedTrace_cfcAbs_pow_two_mul
          (resolvent (gaussianFreeFiniteInterpolation A₀ A q (Y₄ j w)) ζ) m
    simpa only [hmom, v, wgt, U] using h
  have hpoint (w : E × E) :
      ‖∑ k : K, ∑ i : κ, normalizedSandwichTraceBilinear (C i)
        (fderiv ℝ (gaussianFreeFiniteMixedArc A₀ A q ζ a b) (Y w) (Pi.single k 1))
        (fderiv ℝ (gaussianFreeFiniteMixedArc A₀ A q ζ c e) (Z w) (Pi.single k 1))‖ ≤
        ∑ l, ∑ r, U l r w := by
    rw [sum_nativeMixedArc_gradient_sandwich_eq_crossing C A₀ hA₀ A hA q ζ hζ a b c e]
    simp only [Finset.mul_sum]
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro l _
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro r _
    have hvec : (fun j => gaussianFreeFiniteMixedArc A₀ A q ζ
        (a₄ l r j) (b₄ l r j) (Y₄ j w)) =
      ![gaussianFreeFiniteMixedArc A₀ A q ζ (mixedResolventSplitLeft a b l).1 (mixedResolventSplitLeft a b l).2 (Y w),
        gaussianFreeFiniteMixedArc A₀ A q ζ (mixedResolventSplitRight a b l).1 (mixedResolventSplitRight a b l).2 (Y w),
        gaussianFreeFiniteMixedArc A₀ A q ζ (mixedResolventSplitLeft c e r).1 (mixedResolventSplitLeft c e r).2 (Z w),
        gaussianFreeFiniteMixedArc A₀ A q ζ (mixedResolventSplitRight c e r).1 (mixedResolventSplitRight c e r).2 (Z w)] := by
      funext j
      fin_cases j <;> rfl
    simpa only [hvec] using hcross l r w
  calc
    _ ≤ ∫ w : E × E, ∑ l, ∑ r, U l r w ∂μ.prod μ :=
      norm_integral_le_of_norm_le
        (integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun r _ => hU l r)
        (Eventually.of_forall hpoint)
    _ = _ := by
      rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun r _ => hU l r]
      simp only [integral_finsetSum _ fun r _ => hU _ r, hUint, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp only [v, f]
      ring

end NLAlib
