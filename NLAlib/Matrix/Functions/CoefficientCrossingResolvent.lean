import NLAlib.Matrix.Functions.CoefficientCrossingTrace
import NLAlib.Matrix.Functions.ResolventMixedPowers
import NLAlib.ForMathlib.Analysis.FiniteReciprocalExponents
import Mathlib.Analysis.MeanInequalities

/-! # Covariance crossing bounds with different Hermitian resolvents

The four resolvents may come from four different matrices. The actual
Schatten interpolation estimate and scalar weighted AM--GM give a convex
combination of their true modulus traces, retaining the native covariance
scale and exact normalized trace.
Source: arXiv:2108.06312v2, the common-marginal step in Lemma 6.3.
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix Kronecker ComplexOrder MatrixOrder
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
private theorem schattenNorm_resolvent_mixed_power_eq_trace_rpow
    {X : Matrix n n ℂ} (hX : X.IsHermitian) (ζ : ℂ) (a b L : ℕ)
    (hL : 0<L) (hab : 0<a+b) :
    schattenNorm (resolvent X ζ^a*resolvent X (star ζ)^b)
      (ENNReal.ofReal ((L : ℝ)/(a+b : ℕ))) =
        (CFC.abs (resolvent X ζ)^L).trace.re ^ (((a+b : ℕ) : ℝ)/L) := by
  have hab' : (0 : ℝ)<(a+b : ℕ) := by exact_mod_cast hab
  rw [schattenNorm_ofReal _ (by positivity),
    schattenNormReal_resolvent_pow_mul_resolvent_star_pow_eq_sum hX]
  have he : ((a+b : ℕ) : ℝ)*((L : ℝ)/(a+b : ℕ))=(L : ℝ) :=
    mul_div_cancel₀ _ hab'.ne'
  rw [he,one_div_div,← RCLike.re_eq_complex_re,re_trace_cfcAbs_pow_eq_sum_singularValues]
  simp only [Real.rpow_natCast]

open scoped Matrix.Norms.L2Operator in
/-- Different Hermitian matrices are allowed in the mixed resolvent arcs.
Positive arc lengths with total length L allocate the exact Schatten
exponents; scalar AM--GM bounds the product by a weighted sum of the true
ordinary modulus traces. No probability or independence is required. -/
theorem prod_schattenNorm_resolvent_mixed_powers_le_sum_trace
    {κ : Type*} [Fintype κ] (X : κ → Matrix n n ℂ)
    (hX : ∀ j, (X j).IsHermitian) (ζ : ℂ) (a b : κ → ℕ)
    {L : ℕ} (hL : ∑ j, (a j+b j)=L) (hLpos : 0<L)
    (hArc : ∀ j, 0<a j+b j) :
    (∏ j, schattenNorm (resolvent (X j) ζ^a j*resolvent (X j) (star ζ)^b j)
      (ENNReal.ofReal ((L : ℝ)/(a j+b j : ℕ)))) ≤
        ∑ j, (((a j+b j : ℕ) : ℝ)/L)*(CFC.abs (resolvent (X j) ζ)^L).trace.re := by
  have hL0 : (0 : ℝ)<L := by exact_mod_cast hLpos
  have hw : ∑ j, (((a j+b j : ℕ) : ℝ)/L)=1 := by
    rw [← Finset.sum_div,show (∑ j, ((a j+b j : ℕ) : ℝ))=(L : ℝ) by exact_mod_cast hL,
      div_self hL0.ne']
  simp_rw [schattenNorm_resolvent_mixed_power_eq_trace_rpow (hX _) ζ _ _ _ hLpos (hArc _)]
  apply Real.geom_mean_le_arith_mean_weighted
  · intro j _
    positivity
  · exact hw
  · intro j _
    rw [← RCLike.re_eq_complex_re,re_trace_cfcAbs_pow_eq_sum_singularValues]
    exact Finset.sum_nonneg fun i _ => pow_nonneg (singularValues_nonneg _ i) _

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

open scoped Matrix.Norms.L2Operator in
/-- Four genuine different-matrix resolvent arcs retain the actual covariance
crossing scale and a weighted sum of true modulus traces. This is the
pointwise estimate needed before the common-marginal Gaussian expectation
step; arbitrary dependence among the four matrices is allowed.
Source: arXiv:2108.06312v2, Lemmas 4.5 and 6.3.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem norm_coefficientCrossingTraceMultilinear_resolvent_le_sum_trace
    (A : ι → Matrix n n ℂ) (B : κ → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hB : ∀ j, (B j).IsHermitian)
    (X : Fin 4 → Matrix n n ℂ) (hX : ∀ j, (X j).IsHermitian)
    (ζ : ℂ) (a b : Fin 4 → ℕ) {L : ℕ}
    (hL : ∑ j, (a j+b j)=L) (hLpos : 0<L) (hArc : ∀ j, 0<a j+b j) :
    ‖coefficientCrossingTraceMultilinear A B
      (fun j => resolvent (X j) ζ^a j*resolvent (X j) (star ζ)^b j)‖ ≤
      (Real.sqrt (specNorm (coefficientVariance A))*
        Real.sqrt (specNorm (coefficientCovariance A))*
        Real.sqrt (specNorm (coefficientCovariance B))*
        Real.sqrt (specNorm (coefficientVariance B)))*
          ∑ j, (((a j+b j : ℕ) : ℝ)/L)*(CFC.abs (resolvent (X j) ζ)^L).trace.re := by
  have hsSum : ∑ j, ((a j+b j : ℕ) : ℝ)=(L : ℝ) := by exact_mod_cast hL
  have hL0 : (0 : ℝ)<L := by exact_mod_cast hLpos
  have hs0 (j : Fin 4) : (0 : ℝ)<(a j+b j : ℕ) := by exact_mod_cast hArc j
  obtain ⟨hp,hsum⟩ := ENNReal.one_le_ofReal_div_and_sum_inv_toReal_eq_one
    (fun j => ((a j+b j : ℕ) : ℝ)) hsSum hL0 hs0
  exact (norm_coefficientCrossingTraceMultilinear_le_prod_schattenNorm A B hA hB
    (fun j => ENNReal.ofReal ((L : ℝ)/(a j+b j : ℕ))) hp hsum _).trans
      (mul_le_mul_of_nonneg_left
        (prod_schattenNorm_resolvent_mixed_powers_le_sum_trace X hX ζ a b hL hLpos hArc)
        (by positivity))

end NLAlib
