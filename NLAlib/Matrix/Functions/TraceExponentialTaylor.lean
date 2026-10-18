import NLAlib.Matrix.Functions.TraceExponentialRepresentation
import NLAlib.Matrix.Functions.TraceExponentialDerivatives
import NLAlib.ForMathlib.MeasureTheory.CompactExponentialTaylor
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# One-sided and symmetric Taylor bounds for the trace exponential

Stahl's positive measure gives an exact deterministic upper Taylor bound for
an upper-bounded Hermitian perturbation. Symmetrizing opposite perturbations
gives a quadratic lower bound. These are the deterministic analytic inputs to
Tropp (2026), *Comparison theorems for the extreme eigenvalues of a random
symmetric matrix*, Section 4, and the post-BMV roadmap's first work package.
The probability-law and covariance matching steps are separate results.
-/

noncomputable section

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every even directional derivative of a Hermitian trace-exponential pencil
is nonnegative at every real parameter. Source: Stahl's theorem; Tropp (2026),
Proposition 4.4. -/
theorem iteratedDeriv_even_traceExp_add_smul_nonneg
    (A H : Matrix n n ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian)
    (r : ℕ) (t : ℝ) :
    0 ≤ iteratedDeriv (2 * r) (fun x : ℝ => traceExp (A + x • H)) t := by
  obtain ⟨ν, hν⟩ := exists_isCompactExpRepresentation_traceExp A H hA hH
  exact hν.iteratedDeriv_even_nonneg r t

/-- At nonnegative time an upper support endpoint controls every even
directional derivative. Source: Stahl's theorem; Tropp (2026), Proposition 4.4. -/
theorem iteratedDeriv_even_traceExp_add_smul_le_exp_mul_zero
    (A H : Matrix n n ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian)
    (r : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDeriv (2 * r) (fun x : ℝ => traceExp (A + x • H)) t ≤
      Real.exp (t * lambdaMax H) *
        iteratedDeriv (2 * r) (fun x : ℝ => traceExp (A + x • H)) 0 := by
  obtain ⟨ν, hν⟩ := exists_isCompactExpRepresentation_traceExp A H hA hH
  exact hν.iteratedDeriv_even_le_exp_mul_zero r ht

/-- The exact second-order integral Taylor formula for an affine matrix
trace exponential. It holds even without self-adjointness. -/
theorem traceExp_add_eq_add_deriv_add_integral_iteratedDeriv_two
    (A H : Matrix n n ℂ) :
    traceExp (A + H) = traceExp A +
      deriv (fun x : ℝ => traceExp (A + x • H)) 0 +
      ∫ t in (0 : ℝ)..1, (1 - t) *
        iteratedDeriv 2 (fun x : ℝ => traceExp (A + x • H)) t := by
  have hsmooth : ContDiff ℝ 2 (fun t : ℝ => traceExp (A + t • H)) :=
    (contDiff_traceExp (n := n) : ContDiff ℝ 2 _).comp
      (contDiff_const.add (contDiff_id.smul contDiff_const))
  simpa only [one_smul, zero_smul, add_zero] using
    eq_add_deriv_add_integral_iteratedDeriv_two hsmooth

/-- A one-sided upper bound on the direction's largest eigenvalue yields the
exact exponential-integral coefficient in the second-order Taylor upper
bound. Source: Tropp (2026), BMV one-summand replacement argument. -/
theorem traceExp_add_le_add_deriv_add_iteratedDeriv_two_mul_coefficient
    (A H : Matrix n n ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian)
    {R : ℝ} (hR : lambdaMax H ≤ R) :
    traceExp (A + H) ≤ traceExp A +
      deriv (fun x : ℝ => traceExp (A + x • H)) 0 +
      iteratedDeriv 2 (fun x : ℝ => traceExp (A + x • H)) 0 *
        expSecondRemainderCoefficient R := by
  obtain ⟨ν, hν⟩ := exists_isCompactExpRepresentation_traceExp A H hA hH
  simpa only [one_smul, zero_smul, add_zero] using
    (hν.mono le_rfl hR).le_add_deriv_add_iteratedDeriv_two_mul_coefficient

/-- The Taylor upper estimate under the original one-sided Loewner bound on
the perturbation. No lower bound on the perturbation and no sign condition
on the scalar upper bound is needed, including in empty dimension.
Source: Tropp (2026), Section 4.6. -/
theorem traceExp_add_le_add_deriv_add_iteratedDeriv_two_mul_coefficient_of_le
    (A H : Matrix n n ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian)
    {R : ℝ} (hR : H ≤ R • (1 : Matrix n n ℂ)) :
    traceExp (A + H) ≤ traceExp A +
      deriv (fun x : ℝ => traceExp (A + x • H)) 0 +
      iteratedDeriv 2 (fun x : ℝ => traceExp (A + x • H)) 0 *
        expSecondRemainderCoefficient R := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn =>
    have := hn
    have hzero (B : Matrix n n ℂ) : traceExp B = 0 := by
      simp [traceExp, Matrix.trace]
    simp [hzero]
  | inr hn =>
    have := hn
    apply traceExp_add_le_add_deriv_add_iteratedDeriv_two_mul_coefficient A H hA hH
    have hs : ∀ x ∈ spectrum ℝ H, x ≤ R := by
      apply (le_algebraMap_iff_spectrum_le hH.isSelfAdjoint).mp
      simpa only [Algebra.algebraMap_eq_smul_one] using hR
    unfold lambdaMax
    apply csSup_le _ hs
    rw [hH.spectrum_real_eq_range_eigenvalues]
    exact Set.range_nonempty _

/-- Opposite Hermitian perturbations dominate the quadratic Taylor term.
This form permits a symmetric Gaussian law to remove odd terms before
expectation, without third-derivative integrability assumptions.
Source: Tropp (2026), Gaussian lower comparison. -/
theorem two_mul_traceExp_add_iteratedDeriv_two_le_add_traceExp
    (A H : Matrix n n ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian) :
    2 * traceExp A + iteratedDeriv 2 (fun x : ℝ => traceExp (A + x • H)) 0 ≤
      traceExp (A + H) + traceExp (A - H) := by
  obtain ⟨ν, hν⟩ := exists_isCompactExpRepresentation_traceExp A H hA hH
  simpa only [zero_smul, add_zero, one_smul, neg_one_smul, sub_eq_add_neg] using
    hν.two_mul_zero_add_iteratedDeriv_two_le_add

end NLAlib
