import NLAlib.Polynomial.OrthogonalPolynomials.FiniteMomentSystem
import NLAlib.ForMathlib.Analysis.Calculus.MatrixInverse
import NLAlib.ForMathlib.Analysis.Calculus.PolynomialCoefficients

/-!
# Smooth dependence on finitely many moments

Canonical monic coefficients and recurrence coefficients are smooth wherever the
relevant finite Hankel systems and norm denominators are nonsingular. No nearby
representing measures are required. Source: Gautschi (2004), §2.1; AQ22 in the
operator re-derivations. Atlas: `recurrence-coefficient-continuity` and
`recurrence-coefficient-moment-sensitivity`.
-/

noncomputable section

open Polynomial Matrix Finset

namespace NLAlib

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {r : WithTop ℕ∞} {x : E} {L : E → (𝕜[X] →ₗ[𝕜] 𝕜)}

/-- A polynomial family with bounded degree and smooth coefficients can be
paired smoothly with a family of monomial moments. Only moments below `d`
are used. -/
theorem contDiffAt_functional_polynomial_of_degree_lt {p : E → 𝕜[X]} {d : ℕ}
    (hp : ∀ y, (p y).degree < d)
    (hc : ∀ i : Fin d, ContDiffAt 𝕜 r (fun y => (p y).coeff i.val) x)
    (hL : ∀ i : Fin d, ContDiffAt 𝕜 r (fun y => L y (X ^ i.val)) x) :
    ContDiffAt 𝕜 r (fun y => L y (p y)) x := by
  have heq : (fun y => L y (p y)) =
      fun y => ∑ i : Fin d, (p y).coeff i.val * L y (X ^ i.val) := by
    funext y
    nth_rw 1 [eq_sum_monomial_fin_of_degree_lt (hp y)]
    simp only [map_sum, ← C_mul_X_pow_eq_monomial, C_mul', map_smul, smul_eq_mul]
  rw [heq]
  exact ContDiffAt.sum (fun i _ => (hc i).mul (hL i))

/-- Smooth monomial moments give smooth finite-system polynomial coefficients
at every nonsingular order. -/
theorem contDiffAt_orthogonalPolynomialCoefficients {n : ℕ}
    (hL : ∀ k, ContDiffAt 𝕜 r (fun y => L y (X ^ k)) x)
    (hn : hankelMomentDet (L x) n ≠ 0) (i : Fin n) :
    ContDiffAt 𝕜 r (fun y => orthogonalPolynomialCoefficients (L y) n i) x := by
  unfold orthogonalPolynomialCoefficients
  simp only [Matrix.mulVec, dotProduct]
  apply ContDiffAt.sum
  intro j _
  apply ContDiffAt.mul
  · exact ContDiffAt.matrix_inv_apply (A := fun y => hankelMomentMatrix (L y) n)
      (fun k l => hL (k.val + l.val)) hn i j
  · exact (hL (n + j.val)).neg

/-- Every coefficient of the canonical monic polynomial is smooth at a
nonsingular moment system, including its constant leading coefficient. -/
theorem contDiffAt_coeff_monicOrthogonalPolynomial {n : ℕ}
    (hL : ∀ k, ContDiffAt 𝕜 r (fun y => L y (X ^ k)) x)
    (hn : hankelMomentDet (L x) n ≠ 0) (k : ℕ) :
    ContDiffAt 𝕜 r (fun y => (monicOrthogonalPolynomial (L y) n).coeff k) x := by
  simp only [monicOrthogonalPolynomial, orthogonalPolynomialLowerPart,
    coeff_add, finsetSum_coeff, coeff_monomial]
  apply ContDiffAt.add contDiffAt_const
  apply ContDiffAt.sum
  intro i _
  split_ifs
  · exact contDiffAt_orthogonalPolynomialCoefficients hL hn i
  · exact contDiffAt_const

/-- The bilinear squared norm of the canonical monic polynomial is smooth at
each nonsingular finite moment system. -/
theorem contDiffAt_orthogonalPolynomialNorm {n : ℕ}
    (hL : ∀ k, ContDiffAt 𝕜 r (fun y => L y (X ^ k)) x)
    (hn : hankelMomentDet (L x) n ≠ 0) :
    ContDiffAt 𝕜 r (fun y => orthogonalPolynomialNorm (L y) n) x := by
  unfold orthogonalPolynomialNorm
  apply contDiffAt_functional_polynomial_of_degree_lt (d := 2 * n + 1)
  · intro y
    rw [degree_pow, degree_eq_natDegree (monic_monicOrthogonalPolynomial (L y) n).ne_zero,
      natDegree_monicOrthogonalPolynomial]
    simp only [nsmul_eq_mul]
    exact_mod_cast (Nat.lt_succ_self (2 * n))
  · intro i
    simp only [pow_two]
    exact contDiffAt_coeff_mul (contDiffAt_coeff_monicOrthogonalPolynomial hL hn)
      (contDiffAt_coeff_monicOrthogonalPolynomial hL hn) i.val
  · exact fun i => hL i.val

/-- The monic diagonal recurrence coefficient is smooth wherever its finite
Hankel system and squared norm are nonzero. Source: AQ22 and the norm quotient.
atlas: recurrence-coefficient-continuity (partial), recurrence-coefficient-moment-sensitivity (partial) -/
theorem contDiffAt_orthogonalRecurrenceAlpha {n : ℕ}
    (hL : ∀ k, ContDiffAt 𝕜 r (fun y => L y (X ^ k)) x)
    (hn : hankelMomentDet (L x) n ≠ 0)
    (hh : orthogonalPolynomialNorm (L x) n ≠ 0) :
    ContDiffAt 𝕜 r (fun y => orthogonalRecurrenceAlpha (L y) n) x := by
  unfold orthogonalRecurrenceAlpha
  apply ContDiffAt.div _ (contDiffAt_orthogonalPolynomialNorm hL hn) hh
  apply contDiffAt_functional_polynomial_of_degree_lt (d := 2 * n + 2)
  · intro y
    rw [degree_mul, degree_X, degree_pow,
      degree_eq_natDegree (monic_monicOrthogonalPolynomial (L y) n).ne_zero,
      natDegree_monicOrthogonalPolynomial]
    simp only [nsmul_eq_mul]
    exact_mod_cast (show 1 + 2 * n < 2 * n + 2 by omega)
  · intro i
    apply contDiffAt_coeff_mul (fun _ => contDiffAt_const)
    intro k
    simp only [pow_two]
    exact contDiffAt_coeff_mul (contDiffAt_coeff_monicOrthogonalPolynomial hL hn)
      (contDiffAt_coeff_monicOrthogonalPolynomial hL hn) k
  · exact fun i => hL i.val

/-- Positive-order monic subdiagonal recurrence coefficients depend smoothly on
the moments. The boundary coefficient at order zero is constantly zero.
atlas: recurrence-coefficient-continuity (partial), recurrence-coefficient-moment-sensitivity (partial) -/
theorem contDiffAt_orthogonalRecurrenceBeta {n : ℕ}
    (hL : ∀ k, ContDiffAt 𝕜 r (fun y => L y (X ^ k)) x)
    (hn : hankelMomentDet (L x) n ≠ 0)
    (hprev : hankelMomentDet (L x) (n - 1) ≠ 0)
    (hh : orthogonalPolynomialNorm (L x) (n - 1) ≠ 0) :
    ContDiffAt 𝕜 r (fun y => orthogonalRecurrenceBeta (L y) n) x := by
  unfold orthogonalRecurrenceBeta
  split_ifs
  · exact contDiffAt_const
  · exact (contDiffAt_orthogonalPolynomialNorm hL hn).div
      (contDiffAt_orthogonalPolynomialNorm hL hprev) hh

end NLAlib

namespace NLAlib

/-- Bounded-degree polynomial pairings are continuous when their finitely many
coefficients and monomial moments are continuous. -/
theorem continuousAt_functional_polynomial_of_degree_lt
    {T : Type*} [TopologicalSpace T] {a : T}
    {L : T → (ℝ[X] →ₗ[ℝ] ℝ)} {p : T → ℝ[X]} {d : ℕ}
    (hp : ∀ y, (p y).degree < d)
    (hc : ∀ i : Fin d, ContinuousAt (fun y => (p y).coeff i.val) a)
    (hL : ∀ i : Fin d, ContinuousAt (fun y => L y (X ^ i.val)) a) :
    ContinuousAt (fun y => L y (p y)) a := by
  have heq : (fun y => L y (p y)) =
      fun y => ∑ i : Fin d, (p y).coeff i.val * L y (X ^ i.val) := by
    funext y
    nth_rw 1 [eq_sum_monomial_fin_of_degree_lt (hp y)]
    simp only [map_sum, ← C_mul_X_pow_eq_monomial, C_mul', map_smul, smul_eq_mul]
  rw [heq]
  exact tendsto_finsetSum _ (fun i _ => (hc i).mul (hL i))

end NLAlib
