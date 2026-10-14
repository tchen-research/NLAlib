import NLAlib.Polynomial.OrthogonalPolynomials.NormSensitivity
import NLAlib.Polynomial.OrthogonalPolynomials.MeasureOrthogonality

/-!
# First variation of finite orthogonality equations

Differentiating the actual nonsingular moment-system equations gives the lower
orthogonal coefficients of the polynomial variation. Source: AQ27 in the operator
re-derivations, Gautschi (2004), §2.1.
-/

noncomputable section
open Polynomial Filter Topology
namespace NLAlib

/-- The first variation of the canonical monic polynomial paired against a fixed
lower-degree polynomial is the negative variation of its moment pairing.
This follows from the actual orthogonality equations on an open nonsingular
neighborhood. Source: AQ27.
atlas: recurrence-coefficient-moment-sensitivity (partial) -/
theorem functional_monicOrthogonalPolynomialDeriv_mul_eq_neg
    {L : ℝ → (ℝ[X] →ₗ[ℝ] ℝ)} {D : ℝ[X] →ₗ[ℝ] ℝ} {n : ℕ} {x : ℝ}
    (hL : ∀ k, ContDiffAt ℝ 1 (fun y => L y (X ^ k)) x)
    (hD : ∀ k, HasDerivAt (fun y => L y (X ^ k)) (D (X ^ k)) x)
    (hn : hankelMomentDet (L x) n ≠ 0) {q : ℝ[X]} (hq : q.degree < n) :
    L x (monicOrthogonalPolynomialDeriv L n x * q) =
      -D (monicOrthogonalPolynomial (L x) n * q) := by
  let P := fun y => monicOrthogonalPolynomial (L y) n
  let V := monicOrthogonalPolynomialDeriv L n x
  have hP := hasPolynomialDerivAt_monicOrthogonalPolynomial hL hn
  have hVdeg : V.degree ≤ n := (degree_monicOrthogonalPolynomialDeriv_lt L n x).le
  have hPdeg (y : ℝ) : (P y).degree = n := by
    rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial (L y) n).ne_zero,
      natDegree_monicOrthogonalPolynomial]
  have hnn : (n : WithBot ℕ) + n < ((2 * n + 1 : ℕ) : WithBot ℕ) := by
    exact_mod_cast (show n + n < 2 * n + 1 by omega)
  have hpoly := hP.mul (hasCoeffDerivAt_const q x)
  simp only [mul_zero, add_zero] at hpoly
  have hder := hasDerivAt_functional_polynomial (d := 2 * n + 1)
    (p := fun y => P y * q) (p' := V * q)
    (by intro y; apply (degree_mul_le _ _).trans_lt; rw [hPdeg];
        exact (add_le_add le_rfl hq.le).trans_lt hnn)
    ((degree_mul_le _ _).trans_lt ((add_le_add hVdeg hq.le).trans_lt hnn)) hpoly hD
  have hdet : ContinuousAt (fun y => hankelMomentDet (L y) n) x :=
    (ContDiffAt.matrix_det (A := fun y => hankelMomentMatrix (L y) n)
      (fun i j => hL (i.val + j.val))).continuousAt
  have heq : (fun y => L y (P y * q)) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hdet.eventually_ne hn] with y hy
    exact (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial (L y) hy).orthogonal q hq
  have hzero : HasDerivAt (fun y => L y (P y * q)) 0 x :=
    (hasDerivAt_const x 0).congr_of_eventuallyEq heq
  have hsum := hder.unique hzero
  linarith

/-- The actual first variation expands in the lower monic orthogonal basis with
the differentiated moment pairings as coefficients. Source: AQ27.
atlas: recurrence-coefficient-moment-sensitivity (partial) -/
theorem monicOrthogonalPolynomialDeriv_eq_sum
    {L : ℝ → (ℝ[X] →ₗ[ℝ] ℝ)} {D : ℝ[X] →ₗ[ℝ] ℝ} {n : ℕ} {x : ℝ}
    (hL : ∀ k, ContDiffAt ℝ 1 (fun y => L y (X ^ k)) x)
    (hD : ∀ k, HasDerivAt (fun y => L y (X ^ k)) (D (X ^ k)) x)
    (hn : ∀ k ≤ n, hankelMomentDet (L x) k ≠ 0)
    (hh : ∀ k < n, orthogonalPolynomialNorm (L x) k ≠ 0) :
    monicOrthogonalPolynomialDeriv L n x =
      -∑ i ∈ Finset.range n,
        (D (monicOrthogonalPolynomial (L x) n * monicOrthogonalPolynomial (L x) i) /
          orthogonalPolynomialNorm (L x) i) • monicOrthogonalPolynomial (L x) i := by
  obtain ⟨c, hc⟩ := exists_sum_smul_monicOrthogonalPolynomial_eq_of_degree_lt (L x)
    (degree_monicOrthogonalPolynomialDeriv_lt L n x)
  have hcoeff (j : ℕ) (hj : j < n) : c j =
      -D (monicOrthogonalPolynomial (L x) n * monicOrthogonalPolynomial (L x) j) /
        orthogonalPolynomialNorm (L x) j := by
    have hjdeg : (monicOrthogonalPolynomial (L x) j).degree < n := by
      rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial (L x) j).ne_zero,
        natDegree_monicOrthogonalPolynomial]
      exact_mod_cast hj
    have hp := functional_monicOrthogonalPolynomialDeriv_mul_eq_neg hL hD
      (hn n le_rfl) hjdeg
    rw [← hc] at hp
    simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, smul_eq_mul] at hp
    have hsum : (∑ i ∈ Finset.range n, c i *
        L x (monicOrthogonalPolynomial (L x) i * monicOrthogonalPolynomial (L x) j)) =
        c j * orthogonalPolynomialNorm (L x) j := by
      rw [Finset.sum_eq_single j]
      · simp [orthogonalPolynomialNorm, pow_two]
      · intro i hi hij
        rw [functional_monicOrthogonalPolynomial_mul_eq_zero_of_ne (L x)
          (hn i (Finset.mem_range.mp hi).le) (hn j hj.le) hij, mul_zero]
      · exact fun h => (h (Finset.mem_range.mpr hj)).elim
    rw [hsum] at hp
    exact (eq_div_iff (hh j hj)).mpr hp
  rw [← hc, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hcoeff i (Finset.mem_range.mp hi), neg_div, neg_smul]

end NLAlib
