import NLAlib.Polynomial.OrthogonalPolynomials.MomentTruncation
import NLAlib.Polynomial.OrthogonalPolynomials.PositiveMomentFunctional
import NLAlib.Polynomial.OrthogonalPolynomials.UniformContinuity
import NLAlib.Polynomial.Quadrature.GaussContinuity
import NLAlib.Polynomial.Quadrature.GaussMeasure
import NLAlib.Matrix.Norms.Continuity

/-!
# Continuity of measure orthogonal polynomials and Gauss rules

Convergence of the first `2n` moments of actual positive measures gives
coefficient, recurrence, bounded-set polynomial, Jacobi matrix, and canonical
Gauss node and weight convergence. Only the limiting measure needs support
nondegeneracy; early singular moment systems use the total definitions.
Source: Gautschi (2004), §2.1; operator re-derivations AQ22–AQ23.
-/

noncomputable section
open Polynomial MeasureTheory Filter Set
open scoped Topology
namespace NLAlib

variable {ι : Type*} {l : Filter ι} {μs : ι → Measure ℝ} {μ : Measure ℝ}
  {n : ℕ}

/-- Convergence of the finitely many monomial moments is exactly convergence
of the finite moment coordinate vector; higher moments need not converge. -/
theorem tendsto_finiteMomentVector_polynomialIntegral
    (hμs : ∀ N, HasPolynomialMoments (μs N)) (hμ : HasPolynomialMoments μ)
    (hm : ∀ k < 2*n, Tendsto (fun N => ∫ x : ℝ, x^k ∂μs N) l
      (𝓝 (∫ x : ℝ, x^k ∂μ))) :
    Tendsto (fun N => finiteMomentVector (polynomialIntegral (μs N) (hμs N)) n)
      l (𝓝 (finiteMomentVector (polynomialIntegral μ hμ) n)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  simpa only [finiteMomentVector, polynomialIntegral_apply, eval_pow, eval_X] using
    hm i.val i.isLt

private theorem finiteMomentFunctional_measure_posDef (hμ : HasPolynomialMoments μ)
    (hn : (n : ℕ∞) ≤ μ.support.encard) :
    (hankelMomentMatrix
      (finiteMomentFunctional (finiteMomentVector (polynomialIntegral μ hμ) n)) n).PosDef := by
  rw [hankelMomentMatrix_finiteMomentVector_eq _ le_rfl]
  exact (posDef_hankelMomentMatrix_iff_le_support_encard μ hμ n).mpr hn

/-- Every coefficient of each canonical measure polynomial through order `n`
converges from just the first `2n` moments. The limiting support may have
exactly `n` points, including the terminal atomic polynomial.
Source: AQ22, finite Hankel inversion.
atlas: recurrence-coefficient-continuity (partial) -/
theorem tendsto_coeff_monicOrthogonalPolynomial_of_moment_convergence
    (hμs : ∀ N, HasPolynomialMoments (μs N)) (hμ : HasPolynomialMoments μ)
    (hm : ∀ j < 2*n, Tendsto (fun N => ∫ x : ℝ, x^j ∂μs N) l
      (𝓝 (∫ x : ℝ, x^j ∂μ))) (hn : (n : ℕ∞) ≤ μ.support.encard)
    {k : ℕ} (hk : k ≤ n) (j : ℕ) :
    Tendsto (fun N => (monicOrthogonalPolynomial
      (polynomialIntegral (μs N) (hμs N)) k).coeff j) l
      (𝓝 ((monicOrthogonalPolynomial (polynomialIntegral μ hμ) k).coeff j)) := by
  let m := finiteMomentVector (polynomialIntegral μ hμ) n
  have hpos := finiteMomentFunctional_measure_posDef hμ hn
  have hcont := (contDiffAt_coeff_monicOrthogonalPolynomial_finiteMomentFunctional
    (m := m) (r := 1) (hankelMomentDet_ne_zero_of_posDef_of_le hpos hk) j).continuousAt
  have h := hcont.tendsto.comp (tendsto_finiteMomentVector_polynomialIntegral hμs hμ hm)
  simpa only [Function.comp_def, m, monicOrthogonalPolynomial_finiteMomentVector_eq _ hk] using h

/-- Included squared monic norms converge under finite moment convergence.
No positivity is imposed on early approximating moment systems.
Source: AQ22, finite polynomial moment pairing.
atlas: recurrence-coefficient-continuity (partial) -/
theorem tendsto_orthogonalPolynomialNorm_of_moment_convergence
    (hμs : ∀ N, HasPolynomialMoments (μs N)) (hμ : HasPolynomialMoments μ)
    (hm : ∀ j < 2*n, Tendsto (fun N => ∫ x : ℝ, x^j ∂μs N) l
      (𝓝 (∫ x : ℝ, x^j ∂μ))) (hn : (n : ℕ∞) ≤ μ.support.encard)
    {k : ℕ} (hk : k < n) :
    Tendsto (fun N => orthogonalPolynomialNorm (polynomialIntegral (μs N) (hμs N)) k)
      l (𝓝 (orthogonalPolynomialNorm (polynomialIntegral μ hμ) k)) := by
  let m := finiteMomentVector (polynomialIntegral μ hμ) n
  have hpos := finiteMomentFunctional_measure_posDef hμ hn
  have hcont := (contDiffAt_orthogonalPolynomialNorm
    (L := fun v : Fin (2*n) → ℝ => finiteMomentFunctional v) (x := m) (r := 1)
    (fun j => (contDiff_finiteMomentFunctional_apply (X^j)).contDiffAt)
    (hankelMomentDet_ne_zero_of_posDef_of_le hpos hk.le)).continuousAt
  have h := hcont.tendsto.comp (tendsto_finiteMomentVector_polynomialIntegral hμs hμ hm)
  simpa only [Function.comp_def, m, orthogonalPolynomialNorm_finiteMomentVector_eq _ hk] using h

/-- Included monic diagonal recurrence coefficients of actual measures
converge from the first `2n` moments.
Source: AQ22, positive-norm moment quotient.
atlas: recurrence-coefficient-continuity (partial) -/
theorem tendsto_orthogonalRecurrenceAlpha_of_moment_convergence
    (hμs : ∀ N, HasPolynomialMoments (μs N)) (hμ : HasPolynomialMoments μ)
    (hm : ∀ j < 2*n, Tendsto (fun N => ∫ x : ℝ, x^j ∂μs N) l
      (𝓝 (∫ x : ℝ, x^j ∂μ))) (hn : (n : ℕ∞) ≤ μ.support.encard)
    {k : ℕ} (hk : k < n) :
    Tendsto (fun N => orthogonalRecurrenceAlpha (polynomialIntegral (μs N) (hμs N)) k)
      l (𝓝 (orthogonalRecurrenceAlpha (polynomialIntegral μ hμ) k)) := by
  let m := finiteMomentVector (polynomialIntegral μ hμ) n
  have hpos := finiteMomentFunctional_measure_posDef hμ hn
  have hcont := (contDiffAt_orthogonalRecurrenceAlpha_finiteMomentFunctional
    (m := m) (r := 1) (hankelMomentDet_ne_zero_of_posDef_of_le hpos hk.le)
    (orthogonalPolynomialNorm_pos_of_posDef hpos hk).ne').continuousAt
  have h := hcont.tendsto.comp (tendsto_finiteMomentVector_polynomialIntegral hμs hμ hm)
  simpa only [Function.comp_def, m, orthogonalRecurrenceAlpha_finiteMomentVector_eq _ hk] using h

/-- Included monic subdiagonal recurrence coefficients of actual measures
converge from finitely many moments. The library's order-zero coefficient is
the constant zero boundary; the zeroth moment is covered by the moment hypothesis.
Source: AQ22, successive positive-norm quotient.
atlas: recurrence-coefficient-continuity (partial) -/
theorem tendsto_orthogonalRecurrenceBeta_of_moment_convergence
    (hμs : ∀ N, HasPolynomialMoments (μs N)) (hμ : HasPolynomialMoments μ)
    (hm : ∀ j < 2*n, Tendsto (fun N => ∫ x : ℝ, x^j ∂μs N) l
      (𝓝 (∫ x : ℝ, x^j ∂μ))) (hn : (n : ℕ∞) ≤ μ.support.encard)
    {k : ℕ} (hk : k < n) :
    Tendsto (fun N => orthogonalRecurrenceBeta (polynomialIntegral (μs N) (hμs N)) k)
      l (𝓝 (orthogonalRecurrenceBeta (polynomialIntegral μ hμ) k)) := by
  let m := finiteMomentVector (polynomialIntegral μ hμ) n
  have hpos := finiteMomentFunctional_measure_posDef hμ hn
  have hprev : k-1 < n := by omega
  have hcont := (contDiffAt_orthogonalRecurrenceBeta_finiteMomentFunctional
    (m := m) (r := 1) (hankelMomentDet_ne_zero_of_posDef_of_le hpos hk.le)
    (hankelMomentDet_ne_zero_of_posDef_of_le hpos hprev.le)
    (orthogonalPolynomialNorm_pos_of_posDef hpos hprev).ne').continuousAt
  have h := hcont.tendsto.comp (tendsto_finiteMomentVector_polynomialIntegral hμs hμ hm)
  simpa only [Function.comp_def, m, orthogonalRecurrenceBeta_finiteMomentVector_eq _ hk] using h

/-- Canonical measure monic polynomials through order `n` converge uniformly
on every bounded real set, using only the first `2n` moments.
Source: AQ22, the finite coefficient majorant on bounded evaluation sets.
atlas: recurrence-coefficient-continuity (partial) -/
theorem tendstoUniformlyOn_monicOrthogonalPolynomial_of_moment_convergence
    (hμs : ∀ N, HasPolynomialMoments (μs N)) (hμ : HasPolynomialMoments μ)
    (hm : ∀ j < 2*n, Tendsto (fun N => ∫ x : ℝ, x^j ∂μs N) l
      (𝓝 (∫ x : ℝ, x^j ∂μ))) (hn : (n : ℕ∞) ≤ μ.support.encard)
    {k : ℕ} (hk : k ≤ n) {s : Set ℝ} {R : ℝ} (hR : ∀ t ∈ s, |t| ≤ R) :
    TendstoUniformlyOn (fun N t => (monicOrthogonalPolynomial
      (polynomialIntegral (μs N) (hμs N)) k).eval t)
      (monicOrthogonalPolynomial (polynomialIntegral μ hμ) k).eval l s := by
  let m := finiteMomentVector (polynomialIntegral μ hμ) n
  have hpos := finiteMomentFunctional_measure_posDef hμ hn
  have hU := tendstoUniformlyOn_monicOrthogonalPolynomial
    (L := fun v : Fin (2*n) → ℝ => finiteMomentFunctional v) (x := m)
    (fun j => (contDiff_finiteMomentFunctional_apply (X^j)).contDiffAt)
    (hankelMomentDet_ne_zero_of_posDef_of_le hpos hk) hR
  rw [Metric.tendstoUniformlyOn_iff] at hU ⊢
  intro ε hε
  have h := (tendsto_finiteMomentVector_polynomialIntegral hμs hμ hm).eventually (hU ε hε)
  simpa only [m, monicOrthogonalPolynomial_finiteMomentVector_eq _ hk] using h

/-- In particular, finite moment convergence gives uniform convergence of the
canonical order-`n` measure polynomial on each fixed compact real interval.
Source: AQ22, the compact interval statement of Gautschi's continuity theorem.
atlas: recurrence-coefficient-continuity (partial) -/
theorem tendstoUniformlyOn_monicOrthogonalPolynomial_Icc_of_moment_convergence
    (hμs : ∀ N, HasPolynomialMoments (μs N)) (hμ : HasPolynomialMoments μ)
    (hm : ∀ j < 2*n, Tendsto (fun N => ∫ x : ℝ, x^j ∂μs N) l
      (𝓝 (∫ x : ℝ, x^j ∂μ))) (hn : (n : ℕ∞) ≤ μ.support.encard) (a b : ℝ) :
    TendstoUniformlyOn (fun N t => (monicOrthogonalPolynomial
      (polynomialIntegral (μs N) (hμs N)) n).eval t)
      (monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).eval l (Icc a b) := by
  apply tendstoUniformlyOn_monicOrthogonalPolynomial_of_moment_convergence hμs hμ hm hn le_rfl
    (R := max |a| |b|)
  intro t ht
  apply abs_le.mpr
  constructor
  · have h := neg_le_neg (le_max_left |a| |b|)
    exact h.trans ((neg_abs_le a).trans ht.1)
  · exact ht.2.trans ((le_abs_self b).trans (le_max_right |a| |b|))

/-- Canonically indexed Gauss nodes of actual positive measures converge
under finite moment convergence. The indexing uses ordered Hermitian eigenvalues.
Source: AQ23, ordered Jacobi eigenvalue continuity.
atlas: recurrence-coefficient-continuity (partial) -/
theorem tendsto_gaussNodes_of_moment_convergence
    (hμs : ∀ N, HasPolynomialMoments (μs N)) (hμ : HasPolynomialMoments μ)
    (hm : ∀ j < 2*n, Tendsto (fun N => ∫ x : ℝ, x^j ∂μs N) l
      (𝓝 (∫ x : ℝ, x^j ∂μ))) (hn : (n : ℕ∞) ≤ μ.support.encard) (i : Fin n) :
    Tendsto (fun N => gaussNodes (μs N) (hμs N) n i) l (𝓝 (gaussNodes μ hμ n i)) := by
  let m := finiteMomentVector (polynomialIntegral μ hμ) n
  have hpos := finiteMomentFunctional_measure_posDef hμ hn
  have hcont := continuousAt_eigenvalues_orthogonalPolynomialJacobiMatrix
    (L := fun v : Fin (2*n) → ℝ => finiteMomentFunctional v) (x := m)
    (fun j => (contDiff_finiteMomentFunctional_apply (X^j)).contDiffAt)
    (fun k hk => hankelMomentDet_ne_zero_of_posDef_of_le hpos hk.le)
    (fun k hk => orthogonalPolynomialNorm_pos_of_posDef hpos hk) i
  have h := hcont.tendsto.comp (tendsto_finiteMomentVector_polynomialIntegral hμs hμ hm)
  change Tendsto (fun N => momentGaussNodes (finiteMomentFunctional
    (finiteMomentVector (polynomialIntegral (μs N) (hμs N)) n)) n i) l
    (𝓝 (momentGaussNodes (finiteMomentFunctional m) n i)) at h
  simpa only [m, momentGaussNodes_finiteMomentVector_eq, gaussNodes] using h

/-- Canonical integrated-cardinal Gauss weights of actual positive measures
converge from the first `2n` moments. No continuous eigenvector choice is assumed.
Source: AQ23, continuous cardinal polynomials at distinct limiting nodes.
atlas: recurrence-coefficient-continuity (partial) -/
theorem tendsto_gaussWeights_of_moment_convergence
    (hμs : ∀ N, HasPolynomialMoments (μs N)) (hμ : HasPolynomialMoments μ)
    (hm : ∀ j < 2*n, Tendsto (fun N => ∫ x : ℝ, x^j ∂μs N) l
      (𝓝 (∫ x : ℝ, x^j ∂μ))) (hn : (n : ℕ∞) ≤ μ.support.encard) (i : Fin n) :
    Tendsto (fun N => gaussWeights (μs N) (hμs N) n i) l (𝓝 (gaussWeights μ hμ n i)) := by
  let m := finiteMomentVector (polynomialIntegral μ hμ) n
  have hpos := finiteMomentFunctional_measure_posDef hμ hn
  have hcont := continuousAt_momentGaussWeights
    (L := fun v : Fin (2*n) → ℝ => finiteMomentFunctional v) (x := m)
    (fun j => (contDiff_finiteMomentFunctional_apply (X^j)).contDiffAt)
    (fun k hk => hankelMomentDet_ne_zero_of_posDef_of_le hpos hk)
    (fun k hk => orthogonalPolynomialNorm_pos_of_posDef hpos hk) i
  have h := hcont.tendsto.comp (tendsto_finiteMomentVector_polynomialIntegral hμs hμ hm)
  simpa only [Function.comp_def, m, momentGaussWeights_finiteMomentVector_eq, gaussWeights] using h

/-- The finite Hankel determinant of actual measures converges from their first
`2n` moments, including singular limiting systems and the empty determinant.
atlas: recurrence-coefficient-continuity (partial) -/
theorem tendsto_hankelMomentDet_of_moment_convergence
    (hμs : ∀ N, HasPolynomialMoments (μs N)) (hμ : HasPolynomialMoments μ)
    (hm : ∀ j < 2*n, Tendsto (fun N => ∫ x : ℝ, x^j ∂μs N) l
      (𝓝 (∫ x : ℝ, x^j ∂μ))) :
    Tendsto (fun N => hankelMomentDet (polynomialIntegral (μs N) (hμs N)) n)
      l (𝓝 (hankelMomentDet (polynomialIntegral μ hμ) n)) := by
  have hc : Continuous (fun v : Fin (2*n) → ℝ =>
      hankelMomentDet (finiteMomentFunctional v) n) := by
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (contDiff_finiteMomentFunctional_apply (r := 1) (X^(i.val+j.val))).continuous
  have h := hc.continuousAt.tendsto.comp
    (tendsto_finiteMomentVector_polynomialIntegral hμs hμ hm)
  simpa only [Function.comp_def, hankelMomentDet,
    hankelMomentMatrix_finiteMomentVector_eq _ le_rfl] using h

/-- Support nondegeneracy of the limiting measure makes the actual approximating
Hankel systems eventually positive definite. Early measures may have too few
support points; this conclusion is derived from moment convergence.
Source: AQ22, openness of finite moment nondegeneracy within positive measures.
atlas: recurrence-coefficient-continuity (partial) -/
theorem eventually_posDef_hankelMomentMatrix_of_moment_convergence
    (hμs : ∀ N, HasPolynomialMoments (μs N)) (hμ : HasPolynomialMoments μ)
    (hm : ∀ j < 2*n, Tendsto (fun N => ∫ x : ℝ, x^j ∂μs N) l
      (𝓝 (∫ x : ℝ, x^j ∂μ))) (hn : (n : ℕ∞) ≤ μ.support.encard) :
    ∀ᶠ N in l, (hankelMomentMatrix (polynomialIntegral (μs N) (hμs N)) n).PosDef := by
  have hdet : 0 < hankelMomentDet (polynomialIntegral μ hμ) n :=
    (hankelMomentDet_pos_iff_le_support_encard μ hμ n).mpr hn
  filter_upwards [(tendsto_hankelMomentDet_of_moment_convergence hμs hμ hm).eventually
    (eventually_gt_nhds hdet)] with N hN
  exact (posDef_hankelMomentMatrix_iff_det_pos (μs N) (hμs N) n).mpr hN

/-- The actual normalized measure Jacobi matrices converge in spectral distance
from just the first `2n` moments.
Source: AQ23, entrywise continuity in finite dimension and named norm continuity.
atlas: recurrence-coefficient-continuity (partial) -/
theorem tendsto_specNorm_orthogonalPolynomialJacobiMatrix_sub_of_moment_convergence
    (hμs : ∀ N, HasPolynomialMoments (μs N)) (hμ : HasPolynomialMoments μ)
    (hm : ∀ j < 2*n, Tendsto (fun N => ∫ x : ℝ, x^j ∂μs N) l
      (𝓝 (∫ x : ℝ, x^j ∂μ))) (hn : (n : ℕ∞) ≤ μ.support.encard) :
    Tendsto (fun N => specNorm
      (orthogonalPolynomialJacobiMatrix (polynomialIntegral (μs N) (hμs N)) n -
        orthogonalPolynomialJacobiMatrix (polynomialIntegral μ hμ) n)) l (𝓝 0) := by
  let m := finiteMomentVector (polynomialIntegral μ hμ) n
  have hpos := finiteMomentFunctional_measure_posDef hμ hn
  have hentry := continuousAt_orthogonalPolynomialJacobiMatrix_apply
    (L := fun v : Fin (2*n) → ℝ => finiteMomentFunctional v) (x := m)
    (fun j => (contDiff_finiteMomentFunctional_apply (X^j)).contDiffAt)
    (fun k hk => hankelMomentDet_ne_zero_of_posDef_of_le hpos hk.le)
    (fun k hk => orthogonalPolynomialNorm_pos_of_posDef hpos hk)
  have hc := continuousAt_specNorm_of_entrywise
    (A := fun v : Fin (2*n) → ℝ => orthogonalPolynomialJacobiMatrix (finiteMomentFunctional v) n -
      orthogonalPolynomialJacobiMatrix (finiteMomentFunctional m) n)
    (fun i j => (hentry i j).sub continuousAt_const)
  have h := hc.tendsto.comp (tendsto_finiteMomentVector_polynomialIntegral hμs hμ hm)
  simpa only [Function.comp_def, m, orthogonalPolynomialJacobiMatrix_finiteMomentVector_eq,
    sub_self, specNorm_zero] using h

end NLAlib
