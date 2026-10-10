import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import NLAlib.Matrix.PolynomialCalculus

/-!
# The spectral measure of a symmetric matrix and a vector

For a real symmetric (Hermitian) matrix `A` with eigenpairs `(λᵢ, uᵢ)` (Mathlib's
`hA.eigenvalues`, `hA.eigenvectorBasis`) and a vector `v`, the spectral measure is the finite
atomic measure `μ_v = ∑ᵢ (uᵢ ⬝ v)² δ_{λᵢ}` on `ℝ`. Its defining property is
`∫ f dμ_v = vᵀ f(A) v` for every `f : ℝ → ℝ`, where `f(A) = cfc f A` is Mathlib's continuous
functional calculus (every function is continuous on the finite spectrum).

## Main results

* `NLAlib.dotProduct_cfc_mulVec_eq_sum`: `vᵀ f(A) v = ∑ᵢ f(λᵢ) (uᵢ ⬝ v)²` (eigen-expansion for
  an arbitrary function; the polynomial case is `NLAlib.dotProduct_aeval_mulVec_eq_sum`).
* `NLAlib.spectralMeasure`, `NLAlib.integral_spectralMeasure`: `∫ f dμ_v = vᵀ f(A) v`.
* `NLAlib.integral_eval_spectralMeasure`, `NLAlib.integral_pow_spectralMeasure`:
  polynomial and moment forms, `∫ p dμ_v = vᵀ p(A) v`, `∫ xᵏ dμ_v = vᵀ Aᵏ v`.
* `NLAlib.spectralMeasure_univ`: total mass `‖v‖²`; `NLAlib.spectralMeasure_compl_range_eigenvalues`:
  the measure lives on the eigenvalues.

The Hutchinson clause `𝔼_g[gᵀ f(A) g] = tr f(A)` of the atlas entry is `hutchinson-unbiased`
applied to `f(A)` and lives in `NLAlib.Estimation.Unbiased` (layer 4).

Source: Golub–Meurant (2010) [`gm10`], Ch. 7 (Riemann–Stieltjes integral form of `uᵀ f(A) u`);
Ubaru–Chen–Saad (2017) [`ucs17`], §2. Atlas: `spectral-measure`.
-/

noncomputable section

open scoped Matrix
open MeasureTheory Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Eigen-expansion of a quadratic form of a matrix function: for symmetric `A`,
`vᵀ f(A) v = ∑ᵢ f(λᵢ) (uᵢ ⬝ v)²` with `(λᵢ, uᵢ)` the eigenpairs of `A`.
Source: Golub–Meurant (2010) [`gm10`], Ch. 7, eq. (7.1). Atlas: `spectral-measure` (helper;
belongs with the polynomial calculus in `NLAlib.Matrix`). -/
theorem dotProduct_cfc_mulVec_eq_sum {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ)
    (v : n → ℝ) :
    v ⬝ᵥ (cfc f A *ᵥ v) =
      ∑ i, f (hA.eigenvalues i) * ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ v) ^ 2 := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have h1 : v ᵥ* (hA.eigenvectorUnitary : Matrix n n ℝ) =
      fun i => (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ v := by
    ext i; simp [Matrix.vecMul, dotProduct, mul_comm]
  have h2 : (star (hA.eigenvectorUnitary : Matrix n n ℝ)) *ᵥ v =
      fun i => (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ v := by
    ext i; simp [Matrix.mulVec, dotProduct, Matrix.star_apply]
  rw [h1, h2]
  simp only [dotProduct, Matrix.mulVec_diagonal, Function.comp_apply, RCLike.ofReal_real_eq_id,
    id]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The spectral measure `μ_v = ∑ᵢ (uᵢ ⬝ v)² δ_{λᵢ}` of a symmetric matrix `A` and a vector `v`.
Source: Golub–Meurant (2010) [`gm10`], Ch. 7 (the measure `α(λ)` of the Riemann–Stieltjes
integral); Ubaru–Chen–Saad (2017) [`ucs17`], §2. Atlas: `spectral-measure`.
Deviation: indexed by Mathlib's eigenvalue enumeration, so repeated eigenvalues give repeated
atoms (the measure is the same). -/
def spectralMeasure {A : Matrix n n ℝ} (hA : A.IsHermitian) (v : n → ℝ) : Measure ℝ :=
  ∑ i, ENNReal.ofReal (((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ v) ^ 2) •
    Measure.dirac (hA.eigenvalues i)

/-- The spectral measure has total mass `‖v‖² = v ⬝ v`. Source: [`gm10`], Ch. 7.
Atlas: `spectral-measure`. -/
theorem spectralMeasure_univ {A : Matrix n n ℝ} (hA : A.IsHermitian) (v : n → ℝ) :
    spectralMeasure hA v Set.univ = ENNReal.ofReal (v ⬝ᵥ v) := by
  rw [← sum_sq_eigenvectorBasis_dotProduct hA v, spectralMeasure,
    ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
  simp

/-- The spectral measure is finite. Atlas: `spectral-measure`. -/
instance isFiniteMeasure_spectralMeasure {A : Matrix n n ℝ} (hA : A.IsHermitian) (v : n → ℝ) :
    IsFiniteMeasure (spectralMeasure hA v) :=
  ⟨by rw [spectralMeasure_univ]; exact ENNReal.ofReal_lt_top⟩

/-- The spectral measure is carried by the eigenvalues: the complement of
`Set.range hA.eigenvalues` is null. Source: [`gm10`], Ch. 7. Atlas: `spectral-measure`. -/
theorem spectralMeasure_compl_range_eigenvalues {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (v : n → ℝ) : spectralMeasure hA v (Set.range hA.eigenvalues)ᶜ = 0 := by
  simp only [spectralMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Measure.dirac_apply, Set.indicator_of_notMem (by simp), mul_zero]

/-- **Defining property of the spectral measure**: for symmetric `A`, any `v` and any
`f : ℝ → ℝ`, `∫ f dμ_v = vᵀ f(A) v` with `f(A) = cfc f A`.
Source: Golub–Meurant (2010) [`gm10`], Ch. 7, eq. (7.1)–(7.2); Ubaru–Chen–Saad (2017)
[`ucs17`], eq. (2). Atlas: `spectral-measure`.
Deviation: no continuity or measurability of `f` needed (the measure is atomic). -/
theorem integral_spectralMeasure {A : Matrix n n ℝ} (hA : A.IsHermitian) (v : n → ℝ)
    (f : ℝ → ℝ) : ∫ x, f x ∂spectralMeasure hA v = v ⬝ᵥ (cfc f A *ᵥ v) := by
  rw [dotProduct_cfc_mulVec_eq_sum hA f v, spectralMeasure,
    integral_finsetSum_measure fun i _ =>
      (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul,
    mul_comm]

/-- Polynomial form: `∫ p dμ_v = vᵀ p(A) v` for every real polynomial `p`.
Source: Golub–Meurant (2010) [`gm10`], Ch. 7. Atlas: `spectral-measure`. -/
theorem integral_eval_spectralMeasure {A : Matrix n n ℝ} (hA : A.IsHermitian) (v : n → ℝ)
    (p : Polynomial ℝ) :
    ∫ x, p.eval x ∂spectralMeasure hA v = v ⬝ᵥ (Polynomial.aeval A p *ᵥ v) := by
  rw [integral_spectralMeasure hA v, cfc_polynomial p A hA.isSelfAdjoint]

/-- Moment form: `∫ xᵏ dμ_v = vᵀ Aᵏ v`. Source: Golub–Meurant (2010) [`gm10`], Ch. 7
(the moments of the spectral measure). Atlas: `spectral-measure`. -/
theorem integral_pow_spectralMeasure {A : Matrix n n ℝ} (hA : A.IsHermitian) (v : n → ℝ)
    (k : ℕ) : ∫ x, x ^ k ∂spectralMeasure hA v = v ⬝ᵥ ((A ^ k) *ᵥ v) := by
  simpa using integral_eval_spectralMeasure hA v (Polynomial.X ^ k)

/-- Quadratic-form spelling: `∫ f dμ_v = quadForm (f(A)) v`. Atlas: `spectral-measure`. -/
theorem integral_spectralMeasure_eq_quadForm {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (v : n → ℝ) (f : ℝ → ℝ) : ∫ x, f x ∂spectralMeasure hA v = quadForm (cfc f A) v :=
  integral_spectralMeasure hA v f

end NLAlib
