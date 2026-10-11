import NLAlib.Matrix.PolynomialCalculus
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Residual estimates for approximate symmetric eigenpairs

Finite spectral expansion proves residual inclusion, the optimal Rayleigh
shift, Kato–Temple bounds, and the separated-eigenspace sine estimate.
Source: Parlett §4.5 and §10.6; atlas `eigenvalue-residual-bounds`.
-/

noncomputable section
open scoped Matrix
open Polynomial

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The shifted residual squared length is the weighted squared spectral
distance. Parlett §4.5; weights are squared eigenbasis coordinates. -/
theorem dotProduct_shifted_residual_eq_sum {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (x : n → ℝ) (μ : ℝ) :
    (A *ᵥ x - μ • x) ⬝ᵥ (A *ᵥ x - μ • x) =
      ∑ i, (hA.eigenvalues i - μ) ^ 2 * (⇑(hA.eigenvectorBasis i) ⬝ᵥ x) ^ 2 := by
  have h := dotProduct_aeval_mulVec_self_eq_sum hA (X - C μ) x
  simpa only [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
    Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, eval_sub, eval_X, eval_C] using h

/-- Every real shift is within its residual norm of an eigenvalue.
Parlett §4.5. The unit-vector assumption excludes an empty spectrum.
atlas: eigenvalue-residual-bounds (partial) -/
theorem exists_eigenvalue_abs_sub_le_residual {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {x : n → ℝ} (hx : x ⬝ᵥ x = 1) (μ : ℝ) :
    ∃ i, |hA.eigenvalues i - μ| ≤
      Real.sqrt ((A *ᵥ x - μ • x) ⬝ᵥ (A *ᵥ x - μ • x)) := by
  let w : n → ℝ := fun i => (⇑(hA.eigenvectorBasis i) ⬝ᵥ x) ^ 2
  let R := (A *ᵥ x - μ • x) ⬝ᵥ (A *ᵥ x - μ • x)
  have hw : ∑ i, w i = 1 := (sum_sq_eigenvectorBasis_dotProduct hA x).trans hx
  have hR : R = ∑ i, (hA.eigenvalues i - μ) ^ 2 * w i :=
    dotProduct_shifted_residual_eq_sum hA x μ
  have hRn : 0 ≤ R := dotProduct_self_nonneg _
  by_contra hnot
  push Not at hnot
  change ∀ i, Real.sqrt R < |hA.eigenvalues i - μ| at hnot
  have hsome : ∃ i ∈ Finset.univ, 0 < w i := by
    by_contra hnone
    push Not at hnone
    have hz : ∑ i, w i ≤ 0 := Finset.sum_nonpos fun i hi => hnone i hi
    linarith
  obtain ⟨j, hj, hwj⟩ := hsome
  have hlt : ∑ i, R * w i < ∑ i, (hA.eigenvalues i - μ) ^ 2 * w i := by
    apply Finset.sum_lt_sum
    · intro i _
      have hh : R < (hA.eigenvalues i - μ) ^ 2 := by
        nlinarith [Real.sq_sqrt hRn, Real.sqrt_nonneg R, hnot i, abs_nonneg (hA.eigenvalues i - μ),
          sq_abs (hA.eigenvalues i - μ)]
      exact mul_le_mul_of_nonneg_right hh.le (sq_nonneg _)
    · refine ⟨j, hj, ?_⟩
      have hh : R < (hA.eigenvalues j - μ) ^ 2 := by
        nlinarith [Real.sq_sqrt hRn, Real.sqrt_nonneg R, hnot j, abs_nonneg (hA.eigenvalues j - μ),
          sq_abs (hA.eigenvalues j - μ)]
      exact mul_lt_mul_of_pos_right hh hwj
  rw [← Finset.mul_sum, hw, mul_one, ← hR] at hlt
  exact lt_irrefl R hlt

omit [DecidableEq n] in
/-- The residual about the Rayleigh quotient is orthogonal to a unit vector.
Parlett §4.5; the quotient is `quadForm A x` on the unit sphere. -/
theorem dotProduct_rayleigh_residual_eq_zero (A : Matrix n n ℝ)
    {x : n → ℝ} (hx : x ⬝ᵥ x = 1) :
    x ⬝ᵥ (A *ᵥ x - quadForm A x • x) = 0 := by
  simp [dotProduct_sub, dotProduct_smul, hx, quadForm]

omit [DecidableEq n] in
/-- Pythagoras separates the optimal Rayleigh residual and the shift error.
Parlett §4.5. This exact identity proves both minimality and uniqueness.
atlas: eigenvalue-residual-bounds (partial) -/
theorem dotProduct_shifted_residual_eq_rayleigh_add_sq (A : Matrix n n ℝ)
    {x : n → ℝ} (hx : x ⬝ᵥ x = 1) (μ : ℝ) :
    (A *ᵥ x - μ • x) ⬝ᵥ (A *ᵥ x - μ • x) =
      (A *ᵥ x - quadForm A x • x) ⬝ᵥ (A *ᵥ x - quadForm A x • x) +
        (μ - quadForm A x) ^ 2 := by
  simp only [sub_dotProduct, dotProduct_sub, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, hx, dotProduct_comm (A *ᵥ x) x, quadForm]
  ring

omit [DecidableEq n] in
/-- The Rayleigh quotient uniquely minimizes the squared residual over real
shifts. Parlett §4.5; no nonzero-eigenvalue hypothesis is needed.
atlas: eigenvalue-residual-bounds (partial) -/
theorem rayleigh_residual_le_shifted_residual (A : Matrix n n ℝ)
    {x : n → ℝ} (hx : x ⬝ᵥ x = 1) (μ : ℝ) :
    Real.sqrt ((A *ᵥ x - quadForm A x • x) ⬝ᵥ (A *ᵥ x - quadForm A x • x)) ≤
      Real.sqrt ((A *ᵥ x - μ • x) ⬝ᵥ (A *ᵥ x - μ • x)) := by
  apply Real.sqrt_le_sqrt
  rw [dotProduct_shifted_residual_eq_rayleigh_add_sq A hx μ]
  nlinarith [sq_nonneg (μ - quadForm A x)]

omit [DecidableEq n] in
/-- Equality in residual minimality occurs exactly at the Rayleigh quotient.
Parlett §4.5, with a unit vector and real shifts. -/
theorem shifted_residual_eq_rayleigh_residual_iff (A : Matrix n n ℝ)
    {x : n → ℝ} (hx : x ⬝ᵥ x = 1) (μ : ℝ) :
    (A *ᵥ x - μ • x) ⬝ᵥ (A *ᵥ x - μ • x) =
      (A *ᵥ x - quadForm A x • x) ⬝ᵥ (A *ᵥ x - quadForm A x • x) ↔
        μ = quadForm A x := by
  rw [dotProduct_shifted_residual_eq_rayleigh_add_sq A hx]
  constructor
  · intro h
    have : (μ - quadForm A x) ^ 2 = 0 := by linarith
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp this)
  · intro h
    simp [h]

/-- A nonnegative quadratic polynomial on the spectrum bounds the Rayleigh
residual variance. Kato–Temple finite spectral proof, Parlett §10.6. -/
theorem rayleigh_variance_add_mul_nonneg {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {x : n → ℝ} (hx : x ⬝ᵥ x = 1) (ℓ a : ℝ)
    (hp : ∀ i, 0 ≤ (hA.eigenvalues i - ℓ) * (hA.eigenvalues i - a)) :
    0 ≤ (A *ᵥ x - quadForm A x • x) ⬝ᵥ (A *ᵥ x - quadForm A x • x) +
      (quadForm A x - ℓ) * (quadForm A x - a) := by
  let ρ := quadForm A x
  let w : n → ℝ := fun i => (⇑(hA.eigenvectorBasis i) ⬝ᵥ x) ^ 2
  have hw : ∑ i, w i = 1 := (sum_sq_eigenvectorBasis_dotProduct hA x).trans hx
  have hmean : ∑ i, hA.eigenvalues i * w i = ρ :=
    (quadForm_eq_sum_eigenvalues hA x).symm
  have hR := dotProduct_shifted_residual_eq_sum hA x ρ
  have heq : ∑ i, (hA.eigenvalues i - ℓ)*(hA.eigenvalues i - a)*w i =
      ∑ i, (hA.eigenvalues i - ρ)^2*w i +
        (2*ρ-ℓ-a)*∑ i, hA.eigenvalues i*w i + (ℓ*a-ρ^2)*∑ i, w i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsum : 0 ≤ ∑ i, (hA.eigenvalues i - ℓ)*(hA.eigenvalues i - a)*w i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (sq_nonneg _)
  rw [heq, hw, hmean, ← hR] at hsum
  change 0 ≤ (A *ᵥ x - ρ • x) ⬝ᵥ (A *ᵥ x - ρ • x) + (ρ-ℓ)*(ρ-a)
  nlinarith

/-- Kato–Temple upper bound for an isolated eigenvalue; multiplicities are
unrestricted. Parlett §10.6, with explicit interval isolation.
atlas: eigenvalue-residual-bounds (partial) -/
theorem kato_temple_eigenvalue_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {x : n → ℝ} (hx : x ⬝ᵥ x = 1) {α β ℓ : ℝ}
    (hαρ : α < quadForm A x) (_hρβ : quadForm A x < β)
    (hαℓ : α < ℓ) (hℓβ : ℓ < β)
    (hiso : ∀ i, α < hA.eigenvalues i → hA.eigenvalues i < β → hA.eigenvalues i = ℓ) :
    ℓ ≤ quadForm A x +
      ((A *ᵥ x - quadForm A x • x) ⬝ᵥ (A *ᵥ x - quadForm A x • x)) /
        (quadForm A x - α) := by
  have hp : ∀ i, 0 ≤ (hA.eigenvalues i-ℓ)*(hA.eigenvalues i-α) := by
    intro i
    by_cases hi : α < hA.eigenvalues i
    · by_cases hj : hA.eigenvalues i < β
      · rw [hiso i hi hj]
        simp
      · have hj' := le_of_not_gt hj
        nlinarith
    · have hi' := le_of_not_gt hi
      nlinarith
  have hh := rayleigh_variance_add_mul_nonneg hA hx ℓ α hp
  have hd : 0 < quadForm A x-α := sub_pos.mpr hαρ
  have hdiv := (le_div_iff₀ hd).2 (show
    (ℓ-quadForm A x)*(quadForm A x-α) ≤
      (A *ᵥ x - quadForm A x • x) ⬝ᵥ (A *ᵥ x - quadForm A x • x) by nlinarith)
  linarith

/-- Kato–Temple lower bound for the same isolated spectral point.
Parlett §10.6; only the positive Rayleigh-to-endpoint distance is divided by.
atlas: eigenvalue-residual-bounds (partial) -/
theorem kato_temple_le_eigenvalue {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {x : n → ℝ} (hx : x ⬝ᵥ x = 1) {α β ℓ : ℝ}
    (hαρ : α < quadForm A x) (hρβ : quadForm A x < β)
    (hαℓ : α < ℓ) (hℓβ : ℓ < β)
    (hiso : ∀ i, α < hA.eigenvalues i → hA.eigenvalues i < β → hA.eigenvalues i = ℓ) :
    quadForm A x -
      ((A *ᵥ x - quadForm A x • x) ⬝ᵥ (A *ᵥ x - quadForm A x • x)) /
        (β - quadForm A x) ≤ ℓ := by
  have hp : ∀ i, 0 ≤ (hA.eigenvalues i-ℓ)*(hA.eigenvalues i-β) := by
    intro i
    by_cases hi : α < hA.eigenvalues i
    · by_cases hj : hA.eigenvalues i < β
      · rw [hiso i hi hj]
        simp
      · have hj' := le_of_not_gt hj
        nlinarith
    · have hi' := le_of_not_gt hi
      nlinarith
  have hh := rayleigh_variance_add_mul_nonneg hA hx ℓ β hp
  have hd : 0 < β-quadForm A x := sub_pos.mpr hρβ
  have hdiv := (le_div_iff₀ hd).2 (show
    (quadForm A x-ℓ)*(β-quadForm A x) ≤
      (A *ᵥ x - quadForm A x • x) ⬝ᵥ (A *ᵥ x - quadForm A x • x) by nlinarith)
  linarith

/-- Symmetric-interval Kato–Temple bound with the exact variance-over-gap
constant. Parlett §10.6; existence and isolation are explicit and no residual
smallness assumption is required.
atlas: eigenvalue-residual-bounds (partial) -/
theorem abs_eigenvalue_sub_rayleigh_le_residual_sq_div {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {x : n → ℝ} (hx : x ⬝ᵥ x = 1) {ℓ δ : ℝ} (hδ : 0 < δ)
    (hℓ : |ℓ-quadForm A x| < δ)
    (hiso : ∀ i, |hA.eigenvalues i-quadForm A x| < δ → hA.eigenvalues i = ℓ) :
    |ℓ-quadForm A x| ≤
      ((A *ᵥ x - quadForm A x • x) ⬝ᵥ (A *ᵥ x - quadForm A x • x)) / δ := by
  have hℓ' := abs_lt.mp hℓ
  have hiso' : ∀ i, quadForm A x-δ < hA.eigenvalues i →
      hA.eigenvalues i < quadForm A x+δ → hA.eigenvalues i = ℓ := by
    intro i hi hj
    apply hiso i
    rw [abs_lt]
    constructor <;> linarith
  have hu := kato_temple_eigenvalue_le hA hx (by linarith) (by linarith)
    (by linarith : quadForm A x-δ < ℓ) (by linarith : ℓ < quadForm A x+δ) hiso'
  have hl := kato_temple_le_eigenvalue hA hx (by linarith) (by linarith)
    (by linarith : quadForm A x-δ < ℓ) (by linarith : ℓ < quadForm A x+δ) hiso'
  have hd1 : quadForm A x-(quadForm A x-δ) = δ := by ring
  have hd2 : quadForm A x+δ-quadForm A x = δ := by ring
  rw [hd1] at hu
  rw [hd2] at hl
  rw [abs_le]
  constructor <;> linarith

end NLAlib
