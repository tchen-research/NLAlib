import NLAlib.Krylov.Solvers.StationarySplitting
import NLAlib.Krylov.Solvers.Preconditioned
import NLAlib.Krylov.Solvers.PolynomialMethods

/-! # Preconditioned Richardson iteration

The implemented affine recursion has the stated preconditioned residual update and exact
error powers. A split-preconditioning change of coordinates transports the existing weighted
polynomial bounds to both the original `A` and `P` energy forms.

Source: Greenbaum (1997), §2.1; Saad (2003), §4.2.
Atlas: `richardson-iteration`.
-/

noncomputable section

open scoped Matrix Polynomial MatrixOrder
open Polynomial

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Preconditioned Richardson iteration, initialized at `x₀`, with iteration matrix
`I - ω P⁻¹ A` and forcing `ω P⁻¹ c`. Source: Saad (2003), §4.2.
atlas: richardson-iteration (partial) -/
def preconditionedRichardsonIterate (ω : ℝ) (A P : Matrix n n ℝ) (c x₀ : n → ℝ) :
    ℕ → n → ℝ :=
  affineStationaryIterate (1 - ω • (P⁻¹ * A)) (ω • (P⁻¹ *ᵥ c)) x₀

/-- Preconditioned Richardson starts at the specified initializer. -/
@[simp] theorem preconditionedRichardsonIterate_zero (ω : ℝ) (A P : Matrix n n ℝ)
    (c x₀ : n → ℝ) : preconditionedRichardsonIterate ω A P c x₀ 0 = x₀ := rfl

/-- The implemented update is `xₖ₊₁ = xₖ + ω P⁻¹(c - A xₖ)`.
Source: Saad (2003), §4.2.
atlas: richardson-iteration (partial) -/
theorem preconditionedRichardsonIterate_succ (ω : ℝ) (A P : Matrix n n ℝ)
    (c x₀ : n → ℝ) (k : ℕ) :
    preconditionedRichardsonIterate ω A P c x₀ (k + 1) =
      preconditionedRichardsonIterate ω A P c x₀ k +
        ω • (P⁻¹ *ᵥ (c - A *ᵥ preconditionedRichardsonIterate ω A P c x₀ k)) := by
  rw [preconditionedRichardsonIterate, affineStationaryIterate_succ]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, smul_sub]
  module

/-- Exact error powers for the actual preconditioned Richardson recursion.
Source: Greenbaum (1997), §2.1.
atlas: richardson-iteration (partial) -/
theorem preconditionedRichardsonIterate_sub_eq_pow_mulVec (ω : ℝ) (A P : Matrix n n ℝ)
    {c xs : n → ℝ} (hxs : A *ᵥ xs = c) (x₀ : n → ℝ) (k : ℕ) :
    preconditionedRichardsonIterate ω A P c x₀ k - xs =
      ((1 - ω • (P⁻¹ * A)) ^ k) *ᵥ (x₀ - xs) := by
  apply affineStationaryIterate_sub_eq_pow_mulVec
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, hxs]
  abel

/-- Splitting `P⁻¹ = W Wᵀ` turns the actual preconditioned Richardson recursion into ordinary
Richardson on `Wᵀ A W`. Source: Saad (2003), split preconditioning.
atlas: richardson-iteration (partial) -/
theorem preconditionedRichardsonIterate_eq_mulVec_richardsonIterate
    {A P W : Matrix n n ℝ} (hW : Wᵀ * P * W = 1) (ω : ℝ) (c x₀ : n → ℝ) (k : ℕ) :
    preconditionedRichardsonIterate ω A P c x₀ k =
      W *ᵥ richardsonIterate ω (Wᵀ * A * W) (Wᵀ *ᵥ c) (W⁻¹ *ᵥ x₀) k := by
  have hU := isUnit_of_transpose_mul_mul_eq_one hW
  have hd := (Matrix.isUnit_iff_isUnit_det W).mp hU
  have hWW (v : n → ℝ) : W *ᵥ (W⁻¹ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv W hd, Matrix.one_mulVec]
  induction k with
  | zero => simp only [preconditionedRichardsonIterate_zero, richardsonIterate_zero, hWW]
  | succ k ih =>
    rw [preconditionedRichardsonIterate_succ, richardsonIterate_succ,
      Matrix.mulVec_add, Matrix.mulVec_smul, ← ih]
    congr 1
    rw [inv_eq_mul_transpose_of_transpose_mul_mul_eq_one hW]
    simp only [Matrix.mulVec_sub, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
    rw [ih]

private theorem preconditionedRichardson_energy_bounds {A P : Matrix n n ℝ}
    (hP : P.PosDef) {a b ω : ℝ} (ha : 0 < a) (hω : 0 ≤ ω)
    (hlow : a • P ≤ A) (hup : A ≤ b • P) {c xs : n → ℝ}
    (hxs : A *ᵥ xs = c) (x₀ : n → ℝ) (k : ℕ) :
    (quadForm A (preconditionedRichardsonIterate ω A P c x₀ k - xs) ≤
      (max |1 - ω * a| |1 - ω * b| ^ k) ^ 2 * quadForm A (x₀ - xs)) ∧
    (quadForm P (preconditionedRichardsonIterate ω A P c x₀ k - xs) ≤
      (max |1 - ω * a| |1 - ω * b| ^ k) ^ 2 * quadForm P (x₀ - xs)) := by
  obtain ⟨W, -, hW⟩ := exists_isSymm_transpose_mul_mul_eq_one hP
  have hU := isUnit_of_transpose_mul_mul_eq_one hW
  have hd := (Matrix.isUnit_iff_isUnit_det W).mp hU
  have hWW (v : n → ℝ) : W *ᵥ (W⁻¹ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv W hd, Matrix.one_mulVec]
  have hAh : A.IsHermitian := by
    have hh : (b • P - A).IsHermitian := (Matrix.le_iff.mp hup).isHermitian
    have hbp : (b • P).IsHermitian := hP.isHermitian.smul (IsSelfAdjoint.all b)
    simpa only [sub_sub_cancel] using hbp.sub hh
  let B := Wᵀ * A * W
  have hBh : B.IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_mul W hAh
  have hcong (s : ℝ) : Wᵀ * (A - s • P) * W = B - s • 1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hW]
  have hcong' (s : ℝ) : Wᵀ * (s • P - A) * W = s • 1 - B := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hW]
  have hlowB : (B - a • 1).PosSemidef := by
    have hh := (Matrix.le_iff.mp hlow).conjTranspose_mul_mul_same W
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hcong] using hh
  have hupB : (b • 1 - B).PosSemidef := by
    have hh := (Matrix.le_iff.mp hup).conjTranspose_mul_mul_same W
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hcong'] using hh
  have hspec (i : n) : hBh.eigenvalues i ∈ Set.Icc a b := by
    let u : n → ℝ := hBh.eigenvectorBasis i
    have hu : u ⬝ᵥ u = 1 := by
      simpa [u] using eigenvectorBasis_dotProduct_eigenvectorBasis hBh i i
    have hval := eigenvalues_eq_dotProduct_mulVec hBh i
    have h1 := hlowB.dotProduct_mulVec_nonneg u
    have h2 := hupB.dotProduct_mulVec_nonneg u
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul, hu] at h1 h2
    constructor <;> linarith
  have hxs' : B *ᵥ (W⁻¹ *ᵥ xs) = Wᵀ *ᵥ c := by
    dsimp [B]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hWW, hxs]
  have hAq := quadForm_richardsonIterate_sub_le hBh hω hspec (g := X)
    (fun x hx => by simpa only [eval_X] using ha.le.trans hx.1) hxs' (W⁻¹ *ᵥ x₀) k
  have hPq := quadForm_richardsonIterate_sub_le hBh hω hspec (g := 1)
    (by intro x hx; simp) hxs' (W⁻¹ *ᵥ x₀) k
  rw [aeval_X] at hAq
  rw [map_one] at hPq
  have hq (C : Matrix n n ℝ) (v : n → ℝ) :
      quadForm (Wᵀ * C * W) v = quadForm C (W *ᵥ v) := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      quadForm_conjTranspose_mul_mul C W v
  have hqA (v : n → ℝ) : quadForm B v = quadForm A (W *ᵥ v) := hq A v
  have hqP (v : n → ℝ) : quadForm (1 : Matrix n n ℝ) v = quadForm P (W *ᵥ v) := by
    rw [← hW]
    exact hq P v
  have hiter := preconditionedRichardsonIterate_eq_mulVec_richardsonIterate
    (A := A) hW ω c x₀ k
  change preconditionedRichardsonIterate ω A P c x₀ k =
    W *ᵥ richardsonIterate ω B (Wᵀ *ᵥ c) (W⁻¹ *ᵥ x₀) k at hiter
  constructor
  · simpa only [Matrix.mulVec_sub, hqA, hWW, ← hiter] using hAq
  · simpa only [Matrix.mulVec_sub, hqP, hWW, ← hiter] using hPq

/-- The preconditioned Richardson error contracts in the original `A` energy, with the exact
endpoint factor `max(|1-ωa|, |1-ωb|)`. Squared energy forms avoid choosing a square-root norm.
Source: Greenbaum (1997), §2.1; Saad (2003), §4.2.
atlas: richardson-iteration (partial) -/
theorem quadForm_preconditionedRichardsonIterate_sub_le {A P : Matrix n n ℝ}
    (hP : P.PosDef) {a b ω : ℝ} (ha : 0 < a) (hω : 0 ≤ ω)
    (hlow : a • P ≤ A) (hup : A ≤ b • P) {c xs : n → ℝ}
    (hxs : A *ᵥ xs = c) (x₀ : n → ℝ) (k : ℕ) :
    quadForm A (preconditionedRichardsonIterate ω A P c x₀ k - xs) ≤
      (max |1 - ω * a| |1 - ω * b| ^ k) ^ 2 * quadForm A (x₀ - xs) :=
  (preconditionedRichardson_energy_bounds hP ha hω hlow hup hxs x₀ k).1

/-- The same sharp endpoint contraction holds in the preconditioner `P` energy.
Source: Greenbaum (1997), §2.1; Saad (2003), §4.2.
atlas: richardson-iteration (partial) -/
theorem quadForm_preconditionedRichardsonIterate_sub_le_preconditioner
    {A P : Matrix n n ℝ} (hP : P.PosDef) {a b ω : ℝ} (ha : 0 < a) (hω : 0 ≤ ω)
    (hlow : a • P ≤ A) (hup : A ≤ b • P) {c xs : n → ℝ}
    (hxs : A *ᵥ xs = c) (x₀ : n → ℝ) (k : ℕ) :
    quadForm P (preconditionedRichardsonIterate ω A P c x₀ k - xs) ≤
      (max |1 - ω * a| |1 - ω * b| ^ k) ^ 2 * quadForm P (x₀ - xs) :=
  (preconditionedRichardson_energy_bounds hP ha hω hlow hup hxs x₀ k).2

/-- At the optimal relaxation the endpoint contraction factor is `(b-a)/(b+a)`. -/
private theorem max_abs_one_sub_optimal_mul_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    max |1 - 2 / (a + b) * a| |1 - 2 / (a + b) * b| = (b - a) / (b + a) := by
  have hne : a + b ≠ 0 := by linarith
  have hne' : b + a ≠ 0 := by linarith
  have h1 : 1 - 2 / (a + b) * a = (b - a) / (b + a) := by field_simp; ring
  have h2 : 1 - 2 / (a + b) * b = -((b - a) / (b + a)) := by field_simp; ring
  have hnn : 0 ≤ (b - a) / (b + a) := div_nonneg (by linarith) (by linarith)
  rw [h1, h2, abs_neg, max_self, abs_of_nonneg hnn]

/-- The optimal preconditioned Richardson step gives the claimed ratio in `A` energy.
Source: Saad (2003), §4.2.1.
atlas: richardson-iteration (partial) -/
theorem quadForm_preconditionedRichardsonIterate_sub_le_of_optimal
    {A P : Matrix n n ℝ} (hP : P.PosDef) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hlow : a • P ≤ A) (hup : A ≤ b • P) {c xs : n → ℝ}
    (hxs : A *ᵥ xs = c) (x₀ : n → ℝ) (k : ℕ) :
    quadForm A (preconditionedRichardsonIterate (2 / (a + b)) A P c x₀ k - xs) ≤
      (((b - a) / (b + a)) ^ k) ^ 2 * quadForm A (x₀ - xs) := by
  have h := quadForm_preconditionedRichardsonIterate_sub_le hP ha
    (ω := 2 / (a + b)) (by
      have hpos : 0 < a + b := by linarith
      exact div_nonneg (by norm_num) hpos.le) hlow hup hxs x₀ k
  rwa [max_abs_one_sub_optimal_mul_eq ha hab] at h

/-- The optimal preconditioned Richardson step has the same ratio in `P` energy.
Source: Saad (2003), §4.2.1.
atlas: richardson-iteration (partial) -/
theorem quadForm_preconditionedRichardsonIterate_sub_le_preconditioner_of_optimal
    {A P : Matrix n n ℝ} (hP : P.PosDef) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hlow : a • P ≤ A) (hup : A ≤ b • P) {c xs : n → ℝ}
    (hxs : A *ᵥ xs = c) (x₀ : n → ℝ) (k : ℕ) :
    quadForm P (preconditionedRichardsonIterate (2 / (a + b)) A P c x₀ k - xs) ≤
      (((b - a) / (b + a)) ^ k) ^ 2 * quadForm P (x₀ - xs) := by
  have h := quadForm_preconditionedRichardsonIterate_sub_le_preconditioner hP ha
    (ω := 2 / (a + b)) (by
      have hpos : 0 < a + b := by linarith
      exact div_nonneg (by norm_num) hpos.le) hlow hup hxs x₀ k
  rwa [max_abs_one_sub_optimal_mul_eq ha hab] at h

end NLAlib
