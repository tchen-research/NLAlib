import NLAlib.Polynomial.OrthogonalPolynomials.JacobiMoments
import NLAlib.Matrix.Structured.JacobiBorderPowers
import NLAlib.Matrix.Structured.RadauSchurBorders
import NLAlib.Matrix.Structured.LobattoSchurBorder

/-! # Exact moments of actual endpoint Jacobi borders

The constructed moment Jacobi matrix supplies the first `2N` moments. The finite
propagation theorems transfer these to actual Radau corner changes and Lobatto
last couplings. Neither theorem assumes polynomial exactness of its output.
-/

noncomputable section
open Matrix Polynomial MeasureTheory Finset
open scoped Matrix

namespace NLAlib

/-- The leading part of the actual moment Jacobi matrix is its smaller-order matrix. -/
theorem orthogonalPolynomialJacobiMatrix_leading (L : ℝ[X] →ₗ[ℝ] ℝ) (q : ℕ) :
    (orthogonalPolynomialJacobiMatrix L (q + 1)).submatrix Fin.castSucc Fin.castSucc =
      orthogonalPolynomialJacobiMatrix L q := rfl

/-- The actual moment Jacobi matrix is tridiagonal throughout its defined positive
moment hierarchy. -/
theorem isTridiagonal_orthogonalPolynomialJacobiMatrix (L : ℝ[X] →ₗ[ℝ] ℝ) (q : ℕ)
    (hL : ∀ k ≤ q, hankelMomentDet L k ≠ 0) :
    IsTridiagonal (orthogonalPolynomialJacobiMatrix L q) := by
  have hH := isHermitian_orthogonalPolynomialJacobiMatrix L q
  constructor
  · intro i j hij
    have hs : orthogonalPolynomialJacobiMatrix L q i j =
        orthogonalPolynomialJacobiMatrix L q j i := by
      have h := congrFun (congrFun hH i) j
      simpa only [conjTranspose_apply, star_trivial] using h.symm
    rw [hs]
    exact orthogonalPolynomialJacobiMatrix_apply_eq_zero L hL j i hij
  · intro i j hij
    exact orthogonalPolynomialJacobiMatrix_apply_eq_zero L hL j i hij

/-- The actual coupling vector from the order-`q+1` moment matrix to its last column. -/
def momentJacobiLastCoupling (L : ℝ[X] →ₗ[ℝ] ℝ) (q : ℕ) : Fin q → ℝ :=
  fun i => orthogonalPolynomialJacobiMatrix L (q + 1) i.castSucc (Fin.last q)

/-- The actual moment Jacobi matrix is exactly its leading block with its actual
last coupling and corner. -/
theorem orthogonalPolynomialJacobiMatrix_eq_finSymmetricBorder
    (L : ℝ[X] →ₗ[ℝ] ℝ) (q : ℕ) :
    orthogonalPolynomialJacobiMatrix L (q + 1) =
      finSymmetricBorder (orthogonalPolynomialJacobiMatrix L q) (momentJacobiLastCoupling L q)
        (orthogonalPolynomialJacobiMatrix L (q + 1) (Fin.last q) (Fin.last q)) := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · simp
  · rw [finSymmetricBorder_last_castSucc]
    change L (X * orthonormalMomentPolynomial L j.val * orthonormalMomentPolynomial L q) =
      L (X * orthonormalMomentPolynomial L q * orthonormalMomentPolynomial L j.val)
    exact congrArg L (by ac_rfl)
  · rw [finSymmetricBorder_castSucc_last]
    rfl
  · rw [finSymmetricBorder_castSucc_castSucc]
    rfl

/-- The actual left Radau matrix of a finite moment measure, constructed by replacing
the last corner with the scalar Schur corner at `a`. -/
def leftRadauJacobiMatrix (L : ℝ[X] →ₗ[ℝ] ℝ) (q : ℕ) (a : ℝ) :
    Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ :=
  finSymmetricBorder (orthogonalPolynomialJacobiMatrix L q) (momentJacobiLastCoupling L q)
    (leftRadauCorner (orthogonalPolynomialJacobiMatrix L q) (momentJacobiLastCoupling L q) a)

/-- The actual right Radau matrix constructed by the right endpoint Schur corner. -/
def rightRadauJacobiMatrix (L : ℝ[X] →ₗ[ℝ] ℝ) (q : ℕ) (c : ℝ) :
    Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ :=
  finSymmetricBorder (orthogonalPolynomialJacobiMatrix L q) (momentJacobiLastCoupling L q)
    (rightRadauCorner (orthogonalPolynomialJacobiMatrix L q) (momentJacobiLastCoupling L q) c)

/-- Replacing the actual order-`q+1` moment Jacobi corner by either endpoint Schur
corner preserves moments through `2q`. No exactness hypothesis is imposed on either
constructed output. Source: focused reroutes, Section 3 (BL5).
atlas: gauss-radau-lobatto (partial) -/
theorem integral_pow_eq_mass_mul_radauJacobiMatrix_pow {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) (q : ℕ) (hs : (q + 1 : ℕ∞) ≤ μ.support.encard)
    (a c : ℝ) {k : ℕ} (hk : k ≤ 2 * q) :
    let L := polynomialIntegral μ hμ
    (∫ x : ℝ, x ^ k ∂μ) = (∫ _ : ℝ, (1 : ℝ) ∂μ) * (leftRadauJacobiMatrix L q a ^ k) 0 0 ∧
    (∫ x : ℝ, x ^ k ∂μ) = (∫ _ : ℝ, (1 : ℝ) ∂μ) * (rightRadauJacobiMatrix L q c ^ k) 0 0 := by
  dsimp only
  let L := polynomialIntegral μ hμ
  have hL (j : ℕ) (hj : j ≤ q + 1) : hankelMomentDet L j ≠ 0 :=
    hankelMomentDet_ne_zero_of_le_support_encard μ hμ ((by exact_mod_cast hj : (j : ℕ∞) ≤ q + 1).trans hs)
  have hv (i : Fin q) (hi : i.val + 1 < q) : momentJacobiLastCoupling L q i = 0 :=
    orthogonalPolynomialJacobiMatrix_apply_eq_zero L hL i.castSucc (Fin.last q) hi
  have htri := isTridiagonal_orthogonalPolynomialJacobiMatrix L q (fun j hj => hL j (by omega))
  have hm := integral_pow_eq_mass_mul_orthogonalPolynomialJacobiMatrix_pow hμ
    (Nat.succ_pos q) hs (by omega : k < 2 * (q + 1))
  rw [orthogonalPolynomialJacobiMatrix_eq_finSymmetricBorder] at hm
  have hl := pow_finSymmetricBorder_apply_zero_eq_of_corner htri hv
    (leftRadauCorner (orthogonalPolynomialJacobiMatrix L q) (momentJacobiLastCoupling L q) a)
    (orthogonalPolynomialJacobiMatrix L (q + 1) (Fin.last q) (Fin.last q)) k hk
  have hr := pow_finSymmetricBorder_apply_zero_eq_of_corner htri hv
    (rightRadauCorner (orthogonalPolynomialJacobiMatrix L q) (momentJacobiLastCoupling L q) c)
    (orthogonalPolynomialJacobiMatrix L (q + 1) (Fin.last q) (Fin.last q)) k hk
  exact ⟨hm.trans (congrArg (fun x => (∫ _ : ℝ, (1 : ℝ) ∂μ) * x) hl.symm),
    hm.trans (congrArg (fun x => (∫ _ : ℝ, (1 : ℝ) ∂μ) * x) hr.symm)⟩

/-- The actual Lobatto moment matrix, obtained by adjoining the scalar two-endpoint
Schur border with a final-coordinate vector. -/
def lobattoJacobiMatrix (L : ℝ[X] →ₗ[ℝ] ℝ) (q : ℕ) (a c : ℝ) :
    Matrix (Fin (q + 2)) (Fin (q + 2)) ℝ :=
  let J := orthogonalPolynomialJacobiMatrix L (q + 1)
  let e : Fin (q + 1) → ℝ := Pi.single (Fin.last q) 1
  finSymmetricBorder J (Real.sqrt (lobattoCouplingSq J e a c) • e) (lobattoCorner J e a c)

/-- Adjoining the actual Lobatto Schur coupling to the canonical `(q+1)`-block
preserves moments through `2q+1`, requiring no original coefficient after index `q`.
Source: focused reroutes, Section 3 (BL10).
atlas: gauss-radau-lobatto (partial) -/
theorem integral_pow_eq_mass_mul_lobattoJacobiMatrix_pow {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) (q : ℕ) (hs : (q + 1 : ℕ∞) ≤ μ.support.encard)
    (a c : ℝ) {k : ℕ} (hk : k ≤ 2 * q + 1) :
    let L := polynomialIntegral μ hμ
    (∫ x : ℝ, x ^ k ∂μ) = (∫ _ : ℝ, (1 : ℝ) ∂μ) * (lobattoJacobiMatrix L q a c ^ k) 0 0 := by
  dsimp only
  let L := polynomialIntegral μ hμ
  let J := orthogonalPolynomialJacobiMatrix L (q + 1)
  let e : Fin (q + 1) → ℝ := Pi.single (Fin.last q) 1
  have hL (j : ℕ) (hj : j ≤ q + 1) : hankelMomentDet L j ≠ 0 :=
    hankelMomentDet_ne_zero_of_le_support_encard μ hμ ((by exact_mod_cast hj : (j : ℕ∞) ≤ q + 1).trans hs)
  have hv (i : Fin (q + 1)) (hi : i.val < q) :
      (Real.sqrt (lobattoCouplingSq J e a c) • e) i = 0 := by
    have hne : i ≠ Fin.last q := by intro h; have := congrArg Fin.val h; simp at this; omega
    simp [e, hne]
  have htri := isTridiagonal_orthogonalPolynomialJacobiMatrix L (q + 1) hL
  have hm := integral_pow_eq_mass_mul_orthogonalPolynomialJacobiMatrix_pow hμ
    (Nat.succ_pos q) hs (by omega : k < 2 * (q + 1))
  have hl := pow_finSymmetricBorder_apply_zero_eq_of_coupling htri hv (lobattoCorner J e a c) k hk
  rw [pow_finSymmetricBorder_zero_apply_zero] at hl
  exact hm.trans (by congr 1; exact hl.symm)

end NLAlib
