import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! # Positive-vector certificates for nonsingular M-matrices

The order in this file is entrywise. A positive vector with positive image
gives a discrete minimum principle for a Z-matrix. This proves inverse
positivity without assuming a Perron eigenpair or irreducibility.
Source: Berman–Plemmons, Nonnegative Matrices, Chapter 6.
-/

noncomputable section
open Matrix Finset
open scoped Matrix

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A real Z-matrix has nonpositive off-diagonal entries. -/
def IsZMatrix (A : Matrix ι ι ℝ) : Prop := ∀ i j, i ≠ j → A i j ≤ 0

/-- A nonsingular M-matrix is a Z-matrix with an entrywise nonnegative inverse.
Invertibility is explicit, so Lean's total zero inverse cannot satisfy the definition.
Source: Berman–Plemmons, Chapter 6. -/
def IsNonsingularMMatrix (A : Matrix ι ι ℝ) : Prop :=
  A.IsZMatrix ∧ IsUnit A ∧ ∀ i j, 0 ≤ A⁻¹ i j

/-- Discrete minimum principle: a positive supersolution of a Z-matrix forces
every vector with nonnegative image to be nonnegative.
Source: Berman–Plemmons, Chapter 6.
atlas: nonsingular-m-matrix-characterizations (partial) -/
theorem IsZMatrix.nonneg_of_mulVec_nonneg_of_positive_certificate
    {A : Matrix ι ι ℝ} (hA : A.IsZMatrix) {x : ι → ℝ}
    (hx : ∀ i, 0 < x i) (hAx : ∀ i, 0 < (A *ᵥ x) i)
    {u : ι → ℝ} (hu : ∀ i, 0 ≤ (A *ᵥ u) i) : ∀ i, 0 ≤ u i := by
  classical
  intro j
  by_contra hj
  have huj : u j < 0 := lt_of_not_ge hj
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ (fun k => u k / x k)
    ⟨j, mem_univ j⟩
  let a : ℝ := u i / x i
  have ha : a < 0 := (hi j (mem_univ j)).trans_lt (div_neg_of_neg_of_pos huj (hx j))
  have hd (k : ι) : 0 ≤ u k - a * x k := by
    have hk : a ≤ u k / x k := hi k (mem_univ k)
    exact sub_nonneg.mpr ((le_div_iff₀ (hx k)).mp hk)
  have hz : u i - a * x i = 0 := by
    dsimp [a]
    field_simp [(hx i).ne']
    ring
  have hsum : (A *ᵥ (u - a • x)) i ≤ 0 := by
    apply Finset.sum_nonpos
    intro k _
    by_cases hik : i = k
    · subst k
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hz, mul_zero, le_refl]
    · exact mul_nonpos_of_nonpos_of_nonneg (hA i k hik) (hd k)
  have he : (A *ᵥ (u - a • x)) i = (A *ᵥ u) i - a * (A *ᵥ x) i := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
    rfl
  rw [he] at hsum
  have hneg := mul_neg_of_neg_of_pos ha (hAx i)
  linarith [hu i]

/-- A Z-matrix with a positive vector of strictly positive image is invertible
and inverse-positive. No nonempty-dimension assumption is necessary.
Source: Berman–Plemmons, Chapter 6.
atlas: nonsingular-m-matrix-characterizations (partial) -/
theorem IsZMatrix.isNonsingularMMatrix_of_positive_certificate
    {A : Matrix ι ι ℝ} (hA : A.IsZMatrix) {x : ι → ℝ}
    (hx : ∀ i, 0 < x i) (hAx : ∀ i, 0 < (A *ᵥ x) i) :
    A.IsNonsingularMMatrix := by
  have hmono : ∀ {u : ι → ℝ}, (∀ i, 0 ≤ (A *ᵥ u) i) → ∀ i, 0 ≤ u i :=
    fun hu => hA.nonneg_of_mulVec_nonneg_of_positive_certificate hx hAx hu
  have hker : ∀ u, A *ᵥ u = 0 → u = 0 := by
    intro u hu
    have hp : ∀ i, 0 ≤ u i := hmono (by simp [hu])
    have hn : ∀ i, 0 ≤ (-u) i := hmono (by simp [Matrix.mulVec_neg, hu])
    exact funext fun i => le_antisymm (by simpa using hn i) (hp i)
  have hunit : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp <|
    (LinearMap.ker_eq_bot.mp (Matrix.ker_mulVecLin_eq_bot_iff.mpr hker))
  refine ⟨hA, hunit, fun i j => ?_⟩
  have hInv := Matrix.mul_nonsing_inv A (Matrix.isUnit_iff_isUnit_det A |>.mp hunit)
  have hcol : A *ᵥ (fun k => A⁻¹ k j) = fun k => if k = j then 1 else 0 := by
    funext k
    simpa only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.one_apply] using
      congrArg (fun M : Matrix ι ι ℝ => M k j) hInv
  exact hmono (u := fun k => A⁻¹ k j) (by
    rw [hcol]
    intro k
    dsimp only
    split_ifs <;> norm_num) i

/-- Inverse-positive matrices obey the componentwise monotonicity principle.
Source: Berman–Plemmons, Chapter 6.
atlas: nonsingular-m-matrix-characterizations (partial) -/
theorem IsNonsingularMMatrix.nonneg_of_mulVec_nonneg
    {A : Matrix ι ι ℝ} (hA : A.IsNonsingularMMatrix) {u : ι → ℝ}
    (hu : ∀ i, 0 ≤ (A *ᵥ u) i) : ∀ i, 0 ≤ u i := by
  have he : A⁻¹ *ᵥ (A *ᵥ u) = u := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det A |>.mp hA.2.1),
      Matrix.one_mulVec]
  intro i
  rw [← he]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hA.2.2 i j) (hu j)

/-- An inverse-positive matrix has a strictly positive vector with strictly
positive image: its inverse applied to the all-ones vector.
Source: Berman–Plemmons, Chapter 6.
atlas: nonsingular-m-matrix-characterizations (partial) -/
theorem IsNonsingularMMatrix.exists_positive_certificate
    {A : Matrix ι ι ℝ} (hA : A.IsNonsingularMMatrix) :
    ∃ x : ι → ℝ, (∀ i, 0 < x i) ∧ ∀ i, 0 < (A *ᵥ x) i := by
  let x : ι → ℝ := A⁻¹ *ᵥ (fun _ => 1)
  have hx0 : ∀ i, 0 ≤ x i := fun i =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hA.2.2 i j) zero_le_one
  have hAx : A *ᵥ x = fun _ => 1 := by
    dsimp [x]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det A |>.mp hA.2.1),
      Matrix.one_mulVec]
  refine ⟨x, fun i => ?_, fun i => by rw [hAx]; norm_num⟩
  by_contra hi
  have hxi : x i = 0 := le_antisymm (le_of_not_gt hi) (hx0 i)
  have hle : (A *ᵥ x) i ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    by_cases hij : i = j
    · subst j
      simp [hxi]
    · exact mul_nonpos_of_nonpos_of_nonneg (hA.1 i j hij) (hx0 j)
  rw [hAx] at hle
  norm_num at hle

/-- Positive-vector certification is equivalent to inverse positivity for Z-matrices.
Source: Berman–Plemmons, Chapter 6.
atlas: nonsingular-m-matrix-characterizations (partial) -/
theorem isNonsingularMMatrix_iff_positive_certificate {A : Matrix ι ι ℝ}
    (hA : A.IsZMatrix) : A.IsNonsingularMMatrix ↔
      ∃ x : ι → ℝ, (∀ i, 0 < x i) ∧ ∀ i, 0 < (A *ᵥ x) i :=
  ⟨IsNonsingularMMatrix.exists_positive_certificate,
    fun ⟨_, hx, hAx⟩ => hA.isNonsingularMMatrix_of_positive_certificate hx hAx⟩

end Matrix
