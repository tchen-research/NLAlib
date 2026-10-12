import NLAlib.Matrix.BlockContraction
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Quadratic and bilinear tests for block positivity

Positive semidefinite blocks are equivalent to their bilinear Cauchy--Schwarz
inequality and the corresponding absolute cross-term bound. Strict versions
quantify over the appropriate nonzero vectors.
Source: Horn--Johnson (2013), Theorems 7.7.7--7.7.9;
atlas `psd-block-contraction`.
-/

noncomputable section
open Matrix
namespace NLAlib
variable {m n : Type*} [Fintype m] [Fintype n]

/-- The quadratic form of a symmetric block matrix is the sum of both
diagonal quadratic forms and twice the cross term. Horn--Johnson (2013),
Section 7.7; helper for PSD-block quadratic tests. -/
theorem quadForm_fromBlocks (A : Matrix m m ℝ) (B : Matrix m n ℝ)
    (C : Matrix n n ℝ) (x : m → ℝ) (y : n → ℝ) :
    quadForm (fromBlocks A B Bᵀ C) (Sum.elim x y) =
      quadForm A x + 2 * (x ⬝ᵥ B *ᵥ y) + quadForm C y := by
  simp only [quadForm, Matrix.fromBlocks_mulVec, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    sumElim_dotProduct_sumElim, dotProduct_add, Matrix.dotProduct_transpose_mulVec]
  ring

/-- A PSD block matrix satisfies its bilinear Cauchy--Schwarz bound for
every pair of vectors. Horn--Johnson (2013), Theorem 7.7.9.
atlas: psd-block-contraction (partial) -/
theorem sq_bilinear_le_quadForm_mul_of_fromBlocks_posSemidef
    {A : Matrix m m ℝ} {B : Matrix m n ℝ} {C : Matrix n n ℝ}
    (hH : (fromBlocks A B Bᵀ C).PosSemidef) (x : m → ℝ) (y : n → ℝ) :
    (x ⬝ᵥ B *ᵥ y) ^ 2 ≤ quadForm A x * quadForm C y := by
  have hpoly : ∀ t : ℝ, 0 ≤ quadForm A x * (t * t) +
      (2 * (x ⬝ᵥ B *ᵥ y)) * t + quadForm C y := by
    intro t
    have h := hH.dotProduct_mulVec_nonneg (Sum.elim (t • x) y)
    simp only [star_trivial] at h
    change 0 ≤ quadForm (fromBlocks A B Bᵀ C) (Sum.elim (t • x) y) at h
    rw [quadForm_fromBlocks] at h
    simp only [quadForm, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at h ⊢
    nlinarith
  have h := discrim_le_zero hpoly
  dsimp [discrim] at h
  nlinarith

/-- Bilinear Cauchy--Schwarz for PSD diagonal blocks implies the absolute
cross-term bound. Horn--Johnson (2013), Theorem 7.7.9;
helper for the block positivity equivalences. -/
theorem two_abs_bilinear_le_quadForm_add_of_sq_le
    {A : Matrix m m ℝ} {B : Matrix m n ℝ} {C : Matrix n n ℝ}
    (hA : A.PosSemidef) (hC : C.PosSemidef)
    (h : ∀ x y, (x ⬝ᵥ B *ᵥ y) ^ 2 ≤ quadForm A x * quadForm C y) :
    ∀ x y, 2 * |x ⬝ᵥ B *ᵥ y| ≤ quadForm A x + quadForm C y := by
  intro x y
  have ha : 0 ≤ quadForm A x := by simpa only [quadForm, star_trivial] using hA.dotProduct_mulVec_nonneg x
  have hc : 0 ≤ quadForm C y := by simpa only [quadForm, star_trivial] using hC.dotProduct_mulVec_nonneg y
  have hb := h x y
  nlinarith [sq_abs (x ⬝ᵥ B *ᵥ y), abs_nonneg (x ⬝ᵥ B *ᵥ y),
    sq_nonneg (quadForm A x - quadForm C y)]

/-- Bounding twice the absolute cross term by both diagonal quadratic forms
is exactly sufficient for block positivity. Horn--Johnson (2013),
Theorem 7.7.9; helper for the block positivity equivalences. -/
theorem fromBlocks_posSemidef_of_two_abs_bilinear_le_quadForm_add
    {A : Matrix m m ℝ} {B : Matrix m n ℝ} {C : Matrix n n ℝ}
    (hA : A.IsHermitian) (hC : C.IsHermitian)
    (h : ∀ x y, 2 * |x ⬝ᵥ B *ᵥ y| ≤ quadForm A x + quadForm C y) :
    (fromBlocks A B Bᵀ C).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (hA.fromBlocks (by simp) hC)
  intro z
  have hz : z = Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr) := by ext i; cases i <;> rfl
  rw [hz]
  simp only [star_trivial]
  change 0 ≤ quadForm (fromBlocks A B Bᵀ C) (Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr))
  rw [quadForm_fromBlocks]
  have hxy := h (z ∘ Sum.inl) (z ∘ Sum.inr)
  linarith [neg_abs_le ((z ∘ Sum.inl) ⬝ᵥ B *ᵥ (z ∘ Sum.inr))]

/-- The bilinear-square and absolute cross-term inequalities each
characterize PSD block positivity. Zero vectors and singular blocks require
no exceptions. Horn--Johnson (2013), Theorem 7.7.9.
atlas: psd-block-contraction (partial) -/
theorem posSemidef_fromBlocks_iff_bilinear_tests
    {A : Matrix m m ℝ} {B : Matrix m n ℝ} {C : Matrix n n ℝ}
    (hA : A.PosSemidef) (hC : C.PosSemidef) :
    ((fromBlocks A B Bᵀ C).PosSemidef ↔
      ∀ x y, (x ⬝ᵥ B *ᵥ y) ^ 2 ≤ quadForm A x * quadForm C y) ∧
    ((fromBlocks A B Bᵀ C).PosSemidef ↔
      ∀ x y, 2 * |x ⬝ᵥ B *ᵥ y| ≤ quadForm A x + quadForm C y) := by
  have h1 := sq_bilinear_le_quadForm_mul_of_fromBlocks_posSemidef (A := A) (B := B) (C := C)
  have h2 := two_abs_bilinear_le_quadForm_add_of_sq_le (B := B) hA hC
  have h3 := fromBlocks_posSemidef_of_two_abs_bilinear_le_quadForm_add (B := B) hA.isHermitian hC.isHermitian
  exact ⟨⟨h1, fun h => h3 (h2 h)⟩, ⟨fun h => h2 (h1 h), h3⟩⟩

/-- A positive definite block matrix has a strict bilinear Cauchy--Schwarz
bound for nonzero vectors in both blocks. Horn--Johnson (2013), Theorem 7.7.7.
atlas: psd-block-contraction (partial) -/
theorem sq_bilinear_lt_quadForm_mul_of_fromBlocks_posDef
    {A : Matrix m m ℝ} {B : Matrix m n ℝ} {C : Matrix n n ℝ}
    (hH : (fromBlocks A B Bᵀ C).PosDef) {x : m → ℝ} {y : n → ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    (x ⬝ᵥ B *ᵥ y) ^ 2 < quadForm A x * quadForm C y := by
  have hA : A.PosDef := hH.submatrix (Sum.inl_injective : Function.Injective (Sum.inl : m → m ⊕ n))
  have ha : 0 < quadForm A x := by simpa only [quadForm, star_trivial] using hA.dotProduct_mulVec_pos hx
  have hpoly : ∀ t : ℝ, 0 < quadForm A x * (t * t) +
      (2 * (x ⬝ᵥ B *ᵥ y)) * t + quadForm C y := by
    intro t
    have hz : Sum.elim (t • x) y ≠ 0 := by
      intro he
      apply hy
      exact funext fun i => congrFun he (Sum.inr i)
    have h := hH.dotProduct_mulVec_pos hz
    simp only [star_trivial] at h
    change 0 < quadForm (fromBlocks A B Bᵀ C) (Sum.elim (t • x) y) at h
    rw [quadForm_fromBlocks] at h
    simp only [quadForm, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at h ⊢
    nlinarith
  have h := discrim_lt_zero (ne_of_gt ha) hpoly
  dsimp [discrim] at h
  nlinarith

/-- Strict bilinear Cauchy--Schwarz for positive definite diagonal blocks
implies a strict absolute cross-term bound whenever the combined vector is
nonzero. Horn--Johnson (2013), Theorem 7.7.7;
helper for strict block positivity. -/
theorem two_abs_bilinear_lt_quadForm_add_of_sq_lt
    {A : Matrix m m ℝ} {B : Matrix m n ℝ} {C : Matrix n n ℝ}
    (hA : A.PosDef) (hC : C.PosDef)
    (h : ∀ x y, x ≠ 0 → y ≠ 0 → (x ⬝ᵥ B *ᵥ y) ^ 2 < quadForm A x * quadForm C y) :
    ∀ x y, x ≠ 0 ∨ y ≠ 0 → 2 * |x ⬝ᵥ B *ᵥ y| < quadForm A x + quadForm C y := by
  intro x y hxy
  by_cases hx : x = 0
  · subst x
    have hy := hxy.resolve_left (not_ne_iff.mpr rfl)
    have hc := hC.dotProduct_mulVec_pos hy
    simpa [quadForm] using hc
  by_cases hy : y = 0
  · subst y
    have ha := hA.dotProduct_mulVec_pos hx
    simpa [quadForm] using ha
  have ha : 0 < quadForm A x := by simpa only [quadForm, star_trivial] using hA.dotProduct_mulVec_pos hx
  have hc : 0 < quadForm C y := by simpa only [quadForm, star_trivial] using hC.dotProduct_mulVec_pos hy
  have hb := h x y hx hy
  nlinarith [sq_abs (x ⬝ᵥ B *ᵥ y), abs_nonneg (x ⬝ᵥ B *ᵥ y),
    sq_nonneg (quadForm A x - quadForm C y)]

/-- The strict absolute cross-term inequality gives positive definiteness
when both diagonal blocks are symmetric. Horn--Johnson (2013), Theorem 7.7.7;
helper for strict block positivity. -/
theorem fromBlocks_posDef_of_two_abs_bilinear_lt_quadForm_add
    {A : Matrix m m ℝ} {B : Matrix m n ℝ} {C : Matrix n n ℝ}
    (hA : A.IsHermitian) (hC : C.IsHermitian)
    (h : ∀ x y, x ≠ 0 ∨ y ≠ 0 → 2 * |x ⬝ᵥ B *ᵥ y| < quadForm A x + quadForm C y) :
    (fromBlocks A B Bᵀ C).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (hA.fromBlocks (by simp) hC)
  intro z hz
  have hz' : z = Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr) := by ext i; cases i <;> rfl
  have hxy : z ∘ Sum.inl ≠ 0 ∨ z ∘ Sum.inr ≠ 0 := by
    by_contra hh
    simp only [not_or, not_not] at hh
    apply hz
    rw [hz', hh.1, hh.2]
    ext i
    cases i <;> rfl
  have hb := h (z ∘ Sum.inl) (z ∘ Sum.inr) hxy
  rw [hz']
  simp only [star_trivial]
  change 0 < quadForm (fromBlocks A B Bᵀ C) (Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr))
  rw [quadForm_fromBlocks]
  linarith [neg_abs_le ((z ∘ Sum.inl) ⬝ᵥ B *ᵥ (z ∘ Sum.inr))]

/-- With positive definite diagonal blocks, strict bilinear-square tests on
two nonzero vectors and strict absolute tests on every nonzero combined
vector each characterize block positive definiteness.
Horn--Johnson (2013), Theorem 7.7.7.
atlas: psd-block-contraction (partial) -/
theorem posDef_fromBlocks_iff_strict_bilinear_tests
    {A : Matrix m m ℝ} {B : Matrix m n ℝ} {C : Matrix n n ℝ}
    (hA : A.PosDef) (hC : C.PosDef) :
    ((fromBlocks A B Bᵀ C).PosDef ↔
      ∀ x y, x ≠ 0 → y ≠ 0 → (x ⬝ᵥ B *ᵥ y) ^ 2 < quadForm A x * quadForm C y) ∧
    ((fromBlocks A B Bᵀ C).PosDef ↔
      ∀ x y, x ≠ 0 ∨ y ≠ 0 → 2 * |x ⬝ᵥ B *ᵥ y| < quadForm A x + quadForm C y) := by
  have h1 := fun h x y hx hy => sq_bilinear_lt_quadForm_mul_of_fromBlocks_posDef
    (A := A) (B := B) (C := C) h (x := x) (y := y) hx hy
  have h2 := two_abs_bilinear_lt_quadForm_add_of_sq_lt (B := B) hA hC
  have h3 := fromBlocks_posDef_of_two_abs_bilinear_lt_quadForm_add (B := B) hA.isHermitian hC.isHermitian
  exact ⟨⟨h1, fun h => h3 (h2 h)⟩, ⟨fun h => h2 (h1 h), h3⟩⟩

end NLAlib
