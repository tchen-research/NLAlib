import NLAlib.Matrix.Basic.QuadForm
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Kernels of matrices with positive semidefinite Hermitian part

The kernel of an accretive matrix is the common kernel of its Hermitian
and skew-Hermitian components. Source: Horn–Johnson (2013), Lemma 7.1.11
and Observation 7.1.12; operator derivations, (S12).
Atlas: `psd-hermitian-part` (kernel and rank clauses).
-/

noncomputable section
open scoped Matrix ComplexOrder
namespace NLAlib
variable {n : Type*} [Fintype n]

/-- Taking the Hermitian part takes the real part of a quadratic form.
This relates the native self-adjoint-part map to accretivity. -/
theorem quadForm_selfAdjointPart (A : Matrix n n ℂ) (x : n → ℂ) :
    quadForm (selfAdjointPart ℝ A : Matrix n n ℂ) x = (quadForm A x).re := by
  simp only [selfAdjointPart_apply_coe, Matrix.star_eq_conjTranspose,
    quadForm, Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul,
    dotProduct_add]
  have h := star_quadForm A x
  simp only [quadForm] at h
  rw [← h]
  simp [Complex.ext_iff, Complex.real_smul]
  ring

/-- With positive semidefinite Hermitian part, annihilation by `A` implies
annihilation by its Hermitian part. Source: Horn–Johnson (2013), Lemma 7.1.11.
atlas: psd-hermitian-part (partial) -/
theorem selfAdjointPart_mulVec_eq_zero_of_mulVec_eq_zero
    {A : Matrix n n ℂ} (hA : (selfAdjointPart ℝ A : Matrix n n ℂ).PosSemidef)
    {x : n → ℂ} (hx : A *ᵥ x = 0) :
    (selfAdjointPart ℝ A : Matrix n n ℂ) *ᵥ x = 0 := by
  apply (hA.dotProduct_mulVec_zero_iff x).mp
  change quadForm (selfAdjointPart ℝ A : Matrix n n ℂ) x = 0
  rw [quadForm_selfAdjointPart]
  simp [quadForm, hx]

/-- The kernel of an accretive matrix is the common kernel of its real
and imaginary Hermitian parts. Source: operator derivations, (S12).
atlas: psd-hermitian-part (partial) -/
theorem mulVec_eq_zero_iff_realPart_and_imaginaryPart_mulVec_eq_zero
    {A : Matrix n n ℂ} (hA : (selfAdjointPart ℝ A : Matrix n n ℂ).PosSemidef)
    (x : n → ℂ) :
    A *ᵥ x = 0 ↔ (realPart A : Matrix n n ℂ) *ᵥ x = 0 ∧
      (imaginaryPart A : Matrix n n ℂ) *ᵥ x = 0 := by
  have hdec := realPart_add_I_smul_imaginaryPart A
  constructor
  · intro hx
    have hreal := selfAdjointPart_mulVec_eq_zero_of_mulVec_eq_zero hA hx
    change (realPart A : Matrix n n ℂ) *ᵥ x = 0 at hreal
    refine ⟨hreal, ?_⟩
    have heq := congrArg (fun M : Matrix n n ℂ => M *ᵥ x) hdec
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, hreal, zero_add, hx] at heq
    exact (smul_eq_zero.mp heq).resolve_left Complex.I_ne_zero
  · rintro ⟨hr, hi⟩
    rw [← hdec, Matrix.add_mulVec, Matrix.smul_mulVec, hr, hi, smul_zero, add_zero]

/-- An accretive matrix and its adjoint have identical kernels.
Source: Horn–Johnson (2013), Lemma 7.1.11; operator derivations, (S12).
atlas: psd-hermitian-part (partial) -/
theorem mulVec_eq_zero_iff_conjTranspose_mulVec_eq_zero
    {A : Matrix n n ℂ} (hA : (selfAdjointPart ℝ A : Matrix n n ℂ).PosSemidef)
    (x : n → ℂ) : A *ᵥ x = 0 ↔ Aᴴ *ᵥ x = 0 := by
  have hpart : (selfAdjointPart ℝ Aᴴ : Matrix n n ℂ) = selfAdjointPart ℝ A := by
    simp [selfAdjointPart_apply_coe, Matrix.star_eq_conjTranspose, add_comm]
  have hdir (B : Matrix n n ℂ)
      (hB : (selfAdjointPart ℝ B : Matrix n n ℂ).PosSemidef)
      (hb : B *ᵥ x = 0) : Bᴴ *ᵥ x = 0 := by
    have hh := selfAdjointPart_mulVec_eq_zero_of_mulVec_eq_zero hB hb
    have heq : B *ᵥ x + Bᴴ *ᵥ x = 0 := by
      have hscaled := congrArg (fun v : n → ℂ => (2 : ℝ) • v) hh
      simpa [selfAdjointPart_apply_coe, Matrix.star_eq_conjTranspose,
        Matrix.smul_mulVec, Matrix.add_mulVec, smul_smul] using hscaled
    simpa [hb] using heq
  exact ⟨hdir A hA, fun hx => by
    simpa using hdir Aᴴ (hpart.symm ▸ hA) hx⟩

/-- The Hermitian part of an accretive matrix has rank no greater than the
matrix. Source: Horn–Johnson (2013), Observation 7.1.12.
atlas: psd-hermitian-part (partial) -/
theorem rank_selfAdjointPart_le_of_posSemidef
    {A : Matrix n n ℂ} (hA : (selfAdjointPart ℝ A : Matrix n n ℂ).PosSemidef) :
    (selfAdjointPart ℝ A : Matrix n n ℂ).rank ≤ A.rank := by
  have hker : LinearMap.ker A.mulVecLin ≤
      LinearMap.ker (selfAdjointPart ℝ A : Matrix n n ℂ).mulVecLin := by
    intro x hx
    exact selfAdjointPart_mulVec_eq_zero_of_mulVec_eq_zero hA hx
  have hdim := Submodule.finrank_mono hker
  have hdA := A.mulVecLin.finrank_range_add_finrank_ker
  have hdH := (selfAdjointPart ℝ A : Matrix n n ℂ).mulVecLin.finrank_range_add_finrank_ker
  unfold Matrix.rank
  omega

end NLAlib
