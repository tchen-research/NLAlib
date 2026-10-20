import NLAlib.Matrix.Structured.GramDilationCoefficientParameters
import NLAlib.Matrix.Norms.BilinearProbes

/-! # Actual weak coefficient parameter of the Gram linearization

The three-block linearization has a dimension-free bilinear weak budget
in terms of the original non-Hermitian coefficients. The proof uses
actual coordinate restrictions of the source probes.
Source: arXiv:2406.11453v2, Section 5.3.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
namespace NLAlib
variable {ι d : Type*} [Fintype ι] [Fintype d]
local notation "E" => EuclideanSpace ℂ d
local notation "F" => EuclideanSpace ℂ (d ⊕ (d ⊕ d))

private theorem norm_left_restriction_le (v : F) :
    ‖(WithLp.toLp 2 (fun a : d => v (.inl a)) : E)‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
  have hm : 0 ≤ ∑ a : d, ‖v (.inr (.inl a))‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hr : 0 ≤ ∑ a : d, ‖v (.inr (.inr a))‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

private theorem norm_middle_restriction_le (v : F) :
    ‖(WithLp.toLp 2 (fun a : d => v (.inr (.inl a))) : E)‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
  have hl : 0 ≤ ∑ a : d, ‖v (.inl a)‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hr : 0 ≤ ∑ a : d, ‖v (.inr (.inr a))‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

private theorem gramDilation_bilinear_eq
    (A : Matrix d d ℂ) (v w : F) :
    star v.ofLp ⬝ᵥ (dilation (gramCoefficientRow A) *ᵥ w.ofLp) =
      (star (fun a : d => v (.inl a)) ⬝ᵥ (A *ᵥ (fun a => w (.inr (.inl a))))) +
      star (star (fun a : d => w (.inl a)) ⬝ᵥ (A *ᵥ (fun a => v (.inr (.inl a))))) := by
  simp only [dilation, gramCoefficientRow, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Pi.star_apply, Pi.zero_apply, Matrix.zero_apply, star_zero, zero_mul, mul_zero, Finset.sum_const_zero,
    add_zero, zero_add, mul_add, Finset.sum_add_distrib, star_sum, star_mul, star_star]
  rw [add_comm]
  apply congrArg₂ (· + ·)
  · rfl
  · simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring

/-- The actual attained bilinear weak energy of the `3d`-dimensional
Hermitian linearization is at most four times the original energy. The
constant is universal and includes zero coefficients and empty types. -/
theorem bilinearSquareMass_gramCoefficientDilation_le
    (A : ι → Matrix d d ℂ) :
    bilinearSquareMass (gramCoefficientDilation A) Finset.univ ≤
      4 * bilinearSquareMass A Finset.univ := by
  obtain ⟨v, w, hv, hw, he⟩ := exists_bilinearSquareMass_eq
    (gramCoefficientDilation A) Finset.univ
  let vL : E := WithLp.toLp 2 (fun a : d => v (.inl a))
  let vM : E := WithLp.toLp 2 (fun a : d => v (.inr (.inl a)))
  let wL : E := WithLp.toLp 2 (fun a : d => w (.inl a))
  let wM : E := WithLp.toLp 2 (fun a : d => w (.inr (.inl a)))
  have hL := sum_bilinear_sq_le_bilinearSquareMass A Finset.univ vL wM
    ((norm_left_restriction_le v).trans hv) ((norm_middle_restriction_le w).trans hw)
  have hM := sum_bilinear_sq_le_bilinearSquareMass A Finset.univ wL vM
    ((norm_left_restriction_le w).trans hw) ((norm_middle_restriction_le v).trans hv)
  have hpoint (i : ι) :
      ‖star v.ofLp ⬝ᵥ (gramCoefficientDilation A i *ᵥ w.ofLp)‖ ^ 2 ≤
        2 * ‖star vL.ofLp ⬝ᵥ (A i *ᵥ wM.ofLp)‖ ^ 2 +
        2 * ‖star wL.ofLp ⬝ᵥ (A i *ᵥ vM.ofLp)‖ ^ 2 := by
    change ‖star v.ofLp ⬝ᵥ (dilation (gramCoefficientRow (A i)) *ᵥ w.ofLp)‖ ^ 2 ≤ _
    rw [gramDilation_bilinear_eq]
    change ‖(star vL.ofLp ⬝ᵥ (A i *ᵥ wM.ofLp)) +
      star (star wL.ofLp ⬝ᵥ (A i *ᵥ vM.ofLp))‖ ^ 2 ≤ _
    have hn := norm_add_le (star vL.ofLp ⬝ᵥ (A i *ᵥ wM.ofLp))
      (star (star wL.ofLp ⬝ᵥ (A i *ᵥ vM.ofLp)))
    rw [norm_star] at hn
    nlinarith [norm_nonneg ((star vL.ofLp ⬝ᵥ (A i *ᵥ wM.ofLp)) +
        star (star wL.ofLp ⬝ᵥ (A i *ᵥ vM.ofLp))),
      norm_nonneg (star vL.ofLp ⬝ᵥ (A i *ᵥ wM.ofLp)),
      norm_nonneg (star wL.ofLp ⬝ᵥ (A i *ᵥ vM.ofLp)),
      sq_nonneg (‖star vL.ofLp ⬝ᵥ (A i *ᵥ wM.ofLp)‖ -
        ‖star wL.ofLp ⬝ᵥ (A i *ᵥ vM.ofLp)‖)]
  rw [he]
  calc
    _ ≤ ∑ i ∈ Finset.univ, (2 * ‖star vL.ofLp ⬝ᵥ (A i *ᵥ wM.ofLp)‖ ^ 2 +
        2 * ‖star wL.ofLp ⬝ᵥ (A i *ᵥ vM.ofLp)‖ ^ 2) :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = 2 * (∑ i ∈ Finset.univ, ‖star vL.ofLp ⬝ᵥ (A i *ᵥ wM.ofLp)‖ ^ 2) +
        2 * ∑ i ∈ Finset.univ, ‖star wL.ofLp ⬝ᵥ (A i *ᵥ vM.ofLp)‖ ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by linarith


/-- The actual source weak standard deviation of the three-block
linearization is at most twice the original one, with no dimension loss. -/
theorem sqrt_bilinearSquareMass_gramCoefficientDilation_le
    (A : ι → Matrix d d ℂ) :
    Real.sqrt (bilinearSquareMass (gramCoefficientDilation A) Finset.univ) ≤
      2 * Real.sqrt (bilinearSquareMass A Finset.univ) := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (bilinearSquareMass_nonneg _ _), mul_pow,
    Real.sq_sqrt (bilinearSquareMass_nonneg _ _)]
  norm_num only
  exact bilinearSquareMass_gramCoefficientDilation_le A

end NLAlib
