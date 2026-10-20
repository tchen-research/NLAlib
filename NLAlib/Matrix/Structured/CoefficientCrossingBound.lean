import NLAlib.Matrix.Structured.CoefficientCrossingBlock

/-!
# Actual crossed coefficient-word alignment

The actual crossing sum is a rectangular block compression by the true
coefficient stacks. Together with the covariance compression, this proves
the deterministic alignment estimate using the genuine variance and
entry-covariance matrices of the coefficient families.

Source: arXiv:2108.06312v2, Proposition 4.6.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix Kronecker

namespace NLAlib

variable {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq d]

/-- The actual four-insertion crossing sum, with arbitrary intervening
matrices and two finite Hermitian coefficient families. -/
def coefficientCrossingSum (A : ι → Matrix d d ℂ) (B : κ → Matrix d d ℂ)
    (U V W : Matrix d d ℂ) : Matrix d d ℂ :=
  ∑ i, ∑ j, A i*U*B j*V*A i*W*B j

omit [Fintype κ] [DecidableEq κ] [DecidableEq d] in
private theorem coefficientStack_conjTranspose_mul_identity_kronecker_apply
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (U : Matrix d d ℂ) (a : d) (ic : ι × d) :
    ((coefficientStack A)ᴴ*((1 : Matrix ι ι ℂ)⊗ₖU)) a ic =
      (A ic.1*U) a ic.2 := by
  simp [Matrix.mul_apply,Matrix.conjTranspose_apply,coefficientStack,
    Matrix.one_apply,Fintype.sum_prod_type,(hA _).apply,apply_ite]

omit [Fintype ι] [DecidableEq ι] [DecidableEq d] in
private theorem identity_kronecker_mul_coefficientStack_apply
    (B : κ → Matrix d d ℂ) (W : Matrix d d ℂ) (jc : κ × d) (b : d) :
    (((1 : Matrix κ κ ℂ)⊗ₖW)*coefficientStack B) jc b =
      (W*B jc.1) jc.2 b := by
  simp [Matrix.mul_apply,coefficientStack,Matrix.one_apply,Fintype.sum_prod_type,
    ite_mul]

omit [DecidableEq d] in
/-- The true crossing sum is obtained by applying the true coefficient
stacks to the actual mixed crossing block. -/
theorem coefficientCrossingSum_eq_stack_compression
    (A : ι → Matrix d d ℂ) (B : κ → Matrix d d ℂ)
    (hA : ∀ i, (A i).IsHermitian) (U V W : Matrix d d ℂ) :
    coefficientCrossingSum A B U V W =
      ((coefficientStack A)ᴴ*((1 : Matrix ι ι ℂ)⊗ₖU))*
        coefficientCrossingBlock A B V*
          (((1 : Matrix κ κ ℂ)⊗ₖW)*coefficientStack B) := by
  have hLmat : (coefficientStack A)ᴴ*((1 : Matrix ι ι ℂ)⊗ₖU) =
      (fun a ic => (A ic.1*U) a ic.2) := by
    funext a ic
    exact coefficientStack_conjTranspose_mul_identity_kronecker_apply A hA U a ic
  have hRmat : ((1 : Matrix κ κ ℂ)⊗ₖW)*coefficientStack B =
      (fun jc b => (W*B jc.1) jc.2 b) := by
    funext jc b
    exact identity_kronecker_mul_coefficientStack_apply B W jc b
  rw [hLmat,hRmat]
  ext a b
  symm
  calc
    _ = ∑ j, ∑ y, ∑ i, ∑ x,
        (A i*U) a x*(B j*V*A i) x y*(W*B j) y b := by
      simp only [Matrix.mul_apply,Fintype.sum_prod_type,coefficientCrossingBlock,
        Finset.sum_mul]
    _ = ∑ i, ∑ j, ∑ y, ∑ x,
        (A i*U) a x*(B j*V*A i) x y*(W*B j) y b := by
      calc
        _ = ∑ j, ∑ i, ∑ y, ∑ x,
            (A i*U) a x*(B j*V*A i) x y*(W*B j) y b := by
          apply Finset.sum_congr rfl
          intro j _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      simp only [coefficientCrossingSum,Matrix.sum_apply]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = (((A i*U)*(B j*V*A i))*(W*B j)) a b := by
          simp only [Matrix.mul_apply,Finset.sum_mul]
        _ = _ := by simp only [Matrix.mul_assoc]

open scoped Matrix.Norms.L2Operator in
/-- A true rectangular coefficient-stack compression gives the alignment
bound without a unitary-extremal or probabilistic assumption. -/
theorem specNorm_coefficientCrossingSum_le_stack_vectorization
    (A : ι → Matrix d d ℂ) (B : κ → Matrix d d ℂ)
    (hA : ∀ i, (A i).IsHermitian) (U V W : Matrix d d ℂ) :
    specNorm (coefficientCrossingSum A B U V W) ≤
      (specNorm (coefficientStack A)*specNorm (coefficientVectorization A)*
        specNorm (coefficientVectorization B)*specNorm (coefficientStack B))*
          (specNorm U*specNorm V*specNorm W) := by
  have hIι : specNorm (1 : Matrix ι ι ℂ) ≤ 1 := specNorm_one_le
  have hIκ : specNorm (1 : Matrix κ κ ℂ) ≤ 1 := specNorm_one_le
  have hL : specNorm ((coefficientStack A)ᴴ*((1 : Matrix ι ι ℂ)⊗ₖU)) ≤
      specNorm (coefficientStack A)*specNorm U := by
    apply (specNorm_mul_le _ _).trans
    rw [specNorm_conjTranspose,specNorm_kronecker]
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (specNorm_nonneg _) hIι) (specNorm_nonneg _)
  have hR : specNorm (((1 : Matrix κ κ ℂ)⊗ₖW)*coefficientStack B) ≤
      specNorm W*specNorm (coefficientStack B) := by
    apply (specNorm_mul_le _ _).trans
    rw [specNorm_kronecker]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left (specNorm_nonneg _) hIκ) (specNorm_nonneg _)
  rw [coefficientCrossingSum_eq_stack_compression A B hA U V W]
  calc
    _ ≤ (specNorm ((coefficientStack A)ᴴ*((1 : Matrix ι ι ℂ)⊗ₖU))*
        specNorm (coefficientCrossingBlock A B V))*
          specNorm (((1 : Matrix κ κ ℂ)⊗ₖW)*coefficientStack B) :=
      (specNorm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _))
    _ ≤ ((specNorm (coefficientStack A)*specNorm U)*
        (specNorm (coefficientVectorization A)*specNorm V*
          specNorm (coefficientVectorization B)))*
        (specNorm W*specNorm (coefficientStack B)) := by
      have hmid := mul_le_mul hL
        (specNorm_coefficientCrossingBlock_le A B hA V)
        (specNorm_nonneg _)
        (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _))
      exact mul_le_mul hmid hR (specNorm_nonneg _)
        (mul_nonneg
          (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _))
          (mul_nonneg
            (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)) (specNorm_nonneg _)))
    _ = _ := by ring

omit [DecidableEq ι] in
/-- The actual stack norm is the square root of the actual variance norm
for a Hermitian family, retaining all empty dimensions. -/
theorem specNorm_coefficientStack_eq_sqrt_variance
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) :
    specNorm (coefficientStack A) = Real.sqrt (specNorm (coefficientVariance A)) := by
  rw [← coefficientStack_gram A hA,← specNorm_sq_eq_specNorm_conjTranspose_mul_self,
    Real.sqrt_sq (specNorm_nonneg _)]

/-- Genuine covariance alignment for two actual Hermitian coefficient
families. All variance, covariance, and multiplier factors are explicit.
Source: arXiv:2108.06312v2, Proposition 4.6.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem specNorm_coefficientCrossingSum_le_variance_covariance
    (A : ι → Matrix d d ℂ) (B : κ → Matrix d d ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hB : ∀ j, (B j).IsHermitian)
    (U V W : Matrix d d ℂ) :
    specNorm (coefficientCrossingSum A B U V W) ≤
      (Real.sqrt (specNorm (coefficientVariance A))*
        Real.sqrt (specNorm (coefficientCovariance A))*
        Real.sqrt (specNorm (coefficientCovariance B))*
        Real.sqrt (specNorm (coefficientVariance B)))*
          (specNorm U*specNorm V*specNorm W) := by
  simpa only [specNorm_coefficientStack_eq_sqrt_variance A hA,
    specNorm_coefficientStack_eq_sqrt_variance B hB,
    specNorm_coefficientVectorization_eq_sqrt_covariance] using
      specNorm_coefficientCrossingSum_le_stack_vectorization A B hA U V W

end NLAlib

end
