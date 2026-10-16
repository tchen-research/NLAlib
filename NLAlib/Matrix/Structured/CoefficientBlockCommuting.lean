import NLAlib.Matrix.Structured.CoefficientBlock

/-! # Commuting Hermitian coefficients attain the variance parameter

Commutation turns the partially transposed block matrix into an actual
Gram matrix. Equality of the two Gram norms then proves the sharp equality
without choosing or ordering a simultaneous eigenbasis.
Source: Bandeira et al. (2026), Proposition 1.3.
-/
noncomputable section
open Matrix
open scoped Matrix ComplexOrder
namespace NLAlib
variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq ι] [DecidableEq d]

omit [Fintype ι] [DecidableEq ι] [DecidableEq d] in
/-- Commuting coefficients make the partially transposed block an actual Gram matrix. -/
theorem coefficientBlock_eq_stack_gram_of_commute (A : ι → Matrix d d ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hcomm : ∀ i j, Commute (A i) (A j)) :
    coefficientBlock A = coefficientStack A * (coefficientStack A)ᴴ := by
  ext ic je
  simp only [coefficientBlock, Matrix.mul_apply, Matrix.conjTranspose_apply, coefficientStack]
  have he := congrFun (congrFun (hcomm je.1 ic.1).eq ic.2) je.2
  simp only [Matrix.mul_apply] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro a _
  rw [(hA je.1).apply]

omit [DecidableEq ι] [DecidableEq d] in
/-- The coefficient block is PSD in the commuting case. -/
theorem posSemidef_coefficientBlock_of_commute (A : ι → Matrix d d ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hcomm : ∀ i j, Commute (A i) (A j)) :
    (coefficientBlock A).PosSemidef := by
  rw [coefficientBlock_eq_stack_gram_of_commute A hA hcomm]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- Commuting Hermitian coefficients attain the variance spectral norm. -/
theorem specNorm_coefficientBlock_eq_variance_of_commute (A : ι → Matrix d d ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hcomm : ∀ i j, Commute (A i) (A j)) :
    specNorm (coefficientBlock A) = specNorm (coefficientVariance A) := by
  rw [coefficientBlock_eq_stack_gram_of_commute A hA hcomm,
    specNorm_mul_conjTranspose_self, ← coefficientStack_gram A hA,
    ← specNorm_sq_eq_specNorm_conjTranspose_mul_self]

/-- The largest block eigenvalue equals the squared variance parameter when
the coefficients commute; no simultaneous diagonalization premise is needed. -/
theorem lambdaMax_coefficientBlock_eq_variance_of_commute [Nonempty ι] [Nonempty d]
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hcomm : ∀ i j, Commute (A i) (A j)) :
    lambdaMax (coefficientBlock A) = specNorm (coefficientVariance A) := by
  rw [(posSemidef_coefficientBlock_of_commute A hA hcomm).lambdaMax_eq_specNorm,
    specNorm_coefficientBlock_eq_variance_of_commute A hA hcomm]

/-- Pairwise commuting Hermitian coefficients give exactly `kappa = sigma`.
Source: Bandeira et al. (2026), Proposition 1.3.
atlas: coefficient-block-partial-transpose (partial) -/
theorem coefficientBlockKappa_eq_variance_of_commute [Nonempty ι] [Nonempty d]
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hcomm : Pairwise fun i j => Commute (A i) (A j)) :
    coefficientBlockKappa A = Real.sqrt (specNorm (coefficientVariance A)) := by
  have hc : ∀ i j, Commute (A i) (A j) := by
    intro i j
    by_cases hij : i = j
    · subst j; exact Commute.refl _
    · exact hcomm hij
  rw [coefficientBlockKappa, lambdaMax_coefficientBlock_eq_variance_of_commute A hA hc]

end NLAlib
