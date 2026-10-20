import NLAlib.RandomMatrix.Gaussian.Basic.GUECoefficientMatrices
import NLAlib.Matrix.Structured.NormalizedPartialTrace

/-! # Exact native GUE covariance action on arbitrary tensor matrices

The actual independent-real-coordinate GUE family contracts any ensemble
matrix to its normalized partial trace. No tensor-identity premise is
imposed on the argument. This is the algebraic Gaussian integration by
parts term in the finite-N matrix Dyson equation.
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix Kronecker
namespace NLAlib
variable {n d : Type*} [Fintype n] [Fintype d] [DecidableEq n] [DecidableEq d]

/-- The actual normalized GUE covariance sends every matrix to its genuine
normalized trace times the identity. This is a direct consequence of the
true bilinear covariance of the independent real coefficient entries. -/
theorem sum_gueCoefficientMatrix_sandwich (T : Matrix n n ℂ) :
    (∑ k : GUECoordinate Unit n, gueCoefficientMatrix k*T*gueCoefficientMatrix k) =
      normalizedTrace T • (1 : Matrix n n ℂ) := by
  ext a b
  simp only [Matrix.sum_apply,Matrix.mul_apply,Finset.sum_mul]
  calc
    _ = ∑ x : n, ∑ y : n, T y x *
        ∑ k : GUECoordinate Unit n, gueCoefficientMatrix k a y*gueCoefficientMatrix k x b := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      simp_rw [sum_gueCoefficientMatrix_entry_mul]
      by_cases hab : a=b
      · subst b
        simp [normalizedTrace,Matrix.trace,Matrix.diag,← Finset.sum_mul,mul_comm]
      · simp [hab]

omit [DecidableEq d] in
/-- The genuine tensor GUE covariance action on an arbitrary matrix is the
coefficient sandwich of its actual normalized ensemble partial trace.
All empty-dimension conventions agree. Source: native Gaussian integration
by parts in arXiv:2108.06312v2, Sections 5--6. -/
theorem sum_kronecker_gueCoefficientMatrix_sandwich
    (A : Matrix d d ℂ) (T : Matrix (d×n) (d×n) ℂ) :
    (∑ k : GUECoordinate Unit n, (A⊗ₖgueCoefficientMatrix k)*T*
      (A⊗ₖgueCoefficientMatrix k)) =
      (A*normalizedPartialTrace T*A)⊗ₖ(1 : Matrix n n ℂ) := by
  ext ⟨a,r⟩ ⟨b,s⟩
  have hs (g : d×n → ℂ) : (∑ x, g x)=∑ c, ∑ u, g (c,u) := Fintype.sum_prod_type g
  simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.kroneckerMap_apply,hs,Finset.sum_mul]
  calc
    _ = ∑ c : d, ∑ u : n, ∑ e : d, ∑ v : n,
        (A a e*T (e,v) (c,u)*A c b)*
          ∑ k : GUECoordinate Unit n, gueCoefficientMatrix k r v*gueCoefficientMatrix k u s := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      simp_rw [sum_gueCoefficientMatrix_entry_mul]
      by_cases hrs : r=s
      · subst s
        simp only [true_and,Matrix.one_apply_eq,mul_one,mul_ite,mul_zero]
        simp only [normalizedPartialTrace,Finset.mul_sum,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro e _
        apply Finset.sum_congr rfl
        intro u _
        simp [mul_left_comm,mul_comm]
      · simp [hrs]

end NLAlib
