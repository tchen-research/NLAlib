import NLAlib.Matrix.Perturbation.HoffmanWielandtNormal
import NLAlib.Matrix.Inequalities.MajorizationProperties
/-!
# Complex Hermitian diagonal majorization

Squared unitary entries give the exact doubly stochastic map from a Hermitian
spectrum to its real diagonal. Source: Horn--Johnson (2013), Theorem 4.3.45;
supports `real-part-eigenvalue-majorization`.
-/

noncomputable section
open Matrix
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real diagonal of a complex Hermitian matrix is the doubly stochastic
weighted average of its eigenvalues, with squared eigenvector entries as
the weights. Horn--Johnson (2013), Theorem 4.3.45;
helper for real-part eigenvalue majorization. -/
theorem real_diagonal_eq_norm_sq_mulVec_eigenvalues {A : Matrix n n ℂ}
    (hA : A.IsHermitian) :
    (fun i => (A i i).re) =
      (Matrix.of fun i j => ‖(hA.eigenvectorUnitary : Matrix n n ℂ) i j‖ ^ 2) *ᵥ hA.eigenvalues := by
  let U : Matrix n n ℂ := hA.eigenvectorUnitary
  have hs : A = U * diagonal (fun i => (hA.eigenvalues i : ℂ)) * Uᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal, U] using hA.spectral_theorem
  funext i
  calc
    (A i i).re = ((U * diagonal (fun j => (hA.eigenvalues j : ℂ)) * Uᴴ) i i).re :=
      congrArg (fun M : Matrix n n ℂ => (M i i).re) hs
    _ = _ := by
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply,
        Complex.star_def, Complex.re_sum, Matrix.mulVec, dotProduct, Matrix.of_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_right_comm, Complex.mul_conj']
      simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
      rfl

/-- The real diagonal of a complex Hermitian matrix is majorized by its
actual real eigenvalue list. Arbitrary finite indices and repeated eigenvalues
are included. Horn--Johnson (2013), Theorem 4.3.45;
helper for real-part eigenvalue majorization. -/
theorem majorized_real_diagonal_eigenvalues {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    Majorized (fun i => (A i i).re) hA.eigenvalues := by
  rw [real_diagonal_eq_norm_sq_mulVec_eigenvalues hA]
  exact majorized_mulVec_of_doublyStochastic hA.eigenvalues
    (norm_sq_entries_mem_doublyStochastic hA.eigenvectorUnitary)

/-- Every real diagonal entry of a complex Hermitian matrix lies between
its smallest and largest sorted eigenvalues. Horn--Johnson (2013),
Corollary 4.3.46; helper for Bendixson's bounds. -/
theorem real_diagonal_mem_Icc_eigenvalues₀ {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (i : n) (hcard : 0 < Fintype.card n) :
    (A i i).re ∈ Set.Icc
      (hA.eigenvalues₀ ⟨Fintype.card n - 1, Nat.sub_lt hcard (by decide)⟩)
      (hA.eigenvalues₀ ⟨0, hcard⟩) := by
  let D := Matrix.of fun i j => ‖(hA.eigenvectorUnitary : Matrix n n ℂ) i j‖ ^ 2
  have hD := norm_sq_entries_mem_doublyStochastic hA.eigenvectorUnitary
  rw [mem_doublyStochastic_iff_sum] at hD
  have hrow : ∑ j, D i j = 1 := hD.2.1 i
  have hnonneg : ∀ j, 0 ≤ D i j := fun j => hD.1 i j
  have heq := congrFun (real_diagonal_eq_norm_sq_mulVec_eigenvalues hA) i
  change (A i i).re = ∑ j, D i j * hA.eigenvalues j at heq
  rw [heq]
  constructor
  · calc
      _ = ∑ j, D i j * hA.eigenvalues₀ ⟨Fintype.card n - 1, Nat.sub_lt hcard (by decide)⟩ := by
        rw [← Finset.sum_mul, hrow, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
        (hA.eigenvalues₀_antitone (by exact Nat.le_pred_of_lt (Fin.isLt _))) (hnonneg j)
  · calc
      _ ≤ ∑ j, D i j * hA.eigenvalues₀ ⟨0, hcard⟩ := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hA.eigenvalues₀_antitone (by exact Nat.zero_le _)) (hnonneg j)
      _ = _ := by rw [← Finset.sum_mul, hrow, one_mul]

end NLAlib
