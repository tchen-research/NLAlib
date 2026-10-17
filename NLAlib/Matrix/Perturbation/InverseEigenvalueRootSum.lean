import NLAlib.Matrix.Perturbation.InverseEigenvalueReflection
import NLAlib.Matrix.Perturbation.PencilRootSum

/-!
# Identification of the exterior inverse root sum

The labelled exterior inverse branches form the complete characteristic-root
list. Their upper-half-plane labels identify the strict-sublevel branch sum with
the actual multiplicity-counted upper-root sum of the Hermitian pencil.
This is a bridge for the planar approach to `trace-exponential-stahl`.
-/

noncomputable section

open Complex Filter
open scoped Matrix Topology ComplexConjugate

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The diagonal slope matrix `diag (bᵢ - s)` is invertible when `s` avoids its
finitely many diagonal values. -/
theorem isUnit_diagonal_sub_of_ne (b : n → ℝ) (s : ℝ) (hs : ∀ i, s ≠ b i) :
    IsUnit (Matrix.diagonal (fun i => ((b i - s : ℝ) : ℂ))) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_diagonal]
  apply isUnit_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact_mod_cast sub_ne_zero.mpr (hs i).symm

/-- The inverse matrix of a diagonal Hermitian pencil is exactly the affine
pencil used to construct its exterior inverse branches. -/
theorem inv_mul_sub_smul_one_diagonal_eq (A : Matrix n n ℂ) (b : n → ℝ)
    (s : ℝ) (hs : ∀ i, s ≠ b i) (u : ℂ) :
    (Matrix.diagonal (fun i => ((b i - s : ℝ) : ℂ)))⁻¹ *
        (A - u • (1 : Matrix n n ℂ)) =
      -(Matrix.diagonal (fun i => ((s - b i : ℝ) : ℂ)⁻¹) * A) +
        u • Matrix.diagonal (fun i => ((s - b i : ℝ) : ℂ)⁻¹) := by
  let D : Matrix n n ℂ := Matrix.diagonal (fun i => ((b i - s : ℝ) : ℂ))
  let E : Matrix n n ℂ := Matrix.diagonal (fun i => ((s - b i : ℝ) : ℂ)⁻¹)
  have hc (i : n) : ((s - b i : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr (hs i)
  have hneg (i : n) : ((b i - s : ℝ) : ℂ) = -((s - b i : ℝ) : ℂ) := by
    push_cast
    ring
  have hDE : D * (-E) = 1 := by
    rw [Matrix.mul_neg]
    dsimp only [D, E]
    rw [Matrix.diagonal_mul_diagonal]
    have hentry : (fun i => ((b i - s : ℝ) : ℂ) * ((s - b i : ℝ) : ℂ)⁻¹) =
        fun _ => (-1 : ℂ) := by
      funext i
      rw [hneg, neg_mul, mul_inv_cancel₀ (hc i)]
    rw [hentry, ← Matrix.diagonal_neg]
    simp
  have hinv : D⁻¹ = -E := Matrix.inv_eq_right_inv hDE
  change D⁻¹ * (A - u • (1 : Matrix n n ℂ)) = -(E * A) + u • E
  rw [hinv, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.neg_mul, smul_neg]
  abel

/-- A complete exterior inverse branch family with the proved upper labels
computes the actual upper-root sum of the inverse characteristic polynomial. -/
theorem inversePencilUpperRootSum_eq_sum_ite_of_inverse_branches
    (A : Matrix n n ℂ) (b : n → ℝ) (s : ℝ) (hs : ∀ i, s ≠ b i)
    (branch : n → ℂ → ℂ) (u : ℂ)
    (hspec : ∀ i, u - (s : ℂ) * branch i u ∈ spectrum ℂ
      (A - branch i u • Matrix.diagonal (fun i => (b i : ℂ))))
    (hinj : Function.Injective (fun i => branch i u))
    (hlabel : ∀ i, 0 < (branch i u).im ↔ b i < s) :
    inversePencilUpperRootSum A (Matrix.diagonal (fun i => ((b i - s : ℝ) : ℂ))) u =
      ∑ i, if b i < s then branch i u else 0 := by
  classical
  let M : Matrix n n ℂ :=
    -(Matrix.diagonal (fun i => ((s - b i : ℝ) : ℂ)⁻¹) * A) +
      u • Matrix.diagonal (fun i => ((s - b i : ℝ) : ℂ)⁻¹)
  have hmem : ∀ i, branch i u ∈ spectrum ℂ M := fun i =>
    (mem_spectrum_inverse_diagonal_pencil_iff A b s hs u _).mpr (hspec i)
  unfold inversePencilUpperRootSum
  rw [inv_mul_sub_smul_one_diagonal_eq A b s hs u,
    Matrix.sum_filter_roots_charpoly_eq_sum_ite_of_injective_mem_spectrum M
      (fun i => branch i u) hinj hmem]
  apply Finset.sum_congr rfl
  intro i _
  simp only [hlabel i]

open scoped Matrix.Norms.L2Operator in
/-- One constructed family of exterior inverse branches supplies holomorphy,
the complete spectral list, the strict-sublevel labels, Schwarz reflection, and
the identity with the actual upper-root sum throughout the exterior upper half-plane.

atlas: trace-exponential-stahl (partial) -/
theorem exists_exterior_inverse_eigenvalue_branches_root_sum
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (b : n → ℝ)
    (hb : Function.Injective b) (s : ℝ) (hs : ∀ i, s ≠ b i) :
    ∃ R : ℝ, 0 < R ∧ ∃ branch : n → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (branch i) {u | R < ‖u‖} ∧
        Tendsto (fun u => branch i u - u / ((s - b i : ℝ) : ℂ))
          (Bornology.cobounded ℂ) (𝓝 (-A i i / ((s - b i : ℝ) : ℂ)))) ∧
      (∀ u, R < ‖u‖ →
        (∀ i, u - (s : ℂ) * branch i u ∈ spectrum ℂ
          (A - branch i u • Matrix.diagonal (fun i => (b i : ℂ)))) ∧
        Function.Injective (fun i => branch i u)) ∧
      (∀ u, R < ‖u‖ → 0 < u.im → ∀ i, 0 < (branch i u).im ↔ b i < s) ∧
      (∀ i u, R < ‖u‖ → branch i (conj u) = conj (branch i u)) ∧
      ∀ u, R < ‖u‖ → 0 < u.im →
        inversePencilUpperRootSum A (Matrix.diagonal (fun i => ((b i - s : ℝ) : ℂ))) u =
          ∑ i, if b i < s then branch i u else 0 := by
  obtain ⟨R, hR, branch, hbranch, hspec, hlabel, href⟩ :=
    exists_exterior_inverse_eigenvalue_branches_im_pos_iff_conj_eq hA b hb s hs
  refine ⟨R, hR, branch, hbranch, hspec, hlabel, href, ?_⟩
  intro u hu him
  exact inversePencilUpperRootSum_eq_sum_ite_of_inverse_branches A b s hs branch u
    (hspec u hu).1 (hspec u hu).2 (hlabel u hu him)

end NLAlib
