import NLAlib.Matrix.Subspaces.OrthogonalProducts
import NLAlib.Matrix.Basic.MoorePenrose

/-!
# Isometries from matrix Gram identities

Equal Gram matrices identify Euclidean lengths and the associated range
isometry. Extending that isometry provides rank-deficient QR.
Source: operator derivations `root:gram-isometry`; supports `qr-decomposition`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq n]

/-- Equal real Gram matrices give equal Euclidean lengths at every vector,
including deficient rank and empty spaces. Supports `qr-decomposition`. -/
theorem norm_toEuclideanLin_apply_eq_of_gram_eq (A : Matrix m n ℝ) (B : Matrix p n ℝ)
    (hGram : Aᵀ * A = Bᵀ * B) (x : EuclideanSpace ℝ n) :
    ‖A.toEuclideanLin x‖ = ‖B.toEuclideanLin x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have h := congrArg (fun M : Matrix n n ℝ => x.ofLp ⬝ᵥ M *ᵥ x.ofLp) hGram
  rw [← show (A *ᵥ x.ofLp) ⬝ᵥ (A *ᵥ x.ofLp) = x.ofLp ⬝ᵥ ((Aᵀ * A) *ᵥ x.ofLp) from
      star_mulVec_dotProduct_mulVec_self A x.ofLp,
    ← show (B *ᵥ x.ofLp) ⬝ᵥ (B *ᵥ x.ofLp) = x.ofLp ⬝ᵥ ((Bᵀ * B) *ᵥ x.ofLp) from
      star_mulVec_dotProduct_mulVec_self B x.ofLp] at h
  change ‖(WithLp.toLp 2 (A *ᵥ x.ofLp) : EuclideanSpace ℝ m)‖ ^ 2 =
    ‖(WithLp.toLp 2 (B *ᵥ x.ofLp) : EuclideanSpace ℝ p)‖ ^ 2
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simpa only [dotProduct, sq] using h

/-- Every actual Euclidean linear isometry has an orthonormal-column matrix
in the standard coordinates. Supports `qr-decomposition`. -/
theorem hasOrthonormalCols_toEuclideanLin_symm (L : EuclideanSpace ℝ n →ₗᵢ[ℝ] EuclideanSpace ℝ m) :
    HasOrthonormalCols (Matrix.toEuclideanLin.symm L.toLinearMap) := by
  classical
  let Q : Matrix m n ℝ := Matrix.toEuclideanLin.symm L.toLinearMap
  have hQ : Q.toEuclideanLin = L.toLinearMap := Matrix.toEuclideanLin.apply_symm_apply _
  show Qᵀ * Q = 1
  apply Matrix.toEuclideanLin.injective
  calc
    (Qᵀ * Q).toEuclideanLin = LinearMap.adjoint Q.toEuclideanLin ∘ₗ Q.toEuclideanLin := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
        Matrix.conjTranspose_eq_transpose_of_trivial]
    _ = LinearMap.id := by rw [hQ]; exact L.adjoint_comp_self'
    _ = (1 : Matrix n n ℝ).toEuclideanLin := by
      simp only [Matrix.toEuclideanLin, Matrix.toLpLin_one]

/-- Equal Grams imply that the first matrix vanishes on the kernel complement
of the second matrix's row projector. Supports rank-deficient QR. -/
theorem mul_moorePenroseInverse_mul_eq_of_gram_eq (A : Matrix m n ℝ) (R : Matrix p n ℝ)
    (hGram : Aᵀ * A = Rᵀ * R) : A * moorePenroseInverse R * R = A := by
  let F : Matrix n n ℝ := 1 - moorePenroseInverse R * R
  have hRF : R * F = 0 := by
    simp only [F, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
      mul_moorePenroseInverse_mul, sub_self]
  have hAF : A * F = 0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul]
    calc
      Fᵀ * Aᵀ * (A * F) = Fᵀ * (Rᵀ * R) * F := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc Aᵀ A F, hGram]
        simp only [Matrix.mul_assoc]
      _ = 0 := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hRF, Matrix.mul_zero, Matrix.mul_zero]
  simp only [F, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc] at hAF
  exact (sub_eq_zero.mp hAF).symm

/-- Equal Gram matrices with the same ambient row space differ by an actual
orthogonal transformation, also at zero rank. The range isometry extends
through Mathlib's finite-dimensional isometry extension. Source: operator
derivations `root:gram-isometry`; supports `qr-decomposition`. -/
theorem exists_orthogonal_mul_eq_of_gram_eq [DecidableEq m] (A B : Matrix m n ℝ)
    (hGram : Aᵀ * A = Bᵀ * B) :
    ∃ U : Matrix m m ℝ, HasOrthonormalCols U ∧ U * B = A := by
  classical
  let S := LinearMap.range B.toEuclideanLin
  have hReconstruct : A * moorePenroseInverse B * B = A :=
    mul_moorePenroseInverse_mul_eq_of_gram_eq A B hGram
  let L : S →ₗᵢ[ℝ] EuclideanSpace ℝ m :=
    { toLinearMap := (A * moorePenroseInverse B).toEuclideanLin.comp S.subtype
      norm_map' := by
        intro z
        obtain ⟨x, hx⟩ := z.property
        have hApply : (A * moorePenroseInverse B).toEuclideanLin
            (B.toEuclideanLin x) = A.toEuclideanLin x := by
          rw [← LinearMap.comp_apply]
          rw [← Matrix.toLpLin_mul_same]
          exact congrArg (fun M : Matrix m n ℝ => M.toEuclideanLin x) hReconstruct
        change ‖(A * moorePenroseInverse B).toEuclideanLin z.val‖ = ‖z.val‖
        rw [← hx, hApply]
        exact norm_toEuclideanLin_apply_eq_of_gram_eq A B hGram x }
  let U : Matrix m m ℝ := Matrix.toEuclideanLin.symm L.extend.toLinearMap
  refine ⟨U, hasOrthonormalCols_toEuclideanLin_symm L.extend, ?_⟩
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro x
  have hU : U.toEuclideanLin = L.extend.toLinearMap :=
    Matrix.toEuclideanLin.apply_symm_apply _
  have hExtend := L.extend_apply ⟨B.toEuclideanLin x, LinearMap.mem_range_self _ x⟩
  have hApply : (A * moorePenroseInverse B).toEuclideanLin
      (B.toEuclideanLin x) = A.toEuclideanLin x := by
    rw [← LinearMap.comp_apply]
    rw [← Matrix.toLpLin_mul_same]
    exact congrArg (fun M : Matrix m n ℝ => M.toEuclideanLin x) hReconstruct
  calc
    (U * B).toEuclideanLin x = U.toEuclideanLin (B.toEuclideanLin x) := by
      simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
    _ = L.extend (B.toEuclideanLin x) := congrArg (fun T => T (B.toEuclideanLin x)) hU
    _ = L ⟨B.toEuclideanLin x, LinearMap.mem_range_self _ x⟩ := hExtend
    _ = (A * moorePenroseInverse B).toEuclideanLin (B.toEuclideanLin x) := rfl
    _ = A.toEuclideanLin x := hApply

/-- An orthonormal coordinate frame exists whenever the column dimension does
not exceed the row dimension. Supports `qr-decomposition`. -/
theorem exists_hasOrthonormalCols_of_card_le (hCard : Fintype.card n ≤ Fintype.card m) :
    ∃ J : Matrix m n ℝ, HasOrthonormalCols J := by
  classical
  let e : n ↪ m :=
    { toFun := fun j => (Fintype.equivFin m).symm
        ⟨((Fintype.equivFin n) j).val, ((Fintype.equivFin n) j).isLt.trans_le hCard⟩
      inj' := by
        intro i j hij
        apply (Fintype.equivFin n).injective
        apply Fin.ext
        have h := congrArg (fun k => ((Fintype.equivFin m) k).val) hij
        simpa only [Equiv.apply_symm_apply] using h }
  refine ⟨(1 : Matrix m m ℝ).submatrix id e, ?_⟩
  have hOne : HasOrthonormalCols (1 : Matrix m m ℝ) := by simp [HasOrthonormalCols]
  exact hOne.submatrix_cols e

end NLAlib
