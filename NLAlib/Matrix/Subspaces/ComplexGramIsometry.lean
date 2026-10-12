import NLAlib.ForMathlib.Analysis.RangeIsometry

/-!
# Complex unitary transport of equal Gram matrices

Equal-Gram matrices differ by a left unitary factor even when they have
deficient rank. The proof extends an isometry between their actual ranges.
-/

noncomputable section
open scoped InnerProductSpace Matrix
namespace NLAlib

/-- A complex linear isometry has an isometric-column matrix in standard
Euclidean coordinates. Horn–Johnson 2013, Section 2.1; complex CS helper. -/
theorem conjTranspose_mul_self_toEuclideanLin_symm {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n]
    (L : EuclideanSpace ℂ n →ₗᵢ[ℂ] EuclideanSpace ℂ m) :
    (Matrix.toEuclideanLin.symm L.toLinearMap)ᴴ *
      (Matrix.toEuclideanLin.symm L.toLinearMap) = 1 := by
  classical
  let Q : Matrix m n ℂ := Matrix.toEuclideanLin.symm L.toLinearMap
  have hQ : Q.toEuclideanLin = L.toLinearMap := Matrix.toEuclideanLin.apply_symm_apply _
  apply Matrix.toEuclideanLin.injective
  calc
    (Qᴴ * Q).toEuclideanLin = LinearMap.adjoint Q.toEuclideanLin ∘ₗ Q.toEuclideanLin := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]
    _ = LinearMap.id := by rw [hQ]; exact L.adjoint_comp_self'
    _ = (1 : Matrix n n ℂ).toEuclideanLin := by
      simp only [Matrix.toEuclideanLin, Matrix.toLpLin_one]

/-- Equal complex Gram matrices give identical lengths at every vector.
Horn–Johnson 2013, Section 2.1; complex CS equal-Gram helper. -/
theorem norm_toEuclideanLin_apply_eq_of_complex_gram_eq {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p] [DecidableEq n] (A : Matrix m n ℂ) (B : Matrix p n ℂ)
    (hGram : Aᴴ * A = Bᴴ * B) (x : EuclideanSpace ℂ n) :
    ‖A.toEuclideanLin x‖ = ‖B.toEuclideanLin x‖ := by
  classical
  have hG : LinearMap.adjoint A.toEuclideanLin ∘ₗ A.toEuclideanLin =
      LinearMap.adjoint B.toEuclideanLin ∘ₗ B.toEuclideanLin := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same] using
      congrArg (fun M : Matrix n n ℂ => M.toEuclideanLin) hGram
  have hi : inner ℂ (A.toEuclideanLin x) (A.toEuclideanLin x) =
      inner ℂ (B.toEuclideanLin x) (B.toEuclideanLin x) := by
    rw [← LinearMap.adjoint_inner_right, ← LinearMap.adjoint_inner_right]
    exact congrArg (inner ℂ x) (LinearMap.congr_fun hG x)
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [inner_self_eq_norm_sq_to_K] at hi
  exact_mod_cast hi

/-- Two complex matrices of the same shape and with equal Gram matrices
differ by an ambient left unitary factor. Singular and empty matrices are
included. Horn–Johnson 2013, Section 2.1; complex CS completion helper. -/
theorem exists_unitary_mul_eq_of_gram_eq {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] (A B : Matrix m n ℂ)
    (hGram : Aᴴ * A = Bᴴ * B) :
    ∃ U : Matrix.unitaryGroup m ℂ, (U : Matrix m m ℂ) * B = A := by
  classical
  obtain ⟨L, hL⟩ := exists_linearIsometry_comp_eq_of_norm_eq A.toEuclideanLin B.toEuclideanLin
    (norm_toEuclideanLin_apply_eq_of_complex_gram_eq A B hGram)
  let U : Matrix m m ℂ := Matrix.toEuclideanLin.symm L.toLinearMap
  have hU : Uᴴ * U = 1 := conjTranspose_mul_self_toEuclideanLin_symm L
  refine ⟨⟨U, Matrix.mem_unitaryGroup_iff'.mpr hU⟩, ?_⟩
  apply Matrix.toEuclideanLin.injective
  simpa only [U, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
    LinearEquiv.apply_symm_apply] using hL

end NLAlib
