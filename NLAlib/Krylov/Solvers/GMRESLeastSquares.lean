import NLAlib.Krylov.Solvers.GMRESIterate

/-!
# Reduced least-squares realization of real and complex GMRES

Any matrix spanning the actual Krylov space realizes GMRES by solving a smaller
least-squares problem. An Arnoldi factorization `A Q = U H` with orthonormal `U`
reduces this further to `H`, including deficient `H` and early breakdown, provided
the supplied `Q` spans the attained Krylov space.

Source: Saad--Schultz (1986), Section 2; Saad (2003), Section 6.5.1.
atlas: gmres-def (partial)
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {𝕜 n k l : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
  [Fintype k] [Fintype l] [DecidableEq l]

omit [Fintype l] [DecidableEq l] in
/-- Least squares on any spanning matrix gives a GMRES iterate. No independence of
the spanning columns is needed, so exhausted Krylov spaces are included.
atlas: gmres-def (partial) -/
theorem isGMRESIterate_add_mulVec_moorePenroseInverse (A : Matrix n n 𝕜)
    (c x₀ : n → 𝕜) (q : ℕ) (Q : Matrix n k 𝕜)
    (hQ : LinearMap.range Q.mulVecLin = krylovSpace A (c - A *ᵥ x₀) q) :
    IsGMRESIterate A c x₀ q
      (x₀ + Q *ᵥ (moorePenroseInverse (A * Q) *ᵥ (c - A *ᵥ x₀))) := by
  classical
  constructor
  · rw [add_sub_cancel_left, ← hQ]
    exact ⟨_, rfl⟩
  · intro y hy
    rw [← hQ] at hy
    obtain ⟨v, hv⟩ := hy
    have hres : c - A *ᵥ (x₀ + Q *ᵥ (moorePenroseInverse (A * Q) *ᵥ (c - A *ᵥ x₀))) =
        (c - A *ᵥ x₀) - (A * Q) *ᵥ (moorePenroseInverse (A * Q) *ᵥ (c - A *ᵥ x₀)) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
      abel
    have hyres : c - A *ᵥ (x₀ + y) = (c - A *ᵥ x₀) - (A * Q) *ᵥ v := by
      rw [← hv, Matrix.mulVecLin_apply, Matrix.mulVec_add, Matrix.mulVec_mulVec]
      abel
    have h := norm_sub_mulVec_moorePenroseInverse_le (A * Q) (c - A *ᵥ x₀) v
    have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
    simpa only [hres, hyres, norm_toLp_sq_eq_re_star_dotProduct] using hs

/-- The Arnoldi least-squares formula over real or complex scalars. The dimensions
are the actual supplied frame dimensions, so there is no fictitious extra vector at
happy breakdown. The Moore--Penrose inverse handles singular reduced problems.
atlas: gmres-def (partial) -/
theorem isGMRESIterate_of_reduced_leastSquares (A : Matrix n n 𝕜)
    (c x₀ : n → 𝕜) (q : ℕ) (Q : Matrix n k 𝕜) (U : Matrix n l 𝕜) (H : Matrix l k 𝕜)
    (hQ : LinearMap.range Q.mulVecLin = krylovSpace A (c - A *ᵥ x₀) q)
    (hU : HasOrthonormalCols U) (hAQ : A * Q = U * H)
    (r : l → 𝕜) (hr : c - A *ᵥ x₀ = U *ᵥ r) :
    IsGMRESIterate A c x₀ q (x₀ + Q *ᵥ (moorePenroseInverse H *ᵥ r)) := by
  have h := isGMRESIterate_add_mulVec_moorePenroseInverse A c x₀ q Q hQ
  rw [hAQ, moorePenroseInverse_mul_left_of_hasOrthonormalCols U H hU, hr,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec r Uᴴ U, hU.conjTranspose_mul_self,
    Matrix.one_mulVec] at h
  exact h

omit [DecidableEq n] in
private theorem norm_frame_mulVec (U : Matrix n l 𝕜) (hU : HasOrthonormalCols U) (v : l → 𝕜) :
    ‖WithLp.toLp 2 (U *ᵥ v)‖ = ‖WithLp.toLp 2 v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_toLp_sq_eq_re_star_dotProduct, norm_toLp_sq_eq_re_star_dotProduct,
    star_mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols hU]

omit [DecidableEq n] in
/-- Every residual norm in a reduced Arnoldi problem equals its ambient residual norm.
For the standard Arnoldi normalization take `r = ‖r₀‖ e₁`. -/
theorem norm_sub_mulVec_add_mulVec_of_reduced (A : Matrix n n 𝕜) (c x₀ : n → 𝕜)
    (Q : Matrix n k 𝕜) (U : Matrix n l 𝕜) (H : Matrix l k 𝕜)
    (hU : HasOrthonormalCols U) (hAQ : A * Q = U * H)
    (r : l → 𝕜) (hr : c - A *ᵥ x₀ = U *ᵥ r) (v : k → 𝕜) :
    ‖WithLp.toLp 2 (c - A *ᵥ (x₀ + Q *ᵥ v))‖ = ‖WithLp.toLp 2 (r - H *ᵥ v)‖ := by
  have he : c - A *ᵥ (x₀ + Q *ᵥ v) = U *ᵥ (r - H *ᵥ v) := by
    rw [Matrix.mulVec_add, ← sub_sub, hr, Matrix.mulVec_mulVec, hAQ,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub]
  rw [he, norm_frame_mulVec U hU]

/-- The actual GMRES residual norm is the attained minimum in the reduced Arnoldi
least-squares problem. Frame dimensions are arbitrary, including the attained dimension
at happy breakdown and zero-width cases.
atlas: gmres-def (partial) -/
theorem IsGMRESIterate.isLeast_norm_reduced {A : Matrix n n 𝕜} {c x₀ x : n → 𝕜} {q : ℕ}
    (hx : IsGMRESIterate A c x₀ q x) (Q : Matrix n k 𝕜) (U : Matrix n l 𝕜) (H : Matrix l k 𝕜)
    (hQ : LinearMap.range Q.mulVecLin = krylovSpace A (c - A *ᵥ x₀) q)
    (hU : HasOrthonormalCols U) (hAQ : A * Q = U * H)
    (r : l → 𝕜) (hr : c - A *ᵥ x₀ = U *ᵥ r) :
    IsLeast (Set.range fun v : k → 𝕜 => ‖WithLp.toLp 2 (r - H *ᵥ v)‖)
      ‖WithLp.toLp 2 (c - A *ᵥ x)‖ := by
  constructor
  · have hxQ : x - x₀ ∈ LinearMap.range Q.mulVecLin := hQ.symm ▸ hx.1
    obtain ⟨v, hv⟩ := hxQ
    have he : x = x₀ + Q *ᵥ v := by rw [← Matrix.mulVecLin_apply, hv]; abel
    exact ⟨v, by rw [he, norm_sub_mulVec_add_mulVec_of_reduced A c x₀ Q U H hU hAQ r hr]⟩
  · rintro _ ⟨v, rfl⟩
    dsimp only
    rw [← norm_sub_mulVec_add_mulVec_of_reduced A c x₀ Q U H hU hAQ r hr]
    apply hx.norm_le_of_sub_mem
    rw [add_sub_cancel_left, ← hQ]
    exact ⟨v, rfl⟩

end NLAlib
