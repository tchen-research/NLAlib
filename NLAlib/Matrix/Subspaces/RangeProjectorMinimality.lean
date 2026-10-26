import NLAlib.Matrix.Subspaces.RangeProjector

/-!
# The vector residual of a range projector is minimal

The Moore--Penrose range projector is the closest vector in the range, over real or
complex scalars and at every rank. This transfers Mathlib's Hilbert-space best-approximation
theorem to the matrix and Euclidean-vector vocabulary used by GMRES.
Source: Golub--Van Loan (2013), Section 5.5.2.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- Orthogonal projection onto a matrix's range minimizes the Euclidean residual.
No injectivity or nonempty-index assumption is needed. -/
theorem norm_sub_rangeProjector_mulVec_le (B : Matrix m n 𝕜) (b : m → 𝕜) (c : n → 𝕜) :
    ‖WithLp.toLp 2 (b - rangeProjector B *ᵥ b)‖ ≤ ‖WithLp.toLp 2 (b - B *ᵥ c)‖ := by
  have hp := congrArg (fun f : EuclideanSpace 𝕜 m →ₗ[𝕜] EuclideanSpace 𝕜 m =>
    f (WithLp.toLp 2 b)) (toEuclideanLin_rangeProjector B)
  change WithLp.toLp 2 (rangeProjector B *ᵥ b) =
    (columnSpace B).starProjection (WithLp.toLp 2 b) at hp
  have hc : WithLp.toLp 2 (B *ᵥ c) ∈ columnSpace B :=
    ⟨WithLp.toLp 2 c, rfl⟩
  change ‖WithLp.toLp 2 b - WithLp.toLp 2 (rangeProjector B *ᵥ b)‖ ≤
    ‖WithLp.toLp 2 b - WithLp.toLp 2 (B *ᵥ c)‖
  rw [hp, Submodule.starProjection_minimal]
  exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩
    (⟨WithLp.toLp 2 (B *ᵥ c), hc⟩ : columnSpace B)

/-- The Moore--Penrose solution minimizes the residual, over real and complex scalars. -/
theorem norm_sub_mulVec_moorePenroseInverse_le (B : Matrix m n 𝕜)
    (b : m → 𝕜) (c : n → 𝕜) :
    ‖WithLp.toLp 2 (b - B *ᵥ (moorePenroseInverse B *ᵥ b))‖ ≤
      ‖WithLp.toLp 2 (b - B *ᵥ c)‖ := by
  rw [Matrix.mulVec_mulVec]
  exact norm_sub_rangeProjector_mulVec_le B b c

/-- The vector in a matrix's range with minimal Euclidean distance is its orthogonal
projection. In particular the fitted vector is unique even when coefficient vectors are not. -/
theorem eq_rangeProjector_mulVec_of_minimal {B : Matrix m n 𝕜} {b y : m → 𝕜}
    (hy : y ∈ LinearMap.range B.mulVecLin)
    (hmin : ∀ c : n → 𝕜, ‖WithLp.toLp 2 (b - y)‖ ≤ ‖WithLp.toLp 2 (b - B *ᵥ c)‖) :
    y = rangeProjector B *ᵥ b := by
  have hy' : WithLp.toLp 2 y ∈ columnSpace B := by
    obtain ⟨c, rfl⟩ := hy
    exact ⟨WithLp.toLp 2 c, rfl⟩
  have hdist : ‖WithLp.toLp 2 b - WithLp.toLp 2 y‖ =
      ⨅ w : columnSpace B, ‖WithLp.toLp 2 b - w‖ := by
    apply le_antisymm
    · apply le_ciInf
      intro w
      obtain ⟨c, hc⟩ := w.property
      have hh := hmin c.ofLp
      change ‖WithLp.toLp 2 b - WithLp.toLp 2 y‖ ≤
        ‖WithLp.toLp 2 b - Matrix.toEuclideanLin B c‖ at hh
      simpa only [hc] using hh
    · exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩
        (⟨WithLp.toLp 2 y, hy'⟩ : columnSpace B)
  have he := (columnSpace B).eq_starProjection_of_mem_of_inner_eq_zero hy'
    (((columnSpace B).norm_eq_iInf_iff_inner_eq_zero hy').mp hdist)
  have hp := congrArg (fun f : EuclideanSpace 𝕜 m →ₗ[𝕜] EuclideanSpace 𝕜 m =>
    f (WithLp.toLp 2 b)) (toEuclideanLin_rangeProjector B)
  apply WithLp.toLp_injective 2
  exact he.symm.trans hp.symm

end NLAlib
