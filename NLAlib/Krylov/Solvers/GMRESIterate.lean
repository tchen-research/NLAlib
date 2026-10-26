import NLAlib.Krylov.Solvers.GMRES
import NLAlib.Krylov.Spaces.Matrix
import NLAlib.Matrix.Subspaces.RangeProjectorMinimality

/-!
# Real and complex GMRES iterates

The concrete iterate uses the Krylov generator matrix `X` and the least-squares
coefficient vector `(A X)⁺ r₀`. Thus `x₀ + X (A X)⁺ r₀` realizes the native GMRES
predicate for every matrix, including singular matrices and exhausted Krylov spaces.
No inverse of a singular Gram matrix or choice of a full-size orthonormal frame is needed.
For singular matrices the iterate need not be unique; the theorems use residual optimality.

Sources: Saad--Schultz (1986), Sections 2--3; Saad (2003), Section 6.5.
atlas: gmres-def (partial)
-/

noncomputable section
open scoped Matrix Polynomial
open Polynomial
namespace NLAlib

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- A concrete GMRES iterate, using a least-squares solve in the power basis.
This is defined for every grade and every iteration count, including `q = 0`. -/
def gmresIterate (A : Matrix n n 𝕜) (c x₀ : n → 𝕜) (q : ℕ) : n → 𝕜 :=
  let X := krylovMatrix A (c - A *ᵥ x₀) q
  x₀ + X *ᵥ (moorePenroseInverse (A * X) *ᵥ (c - A *ᵥ x₀))

/-- The concrete iterate lies in the required affine Krylov space. -/
theorem gmresIterate_sub_mem_krylovSpace (A : Matrix n n 𝕜) (c x₀ : n → 𝕜) (q : ℕ) :
    gmresIterate A c x₀ q - x₀ ∈ krylovSpace A (c - A *ᵥ x₀) q := by
  rw [gmresIterate, add_sub_cancel_left, ← range_krylovMatrix]
  exact ⟨_, rfl⟩

/-- The power-basis least-squares formula is a GMRES iterate over either real or complex
scalars, without rank assumptions.
atlas: gmres-def (partial) -/
theorem isGMRESIterate_gmresIterate (A : Matrix n n 𝕜) (c x₀ : n → 𝕜) (q : ℕ) :
    IsGMRESIterate A c x₀ q (gmresIterate A c x₀ q) := by
  refine ⟨gmresIterate_sub_mem_krylovSpace A c x₀ q, ?_⟩
  intro y hy
  let X := krylovMatrix A (c - A *ᵥ x₀) q
  have hyX : y ∈ LinearMap.range X.mulVecLin := (range_krylovMatrix A _ q).symm ▸ hy
  obtain ⟨v, hv⟩ := hyX
  have hres : c - A *ᵥ gmresIterate A c x₀ q =
      (c - A *ᵥ x₀) - (A * X) *ᵥ (moorePenroseInverse (A * X) *ᵥ (c - A *ᵥ x₀)) := by
    change c - A *ᵥ (x₀ + X *ᵥ _) = _
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
    abel
  have hyres : c - A *ᵥ (x₀ + y) = (c - A *ᵥ x₀) - (A * X) *ᵥ v := by
    rw [← hv, Matrix.mulVecLin_apply, Matrix.mulVec_add, Matrix.mulVec_mulVec]
    abel
  have h := norm_sub_mulVec_moorePenroseInverse_le (A * X) (c - A *ᵥ x₀) v
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [hres, hyres, norm_toLp_sq_eq_re_star_dotProduct] using hs

variable {A : Matrix n n 𝕜} {c x₀ x : n → 𝕜} {q : ℕ}

/-- A GMRES iterate beats every competitor in the affine Krylov space, in Euclidean norm. -/
theorem IsGMRESIterate.norm_le_of_sub_mem (hx : IsGMRESIterate A c x₀ q x)
    {z : n → 𝕜} (hz : z - x₀ ∈ krylovSpace A (c - A *ᵥ x₀) q) :
    ‖WithLp.toLp 2 (c - A *ᵥ x)‖ ≤ ‖WithLp.toLp 2 (c - A *ᵥ z)‖ := by
  have h := IsAffineMinimizer.le_of_sub_mem hx hz
  rw [← norm_toLp_sq_eq_re_star_dotProduct, ← norm_toLp_sq_eq_re_star_dotProduct] at h
  nlinarith [norm_nonneg (WithLp.toLp 2 (c - A *ᵥ x)),
    norm_nonneg (WithLp.toLp 2 (c - A *ᵥ z))]

/-- The residual of every GMRES minimizer is the complementary orthogonal projection
of the initial residual. This identity is valid for singular and inconsistent systems.
atlas: gmres-def (partial) -/
theorem IsGMRESIterate.residual_eq_rangeProjector (hx : IsGMRESIterate A c x₀ q x) :
    c - A *ᵥ x = (c - A *ᵥ x₀) -
      rangeProjector (A * krylovMatrix A (c - A *ᵥ x₀) q) *ᵥ (c - A *ᵥ x₀) := by
  let X := krylovMatrix A (c - A *ᵥ x₀) q
  have hxK : x - x₀ ∈ LinearMap.range X.mulVecLin :=
    (range_krylovMatrix A _ q).symm ▸ hx.1
  obtain ⟨v, hv⟩ := hxK
  change X *ᵥ v = x - x₀ at hv
  have hmem : A *ᵥ (x - x₀) ∈ LinearMap.range (A * X).mulVecLin := by
    refine ⟨v, ?_⟩
    simp only [Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, hv]
  have hr : (c - A *ᵥ x₀) - A *ᵥ (x - x₀) = c - A *ᵥ x := by
    rw [Matrix.mulVec_sub]
    abel
  have he := eq_rangeProjector_mulVec_of_minimal hmem (b := c - A *ᵥ x₀) (by
    intro z
    rw [hr]
    have hz : x₀ + X *ᵥ z - x₀ ∈ krylovSpace A (c - A *ᵥ x₀) q := by
      rw [add_sub_cancel_left, ← range_krylovMatrix]
      exact ⟨z, rfl⟩
    have h := hx.norm_le_of_sub_mem hz
    have hzr : c - A *ᵥ (x₀ + X *ᵥ z) = (c - A *ᵥ x₀) - (A * X) *ᵥ z := by
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
      abel
    rwa [hzr] at h)
  rw [← he]
  exact hr.symm

/-- All GMRES minimizers have the same residual, even when the matrix is singular.
atlas: gmres-def (partial) -/
theorem IsGMRESIterate.residual_eq {x' : n → 𝕜} (hx : IsGMRESIterate A c x₀ q x)
    (hx' : IsGMRESIterate A c x₀ q x') : c - A *ᵥ x = c - A *ᵥ x' := by
  rw [hx.residual_eq_rangeProjector, hx'.residual_eq_rangeProjector]

/-- Injectivity of the matrix-vector map makes the GMRES iterate itself unique.
atlas: gmres-def (partial) -/
theorem IsGMRESIterate.eq_of_mulVec_injective {x' : n → 𝕜}
    (hA : Function.Injective A.mulVec) (hx : IsGMRESIterate A c x₀ q x)
    (hx' : IsGMRESIterate A c x₀ q x') : x = x' :=
  hA (sub_right_injective (hx.residual_eq hx'))

/-- The actual residual is a residual polynomial over the scalar field, including complex
coefficients for complex matrices. -/
theorem IsGMRESIterate.exists_residual_polynomial (hx : IsGMRESIterate A c x₀ q x) :
    ∃ p : 𝕜[X], p.degree ≤ q ∧ p.eval 0 = 1 ∧
      c - A *ᵥ x = aeval A p *ᵥ (c - A *ᵥ x₀) :=
  exists_sub_mulVec_eq_aeval_mulVec_of_sub_mem_krylovSpace hx.1

/-- Real or complex GMRES beats every admissible residual polynomial.
atlas: gmres-def (partial) -/
theorem IsGMRESIterate.norm_le_aeval (hx : IsGMRESIterate A c x₀ q x)
    {p : 𝕜[X]} (hp : p.degree ≤ q) (hp0 : p.eval 0 = 1) :
    ‖WithLp.toLp 2 (c - A *ᵥ x)‖ ≤
      ‖WithLp.toLp 2 (aeval A p *ᵥ (c - A *ᵥ x₀))‖ := by
  obtain ⟨y, hy, he⟩ := exists_mem_krylovSpace_sub_mulVec_eq_aeval_mulVec A c x₀ hp hp0
  rw [← he]
  exact hx.norm_le_of_sub_mem (by simpa using hy)

/-- The minimum over residual polynomials is attained and equals the GMRES residual norm.
atlas: gmres-def (partial) -/
theorem IsGMRESIterate.isLeast_norm_aeval (hx : IsGMRESIterate A c x₀ q x) :
    IsLeast {v | ∃ p : 𝕜[X], p.degree ≤ q ∧ p.eval 0 = 1 ∧
      v = ‖WithLp.toLp 2 (aeval A p *ᵥ (c - A *ᵥ x₀))‖}
      ‖WithLp.toLp 2 (c - A *ᵥ x)‖ := by
  constructor
  · obtain ⟨p, hp, hp0, he⟩ := hx.exists_residual_polynomial
    exact ⟨p, hp, hp0, by rw [he]⟩
  · rintro _ ⟨p, hp, hp0, rfl⟩
    exact hx.norm_le_aeval hp hp0

/-- Residual norms are nonincreasing, including counts beyond breakdown.
atlas: gmres-def (partial) -/
theorem IsGMRESIterate.norm_le_of_le {q' : ℕ} {x' : n → 𝕜}
    (hx : IsGMRESIterate A c x₀ q x) (hx' : IsGMRESIterate A c x₀ q' x') (h : q ≤ q') :
    ‖WithLp.toLp 2 (c - A *ᵥ x')‖ ≤ ‖WithLp.toLp 2 (c - A *ᵥ x)‖ :=
  hx'.norm_le_of_sub_mem (krylovSpace_mono A _ h hx.1)

/-- Invertible systems terminate at the grade, over both real and complex scalars.
atlas: gmres-def (partial) -/
theorem IsGMRESIterate.residual_eq_zero_of_grade_le (hA : IsUnit A)
    (hx : IsGMRESIterate A c x₀ q x) (hq : krylovGrade A (c - A *ᵥ x₀) ≤ q) :
    c - A *ᵥ x = 0 := by
  obtain ⟨xs, hxs⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hA c
  have h := hx.norm_le_of_sub_mem
    (krylovSpace_mono A _ hq (sub_mem_krylovSpace_krylovGrade hA hxs x₀))
  simp only [hxs, sub_self, WithLp.toLp_zero, norm_zero] at h
  exact WithLp.toLp_injective 2 (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

end NLAlib
