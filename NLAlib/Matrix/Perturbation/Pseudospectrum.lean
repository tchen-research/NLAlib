import NLAlib.Matrix.Basic.TruncatedSVDRegularization
import NLAlib.Matrix.Basic.MoorePenroseTransformations
import NLAlib.Matrix.Spectral.SquareSmallestSingularValue
import NLAlib.Matrix.Perturbation.BauerFike
/-!
# Attained pseudospectral perturbation distance

The smallest singular value of `zI-A` is exactly the least spectral norm
of a perturbation that makes `z` an eigenvalue. A rank-one perturbation
attains this minimum, including zero radius and singular shifted matrices.

Source: Trefethen–Embree (2005), §2; matrix-toolkit re-derivation, §38.
Atlas: `pseudospectrum-perturbation-equivalence`.
-/
noncomputable section
open Matrix
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- A smallest singular vector attains the unit-sphere minimum, including
singular matrices. -/
theorem exists_unit_norm_mulVec_eq_singularValues_last [Nonempty n] (C : Matrix n n 𝕜) :
    ∃ v : n → 𝕜, ‖WithLp.toLp 2 v‖ = 1 ∧
      ‖WithLp.toLp 2 (C *ᵥ v)‖ = singularValues C (Fintype.card n - 1) := by
  obtain ⟨U, V, h⟩ := exists_isSVD C
  let j : Fin (Fintype.card n) := ⟨Fintype.card n - 1, by have := Fintype.card_pos (α := n); omega⟩
  have hd : (rectDiag (singularValues C) : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) 𝕜) =
      diagonal (fun i : Fin (Fintype.card n) => (singularValues C i : 𝕜)) := by
    ext i k
    by_cases hik : i = k
    · subst k; simp [rectDiag_apply_ofReal]
    · have hv : i.val ≠ k.val := fun he => hik (Fin.ext he)
      simp [rectDiag_apply_ofReal, hik, hv]
  have hcol : C *ᵥ V.col j = (singularValues C j : 𝕜) • U.col j := by
    have he := congrArg (fun M => M.col j) h.mul_right
    rw [hd] at he
    change C *ᵥ V.col j = (U * diagonal (fun i : Fin (Fintype.card n) => (singularValues C i : 𝕜))).col j at he
    rw [he]
    ext i
    simp [Matrix.col, Matrix.mul_diagonal, mul_comm]
  have hV : ‖WithLp.toLp 2 (V.col j)‖ = 1 :=
    (HasOrthonormalCols.orthonormal h.conjTranspose_mul_right).norm_eq_one j
  have hU : ‖WithLp.toLp 2 (U.col j)‖ = 1 :=
    (HasOrthonormalCols.orthonormal h.conjTranspose_mul_left).norm_eq_one j
  refine ⟨V.col j, hV, ?_⟩
  rw [hcol, WithLp.toLp_smul, norm_smul, hU, mul_one, RCLike.norm_ofReal,
    abs_of_nonneg (singularValues_nonneg C j)]

/-- The outer product with a unit right vector has spectral norm bounded
by the Euclidean norm of its left vector. -/
theorem specNorm_vecMulVec_star_le_of_norm_eq_one (u v : n → 𝕜)
    (hv : ‖WithLp.toLp 2 v‖ = 1) :
    specNorm (Matrix.vecMulVec u (star v)) ≤ ‖WithLp.toLp 2 u‖ := by
  have hvsq : ∑ j, ‖v j‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq (WithLp.toLp 2 v), hv, one_pow]
  have husq : ∑ j, ‖u j‖ ^ 2 = ‖WithLp.toLp 2 u‖ ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq]
  have hf : frobSq (Matrix.vecMulVec u (star v)) = ‖WithLp.toLp 2 u‖ ^ 2 := by
    simp only [frobSq_eq_sum_norm_sq, Matrix.vecMulVec_apply, Pi.star_apply, norm_mul,
      norm_star, mul_pow, ← Finset.mul_sum, hvsq, mul_one, husq]
  have hn : frobNorm (Matrix.vecMulVec u (star v)) = ‖WithLp.toLp 2 u‖ := by
    have hs := frobNorm_sq (Matrix.vecMulVec u (star v))
    rw [hf] at hs
    nlinarith [frobNorm_nonneg (Matrix.vecMulVec u (star v)), norm_nonneg (WithLp.toLp 2 u)]
  exact (specNorm_le_frobNorm _).trans_eq hn

open scoped Matrix.Norms.L2Operator in
/-- Every perturbation producing the requested eigenvalue has norm at
least the smallest singular value of the original shifted matrix. -/
theorem singularValues_last_shift_le_specNorm_of_mem_spectrum (A E : Matrix n n ℂ)
    (z : ℂ) (hz : z ∈ spectrum ℂ (A + E)) :
    singularValues (z • 1 - A) (Fintype.card n - 1) ≤ specNorm E := by
  obtain ⟨x, hx, he⟩ := exists_mulVec_eq_smul_of_mem_spectrum hz
  have hres : (z • 1 - A) *ᵥ x = E *ᵥ x := by
    rw [Matrix.add_mulVec] at he
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    linear_combination -he
  have hxnorm : 0 < ‖WithLp.toLp 2 x‖ := norm_pos_iff.mpr fun hzero =>
    hx (congrArg WithLp.ofLp hzero)
  have hlo := singularValues_last_mul_norm_le (z • 1 - A) x
  rw [hres] at hlo
  have hup := E.l2_opNorm_mulVec (WithLp.toLp 2 x)
  exact (mul_le_mul_iff_left₀ hxnorm).mp (hlo.trans hup)

/-- A rank-one perturbation attains the exact minimum, and every competing
perturbation has at least that norm. This includes zero singular values.
atlas: pseudospectrum-perturbation-equivalence (partial) -/
theorem exists_rank_one_perturbation_minimum [Nonempty n] (A : Matrix n n ℂ) (z : ℂ) :
    ∃ E : Matrix n n ℂ, E.rank ≤ 1 ∧ z ∈ spectrum ℂ (A + E) ∧
      specNorm E = singularValues (z • 1 - A) (Fintype.card n - 1) ∧
      ∀ F : Matrix n n ℂ, z ∈ spectrum ℂ (A + F) → specNorm E ≤ specNorm F := by
  obtain ⟨v, hv, hres⟩ := exists_unit_norm_mulVec_eq_singularValues_last (z • 1 - A)
  let u := (z • 1 - A) *ᵥ v
  let E := Matrix.vecMulVec u (star v)
  have hdot : star v ⬝ᵥ v = (1 : ℂ) := by
    have he : inner ℂ (WithLp.toLp 2 v) (WithLp.toLp 2 v) = (1 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, hv]; norm_num
    simpa only [EuclideanSpace.inner_toLp_toLp, dotProduct_comm] using he
  have hv0 : v ≠ 0 := by intro hz; simp [hz] at hv
  have heig : (A + E) *ᵥ v = z • v := by
    simp only [Matrix.add_mulVec, E, Matrix.vecMulVec_mulVec, hdot, MulOpposite.op_one, one_smul]
    dsimp [u]
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    abel
  have hspec : z ∈ spectrum ℂ (A + E) :=
    Matrix.mem_spectrum_of_isRoot_charpoly (isRoot_charpoly_of_mulVec_eq_smul hv0 heig)
  have hup : specNorm E ≤ singularValues (z • 1 - A) (Fintype.card n - 1) := by
    exact (specNorm_vecMulVec_star_le_of_norm_eq_one u v hv).trans_eq hres
  have heq := le_antisymm hup (singularValues_last_shift_le_specNorm_of_mem_spectrum A E z hspec)
  refine ⟨E, Matrix.rank_vecMulVec_le _ _, hspec, heq, ?_⟩
  intro F hF
  rw [heq]
  exact singularValues_last_shift_le_specNorm_of_mem_spectrum A F z hF

/-- Closed perturbation and smallest-singular-value pseudospectra coincide,
including the radius-zero endpoint.
atlas: pseudospectrum-perturbation-equivalence (partial) -/
theorem exists_perturbation_mem_spectrum_iff_singularValues_last_le [Nonempty n]
    (A : Matrix n n ℂ) (z : ℂ) (ε : ℝ) :
    (∃ E : Matrix n n ℂ, specNorm E ≤ ε ∧ z ∈ spectrum ℂ (A + E)) ↔
      singularValues (z • 1 - A) (Fintype.card n - 1) ≤ ε := by
  constructor
  · rintro ⟨E, hE, hz⟩
    exact (singularValues_last_shift_le_specNorm_of_mem_spectrum A E z hz).trans hE
  · intro hε
    obtain ⟨E, _, hz, hnorm, _⟩ := exists_rank_one_perturbation_minimum A z
    exact ⟨E, hnorm ▸ hε, hz⟩

/-- The closed pseudospectrum equivalently consists of points with a unit
approximate eigenvector whose residual is at most the radius.
atlas: pseudospectrum-perturbation-equivalence (partial) -/
theorem exists_unit_residual_le_iff_singularValues_last_le [Nonempty n]
    (A : Matrix n n ℂ) (z : ℂ) (ε : ℝ) :
    (∃ v : n → ℂ, ‖WithLp.toLp 2 v‖ = 1 ∧ ‖WithLp.toLp 2 ((z • 1 - A) *ᵥ v)‖ ≤ ε) ↔
      singularValues (z • 1 - A) (Fintype.card n - 1) ≤ ε := by
  constructor
  · rintro ⟨v, hv, hbound⟩
    exact (singularValues_last_le_norm_mulVec _ hv).trans hbound
  · intro hε
    obtain ⟨v, hv, he⟩ := exists_unit_norm_mulVec_eq_singularValues_last (z • 1 - A)
    exact ⟨v, hv, he ▸ hε⟩

end NLAlib


