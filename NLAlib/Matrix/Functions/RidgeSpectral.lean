import NLAlib.Matrix.Functions.RidgeKernel
import NLAlib.Matrix.Functions.CFCTrace
import NLAlib.Matrix.Spectral.GramSpectralSums

/-!
# The finite spectral formula for ridge effective dimension

The ridge kernel is the scalar filter `x / (x + ρ)` applied to the row Gram matrix.
Consequently the effective dimension is a finite sum of
`σ_i(A)² / (σ_i(A)² + ρ)`, is at most `rank A`, and is invariant under transposition.
No singular-vector selector or rank assumption is used.

Source: Cohen–Musco–Musco 2017, ridge scores and Lemma 4, in the transposed general-ρ form;
`sketching_lowrank_routes_2026_10_24/sketching.tex`, ridge derivation.
Atlas: `ridge-leverage-effective-dimension`.
-/

noncomputable section

open scoped Matrix MatrixOrder

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The ridge kernel is the finite functional calculus filter `x / (x + ρ)` of the row Gram
matrix. This identifies its spectral values without selecting individual singular vectors. -/
theorem ridgeKernel_eq_cfc (A : Matrix m n ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ridgeKernel A ρ = cfc (fun x : ℝ => x / (x + ρ)) (A * Aᵀ) := by
  let G := A * Aᵀ
  have hG : G.PosSemidef := by
    simpa only [G, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_transpose] using Matrix.posSemidef_conjTranspose_mul_self Aᵀ
  have hfin (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ G) := by
    rw [hG.isHermitian.spectrum_real_eq_range_eigenvalues]
    exact (Set.finite_range _).continuousOn f
  have hshift : cfc (fun x : ℝ => x + ρ) G = ridgeGram Aᵀ ρ := by
    have hs := cfc_add_const ρ (fun x : ℝ => x) G (hfin _) hG.isHermitian
    calc
      cfc (fun x : ℝ => x + ρ) G =
          cfc (fun x : ℝ => x) G + algebraMap ℝ (Matrix m m ℝ) ρ := hs
      _ = G + algebraMap ℝ (Matrix m m ℝ) ρ :=
        congrArg (fun X : Matrix m m ℝ => X + algebraMap ℝ (Matrix m m ℝ) ρ)
          (cfc_id' ℝ G hG.isHermitian)
      _ = ridgeGram Aᵀ ρ := by
        simp only [Algebra.algebraMap_eq_smul_one, G, ridgeGram, Matrix.transpose_transpose]
  have hprod : ridgeGram Aᵀ ρ * cfc (fun x : ℝ => x / (x + ρ)) G = G := by
    rw [← hshift, ← cfc_mul _ _ G (hfin _) (hfin _)]
    calc
      cfc (fun x : ℝ => (x + ρ) * (x / (x + ρ))) G = cfc (fun x : ℝ => x) G := by
        apply cfc_congr
        intro x hx
        rw [hG.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
        obtain ⟨i, rfl⟩ := hx
        have hden : hG.isHermitian.eigenvalues i + ρ ≠ 0 :=
          ne_of_gt (add_pos_of_nonneg_of_pos (hG.eigenvalues_nonneg i) hρ)
        field_simp
      _ = G := cfc_id' ℝ G hG.isHermitian
  have hi := (Matrix.isUnit_iff_isUnit_det _).mp (posDef_ridgeGram Aᵀ hρ).isUnit
  have hK : ridgeGram Aᵀ ρ * ridgeKernel A ρ = G := by
    rw [ridgeKernel_eq_one_sub_smul_inv A hρ, Matrix.mul_sub, Matrix.mul_one,
      Matrix.mul_smul, Matrix.mul_nonsing_inv _ hi]
    simp only [ridgeGram, Matrix.transpose_transpose, G]
    abel
  have hh := congrArg (fun X => (ridgeGram Aᵀ ρ)⁻¹ * X) (hK.trans hprod.symm)
  simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hi, Matrix.one_mul] using hh

/-- The effective dimension is the sum of the ridge-filtered squared singular values.
The full row-length zero-padded prefix covers rectangular, singular and empty matrices.
atlas: ridge-leverage-effective-dimension (partial) -/
theorem ridgeEffectiveDimension_eq_sum_singularValues (A : Matrix m n ℝ) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ridgeEffectiveDimension A ρ =
      ∑ i ∈ Finset.range (Fintype.card m),
        singularValues A i ^ 2 / (singularValues A i ^ 2 + ρ) := by
  have hG : (A * Aᵀ).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_mul_conjTranspose_self A
  rw [ridgeEffectiveDimension_eq_trace, ridgeKernel_eq_cfc A hρ,
    trace_cfc_eq_sum_eigenvalues hG]
  have h := sum_eigenvalues_gram_eq_sum_singularValues Aᵀ (fun x : ℝ => x / (x + ρ))
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose,
    singularValues_transpose, RCLike.ofReal_real_eq_id, id_eq] using h

/-- Ridge effective dimension is at most the matrix rank. Only the nonzero singular
directions contribute, and every contributing ridge coefficient is at most one.
atlas: ridge-leverage-effective-dimension (partial) -/
theorem ridgeEffectiveDimension_le_rank (A : Matrix m n ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ridgeEffectiveDimension A ρ ≤ (A.rank : ℝ) := by
  let f := fun i : ℕ => singularValues A i ^ 2 / (singularValues A i ^ 2 + ρ)
  have hsum : ∑ i ∈ Finset.range A.rank, f i =
      ∑ i ∈ Finset.range (Fintype.card m), f i := by
    apply Finset.sum_subset (Finset.range_mono A.rank_le_card_height)
    intro i _ hi
    have hr : A.rank ≤ i := by simpa only [Finset.mem_range, not_lt] using hi
    simp only [f, singularValues_eq_zero_of_rank_le A hr, zero_pow (by decide : 2 ≠ 0),
      zero_div]
  rw [ridgeEffectiveDimension_eq_sum_singularValues A hρ, ← hsum]
  calc
    ∑ i ∈ Finset.range A.rank, f i ≤ ∑ _i ∈ Finset.range A.rank, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact (div_le_one (add_pos_of_nonneg_of_pos (sq_nonneg _) hρ)).2 (by linarith)
    _ = (A.rank : ℝ) := by simp

/-- Transposing a real matrix preserves its ridge effective dimension, including rectangular
zero padding and every deficient rank. -/
theorem ridgeEffectiveDimension_transpose (A : Matrix m n ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ridgeEffectiveDimension Aᵀ ρ = ridgeEffectiveDimension A ρ := by
  rw [ridgeEffectiveDimension_eq_sum_singularValues Aᵀ hρ,
    ridgeEffectiveDimension_eq_sum_singularValues A hρ]
  simp only [singularValues_transpose]
  let f := fun x : ℝ => x ^ 2 / (x ^ 2 + ρ)
  have hf : f 0 = 0 := by simp [f]
  have hn := sum_range_singularValues_map_eq_of_min_le A f hf
    (N := Fintype.card n) (min_le_right _ _)
  have hm := sum_range_singularValues_map_eq_of_min_le A f hf
    (N := Fintype.card m) (min_le_left _ _)
  exact hn.trans hm.symm

end NLAlib
