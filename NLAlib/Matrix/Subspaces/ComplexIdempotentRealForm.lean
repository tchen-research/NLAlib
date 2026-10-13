import NLAlib.Matrix.Subspaces.ComplexObliqueCanonical
import NLAlib.Matrix.Spectral.GramSingularValues
import NLAlib.Matrix.Spectral.SpectralBounds
/-!
# Unitary reduction of complex idempotents to real idempotents

The complex canonical idempotent form is real. Transporting it back to the
original finite labels gives a same-dimension real representative with exactly
the same singular values, rank and Euclidean norm.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- Every complex idempotent is unitarily similar to a real idempotent
on the same finite labels. The entire actual singular-value sequence,
rank, projection norm and complementary norm are preserved exactly.
Horn–Johnson 2013, Corollary 3.4.3.3; complex CS transport helper. -/
theorem exists_real_idempotent_unitary_similarity {n : Type*}
    [Fintype n] [DecidableEq n] (P : Matrix n n ℂ) (hP : IsIdempotentElem P) :
    ∃ U : Matrix.unitaryGroup n ℂ, ∃ R : Matrix n n ℝ,
      IsIdempotentElem R ∧ P = (U : Matrix n n ℂ) * R.map Complex.ofReal * (U : Matrix n n ℂ)ᴴ ∧
      (∀ i, singularValues P i = singularValues R i) ∧
      P.rank = R.rank ∧ ‖P‖ = specNorm R ∧ ‖1 - P‖ = specNorm (1 - R) := by
  classical
  obtain ⟨g, hg, t, ht0, ht, htpos, H, hH, hHt, hBlock⟩ := exists_unitary_idempotent_canonical P hP
  let e : (Fin P.rank ⊕ Fin (Fintype.card n - P.rank)) ≃ n := Fintype.equivOfCardEq (by
    simp only [Fintype.card_sum, Fintype.card_fin]
    exact Nat.add_sub_of_le P.rank_le_card_height)
  let N : Matrix (Fin P.rank ⊕ Fin (Fintype.card n - P.rank))
      (Fin P.rank ⊕ Fin (Fintype.card n - P.rank)) ℝ := Matrix.fromBlocks 1 (rectDiag t) 0 0
  let R := N.reindex e e
  let Q : Matrix n n ℂ := H.submatrix id e.symm
  have hQ : Qᴴ * Q = 1 := by
    simp only [Q, Matrix.conjTranspose_submatrix]
    rw [show Hᴴ.submatrix e.symm id * H.submatrix id e.symm =
      (Hᴴ * H).submatrix e.symm e.symm from
      Matrix.submatrix_mul_equiv Hᴴ H e.symm (Equiv.refl n) e.symm, hH]
    ext i j
    simp [Matrix.one_apply, e.symm.injective.eq_iff]
  let U : Matrix.unitaryGroup n ℂ := ⟨Q, Matrix.mem_unitaryGroup_iff'.mpr hQ⟩
  have hN : N * N = N := by simp [N, Matrix.fromBlocks_multiply]
  have hR : IsIdempotentElem R := by
    change R * R = R
    simp only [R, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, hN]
  have hNmap : N.map Complex.ofReal = Matrix.fromBlocks 1 ((rectDiag t).map Complex.ofReal) 0 0 := by
    simp [N, Matrix.fromBlocks_map]
  have hPform : P = H * N.map Complex.ofReal * Hᴴ := by
    calc
      P = (H * Hᴴ) * P * (H * Hᴴ) := by rw [hHt]; simp
      _ = H * (Hᴴ * P * H) * Hᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hBlock, ← hNmap]
  have hfactor : P = (U : Matrix n n ℂ) * R.map Complex.ofReal * (U : Matrix n n ℂ)ᴴ := by
    rw [hPform]
    change _ = Q * R.map Complex.ofReal * Qᴴ
    have hMap : R.map Complex.ofReal = (N.map Complex.ofReal).submatrix e.symm e.symm := rfl
    rw [hMap]
    simp only [Q, Matrix.conjTranspose_submatrix]
    rw [Matrix.submatrix_mul_equiv H (N.map Complex.ofReal) id e.symm e.symm,
      Matrix.submatrix_mul_equiv (H * N.map Complex.ofReal) Hᴴ id e.symm id,
      Matrix.submatrix_id_id]
  have hspec (i : ℕ) : singularValues P i = singularValues R i := by
    rw [hfactor]
    have hU₁ : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self U
    rw [singularValues_eq_of_gram_charpoly_eq _ (R.map Complex.ofReal) (by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (U : Matrix n n ℂ)ᴴ (U : Matrix n n ℂ), hU₁, Matrix.one_mul,
        Matrix.charpoly_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, hU₁, Matrix.mul_one])]
    exact singularValues_map_ofReal (𝕜 := ℂ) R i
  have hnorm (A : Matrix n n ℝ) :
      ‖(U : Matrix n n ℂ) * A.map Complex.ofReal * (U : Matrix n n ℂ)ᴴ‖ = specNorm A := by
    change ‖((U : Matrix n n ℂ) * A.map Complex.ofReal) * ((star U : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ)‖ = _
    rw [CStarRing.norm_mul_coe_unitary _ (star U), CStarRing.norm_coe_unitary_mul,
      ← specNorm_eq_norm, ← singularValues_zero_eq_specNorm, ← singularValues_zero_eq_specNorm]
    exact singularValues_map_ofReal (𝕜 := ℂ) A 0
  have hrank : P.rank = R.rank := eq_of_forall_lt_iff fun k => by
    rw [← singularValues_ne_zero_iff, ← singularValues_ne_zero_iff, hspec]
  refine ⟨U, R, hR, hfactor, hspec, hrank, ?_, ?_⟩
  · rw [hfactor, hnorm]
  · have hcomp : 1 - P = (U : Matrix n n ℂ) * (1 - R).map Complex.ofReal * (U : Matrix n n ℂ)ᴴ := by
      have hmap : (1 - R).map Complex.ofReal = 1 - R.map Complex.ofReal := by
        ext i j; by_cases h : i = j <;> simp [h]
      rw [hmap, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
        show (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 from Unitary.coe_mul_star_self U,
        ← hfactor]
    rw [hcomp, hnorm]

end NLAlib
