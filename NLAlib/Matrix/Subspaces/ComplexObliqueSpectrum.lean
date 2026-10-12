import NLAlib.Matrix.Subspaces.ComplexIdempotentRealForm
import NLAlib.Matrix.Subspaces.ObliqueProjectionNorms
/-!
# Actual singular coefficients and norms of complex idempotents

Unitary reduction to a same-dimension real representative transports the
complete canonical singular-spectrum and complementary norm formulas.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- Every complex idempotent has its full unitary oblique canonical form,
and the actual singular values are `sqrt(1+tᵢ²)` on the range and zero
after the rank. Exactly the first `g` values exceed one, with canonical
coefficient `sqrt(σᵢ²-1)`. Horn–Johnson 2013, Corollary 3.4.3.3;
all rank endpoints and the empty matrix are included.
atlas: cs-decomposition (partial) -/
theorem exists_unitary_idempotent_canonical_spectrum {n : Type*}
    [Fintype n] [DecidableEq n] (P : Matrix n n ℂ) (hP : IsIdempotentElem P) :
    ∃ g : ℕ, g ≤ min P.rank (Fintype.card n - P.rank) ∧
    ∃ t : ℕ → ℝ, (∀ i, 0 ≤ t i) ∧ Antitone t ∧ (∀ i, 0 < t i ↔ i < g) ∧
    ∃ H : Matrix n (Fin P.rank ⊕ Fin (Fintype.card n - P.rank)) ℂ,
      Hᴴ * H = 1 ∧ H * Hᴴ = 1 ∧
      Hᴴ * P * H = Matrix.fromBlocks 1 ((rectDiag t).map Complex.ofReal) 0 0 ∧
      (∀ i, P.toEuclideanLin.singularValues i =
        if i < P.rank then Real.sqrt (1 + t i ^ 2) else 0) ∧
      (∀ i, 1 < P.toEuclideanLin.singularValues i ↔ i < g) ∧
      (∀ i < g, t i = Real.sqrt (P.toEuclideanLin.singularValues i ^ 2 - 1)) := by
  obtain ⟨U, R, hR, hPR, hspec, hRank, _, _⟩ := exists_real_idempotent_unitary_similarity P hP
  obtain ⟨g, hg, t, ht0, ht, htpos, L, hL, hLt, hBlock, hSpec, hGt, hCoeff⟩ :=
    exists_orthogonal_idempotent_canonical_spectrum R hR
  rw [hRank]
  have hU : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self U
  have hUt : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 := Unitary.coe_mul_star_self U
  let LC := L.map Complex.ofReal
  have hLC : LCᴴ * LC = 1 := by
    rw [show LCᴴ = Lᵀ.map Complex.ofReal from conjTranspose_map_ofReal _, ← map_ofReal_mul, hL]
    simp
  have hLCt : LC * LCᴴ = 1 := by
    rw [show LCᴴ = Lᵀ.map Complex.ofReal from conjTranspose_map_ofReal _, ← map_ofReal_mul, hLt]
    simp
  let H := (U : Matrix n n ℂ) * LC
  have hconj : (U : Matrix n n ℂ)ᴴ * P * (U : Matrix n n ℂ) = R.map Complex.ofReal := by
    rw [hPR]
    calc
      _ = ((U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ)) * R.map Complex.ofReal *
          ((U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.one_mul, Matrix.mul_one]
  refine ⟨g, hg, t, ht0, ht, htpos, H, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [H, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : Matrix n n ℂ)ᴴ (U : Matrix n n ℂ) LC, hU, Matrix.one_mul, hLC]
  · simp only [H, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc LC LCᴴ (U : Matrix n n ℂ)ᴴ, hLCt, Matrix.one_mul, hUt]
  · calc
      Hᴴ * P * H = LCᴴ * ((U : Matrix n n ℂ)ᴴ * P * (U : Matrix n n ℂ)) * LC := by
        simp only [H, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (Lᵀ * R * L).map Complex.ofReal := by
        rw [hconj, show LCᴴ = Lᵀ.map Complex.ofReal from conjTranspose_map_ofReal _,
          ← map_ofReal_mul, ← map_ofReal_mul]
      _ = _ := by rw [hBlock]; simp [Matrix.fromBlocks_map]
  · intro i; rw [hspec, hSpec]
  · intro i; rw [hspec]; exact hGt i
  · intro i hi; rw [hspec]; exact hCoeff i hi

/-- Complementary proper nonzero complex idempotents have equal Euclidean
operator norm. Rank-zero, full-rank and empty-dimensional endpoint formulas
are stated separately and exactly. Horn–Johnson 2013, Corollary 3.4.3.3.
atlas: cs-decomposition (partial) -/
theorem complex_idempotent_complement_norm_properties {n : Type*}
    [Fintype n] [DecidableEq n] (P : Matrix n n ℂ) (hP : IsIdempotentElem P) :
    (0 < P.rank → P.rank < Fintype.card n → ‖1 - P‖ = ‖P‖) ∧
    (P.rank = 0 → ‖P‖ = 0 ∧ ‖1 - P‖ = if Fintype.card n = 0 then 0 else 1) ∧
    (P.rank = Fintype.card n → ‖P‖ = (if Fintype.card n = 0 then 0 else 1) ∧ ‖1 - P‖ = 0) := by
  obtain ⟨_, R, hR, _, _, hRank, hNorm, hComp⟩ := exists_real_idempotent_unitary_similarity P hP
  rw [hRank, hNorm, hComp]
  exact ⟨specNorm_one_sub_eq_of_idempotent_of_rank_pos_lt hR,
    (specNorm_idempotent_rank_endpoints hR).1, (specNorm_idempotent_rank_endpoints hR).2⟩

end NLAlib
