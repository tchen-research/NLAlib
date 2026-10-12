import NLAlib.Matrix.ObliqueProjectionSpectrum
import NLAlib.Matrix.ObliqueComplementSpectrum

/-!
# Complementary oblique projection norms and endpoints

Nontrivial complementary idempotents have equal spectral norms. Rank zero,
full rank and the empty ambient space have their exact separate formulas.
Horn–Johnson 2013, Corollary 3.4.3.3.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

private theorem native_singularValue_zero_eq_specNorm {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) :
    A.toEuclideanLin.singularValues 0 = specNorm A :=
  (singularValues_reindex_eq_toEuclideanLin_singularValues A 0).symm.trans
    (singularValues_reindex_zero_eq_specNorm A)

/-- An idempotent and its complement have a common norm factor at least one,
with the factor present exactly when the corresponding range is nonzero.
At either rank endpoint this factor is one, also in empty dimension.
Horn–Johnson 2013, Corollary 3.4.3.3; supports `cs-decomposition`. -/
theorem exists_idempotent_complement_norm_factor {n : Type*}
    [Fintype n] [DecidableEq n] (P : Matrix n n ℝ) (hP : IsIdempotentElem P) :
    ∃ a : ℝ, 1 ≤ a ∧
      specNorm P = (if P.rank = 0 then 0 else a) ∧
      specNorm (1 - P) = (if P.rank = Fintype.card n then 0 else a) ∧
      (P.rank = 0 ∨ P.rank = Fintype.card n → a = 1) := by
  obtain ⟨g, hg, t, ht0, ht, htpos, H, hH, hHt, hBlock, hSpec, _, _⟩ :=
    exists_orthogonal_idempotent_canonical_spectrum P hP
  let N := Matrix.fromBlocks (1 : Matrix (Fin P.rank) (Fin P.rank) ℝ)
    (rectDiag t : Matrix (Fin P.rank) (Fin (Fintype.card n - P.rank)) ℝ)
    0 (0 : Matrix (Fin (Fintype.card n - P.rank)) (Fin (Fintype.card n - P.rank)) ℝ)
  have hz (i : ℕ) (hi : min P.rank (Fintype.card n - P.rank) ≤ i) : t i = 0 := by
    have hgi := hg.trans hi
    exact le_antisymm (le_of_not_gt (fun h => (not_lt_of_ge hgi) ((htpos i).mp h))) (ht0 i)
  have hForm : 1 - P = H * (1 - N) * Hᵀ := by
    have hPForm : P = H * N * Hᵀ := by
      calc
        P = (H * Hᵀ) * P * (H * Hᵀ) := by rw [hHt]; simp
        _ = H * (Hᵀ * P * H) * Hᵀ := by simp only [Matrix.mul_assoc]
        _ = H * N * Hᵀ := by rw [hBlock]
    calc
      _ = H * Hᵀ - H * N * Hᵀ := congrArg₂ (· - ·) hHt.symm hPForm
      _ = _ := by rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  have hComplement : specNorm (1 - P) =
      if 0 < Fintype.card n - P.rank then Real.sqrt (1 + t 0 ^ 2) else 0 := by
    rw [← native_singularValue_zero_eq_specNorm]
    calc
      _ = (H * (1 - N) * Hᵀ).toEuclideanLin.singularValues 0 :=
        congrArg (fun A : Matrix n n ℝ => A.toEuclideanLin.singularValues 0) hForm
      _ = (1 - N).toEuclideanLin.singularValues 0 := by
        rw [toEuclideanLin_singularValues_mul_isometry_transpose hH,
          toEuclideanLin_singularValues_isometry_mul hH]
      _ = _ := singularValues_one_sub_oblique_canonical t ht0 ht hz 0
  refine ⟨Real.sqrt (1 + t 0 ^ 2), ?_, ?_, ?_, ?_⟩
  · have hs := Real.sq_sqrt (show 0 ≤ 1 + t 0 ^ 2 by positivity)
    have hn := Real.sqrt_nonneg (1 + t 0 ^ 2)
    nlinarith [sq_nonneg (t 0)]
  · have hs := hSpec 0
    rw [native_singularValue_zero_eq_specNorm] at hs
    rw [hs]
    split_ifs <;> first | rfl | omega
  · rw [hComplement]
    have hRank := P.rank_le_card_height
    split_ifs <;> first | rfl | omega
  · intro hEnd
    have hzero : t 0 = 0 := hz 0 (by rcases hEnd with h | h <;> simp [h])
    simp [hzero]

/-- Complementary nonzero proper idempotents have equal spectral norm.
Both strict rank inequalities are necessary: the zero and identity endpoints
are treated separately. Horn–Johnson 2013, Corollary 3.4.3.3.
atlas: cs-decomposition (partial) -/
theorem specNorm_one_sub_eq_of_idempotent_of_rank_pos_lt {n : Type*}
    [Fintype n] [DecidableEq n] {P : Matrix n n ℝ} (hP : IsIdempotentElem P)
    (hr : 0 < P.rank) (hn : P.rank < Fintype.card n) :
    specNorm (1 - P) = specNorm P := by
  obtain ⟨a, _, h1, h2, _⟩ := exists_idempotent_complement_norm_factor P hP
  rw [h1, h2, if_neg (Nat.ne_of_gt hr), if_neg (Nat.ne_of_lt hn)]

/-- At rank zero the idempotent norm is zero and the complement norm is one
in positive dimension; at full rank these roles reverse. Empty dimension
gives zero for both. Horn–Johnson 2013, Corollary 3.4.3.3.
atlas: cs-decomposition (partial) -/
theorem specNorm_idempotent_rank_endpoints {n : Type*}
    [Fintype n] [DecidableEq n] {P : Matrix n n ℝ} (hP : IsIdempotentElem P) :
    (P.rank = 0 → specNorm P = 0 ∧
      specNorm (1 - P) = if Fintype.card n = 0 then 0 else 1) ∧
    (P.rank = Fintype.card n →
      specNorm P = (if Fintype.card n = 0 then 0 else 1) ∧ specNorm (1 - P) = 0) := by
  obtain ⟨a, _, h1, h2, hEnd⟩ := exists_idempotent_complement_norm_factor P hP
  constructor
  · intro hz
    rw [h1, h2, hz, if_pos rfl, hEnd (Or.inl hz)]
    simp only [eq_comm]
    trivial
  · intro hf
    rw [h1, h2, hf, if_pos rfl, hEnd (Or.inr hf)]
    exact ⟨rfl, rfl⟩

end NLAlib
