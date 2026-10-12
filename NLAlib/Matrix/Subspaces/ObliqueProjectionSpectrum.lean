import NLAlib.Matrix.Subspaces.ObliqueCanonicalSpectrum
import NLAlib.Matrix.Subspaces.ObliqueProjectionCanonical
/-!
# Oblique canonical coefficients and the actual singular spectrum

The canonical off-diagonal coefficients are the square roots of the excess
squared singular values above one, with multiplicities and endpoints included.
Horn–Johnson 2013, Corollary 3.4.3.3.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- The complete orthogonal oblique-projector canonical form, together with
the actual singular spectrum at every natural index. Exactly the first `g`
singular values exceed one, and their blocks have coefficient
`sqrt(σᵢ(P)²-1)`; all other range values are one and all kernel values are zero.
Horn–Johnson 2013, Corollary 3.4.3.3; derivations §alg:cs.
atlas: cs-decomposition (partial) -/
theorem exists_orthogonal_idempotent_canonical_spectrum {n : Type*}
    [Fintype n] [DecidableEq n] (P : Matrix n n ℝ) (hP : IsIdempotentElem P) :
    ∃ g : ℕ, g ≤ min P.rank (Fintype.card n - P.rank) ∧
    ∃ t : ℕ → ℝ, (∀ i, 0 ≤ t i) ∧ Antitone t ∧ (∀ i, 0 < t i ↔ i < g) ∧
    ∃ H : Matrix n (Fin P.rank ⊕ Fin (Fintype.card n - P.rank)) ℝ,
      HasOrthonormalCols H ∧ H * Hᵀ = 1 ∧
      Hᵀ * P * H = Matrix.fromBlocks 1 (rectDiag t) 0 0 ∧
      (∀ i, P.toEuclideanLin.singularValues i =
        if i < P.rank then Real.sqrt (1 + t i ^ 2) else 0) ∧
      (∀ i, 1 < P.toEuclideanLin.singularValues i ↔ i < g) ∧
      (∀ i < g, t i = Real.sqrt (P.toEuclideanLin.singularValues i ^ 2 - 1)) := by
  obtain ⟨g, hg, t, ht0, ht, htpos, H, hH, hHt, hBlock⟩ :=
    exists_orthogonal_idempotent_canonical P hP
  let N := Matrix.fromBlocks (1 : Matrix (Fin P.rank) (Fin P.rank) ℝ)
    (rectDiag t : Matrix (Fin P.rank) (Fin (Fintype.card n - P.rank)) ℝ)
    0 (0 : Matrix (Fin (Fintype.card n - P.rank)) (Fin (Fintype.card n - P.rank)) ℝ)
  have hz (i : ℕ) (hi : g ≤ i) : t i = 0 :=
    le_antisymm (le_of_not_gt (fun h => (not_lt_of_ge hi) ((htpos i).mp h))) (ht0 i)
  have hForm : P = H * N * Hᵀ := by
    calc
      P = (H * Hᵀ) * P * (H * Hᵀ) := by rw [hHt]; simp
      _ = H * (Hᵀ * P * H) * Hᵀ := by simp only [Matrix.mul_assoc]
      _ = H * N * Hᵀ := by rw [hBlock]
  have hSpec (i : ℕ) : P.toEuclideanLin.singularValues i =
      if i < P.rank then Real.sqrt (1 + t i ^ 2) else 0 := by
    calc
      _ = (H * N * Hᵀ).toEuclideanLin.singularValues i :=
        congrArg (fun A : Matrix n n ℝ => A.toEuclideanLin.singularValues i) hForm
      _ = N.toEuclideanLin.singularValues i := by
        rw [← singularValues_eq_linearMap, ← singularValues_eq_linearMap,
          singularValues_mul_isometry_transpose hH, singularValues_isometry_mul hH]
      _ = _ := singularValues_oblique_canonical t ht0 ht (fun j hj => hz j (hg.trans hj)) i
  refine ⟨g, hg, t, ht0, ht, htpos, H, hH, hHt, hBlock, hSpec, ?_, ?_⟩
  · intro i
    rw [hSpec]
    by_cases hir : i < P.rank
    · rw [if_pos hir]
      constructor
      · intro hi
        by_contra hig
        rw [hz i (Nat.le_of_not_gt hig)] at hi
        norm_num at hi
      · intro hi
        have hp := (htpos i).mpr hi
        have hs := Real.sq_sqrt (show 0 ≤ 1 + t i ^ 2 by positivity)
        have hn := Real.sqrt_nonneg (1 + t i ^ 2)
        nlinarith
    · rw [if_neg hir]
      exact iff_of_false (by norm_num) (fun hi => hir (hi.trans_le (hg.trans (min_le_left _ _))))
  · intro i hi
    rw [hSpec i, if_pos (hi.trans_le (hg.trans (min_le_left _ _))),
      Real.sq_sqrt (by positivity), add_sub_cancel_left, Real.sqrt_sq (ht0 i)]

end NLAlib
