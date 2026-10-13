import NLAlib.Matrix.Subspaces.CSDecomposition
import NLAlib.Matrix.Subspaces.CSRank
import NLAlib.Matrix.Subspaces.ObliqueProjectionSecant
import NLAlib.Matrix.Subspaces.ObliqueProjectionNorms
/-!
# Complete cosine–sine and oblique projection contract

The full block-orthogonal CS form, complementary block ranks, actual oblique
canonical singular coefficients, positive-rank secant and all norm endpoints.
Horn–Johnson 2013, Lemma 2.1.10, Theorem 2.7.1 and Corollary 3.4.3.3.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- The complete real CS and oblique-projection theorem. The CS factors have
one `p` and one `q` block on each side, with actual singular-value cosines and
literal coordinate inclusion. The oblique canonical coefficients have their
full actual singular-spectrum identities. The secant is asserted at positive
rank for the actual range and kernel-complement subspaces; complementary norm
equality requires proper positive rank and both rank endpoints are explicit.
Horn–Johnson 2013, Lemma 2.1.10, Theorem 2.7.1 and Corollary 3.4.3.3;
derivations §alg:cs. Empty spaces and zero/pi/2 CS angles are included.
atlas: cs-decomposition (partial) -/
theorem cs_decomposition_properties {p q n : Type*}
    [Fintype p] [Fintype q] [Fintype n]
    [DecidableEq p] [DecidableEq q] [DecidableEq n]
    (U : Matrix (p ⊕ q) (p ⊕ q) ℝ) (hU : HasOrthonormalCols U)
    (hCard : Fintype.card p ≤ Fintype.card q)
    (P : Matrix n n ℝ) (hP : IsIdempotentElem P) :
    (∃ e : p ↪ q,
      let c := fun i : p => singularValues U.toBlocks₁₁ ((Fintype.equivFin p) i)
      (∀ i, c i ∈ Set.Icc (0 : ℝ) 1) ∧
      ∃ V₁ W₁ : Matrix p p ℝ, ∃ V₂ W₂ : Matrix q q ℝ,
        HasOrthonormalCols V₁ ∧ HasOrthonormalCols W₁ ∧
        HasOrthonormalCols V₂ ∧ HasOrthonormalCols W₂ ∧
        (Matrix.fromBlocks V₁ 0 0 V₂)ᵀ * U * Matrix.fromBlocks W₁ 0 0 W₂ =
          csCanonicalMatrix c ((1 : Matrix q q ℝ).submatrix id e)) ∧
    U.toBlocks₁₂.rank = U.toBlocks₂₁.rank ∧
    U.toBlocks₂₂.rank = U.toBlocks₁₁.rank + Fintype.card q - Fintype.card p ∧
    (∃ g : ℕ, g ≤ min P.rank (Fintype.card n - P.rank) ∧
      ∃ t : ℕ → ℝ, (∀ i, 0 ≤ t i) ∧ Antitone t ∧ (∀ i, 0 < t i ↔ i < g) ∧
      ∃ H : Matrix n (Fin P.rank ⊕ Fin (Fintype.card n - P.rank)) ℝ,
        HasOrthonormalCols H ∧ H * Hᵀ = 1 ∧
        Hᵀ * P * H = Matrix.fromBlocks 1 (rectDiag t) 0 0 ∧
        (∀ i, singularValues P i =
          if i < P.rank then Real.sqrt (1 + t i ^ 2) else 0) ∧
        (∀ i, 1 < singularValues P i ↔ i < g) ∧
        (∀ i < g, t i = Real.sqrt (singularValues P i ^ 2 - 1))) ∧
    (∀ hr : 0 < P.rank, ∃ Q W : Matrix n (Fin P.rank) ℝ,
      HasOrthonormalCols Q ∧ HasOrthonormalCols W ∧
      LinearMap.range Q.toEuclideanLin = LinearMap.range P.toEuclideanLin ∧
      LinearMap.range W.toEuclideanLin = (LinearMap.ker P.toEuclideanLin)ᗮ ∧
      let θ := principalAnglesFintype W Q ⟨P.rank - 1, by simpa using Nat.sub_lt hr Nat.one_pos⟩
      (∀ i, principalAnglesFintype W Q i ≤ θ) ∧
      θ < Real.pi / 2 ∧ specNorm P = 1 / Real.cos θ) ∧
    (0 < P.rank → P.rank < Fintype.card n → specNorm (1 - P) = specNorm P) ∧
    (P.rank = 0 → specNorm P = 0 ∧
      specNorm (1 - P) = if Fintype.card n = 0 then 0 else 1) ∧
    (P.rank = Fintype.card n →
      specNorm P = (if Fintype.card n = 0 then 0 else 1) ∧ specNorm (1 - P) = 0) := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hCard
  refine ⟨⟨e, exists_cs_decomposition_of_embedding U hU e⟩,
    rank_offDiagonal_blocks_eq_of_orthogonal U hU,
    rank_bottomRight_eq_rank_topLeft_add_card_sub_of_orthogonal U hU hCard,
    exists_orthogonal_idempotent_canonical_spectrum P hP, ?_,
    specNorm_one_sub_eq_of_idempotent_of_rank_pos_lt hP,
    (specNorm_idempotent_rank_endpoints hP).1, (specNorm_idempotent_rank_endpoints hP).2⟩
  intro hr
  exact exists_range_kernel_frames_specNorm_eq_secant P hP hr

end NLAlib
