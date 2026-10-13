import NLAlib.Matrix.Subspaces.ComplexCSDecomposition
import NLAlib.Matrix.Subspaces.ComplexCSRank
import NLAlib.Matrix.Subspaces.ComplexObliqueSpectrum
import NLAlib.Matrix.Subspaces.ComplexObliqueSecant
/-!
# Complete complex cosine-sine and oblique projection contract

The full complex unitary CS form, complementary ranks, actual canonical
oblique singular spectrum, principal-angle secant and every norm endpoint.
The corresponding real orthogonal contract is in `CSToolkit`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- The complete complex unitary CS and complex oblique-projection
theorem. Four unitary factors have block sizes `p,p,q,q`; their cosines
are actual singular values. Every complex idempotent has its actual canonical
singular coefficients, range/kernel principal-angle secant at positive rank,
equal complementary norms at proper positive rank, and exact norm endpoints.
Together with `cs_decomposition_properties`, this supplies both the real
orthogonal and advertised complex unitary contracts without narrowing either.
Horn–Johnson 2013, Lemma 2.1.10, Theorem 2.7.1 and Corollary 3.4.3.3;
derivations Section alg:cs. Empty spaces and zero/pi/2 CS angles are included.
atlas: cs-decomposition -/
theorem complex_cs_decomposition_properties {p q n : Type*}
    [Fintype p] [Fintype q] [Fintype n]
    [DecidableEq p] [DecidableEq q] [DecidableEq n]
    (U : Matrix (p ⊕ q) (p ⊕ q) ℂ) (hU : Uᴴ * U = 1)
    (hCard : Fintype.card p ≤ Fintype.card q)
    (P : Matrix n n ℂ) (hP : IsIdempotentElem P) :
    (∃ e : p ↪ q,
      let c := fun i : p => singularValues U.toBlocks₁₁ ((Fintype.equivFin p) i)
      (∀ i, c i ∈ Set.Icc (0 : ℝ) 1) ∧
      ∃ V₁ W₁ : Matrix p p ℂ, ∃ V₂ W₂ : Matrix q q ℂ,
        V₁ᴴ * V₁ = 1 ∧ W₁ᴴ * W₁ = 1 ∧ V₂ᴴ * V₂ = 1 ∧ W₂ᴴ * W₂ = 1 ∧
        (Matrix.fromBlocks V₁ 0 0 V₂)ᴴ * U * Matrix.fromBlocks W₁ 0 0 W₂ =
          (csCanonicalMatrix c ((1 : Matrix q q ℝ).submatrix id e)).map Complex.ofReal) ∧
    U.toBlocks₁₂.rank = U.toBlocks₂₁.rank ∧
    U.toBlocks₂₂.rank = U.toBlocks₁₁.rank + Fintype.card q - Fintype.card p ∧
    (∃ g : ℕ, g ≤ min P.rank (Fintype.card n - P.rank) ∧
      ∃ t : ℕ → ℝ, (∀ i, 0 ≤ t i) ∧ Antitone t ∧ (∀ i, 0 < t i ↔ i < g) ∧
      ∃ H : Matrix n (Fin P.rank ⊕ Fin (Fintype.card n - P.rank)) ℂ,
        Hᴴ * H = 1 ∧ H * Hᴴ = 1 ∧
        Hᴴ * P * H = Matrix.fromBlocks 1 ((rectDiag t).map Complex.ofReal) 0 0 ∧
        (∀ i, singularValues P i =
          if i < P.rank then Real.sqrt (1 + t i ^ 2) else 0) ∧
        (∀ i, 1 < singularValues P i ↔ i < g) ∧
        (∀ i < g, t i = Real.sqrt (singularValues P i ^ 2 - 1))) ∧
    (∀ hr : 0 < P.rank, ∃ Q W : Matrix n (Fin P.rank) ℂ,
      Qᴴ * Q = 1 ∧ Wᴴ * W = 1 ∧
      LinearMap.range Q.toEuclideanLin = LinearMap.range P.toEuclideanLin ∧
      LinearMap.range W.toEuclideanLin = (LinearMap.ker P.toEuclideanLin)ᗮ ∧
      let θ := principalAnglesFintype W Q ⟨P.rank - 1, by simpa using Nat.sub_lt hr Nat.one_pos⟩
      (∀ i, principalAnglesFintype W Q i ≤ θ) ∧
      θ < Real.pi / 2 ∧ ‖P‖ = 1 / Real.cos θ) ∧
    (0 < P.rank → P.rank < Fintype.card n → ‖1 - P‖ = ‖P‖) ∧
    (P.rank = 0 → ‖P‖ = 0 ∧ ‖1 - P‖ = if Fintype.card n = 0 then 0 else 1) ∧
    (P.rank = Fintype.card n →
      ‖P‖ = (if Fintype.card n = 0 then 0 else 1) ∧ ‖1 - P‖ = 0) := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hCard
  exact ⟨⟨e, exists_complex_cs_decomposition_of_embedding U hU e⟩,
    rank_offDiagonal_blocks_eq_of_unitary U hU,
    rank_bottomRight_eq_rank_topLeft_add_card_sub_of_unitary U hU hCard,
    exists_unitary_idempotent_canonical_spectrum P hP,
    exists_complex_range_kernel_frames_norm_eq_secant P hP,
    (complex_idempotent_complement_norm_properties P hP).1,
    (complex_idempotent_complement_norm_properties P hP).2.1,
    (complex_idempotent_complement_norm_properties P hP).2.2⟩

end NLAlib
