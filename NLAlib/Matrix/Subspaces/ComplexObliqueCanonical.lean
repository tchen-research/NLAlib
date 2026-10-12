import NLAlib.Matrix.Subspaces.ComplexObliqueBlocks
import NLAlib.Matrix.Spectral.ComplexRectangularSVD
/-!
# Complex unitary canonical form of an oblique projection

Every complex idempotent is unitarily similar to a real canonical matrix
consisting of oblique planes, scalar ones and scalar zeros.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- Every complex idempotent is unitarily similar to the complexification
of `[I diag(t);0 0]`, where `t` is nonnegative, decreasing, and positive
exactly on the first `g` coordinates. These are the actual canonical
oblique planes `[1 tᵢ;0 0]`, with all remaining ones and zeros included.
Horn–Johnson 2013, Corollary 3.4.3.3; zero and full rank are allowed.
atlas: cs-decomposition (partial) -/
theorem exists_unitary_idempotent_canonical {n : Type*}
    [Fintype n] [DecidableEq n] (P : Matrix n n ℂ) (hP : IsIdempotentElem P) :
    ∃ g : ℕ, g ≤ min P.rank (Fintype.card n - P.rank) ∧
    ∃ t : ℕ → ℝ, (∀ i, 0 ≤ t i) ∧ Antitone t ∧ (∀ i, 0 < t i ↔ i < g) ∧
    ∃ H : Matrix n (Fin P.rank ⊕ Fin (Fintype.card n - P.rank)) ℂ,
      Hᴴ * H = 1 ∧ H * Hᴴ = 1 ∧
      Hᴴ * P * H = Matrix.fromBlocks 1 ((rectDiag t).map Complex.ofReal) 0 0 := by
  obtain ⟨H, T, hH, hHt, hBlock⟩ := exists_unitary_idempotent_range_blocks P hP
  obtain ⟨V₀, W₀, hSVD⟩ := exists_complex_rectangular_svd T
  let V := (V₀ : Matrix (Fin P.rank) (Fin P.rank) ℂ)
  let W := (W₀ : Matrix (Fin (Fintype.card n - P.rank)) (Fin (Fintype.card n - P.rank)) ℂ)
  have hV : Vᴴ * V = 1 := Unitary.coe_star_mul_self V₀
  have hW : Wᴴ * W = 1 := Unitary.coe_star_mul_self W₀
  let K := Matrix.fromBlocks V 0 0 W
  have hK : Kᴴ * K = 1 := by
    simp only [K, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, hV, hW, Matrix.fromBlocks_one]
  have hpos (i : ℕ) : 0 < T.toEuclideanLin.singularValues i ↔ i < T.rank := by
    rw [LinearMap.singularValues_pos_iff_lt_finrank_range]
    have hr : Module.finrank ℂ T.toEuclideanLin.range = T.rank :=
      (T.rank_eq_finrank_range_toLin
        (EuclideanSpace.basisFun (Fin P.rank) ℂ).toBasis
        (EuclideanSpace.basisFun (Fin (Fintype.card n - P.rank)) ℂ).toBasis).symm
    rw [hr]
  refine ⟨T.rank, le_min T.rank_le_height T.rank_le_width,
    (fun i => T.toEuclideanLin.singularValues i), T.toEuclideanLin.singularValues_nonneg,
    T.toEuclideanLin.singularValues_antitone, hpos, H * K, ?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Hᴴ H K,
      hH, Matrix.one_mul, hK]
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc K Kᴴ Hᴴ,
      mul_eq_one_comm.mp hK, Matrix.one_mul, hHt]
  · rw [Matrix.conjTranspose_mul]
    calc
      _ = Kᴴ * (Hᴴ * P * H) * K := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hBlock]
        simp only [K, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
          Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
          add_zero, zero_add, Matrix.mul_one, hV]
        exact congrArg (fun B => Matrix.fromBlocks 1 B 0 0) hSVD

end NLAlib
