import NLAlib.Matrix.Functions.OddPolarIteration
import NLAlib.Matrix.Spectral.CoordinateRankOne

/-! # The scalar interval error is the worst-case matrix polar error

An actual rank-one matrix in every nonempty rectangular shape realizes each
positive scalar in the interval. Thus an interval bound is equivalent to a
uniform matrix bound over the corresponding nonzero-singular-value class.
Zero matrices are included and force nonnegative uniform error bounds.
Source: Polar Express, Theorem 3.3, compact-SVD extension.
-/
noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Each scalar error is realized by an actual rank-one input of any fixed
nonempty shape, with no assumption about the update coefficients. -/
theorem specNorm_polar_sub_oddMatrixIterate_coordinateRankOneMatrix
    (i₀ : m) (j₀ : n) {x : ℝ} (hx : 0 < x)
    (q : ℕ) (a : ℕ → ℕ → ℝ) (T : ℕ) :
    specNorm (canonicalPartialPolar (coordinateRankOneMatrix i₀ j₀ x) -
      oddMatrixIterate q a (coordinateRankOneMatrix i₀ j₀ x) T) =
        |1 - oddScalarComposition q a x T| := by
  rw [(isThinSVD_coordinateRankOneMatrix i₀ j₀ hx).specNorm_polar_sub_oddMatrixIterate_eq]
  simp

/-- Uniform matrix polar-error bounds are exactly scalar interval bounds.
The forward direction uses a concrete rank-one witness for every scalar;
the reverse direction covers every rank, including zero.
Source: Polar Express, Theorem 3.3, compact-SVD extension.
atlas: polar-minimax-polynomial-iteration (partial) -/
theorem oddMatrixIterate_uniform_error_iff [Nonempty m] [Nonempty n]
    (q : ℕ) (a : ℕ → ℕ → ℝ) (T : ℕ) {l u ε : ℝ} (hl : 0 < l) :
    (∀ A : Matrix m n ℂ,
      (∀ k, 0 < singularValues A k → singularValues A k ∈ Set.Icc l u) →
        specNorm (canonicalPartialPolar A - oddMatrixIterate q a A T) ≤ ε) ↔
      0 ≤ ε ∧ ∀ x ∈ Set.Icc l u, |1 - oddScalarComposition q a x T| ≤ ε := by
  constructor
  · intro h
    have hzero := h 0 (by
      intro k hk
      rw [singularValues_eq_zero_of_rank_le _ (by simp)] at hk
      exact (lt_irrefl _ hk).elim)
    refine ⟨(specNorm_nonneg _).trans hzero, fun x hx => ?_⟩
    let i₀ : m := Classical.choice inferInstance
    let j₀ : n := Classical.choice inferInstance
    have hx0 : 0 < x := hl.trans_le hx.1
    have hm := h (coordinateRankOneMatrix i₀ j₀ x) (fun k hk => by
      rwa [singularValues_coordinateRankOneMatrix_of_pos i₀ j₀ hx0 hk])
    rwa [specNorm_polar_sub_oddMatrixIterate_coordinateRankOneMatrix i₀ j₀ hx0] at hm
  · rintro ⟨hε, hb⟩ A hA
    obtain ⟨U, V, ht⟩ := exists_isThinSVD A
    exact ht.specNorm_polar_sub_oddMatrixIterate_le q a T
      (fun i => hA i (ht.pos i)) hε hb

end NLAlib
