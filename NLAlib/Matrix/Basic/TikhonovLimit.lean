import NLAlib.Matrix.Basic.Tikhonov
/-!
# The zero-parameter limit of Tikhonov regularization

The limit is the Moore–Penrose inverse at every rank, including the zero
matrix. A fixed positive thin SVD reduces the limit to scalar rational
functions whose denominators remain nonzero at zero.

Source: Hansen, §4.3; matrix-toolkit re-derivation, §25.
Atlas: `tikhonov-spectral-filter`.
-/
noncomputable section
open Matrix Filter Topology
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]
variable [DecidableEq m] [DecidableEq n]

/-- The actual Tikhonov inverse converges to the full Moore–Penrose inverse
as the positive regularization parameter tends to zero, without a rank
assumption. Combined with the unique-minimizer and noise theorems, this is
the complete ordinary Tikhonov contract.
atlas: tikhonov-spectral-filter (partial) -/
theorem tendsto_tikhonovInverse_zero (A : Matrix m n 𝕜) :
    Tendsto (tikhonovInverse A) (𝓝[>] (0 : ℝ)) (𝓝 (moorePenroseInverse A)) := by
  obtain ⟨U, V, h⟩ := exists_isThinSVD A
  let F := fun β : ℝ => V * diagonal
    (fun i : Fin A.rank => ((singularValues A i / (singularValues A i ^ 2 + β) : ℝ) : 𝕜)) * Uᴴ
  have hscalar (i : Fin A.rank) : ContinuousAt
      (fun β : ℝ => ((singularValues A i / (singularValues A i ^ 2 + β) : ℝ) : 𝕜)) 0 := by
    apply RCLike.continuous_ofReal.continuousAt.comp
    apply continuousAt_const.div (continuousAt_const.add continuousAt_id)
    have hp := h.pos i
    simpa using (sq_pos_of_pos hp).ne'
  have hdiag : ContinuousAt (fun β : ℝ => diagonal
      (fun i : Fin A.rank => ((singularValues A i / (singularValues A i ^ 2 + β) : ℝ) : 𝕜))) 0 := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    by_cases hij : i = j
    · subst j
      simpa only [Matrix.diagonal_apply_eq] using hscalar i
    · simpa only [Matrix.diagonal_apply_ne _ hij] using
        (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : 𝕜)) 0)
  have hmul : Continuous (fun M : Matrix (Fin A.rank) (Fin A.rank) 𝕜 => V * M * Uᴴ) := by
    fun_prop
  have hcont : ContinuousAt F 0 := hmul.continuousAt.comp hdiag
  have hF0 : F 0 = moorePenroseInverse A := by
    rw [h.moorePenroseInverse_eq]
    dsimp [F]
    congr 2
    funext i
    have hp := (h.pos i).ne'
    norm_cast
    simp only [add_zero]
    field_simp
  have heq : tikhonovInverse A =ᶠ[𝓝[>] (0 : ℝ)] F := by
    filter_upwards [self_mem_nhdsWithin] with β hβ
    exact h.tikhonovInverse_eq hβ
  rw [← hF0]
  exact (hcont.tendsto.mono_left inf_le_left).congr' heq.symm

/-- Convergence of the regularized solution in the Euclidean vector space.
atlas: tikhonov-spectral-filter (partial) -/
theorem tendsto_tikhonovInverse_mulVec_zero (A : Matrix m n 𝕜) (b : m → 𝕜) :
    Tendsto (fun β : ℝ => (WithLp.toLp 2 (tikhonovInverse A β *ᵥ b) : EuclideanSpace 𝕜 n))
      (𝓝[>] (0 : ℝ)) (𝓝 (WithLp.toLp 2 (moorePenroseInverse A *ᵥ b))) := by
  have hc : Continuous (fun M : Matrix n m 𝕜 =>
      (WithLp.toLp 2 (M *ᵥ b) : EuclideanSpace 𝕜 n)) := by fun_prop
  exact hc.continuousAt.tendsto.comp (tendsto_tikhonovInverse_zero A)

end NLAlib
