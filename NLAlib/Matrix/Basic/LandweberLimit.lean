import NLAlib.Matrix.Basic.Landweber
/-!
# Convergence of Landweber iteration

For the exact step-size interval, every positive singular multiplier has
modulus strictly smaller than one. The nullspace multiplier is exactly
one, yielding the Moore–Penrose solution plus the initial null component.
Source: Hansen, §6.3; matrix-toolkit re-derivation, §27.
Atlas: `landweber-spectral-filter`.
-/
noncomputable section
open Matrix Filter Topology
open scoped Matrix
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]
variable [DecidableEq m] [DecidableEq n]

/-- In the open stability interval, powers of the Landweber step converge
to the orthogonal projector onto the true kernel of the forward matrix. -/
theorem tendsto_landweberStepMatrix_pow (A : Matrix m n 𝕜) (hA : A ≠ 0)
    {η : ℝ} (hη : 0 < η) (hstep : η < 2 / specNorm A ^ 2) :
    Tendsto (fun t : ℕ => landweberStepMatrix A η ^ t) atTop
      (𝓝 (1 - moorePenroseInverse A * A)) := by
  obtain ⟨U, V, h⟩ := exists_isThinSVD A
  have hN : 0 < specNorm A := by
    open scoped Matrix.Norms.L2Operator in
      rw [specNorm_eq_norm]
      exact norm_pos_iff.mpr hA
  have hηN : η * specNorm A ^ 2 < 2 :=
    (lt_div_iff₀ (sq_pos_of_pos hN)).mp hstep
  have hscalar (i : Fin A.rank) : Tendsto
      (fun t : ℕ => (((1 - η * singularValues A i ^ 2) ^ t : ℝ) : 𝕜)) atTop (𝓝 0) := by
    have hs := h.pos i
    have hsN := singularValues_le_specNorm A i
    have hηs : η * singularValues A i ^ 2 < 2 :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.le hsN 2) hη.le).trans_lt hηN
    have hroot : |1 - η * singularValues A i ^ 2| < 1 := by
      rw [abs_lt]
      constructor <;> nlinarith [mul_pos hη (sq_pos_of_pos hs)]
    have hp : Tendsto (fun t : ℕ => (1 - η * singularValues A i ^ 2) ^ t)
        atTop (𝓝 (0 : ℝ)) := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hroot
    simpa only [RCLike.ofReal_zero, Function.comp_def] using
      (RCLike.continuous_ofReal : Continuous (fun x : ℝ => (x : 𝕜))).continuousAt.tendsto.comp hp
  have hdiag : Tendsto (fun t : ℕ => diagonal
      (fun i : Fin A.rank => (((1 - η * singularValues A i ^ 2) ^ t : ℝ) : 𝕜)))
      atTop (𝓝 (0 : Matrix (Fin A.rank) (Fin A.rank) 𝕜)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    by_cases hij : i = j
    · subst j; simpa using hscalar i
    · simpa [Matrix.diagonal_apply_ne _ hij] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : 𝕜)) atTop (𝓝 0))
  have hc : Continuous (fun M : Matrix (Fin A.rank) (Fin A.rank) 𝕜 =>
      (1 - V * Vᴴ) + V * M * Vᴴ) := by fun_prop
  have ht := hc.continuousAt.tendsto.comp hdiag
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero] at ht
  rw [h.moorePenroseInverse_mul_eq]
  exact ht.congr' (Filter.Eventually.of_forall fun t => (h.landweberStepMatrix_pow η t).symm)

/-- The actual Landweber recurrence converges from arbitrary initialization
to `A†b + P_ker(A) x₀`. Thus only zero initialization guarantees the minimum
norm solution. The zero-matrix case is the separate constant-iterate theorem.
atlas: landweber-spectral-filter (partial) -/
theorem tendsto_landweberIterate (A : Matrix m n 𝕜) (hA : A ≠ 0) (b : m → 𝕜)
    {η : ℝ} (hη : 0 < η) (hstep : η < 2 / specNorm A ^ 2) (x₀ : n → 𝕜) :
    Tendsto (fun t => (WithLp.toLp 2 (landweberIterate A b η x₀ t) : EuclideanSpace 𝕜 n))
      atTop (𝓝 (WithLp.toLp 2 (moorePenroseInverse A *ᵥ b +
        (1 - moorePenroseInverse A * A) *ᵥ x₀))) := by
  have hc : Continuous (fun M : Matrix n n 𝕜 => (WithLp.toLp 2
      (moorePenroseInverse A *ᵥ b + M *ᵥ (x₀ - moorePenroseInverse A *ᵥ b)) :
        EuclideanSpace 𝕜 n)) := by fun_prop
  have ht := hc.continuousAt.tendsto.comp (tendsto_landweberStepMatrix_pow A hA hη hstep)
  have hkill : (1 - moorePenroseInverse A * A) * moorePenroseInverse A = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, moorePenroseInverse_mul_moorePenroseInverse, sub_self]
  have hz : (1 - moorePenroseInverse A * A) *ᵥ (x₀ - moorePenroseInverse A *ᵥ b) =
      (1 - moorePenroseInverse A * A) *ᵥ x₀ := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hkill, Matrix.zero_mulVec, sub_zero]
  rw [hz] at ht
  apply ht.congr'
  apply Filter.Eventually.of_forall
  intro t
  apply congrArg (fun v : n → 𝕜 => (WithLp.toLp 2 v : EuclideanSpace 𝕜 n))
  have he := landweberIterate_sub_pinv A b η x₀ t
  linear_combination -he

/-- Zero-start Landweber converges to the Moore–Penrose least-squares
solution, at every nonzero matrix rank and throughout the sharp open
step-size interval.
atlas: landweber-spectral-filter (partial) -/
theorem tendsto_landweberIterate_zero (A : Matrix m n 𝕜) (hA : A ≠ 0) (b : m → 𝕜)
    {η : ℝ} (hη : 0 < η) (hstep : η < 2 / specNorm A ^ 2) :
    Tendsto (fun t => (WithLp.toLp 2 (landweberIterate A b η 0 t) : EuclideanSpace 𝕜 n))
      atTop (𝓝 (WithLp.toLp 2 (moorePenroseInverse A *ᵥ b))) := by
  simpa using tendsto_landweberIterate A hA b hη hstep 0

end NLAlib
