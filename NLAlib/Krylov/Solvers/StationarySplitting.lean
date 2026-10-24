import NLAlib.Matrix.Spectral.MatrixPowerFixedPoint
import NLAlib.Matrix.Spectral.MatrixPowerReal

/-! # Stationary splittings and their convergence criterion

The actual affine recursion is related to powers of its iteration matrix. For an invertible
splitting matrix `M`, the iteration converges to the unique solution for every right-hand
side and every initializer exactly when those powers decay. Existing real and complex
matrix-power criteria give the spectral-radius characterization.

Source: Darve, *Splitting Methods and Convergence Theory*, convergence theorem and error
recursion; Darve–Wootters (2021), classical iterative methods.
Atlas: `stationary-splitting-convergence`.
-/

noncomputable section

open Filter
open scoped Matrix Topology

namespace NLAlib

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The stationary affine iteration `xₖ₊₁ = H xₖ + d`, initialized at `x₀`.
Source: Darve–Wootters (2021), classical iterative methods. -/
def affineStationaryIterate (H : Matrix n n 𝕜) (d x₀ : n → 𝕜) : ℕ → n → 𝕜
  | 0 => x₀
  | k + 1 => H *ᵥ affineStationaryIterate H d x₀ k + d

omit [DecidableEq n] in
/-- The affine stationary iteration starts at the specified initializer. -/
@[simp] theorem affineStationaryIterate_zero (H : Matrix n n 𝕜) (d x₀ : n → 𝕜) :
    affineStationaryIterate H d x₀ 0 = x₀ := rfl

omit [DecidableEq n] in
/-- The stationary recursion applies the iteration matrix and adds its fixed forcing. -/
theorem affineStationaryIterate_succ (H : Matrix n n 𝕜) (d x₀ : n → 𝕜) (k : ℕ) :
    affineStationaryIterate H d x₀ (k + 1) = H *ᵥ affineStationaryIterate H d x₀ k + d := rfl

/-- Error about any fixed point is exactly the iteration-matrix power applied to initial error.
Source: Darve, *Splitting Methods and Convergence Theory*, error recursion. -/
theorem affineStationaryIterate_sub_eq_pow_mulVec {H : Matrix n n 𝕜} {d xs : n → 𝕜}
    (hxs : H *ᵥ xs + d = xs) (x₀ : n → 𝕜) (k : ℕ) :
    affineStationaryIterate H d x₀ k - xs = (H ^ k) *ᵥ (x₀ - xs) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [affineStationaryIterate_succ, pow_succ', ← Matrix.mulVec_mulVec, ← ih,
      Matrix.mulVec_sub, eq_sub_iff_add_eq.mpr hxs]
    abel

/-- The actual splitting recursion `xₖ₊₁ = M⁻¹ N xₖ + M⁻¹ b`.
Source: Darve, *Splitting Methods and Convergence Theory*.
atlas: stationary-splitting-convergence (partial) -/
def splittingIterate (M N : Matrix n n 𝕜) (b x₀ : n → 𝕜) : ℕ → n → 𝕜 :=
  affineStationaryIterate (M⁻¹ * N) (M⁻¹ *ᵥ b) x₀

/-- A splitting iteration starts at its specified initializer. -/
@[simp] theorem splittingIterate_zero (M N : Matrix n n 𝕜) (b x₀ : n → 𝕜) :
    splittingIterate M N b x₀ 0 = x₀ := rfl

/-- The actual splitting iteration uses the prescribed affine update.
Source: Darve, *Splitting Methods and Convergence Theory*.
atlas: stationary-splitting-convergence (partial) -/
theorem splittingIterate_succ (M N : Matrix n n 𝕜) (b x₀ : n → 𝕜) (k : ℕ) :
    splittingIterate M N b x₀ (k + 1) = (M⁻¹ * N) *ᵥ splittingIterate M N b x₀ k +
      M⁻¹ *ᵥ b := rfl

/-- With invertible `M`, the splitting fixed-point equation is the original linear system. -/
theorem splitting_fixedPoint_iff {M N : Matrix n n 𝕜} (hM : IsUnit M) (b xs : n → 𝕜) :
    (M⁻¹ * N) *ᵥ xs + M⁻¹ *ᵥ b = xs ↔ (M - N) *ᵥ xs = b := by
  have hd := (Matrix.isUnit_iff_isUnit_det M).mp hM
  have hmul : M *ᵥ ((M⁻¹ * N) *ᵥ xs + M⁻¹ *ᵥ b) = N *ᵥ xs + b := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv M hd, Matrix.one_mul, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv M hd, Matrix.one_mulVec]
  constructor
  · intro h
    rw [h] at hmul
    rw [Matrix.sub_mulVec]
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hmul)
  · intro h
    apply Matrix.mulVec_injective_iff_isUnit.mpr hM
    rw [hmul]
    rw [Matrix.sub_mulVec] at h
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp h).symm

/-- A splitting factors as `M (I - M⁻¹N)` when `M` is invertible.
atlas: stationary-splitting-convergence (partial) -/
theorem sub_eq_mul_one_sub_inv_mul {M N : Matrix n n 𝕜} (hM : IsUnit M) :
    M - N = M * (1 - M⁻¹ * N) := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp hM), Matrix.one_mul]

/-- The splitting iteration has the exact advertised error-power identity at every step.
Source: Darve, *Splitting Methods and Convergence Theory*, error recursion.
atlas: stationary-splitting-convergence (partial) -/
theorem splittingIterate_sub_eq_pow_mulVec {M N : Matrix n n 𝕜} (hM : IsUnit M)
    {b xs : n → 𝕜} (hxs : (M - N) *ᵥ xs = b) (x₀ : n → 𝕜) (k : ℕ) :
    splittingIterate M N b x₀ k - xs = ((M⁻¹ * N) ^ k) *ᵥ (x₀ - xs) :=
  affineStationaryIterate_sub_eq_pow_mulVec ((splitting_fixedPoint_iff hM b xs).mpr hxs) x₀ k

/-- Every right-hand side has a unique solution, and the actual splitting iteration converges
to that solution from every initializer. This is the full convergence contract, including
uniqueness of the linear-system solution.
atlas: stationary-splitting-convergence (partial) -/
def SplittingConverges (M N : Matrix n n 𝕜) : Prop :=
  ∀ b : n → 𝕜, ∃ xs : n → 𝕜,
    (M - N) *ᵥ xs = b ∧ (∀ ys, (M - N) *ᵥ ys = b → ys = xs) ∧
      ∀ x₀, Tendsto (splittingIterate M N b x₀) atTop (𝓝 xs)

/-- Decaying splitting powers make the original matrix invertible; no existence hypothesis
on a solution is required.
atlas: stationary-splitting-convergence (partial) -/
theorem isUnit_sub_of_tendsto_splitting_pow_zero {M N : Matrix n n 𝕜} (hM : IsUnit M)
    (hpow : Tendsto (fun k : ℕ => (M⁻¹ * N) ^ k) atTop (𝓝 0)) : IsUnit (M - N) := by
  rw [sub_eq_mul_one_sub_inv_mul hM]
  exact hM.mul (Matrix.isUnit_one_sub_of_tendsto_pow_zero hpow)

/-- The complete all-right-hand-sides splitting convergence contract is equivalent to matrix
power decay. Source: Darve, *Splitting Methods and Convergence Theory*.
atlas: stationary-splitting-convergence (partial) -/
theorem splittingConverges_iff_tendsto_pow_zero {M N : Matrix n n 𝕜} (hM : IsUnit M) :
    SplittingConverges M N ↔ Tendsto (fun k : ℕ => (M⁻¹ * N) ^ k) atTop (𝓝 0) := by
  constructor
  · intro h
    obtain ⟨xs, -, huniq, hlim⟩ := h 0
    have hxs : xs = 0 := (huniq 0 (by simp)).symm
    subst xs
    apply (Matrix.tendsto_pow_zero_iff_forall_mulVec _).mpr
    intro x₀
    have heq (k : ℕ) : splittingIterate M N 0 x₀ k = ((M⁻¹ * N) ^ k) *ᵥ x₀ := by
      simpa using splittingIterate_sub_eq_pow_mulVec hM (b := 0) (xs := 0) (by simp) x₀ k
    exact (hlim x₀).congr' (Filter.Eventually.of_forall heq)
  · intro hpow b
    have hA := isUnit_sub_of_tendsto_splitting_pow_zero hM hpow
    let xs := (M - N)⁻¹ *ᵥ b
    have hxs : (M - N) *ᵥ xs = b := by
      dsimp [xs]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).mp hA), Matrix.one_mulVec]
    refine ⟨xs, hxs, ?_, ?_⟩
    · intro ys hys
      exact Matrix.mulVec_injective_iff_isUnit.mpr hA (hys.trans hxs.symm)
    · intro x₀
      have ht := ((Matrix.tendsto_pow_zero_iff_forall_mulVec _).mp hpow (x₀ - xs)).add_const xs
      have heq (k : ℕ) : splittingIterate M N b x₀ k =
          ((M⁻¹ * N) ^ k) *ᵥ (x₀ - xs) + xs :=
        eq_add_of_sub_eq (splittingIterate_sub_eq_pow_mulVec hM hxs x₀ k)
      simpa only [zero_add, ← heq] using ht

/-- Complex stationary splitting converges for every system and start exactly when its
iteration matrix has spectral radius below one.
Source: Darve, *Splitting Methods and Convergence Theory*, convergence theorem.
atlas: stationary-splitting-convergence (partial) -/
theorem splittingConverges_iff_spectralRadius_lt_one {M N : Matrix n n ℂ} (hM : IsUnit M) :
    SplittingConverges M N ↔ spectralRadius ℂ (M⁻¹ * N) < 1 := by
  rw [splittingConverges_iff_tendsto_pow_zero hM,
    tendsto_matrix_pow_zero_iff_spectralRadius_lt_one]

/-- For real matrices the exact convergence criterion uses the complexified spectral radius,
so nonreal eigenvalues are covered. Source: Darve, convergence theorem.
atlas: stationary-splitting-convergence (partial) -/
theorem splittingConverges_iff_complex_spectralRadius_lt_one
    {M N : Matrix n n ℝ} (hM : IsUnit M) :
    SplittingConverges M N ↔ spectralRadius ℂ ((M⁻¹ * N).map Complex.ofReal) < 1 := by
  rw [splittingConverges_iff_tendsto_pow_zero hM,
    tendsto_real_matrix_pow_zero_iff_complex_spectralRadius_lt_one]

end NLAlib
