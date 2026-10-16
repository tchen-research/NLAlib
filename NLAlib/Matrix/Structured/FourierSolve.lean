import NLAlib.Matrix.Structured.FourierCirculant

/-! # Singular circulant solves in Fourier coordinates

Reciprocal multipliers give the minimum-norm least-squares solution. All
statements include zero Fourier modes; no invertibility assumption is hidden
in the solve definition. Source: Meyer, Matrix Analysis, §5.5.
-/

noncomputable section
open Matrix Finset
open scoped Matrix

namespace NLAlib
variable {n : ℕ} [NeZero n]

/-- The finite Fourier transform converts circulant multiplication into
coordinatewise multiplication by the transform of its generating column. -/
theorem dft_circulant_mulVec (c x : ZMod n → ℂ) :
    ZMod.dft (Matrix.circulant c *ᵥ x) = fun j => ZMod.dft c j * ZMod.dft x j := by
  rw [← fourierMatrix_mulVec, Matrix.mulVec_mulVec, fourierMatrix_mul_circulant,
    ← Matrix.mulVec_mulVec, fourierMatrix_mulVec]
  exact funext (Matrix.mulVec_diagonal _ _)

/-- Cyclic convolution is exactly the inverse transform of the product of transforms.
Source: Meyer §5.5.
atlas: toeplitz-circulant-fft-product (partial) -/
theorem circulant_mulVec_eq_invDFT (c x : ZMod n → ℂ) :
    Matrix.circulant c *ᵥ x = ZMod.dft.symm (fun j => ZMod.dft c j * ZMod.dft x j) := by
  apply ZMod.dft.injective
  rw [LinearEquiv.apply_symm_apply, dft_circulant_mulVec]

/-- Reciprocal Fourier modes, with zero reciprocal at zero modes. -/
def fourierCirculantSolve (c b : ZMod n → ℂ) : ZMod n → ℂ :=
  ZMod.dft.symm (fun j => (ZMod.dft c j)⁻¹ * ZMod.dft b j)

/-- The Fourier solve is exactly multiplication by the canonical pseudoinverse.
Source: Meyer §5.5.
atlas: circulant-fourier-pseudoinverse (partial) -/
theorem fourierCirculantSolve_eq_moorePenroseInverse_mulVec (c b : ZMod n → ℂ) :
    fourierCirculantSolve c b = moorePenroseInverse (Matrix.circulant c) *ᵥ b := by
  rw [moorePenroseInverse_circulant, circulant_mulVec_eq_invDFT,
    LinearEquiv.apply_symm_apply]
  rfl

/-- The normalized Fourier transform agrees with matrix-vector multiplication by `U`. -/
theorem fourierUnitary_mulVec (x : ZMod n → ℂ) :
    fourierUnitary n *ᵥ x = (Real.sqrt (n : ℝ) : ℂ)⁻¹ • ZMod.dft x := by
  rw [fourierUnitary, Matrix.smul_mulVec, fourierMatrix_mulVec]

/-- Unitary Fourier coordinates preserve the Euclidean vector norm. -/
theorem norm_fourierUnitary_mulVec (x : ZMod n → ℂ) :
    ‖WithLp.toLp 2 (fourierUnitary n *ᵥ x)‖ = ‖WithLp.toLp 2 x‖ := by
  exact (fourierUnitary_hasOrthonormalCols (n := n)).toLinearIsometry.norm_map
    (WithLp.toLp 2 x)

/-- Normalized Fourier coordinates of a circulant product. -/
theorem fourierUnitary_circulant_mulVec (c x : ZMod n → ℂ) :
    fourierUnitary n *ᵥ (Matrix.circulant c *ᵥ x) =
      fun j => ZMod.dft c j * (fourierUnitary n *ᵥ x) j := by
  rw [fourierUnitary_mulVec, dft_circulant_mulVec, fourierUnitary_mulVec]
  funext j
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Fourier coordinates of the minimum-norm solve. -/
theorem fourierUnitary_fourierCirculantSolve (c b : ZMod n → ℂ) :
    fourierUnitary n *ᵥ fourierCirculantSolve c b =
      fun j => (ZMod.dft c j)⁻¹ * (fourierUnitary n *ᵥ b) j := by
  simp only [fourierCirculantSolve, fourierUnitary_mulVec, LinearEquiv.apply_symm_apply]
  funext j
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Only zero Fourier modes remain in the optimal residual. -/
theorem fourierCirculantSolve_residual_coordinates (c b : ZMod n → ℂ) :
    fourierUnitary n *ᵥ (b - Matrix.circulant c *ᵥ fourierCirculantSolve c b) =
      fun j => if ZMod.dft c j = 0 then (fourierUnitary n *ᵥ b) j else 0 := by
  rw [Matrix.mulVec_sub, fourierUnitary_circulant_mulVec,
    fourierUnitary_fourierCirculantSolve]
  funext j
  by_cases hj : ZMod.dft c j = 0 <;> simp [hj]

/-- Exact residual energy, including singular circulants and repeated zero modes.
Source: Meyer §5.5.
atlas: circulant-fourier-pseudoinverse (partial) -/
theorem fourierCirculantSolve_residual_sq (c b : ZMod n → ℂ) :
    ‖WithLp.toLp 2 (b - Matrix.circulant c *ᵥ fourierCirculantSolve c b)‖ ^ 2 =
      ∑ j with ZMod.dft c j = 0, ‖(fourierUnitary n *ᵥ b) j‖ ^ 2 := by
  rw [← norm_fourierUnitary_mulVec, fourierCirculantSolve_residual_coordinates,
    EuclideanSpace.norm_sq_eq]
  simp only [apply_ite norm, norm_zero, ite_pow, zero_pow two_ne_zero,
    Finset.sum_filter]

/-- The Fourier pseudoinverse solve minimizes the Euclidean residual over all vectors.
Source: Meyer §5.5.
atlas: circulant-fourier-pseudoinverse (partial) -/
theorem fourierCirculantSolve_leastSquares (c b x : ZMod n → ℂ) :
    ‖WithLp.toLp 2 (b - Matrix.circulant c *ᵥ fourierCirculantSolve c b)‖ ≤
      ‖WithLp.toLp 2 (b - Matrix.circulant c *ᵥ x)‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [fourierCirculantSolve_residual_sq, ← norm_fourierUnitary_mulVec,
    Matrix.mulVec_sub, fourierUnitary_circulant_mulVec, EuclideanSpace.norm_sq_eq]
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : ZMod.dft c j = 0
  · simp [hj]
  · simp only [hj, if_false]
    exact sq_nonneg _

/-- Exact solvability is precisely compatibility at every zero Fourier mode.
Source: Meyer §5.5.
atlas: circulant-fourier-pseudoinverse (partial) -/
theorem exists_circulant_mulVec_eq_iff (c b : ZMod n → ℂ) :
    (∃ x, Matrix.circulant c *ᵥ x = b) ↔
      ∀ j, ZMod.dft c j = 0 → ZMod.dft b j = 0 := by
  constructor
  · rintro ⟨x, hx⟩ j hj
    have h := congrFun (dft_circulant_mulVec c x) j
    simpa only [hx, hj, zero_mul] using h
  · intro h
    refine ⟨fourierCirculantSolve c b, ZMod.dft.injective ?_⟩
    rw [dft_circulant_mulVec]
    simp only [fourierCirculantSolve, LinearEquiv.apply_symm_apply]
    funext j
    by_cases hj : ZMod.dft c j = 0 <;> simp [hj, h j]

/-- Residual energy splits into the unavoidable zero modes and the nonzero-mode
fitting error. This identity also characterizes every least-squares minimizer. -/
theorem circulant_residual_sq_eq_optimal_add (c b x : ZMod n → ℂ) :
    ‖WithLp.toLp 2 (b - Matrix.circulant c *ᵥ x)‖ ^ 2 =
      ‖WithLp.toLp 2 (b - Matrix.circulant c *ᵥ fourierCirculantSolve c b)‖ ^ 2 +
      ∑ j with ZMod.dft c j ≠ 0,
        ‖(fourierUnitary n *ᵥ b) j - ZMod.dft c j * (fourierUnitary n *ᵥ x) j‖ ^ 2 := by
  rw [fourierCirculantSolve_residual_sq, ← norm_fourierUnitary_mulVec,
    Matrix.mulVec_sub, fourierUnitary_circulant_mulVec, EuclideanSpace.norm_sq_eq]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : ZMod.dft c j = 0 <;> simp [hj]

/-- Every residual minimizer fits all nonzero Fourier modes exactly. -/
theorem circulant_fit_modes_of_residual_le_optimal (c b x : ZMod n → ℂ)
    (hx : ‖WithLp.toLp 2 (b - Matrix.circulant c *ᵥ x)‖ ≤
      ‖WithLp.toLp 2 (b - Matrix.circulant c *ᵥ fourierCirculantSolve c b)‖) :
    ∀ j, ZMod.dft c j ≠ 0 →
      (fourierUnitary n *ᵥ x) j = (ZMod.dft c j)⁻¹ * (fourierUnitary n *ᵥ b) j := by
  have he := circulant_residual_sq_eq_optimal_add c b x
  have hsq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hx
  have hs : (∑ j with ZMod.dft c j ≠ 0,
      ‖(fourierUnitary n *ᵥ b) j - ZMod.dft c j * (fourierUnitary n *ᵥ x) j‖ ^ 2) ≤ 0 := by
    linarith
  intro j hj
  have hsingle := Finset.single_le_sum
    (s := Finset.univ.filter (fun j => ZMod.dft c j ≠ 0))
    (f := fun j => ‖(fourierUnitary n *ᵥ b) j - ZMod.dft c j * (fourierUnitary n *ᵥ x) j‖ ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_filter.mpr ⟨mem_univ j, hj⟩)
  have hn : ‖(fourierUnitary n *ᵥ b) j - ZMod.dft c j * (fourierUnitary n *ᵥ x) j‖ = 0 := by
    nlinarith [norm_nonneg ((fourierUnitary n *ᵥ b) j -
      ZMod.dft c j * (fourierUnitary n *ᵥ x) j)]
  have hz := sub_eq_zero.mp (norm_eq_zero.mp hn)
  rw [hz, ← mul_assoc, inv_mul_cancel₀ hj, one_mul]

/-- Among all Euclidean residual minimizers, the Fourier reciprocal-mode solve
has minimum Euclidean norm. The hypothesis is the usual least-squares property,
with no normal-equation certificate supplied by the caller.
Source: Meyer §5.5.
atlas: circulant-fourier-pseudoinverse (partial) -/
theorem fourierCirculantSolve_minimum_norm (c b x : ZMod n → ℂ)
    (hx : ∀ y : ZMod n → ℂ,
      ‖WithLp.toLp 2 (b - Matrix.circulant c *ᵥ x)‖ ≤
        ‖WithLp.toLp 2 (b - Matrix.circulant c *ᵥ y)‖) :
    ‖WithLp.toLp 2 (fourierCirculantSolve c b)‖ ≤ ‖WithLp.toLp 2 x‖ := by
  have hfit := circulant_fit_modes_of_residual_le_optimal c b x (hx _)
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← norm_fourierUnitary_mulVec (fourierCirculantSolve c b),
    ← norm_fourierUnitary_mulVec x, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq, fourierUnitary_fourierCirculantSolve]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : ZMod.dft c j = 0
  · simp [hj]
  · rw [PiLp.toLp_apply, PiLp.toLp_apply, hfit j hj]

/-- When every mode is nonzero the Fourier solve is the unique exact solution.
Source: Meyer §5.5.
atlas: circulant-fourier-pseudoinverse (partial) -/
theorem circulant_mulVec_eq_iff_fourierCirculantSolve (c b x : ZMod n → ℂ)
    (hc : ∀ j, ZMod.dft c j ≠ 0) :
    Matrix.circulant c *ᵥ x = b ↔ x = fourierCirculantSolve c b := by
  have hsolve : Matrix.circulant c *ᵥ fourierCirculantSolve c b = b := by
    apply ZMod.dft.injective
    rw [dft_circulant_mulVec]
    simp only [fourierCirculantSolve, LinearEquiv.apply_symm_apply]
    funext j
    rw [← mul_assoc, mul_inv_cancel₀ (hc j), one_mul]
  constructor
  · intro hx
    exact Matrix.mulVec_injective_of_isUnit ((isUnit_circulant_iff_dft_ne_zero c).mpr hc)
      (hx.trans hsolve.symm)
  · rintro rfl
    exact hsolve

end NLAlib
