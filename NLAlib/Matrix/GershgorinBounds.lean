import NLAlib.Matrix.GershgorinBasic
import NLAlib.Matrix.EigenvectorDeflationBlocks
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Row, column and weighted Gershgorin spectral-radius bounds

The suprema are in the nonnegative reals, so the empty maximum is zero.
Positive real weights are handled by an actual diagonal similarity.
Source: Horn–Johnson (2013), Corollaries 6.1.3 and 6.1.5.
-/

noncomputable section
open scoped Matrix NNReal

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A spectral point's modulus is bounded by one complete absolute row sum.
Source: Horn–Johnson (2013), Corollary 6.1.5; the diagonal contribution is
added to the closed-disc radius. -/
theorem exists_norm_le_row_sum_of_mem_spectrum {A : Matrix n n ℂ} {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ A) : ∃ i, ‖μ‖ ≤ ∑ j, ‖A i j‖ := by
  obtain ⟨i, hi⟩ := exists_mem_gershgorinRowDisc_of_mem_spectrum hμ
  have hnorm : ‖μ - A i i‖ ≤ gershgorinRowRadius A i := by
    simpa only [gershgorinRowDisc, Metric.mem_closedBall, dist_eq_norm] using hi
  refine ⟨i, ?_⟩
  calc
    ‖μ‖ = ‖(μ - A i i) + A i i‖ := by rw [sub_add_cancel]
    _ ≤ ‖μ - A i i‖ + ‖A i i‖ := norm_add_le _ _
    _ ≤ gershgorinRowRadius A i + ‖A i i‖ := add_le_add hnorm le_rfl
    _ = ∑ j, ‖A i j‖ := Finset.sum_erase_add _ _ (Finset.mem_univ i)

/-- The complex spectral radius is bounded by the maximum absolute row sum.
Source: Horn–Johnson (2013), Corollary 6.1.5; `toNNReal` preserves the
nonnegative sums, and the finite supremum is zero for an empty shape.
atlas: gershgorin-diagonal-dominance (partial) -/
theorem spectralRadius_le_max_row_sum (A : Matrix n n ℂ) :
    spectralRadius ℂ A ≤
      (Finset.univ.sup (fun i => Real.toNNReal (∑ j, ‖A i j‖)) : ENNReal) := by
  apply iSup₂_le
  intro μ hμ
  obtain ⟨i, hi⟩ := exists_norm_le_row_sum_of_mem_spectrum hμ
  have hn : ‖μ‖₊ ≤ Real.toNNReal (∑ j, ‖A i j‖) := by
    simpa only [norm_toNNReal] using Real.toNNReal_mono hi
  exact_mod_cast hn.trans (Finset.le_sup
    (f := fun i : n => Real.toNNReal (∑ j, ‖A i j‖)) (Finset.mem_univ i))

/-- The complex spectral radius is bounded by the maximum absolute column
sum. Source: Horn–Johnson (2013), Corollary 6.1.5; transpose preserves the
characteristic polynomial, and the empty maximum is zero.
atlas: gershgorin-diagonal-dominance (partial) -/
theorem spectralRadius_le_max_column_sum (A : Matrix n n ℂ) :
    spectralRadius ℂ A ≤
      (Finset.univ.sup (fun j => Real.toNNReal (∑ i, ‖A i j‖)) : ENNReal) := by
  have hspec : spectrum ℂ Aᵀ = spectrum ℂ A := by
    ext μ
    simp only [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_transpose]
  have h := spectralRadius_le_max_row_sum Aᵀ
  simpa only [spectralRadius, hspec, Matrix.transpose_apply] using h

/-- The spectral radius is bounded by the smaller of the maximum absolute
row and column sums. Source: Horn–Johnson (2013), Corollary 6.1.5;
the finite nonnegative suprema include dimension zero.
atlas: gershgorin-diagonal-dominance (partial) -/
theorem spectralRadius_le_min_max_row_column_sum (A : Matrix n n ℂ) :
    spectralRadius ℂ A ≤ min
      (Finset.univ.sup (fun i => Real.toNNReal (∑ j, ‖A i j‖)) : ENNReal)
      (Finset.univ.sup (fun j => Real.toNNReal (∑ i, ‖A i j‖)) : ENNReal) :=
  le_min (spectralRadius_le_max_row_sum A) (spectralRadius_le_max_column_sum A)

/-- Positive real diagonal weights give the maximum weighted absolute row
sum bound on spectral radius. Source: Horn–Johnson (2013), Corollary 6.1.5;
the right side is `max_i p_i⁻¹ ∑_j p_j |a_ij|`, with empty maximum zero.
atlas: gershgorin-diagonal-dominance (partial) -/
theorem spectralRadius_le_max_weighted_row_sum
    (A : Matrix n n ℂ) (p : n → ℝ) (hp : ∀ i, 0 < p i) :
    spectralRadius ℂ A ≤
      (Finset.univ.sup (fun i => Real.toNNReal ((p i)⁻¹ * ∑ j, p j * ‖A i j‖)) : ENNReal) := by
  let D : Matrix n n ℂ := Matrix.diagonal (fun i => (p i : ℂ))
  let H : Matrix n n ℂ := Matrix.diagonal (fun i => (p i : ℂ)⁻¹)
  have hpi (i : n) : (p i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hp i).ne'
  have hHD : H * D = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [inv_mul_cancel₀ (hpi _), Matrix.diagonal_one]
  have hD : IsUnit D := (Matrix.isUnit_iff_isUnit_det D).mpr (Matrix.isUnit_det_of_left_inverse hHD)
  have hInv : D⁻¹ = H := Matrix.inv_eq_left_inv hHD
  have hentry (i j : n) : ‖(D⁻¹ * A * D) i j‖ = (p i)⁻¹ * ‖A i j‖ * p j := by
    rw [hInv]
    dsimp only [H, D]
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, norm_mul, norm_mul, norm_inv]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hp i), abs_of_pos (hp j)]
  have hrow (i : n) : (∑ j, ‖(D⁻¹ * A * D) i j‖) = (p i)⁻¹ * ∑ j, p j * ‖A i j‖ := by
    simp only [hentry, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  apply iSup₂_le
  intro μ hμ
  have hμD := (mem_spectrum_nonsing_inv_mul_mul_iff A D hD μ).mpr hμ
  obtain ⟨i, hi⟩ := exists_norm_le_row_sum_of_mem_spectrum hμD
  rw [hrow] at hi
  have hn : ‖μ‖₊ ≤ Real.toNNReal ((p i)⁻¹ * ∑ j, p j * ‖A i j‖) := by
    simpa only [norm_toNNReal] using Real.toNNReal_mono hi
  exact_mod_cast hn.trans (Finset.le_sup
    (f := fun i : n => Real.toNNReal ((p i)⁻¹ * ∑ j, p j * ‖A i j‖)) (Finset.mem_univ i))

end NLAlib
