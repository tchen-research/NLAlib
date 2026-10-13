import NLAlib.Matrix.Inequalities.RelativeSpectrum
/-!
# Strict relative-spectrum bounds

The finite relative spectrum detects strict positive definiteness of
a Schur complement. Source: Horn--Johnson (2013), Theorem 7.7.7;
supports `psd-block-contraction`.
-/

noncomputable section
open Matrix
open scoped MatrixOrder
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A finite real spectral list has spectral radius equal to its supremum
absolute norm, including the empty list. Horn--Johnson (2013), Section 1.1;
helper for strict relative-spectrum bounds. -/
theorem spectralRadius_eq_nnnorm_of_spectrum_eq_range {A : Matrix n n ℝ}
    {d : n → ℝ} (h : spectrum ℝ A = Set.range d) :
    spectralRadius ℝ A = (‖d‖₊ : ENNReal) := by
  rw [spectralRadius, h, Pi.nnnorm_def, Finset.sup_univ_eq_ciSup,
    ENNReal.coe_iSup (Set.finite_range (fun i => ‖d i‖₊)).bddAbove]
  simp only [Set.mem_range, iSup_exists]
  rw [iSup_comm]
  simp

/-- For a positive definite `A` and PSD `B`, positive definiteness of `A-B`
is equivalent to relative spectral radius strictly below one. Empty spaces
satisfy both sides. Horn--Johnson (2013), Theorem 7.7.7;
helper for PSD-block strict tests. -/
theorem posDef_sub_iff_relative_spectralRadius_lt_one {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.PosSemidef) :
    (A - B).PosDef ↔ spectralRadius ℝ (A⁻¹ * B) < 1 := by
  obtain ⟨S, d, hS, hAA, hBB, hd⟩ := exists_definite_pair_congruence_diagonal hA hB.isHermitian
  have hdiff : A - B = S * diagonal (fun i => 1 - d i) * Sᵀ := by
    calc
      A - B = S * 1 * Sᵀ - S * diagonal d * Sᵀ := by rw [Matrix.mul_one, ← hAA, ← hBB]
      _ = S * (1 - diagonal d) * Sᵀ := by rw [Matrix.mul_sub, Matrix.sub_mul]
      _ = S * diagonal (fun i => 1 - d i) * Sᵀ := by rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
  rw [hdiff]
  have hp : (S * diagonal (fun i => 1 - d i) * Sᵀ).PosDef ↔
      ∀ i, d i < 1 := by
    rw [show Sᵀ = star S from rfl, hS.posDef_star_right_conjugate_iff, Matrix.posDef_diagonal_iff]
    simp only [sub_pos]
  rw [hp, spectralRadius_eq_nnnorm_of_spectrum_eq_range
    (spectrum_inverse_mul_eq_range_of_congruence hS hAA hBB)]
  rw [show (1 : ENNReal) = ((1 : NNReal) : ENNReal) from rfl, ENNReal.coe_lt_coe,
    ← NNReal.coe_lt_coe]
  change (∀ i, d i < 1) ↔ ‖d‖ < (1 : ℝ)
  rw [pi_norm_lt_iff zero_lt_one]
  simp only [Real.norm_eq_abs, abs_of_nonneg (hd hB _)]

/-- The spectral radius of a real PSD matrix is its spectral norm.
Horn--Johnson (2013), Section 5.6; helper for PSD-block strict tests. -/
theorem spectralRadius_eq_specNorm_of_posSemidef {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    spectralRadius ℝ A = ENNReal.ofReal (specNorm A) := by
  rw [spectralRadius_eq_nnnorm_of_spectrum_eq_range hA.isHermitian.spectrum_real_eq_range_eigenvalues]
  have hn : specNorm A = ‖hA.isHermitian.eigenvalues‖ := by
    calc
      specNorm A = specNorm ((hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ) *
          diagonal hA.isHermitian.eigenvalues *
          (hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)ᵀ) :=
        congrArg specNorm (eq_eigenvectorUnitary_mul_diagonal_mul_transpose hA.isHermitian)
      _ = ‖hA.isHermitian.eigenvalues‖ := by
        rw [← Matrix.conjTranspose_eq_transpose_of_trivial,
          specNorm_mul_conjTranspose_right_of_hasOrthonormalCols
          (transpose_eigenvectorUnitary_mul_self hA.isHermitian),
          specNorm_mul_left_of_hasOrthonormalCols (transpose_eigenvectorUnitary_mul_self hA.isHermitian),
          specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
  rw [hn]
  exact ENNReal.ofReal_coe_nnreal.symm

/-- The complement of a PSD real matrix is positive definite exactly when
its spectral norm is strictly below one. Horn--Johnson (2013), Lemma 7.7.6;
helper for strict block contractions. -/
theorem posDef_one_sub_iff_specNorm_lt_one_of_posSemidef {A : Matrix n n ℝ}
    (hA : A.PosSemidef) : (1 - A).PosDef ↔ specNorm A < 1 := by
  rw [posDef_sub_iff_relative_spectralRadius_lt_one Matrix.PosDef.one hA, inv_one,
    Matrix.one_mul, spectralRadius_eq_specNorm_of_posSemidef hA]
  rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff zero_lt_one]

end NLAlib
