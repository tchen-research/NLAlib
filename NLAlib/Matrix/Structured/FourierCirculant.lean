import NLAlib.Matrix.Spectral.DiagonalSingularValues
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.LinearAlgebra.Matrix.Circulant
import NLAlib.Matrix.Basic.MoorePenroseTransformations
import NLAlib.Matrix.Perturbation.ConditionNumber
import NLAlib.Matrix.Spectral.SingularValueInvariance

/-! # Fourier diagonalization of circulant matrices

The matrix of Mathlib's unnormalized negative-exponent `ZMod.dft` becomes
unitary after division by the square root of the dimension. It diagonalizes
Mathlib's `Matrix.circulant`, including repeated and zero Fourier modes.
Source: Meyer, Matrix Analysis and Applied Linear Algebra, §5.5.
-/

noncomputable section
open Matrix Finset
open scoped Matrix

namespace NLAlib

variable {n : ℕ} [NeZero n]

/-- The matrix of Mathlib's unnormalized negative-exponent finite Fourier transform. -/
def fourierMatrix (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  fun i j => ZMod.stdAddChar (-(j * i))

/-- Multiplication by the Fourier matrix is exactly Mathlib's discrete Fourier transform. -/
theorem fourierMatrix_mulVec (x : ZMod n → ℂ) : fourierMatrix n *ᵥ x = ZMod.dft x := by
  ext i
  simp only [fourierMatrix, Matrix.mulVec, dotProduct, ZMod.dft_apply, smul_eq_mul]

/-- Conjugating a standard Fourier character reverses its sign. -/
theorem star_stdAddChar (i : ZMod n) : star (ZMod.stdAddChar i) = ZMod.stdAddChar (-i) := by
  have h := (ZMod.toCircle (N := n)).map_neg_eq_inv i
  simpa only [ZMod.stdAddChar_apply, Circle.coe_inv_eq_conj, Complex.star_def] using
    congrArg (fun z : Circle => (z : ℂ)) h.symm

/-- Orthogonality of the finite characters, including the one-dimensional case. -/
theorem sum_stdAddChar_mul (a : ZMod n) :
    (∑ i : ZMod n, ZMod.stdAddChar (a * i)) = if a = 0 then (n : ℂ) else 0 := by
  split_ifs with ha
  · simp [ha, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar n ha)

/-- The unnormalized Fourier matrix has Gram matrix `n I`. -/
theorem fourierMatrix_mul_conjTranspose :
    fourierMatrix n * (fourierMatrix n)ᴴ = (n : ℂ) • (1 : Matrix (ZMod n) (ZMod n) ℂ) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, fourierMatrix,
    star_stdAddChar, neg_neg, ← AddChar.map_add_eq_mul]
  have he (k : ZMod n) : -(k * i) + k * j = (j - i) * k := by ring
  simp_rw [he]
  rw [sum_stdAddChar_mul]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    sub_eq_zero, eq_comm]

/-- The normalized Fourier matrix, with normalization `1/√n`. -/
def fourierUnitary (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  ((Real.sqrt (n : ℝ) : ℂ)⁻¹) • fourierMatrix n

/-- The normalized Fourier matrix is unitary.
Source: Meyer §5.5, character orthogonality.
atlas: circulant-fourier-diagonalization (partial) -/
theorem fourierUnitary_mem_unitaryGroup : fourierUnitary n ∈ Matrix.unitaryGroup (ZMod n) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change fourierUnitary n * (fourierUnitary n)ᴴ = 1
  have he : (Real.sqrt (n : ℝ) : ℂ) ^ 2 = n := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg n)
  rw [fourierUnitary, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    fourierMatrix_mul_conjTranspose, smul_smul, smul_smul]
  simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hc : ((Real.sqrt (n : ℝ) : ℂ)⁻¹ * (Real.sqrt (n : ℝ) : ℂ)⁻¹) * n = 1 := by
    rw [← mul_inv, ← pow_two, he, inv_mul_cancel₀ (by exact_mod_cast NeZero.ne n)]
  rw [hc, one_smul]

/-- Left multiplication by the Fourier matrix diagonalizes circulant convolution. -/
theorem fourierMatrix_mul_circulant (c : ZMod n → ℂ) :
    fourierMatrix n * Matrix.circulant c = Matrix.diagonal (ZMod.dft c) * fourierMatrix n := by
  ext i j
  rw [Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, fourierMatrix, Matrix.circulant_apply,
    ZMod.dft_apply, smul_eq_mul, sum_mul]
  refine Fintype.sum_equiv (Equiv.subRight j) _ _ ?_
  intro k
  simp only [Equiv.subRight_apply]
  calc
    _ = (ZMod.stdAddChar (-((k - j) * i)) * ZMod.stdAddChar (-(j * i))) * c (k - j) := by
      congr 1
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = _ := by ring

/-- Fourier diagonalization of every circulant, with the unnormalized transform as diagonal.
Source: Meyer §5.5, Exercise 5.5.22; the normalization is explicit.
atlas: circulant-fourier-diagonalization (partial) -/
theorem fourierUnitary_mul_circulant_mul_conjTranspose (c : ZMod n → ℂ) :
    fourierUnitary n * Matrix.circulant c * (fourierUnitary n)ᴴ = Matrix.diagonal (ZMod.dft c) := by
  have hu : fourierUnitary n * (fourierUnitary n)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (fourierUnitary_mem_unitaryGroup (n := n))
  have hcomm : fourierUnitary n * Matrix.circulant c =
      Matrix.diagonal (ZMod.dft c) * fourierUnitary n := by
    simp only [fourierUnitary, Matrix.smul_mul, Matrix.mul_smul, fourierMatrix_mul_circulant]
  rw [hcomm, Matrix.mul_assoc, hu, Matrix.mul_one]

/-- Fourier coordinates are an orthonormal coordinate system. -/
theorem fourierUnitary_hasOrthonormalCols : HasOrthonormalCols (fourierUnitary n) := by
  exact Matrix.mem_unitaryGroup_iff'.mp (fourierUnitary_mem_unitaryGroup (n := n))

/-- Reconstruction of a circulant from its Fourier multipliers. -/
theorem circulant_eq_fourierUnitary_conjTranspose_mul_diagonal (c : ZMod n → ℂ) :
    Matrix.circulant c = (fourierUnitary n)ᴴ * Matrix.diagonal (ZMod.dft c) * fourierUnitary n := by
  have h := fourierUnitary_mul_circulant_mul_conjTranspose c
  have hu := fourierUnitary_hasOrthonormalCols (n := n)
  calc
    Matrix.circulant c = (fourierUnitary n)ᴴ *
        (fourierUnitary n * Matrix.circulant c * (fourierUnitary n)ᴴ) * fourierUnitary n := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (fourierUnitary n)ᴴ (fourierUnitary n),
        hu.conjTranspose_mul_self, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by rw [h]

open scoped Matrix.Norms.L2Operator in
/-- The spectral norm of a circulant is the largest modulus of its Fourier modes.
The function norm is the finite maximum, including `n = 1`.
Source: Meyer §5.5.
atlas: circulant-fourier-diagonalization (partial) -/
theorem specNorm_circulant_eq_norm_dft (c : ZMod n → ℂ) :
    specNorm (Matrix.circulant c) = ‖ZMod.dft c‖ := by
  rw [circulant_eq_fourierUnitary_conjTranspose_mul_diagonal]
  have hr := specNorm_mul_conjTranspose_right_of_hasOrthonormalCols
      (fourierUnitary_hasOrthonormalCols (n := n)).conjTranspose
      ((fourierUnitary n)ᴴ * Matrix.diagonal (ZMod.dft c))
  simp only [Matrix.conjTranspose_conjTranspose] at hr
  rw [hr,
    specNorm_mul_left_of_hasOrthonormalCols
      (fourierUnitary_hasOrthonormalCols (n := n)).conjTranspose,
    specNorm_eq_norm, Matrix.l2_opNorm_diagonal]

/-- A circulant is invertible precisely when no Fourier mode vanishes.
Source: Meyer §5.5.
atlas: circulant-fourier-diagonalization (partial) -/
theorem isUnit_circulant_iff_dft_ne_zero (c : ZMod n → ℂ) :
    IsUnit (Matrix.circulant c) ↔ ∀ i, ZMod.dft c i ≠ 0 := by
  have hu := (fourierUnitary_hasOrthonormalCols (n := n)).isUnit
  have hut := (fourierUnitary_hasOrthonormalCols (n := n)).conjTranspose.isUnit
  constructor
  · intro hc i
    have hd : IsUnit (Matrix.diagonal (ZMod.dft c)) := by
      rw [← fourierUnitary_mul_circulant_mul_conjTranspose]
      exact (hu.mul hc).mul hut
    exact ((Matrix.isUnit_diagonal.mp hd).apply i).ne_zero
  · intro hc
    rw [circulant_eq_fourierUnitary_conjTranspose_mul_diagonal]
    exact (hut.mul (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr
      (fun i => isUnit_iff_ne_zero.mpr (hc i))))).mul hu

/-- Scalar reciprocal modes satisfy the four Penrose identities, even at zero modes. -/
theorem isMoorePenroseInverse_diagonal_reciprocal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℂ) : IsMoorePenroseInverse (Matrix.diagonal d) (Matrix.diagonal (fun i => (d i)⁻¹)) := by
  constructor
  · simp only [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : d i = 0 <;> simp [hi]
  · simp only [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : d i = 0 <;> simp [hi]
  · simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    by_cases hi : d i = 0 <;> simp [hi]
  · simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    by_cases hi : d i = 0 <;> simp [hi]

/-- The Moore–Penrose inverse in Fourier coordinates is the reciprocal multiplier,
with the total field inverse assigning zero at zero modes.
Source: Meyer §5.5.
atlas: circulant-fourier-pseudoinverse (partial) -/
theorem moorePenroseInverse_circulant_eq_fourier (c : ZMod n → ℂ) :
    moorePenroseInverse (Matrix.circulant c) = (fourierUnitary n)ᴴ *
      Matrix.diagonal (fun i => (ZMod.dft c i)⁻¹) * fourierUnitary n := by
  have hu := (fourierUnitary_hasOrthonormalCols (n := n)).conjTranspose
  have h := (isMoorePenroseInverse_diagonal_reciprocal (ZMod.dft c)).unitary_transform
    (fourierUnitary n)ᴴ (fourierUnitary n)ᴴ hu hu
  simp only [Matrix.conjTranspose_conjTranspose] at h
  rw [← circulant_eq_fourierUnitary_conjTranspose_mul_diagonal] at h
  exact (isMoorePenroseInverse (Matrix.circulant c)).unique h

/-- Inverse Fourier transformation of reciprocal modes produces the pseudoinverse column.
Source: Meyer §5.5.
atlas: circulant-fourier-pseudoinverse (partial) -/
theorem moorePenroseInverse_circulant (c : ZMod n → ℂ) :
    moorePenroseInverse (Matrix.circulant c) =
      Matrix.circulant (ZMod.dft.symm (fun i => (ZMod.dft c i)⁻¹)) := by
  rw [moorePenroseInverse_circulant_eq_fourier,
    circulant_eq_fourierUnitary_conjTranspose_mul_diagonal]
  simp only [LinearEquiv.apply_symm_apply]

open scoped Matrix.Norms.L2Operator in
/-- The finite spectral condition number is the largest Fourier modulus times
the largest reciprocal modulus; equivalently, the maximum-to-minimum ratio.
Source: Meyer §5.5.
atlas: circulant-fourier-diagonalization (partial) -/
theorem conditionNumber_circulant_of_dft_ne_zero (c : ZMod n → ℂ)
    (hc : ∀ i, ZMod.dft c i ≠ 0) :
    conditionNumber (Matrix.circulant c) =
      ENNReal.ofReal (‖ZMod.dft c‖ * ‖fun i => (ZMod.dft c i)⁻¹‖) := by
  have hC := (isUnit_circulant_iff_dft_ne_zero c).mpr hc
  rw [conditionNumber_of_isUnit hC, ← moorePenroseInverse_eq_inv_of_isUnit _ hC,
    moorePenroseInverse_circulant, specNorm_circulant_eq_norm_dft,
    specNorm_circulant_eq_norm_dft, LinearEquiv.apply_symm_apply]

/-- The singular values of a circulant are precisely the moduli of its DFT,
as a multiset; repeated modes and all rank deficiencies are included.
Source: Meyer §5.5.
atlas: circulant-fourier-diagonalization (partial) -/
theorem multiset_singularValues_circulant (c : ZMod n → ℂ) :
    (Finset.univ : Finset (Fin (Fintype.card (ZMod n)))).val.map
      (fun i : Fin (Fintype.card (ZMod n)) => singularValues (Matrix.circulant c) (i : ℕ)) =
    (Finset.univ : Finset (ZMod n)).val.map (fun i => ‖ZMod.dft c i‖) := by
  have hs : singularValues (Matrix.circulant c) =
      singularValues (Matrix.diagonal (ZMod.dft c)) := by
    rw [circulant_eq_fourierUnitary_conjTranspose_mul_diagonal,
      singularValues_mul_unitary _ (fourierUnitary_hasOrthonormalCols (n := n)),
      singularValues_isometry_mul (fourierUnitary_hasOrthonormalCols (n := n)).conjTranspose]
  rw [hs]
  exact multiset_singularValues_diagonal_complex _

end NLAlib
