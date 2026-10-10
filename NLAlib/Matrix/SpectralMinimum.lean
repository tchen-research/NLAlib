import NLAlib.Matrix.Spectral
import NLAlib.Matrix.GramSoftMinSpectral
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-!
# Identifying the Rayleigh minimum from a diagonalization

Finite deterministic helpers identify the spectral minimum used by NLAlib
with a smallest diagonal eigenvalue. These connect inverse-power limits to
the exact smallest-singular-value vocabulary of the Gaussian theorems.

Atlas: wishart-lambda-min-tail and norm-lipschitz.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A unit eigenvector and positivity above its eigenvalue identify the
Rayleigh minimum. Source: the finite spectral variational principle;
atlas norm-lipschitz and wishart-lambda-min-tail (operator bridge). -/
theorem lamMin_eq_of_unit_eigenvector_of_posSemidef_sub {A : Matrix ι ι ℝ}
    {a : ℝ} (hpos : (A - a • 1).PosSemidef) (v : ι → ℝ)
    (hv : v ⬝ᵥ v = 1) (heig : A *ᵥ v = a • v) : lamMin A = a := by
  have hu : Nonempty {x : ι → ℝ // x ⬝ᵥ x = 1} := ⟨⟨v, hv⟩⟩
  apply le_antisymm
  · have h := lamMin_le A hv
    simpa only [heig, dotProduct_smul, smul_eq_mul, hv, mul_one] using h
  · unfold lamMin
    apply le_ciInf
    intro x
    have hp := hpos.dotProduct_mulVec_nonneg x.val
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul, x.property,
      mul_one] at hp
    linarith

/-- The minimum of an orthogonally diagonalized real matrix is the smallest
diagonal entry. Source: Rayleigh minimum and finite diagonal positivity;
atlas wishart-lambda-min-tail and norm-lipschitz (operator bridge). -/
theorem lamMin_eq_of_orthogonal_diagonalization
    (A U : Matrix ι ι ℝ) (hU : Uᵀ * U = 1) (l : ι → ℝ)
    (hdiag : Uᵀ * A * U = Matrix.diagonal l) (i₀ : ι)
    (hmin : ∀ i, l i₀ ≤ l i) : lamMin A = l i₀ := by
  have hU' : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have hA : A = U * Matrix.diagonal l * Uᵀ := by
    rw [← hdiag]
    simp only [← Matrix.mul_assoc, hU', Matrix.one_mul]
    rw [Matrix.mul_assoc A U Uᵀ, hU']
    simp
  have hdif : Matrix.diagonal (fun i => l i - l i₀) =
      Matrix.diagonal l - l i₀ • (1 : Matrix ι ι ℝ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  have hpd : (Matrix.diagonal (fun i => l i - l i₀)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr fun i => sub_nonneg.mpr (hmin i)
  have hpos := hpd.mul_mul_conjTranspose_same U
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, hdif, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU'] at hpos
  rw [← hA] at hpos
  let e : ι → ℝ := Pi.single i₀ 1
  let v : ι → ℝ := U *ᵥ e
  have hv : v ⬝ᵥ v = 1 := by
    dsimp [v]
    rw [← dotProduct_transpose_mul_mulVec, hU, Matrix.one_mulVec]
    simp [e, dotProduct, Pi.single_apply]
  have heig : A *ᵥ v = l i₀ • v := by
    rw [hA]
    dsimp [v]
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mul_assoc, hU, Matrix.mul_one]
    rw [← Matrix.mulVec_mulVec]
    simp [e]
  exact lamMin_eq_of_unit_eigenvector_of_posSemidef_sub hpos v hv heig

/-- The maximal inverse regularized-Gram eigenvalue identifies the unregularized
smallest singular value exactly. Source: orthogonal diagonalization and the
Rayleigh minimum; atlas wishart-lambda-min-tail (operator limit bridge). -/
theorem sigmaMin_transpose_sq_eq_inv_inverse_eigenvalue_sub
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ε : ℝ) (G : Matrix ι κ ℝ) (hpd : (regularizedGram ε G).PosDef) (i₀ : ι)
    (hmax : ∀ i, hpd.inv.isHermitian.eigenvalues i ≤
      hpd.inv.isHermitian.eigenvalues i₀) :
    sigmaMin Gᵀ ^ 2 = (hpd.inv.isHermitian.eigenvalues i₀)⁻¹ - ε := by
  let hR := hpd.inv.isHermitian
  let U : Matrix ι ι ℝ := hR.eigenvectorUnitary
  let b := hR.eigenvalues
  have hU : Uᵀ * U = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hR.eigenvectorUnitary
  have hdiag : Uᵀ * (G * Gᵀ) * U =
      Matrix.diagonal (fun i => (b i)⁻¹ - ε) := by
    have h := regularizedGram_inv_basis_conj_eq ε G hpd
    simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_transpose,
      U, hR, b] using h
  have hmin : ∀ i, (b i₀)⁻¹ - ε ≤ (b i)⁻¹ - ε := by
    intro i
    have hbi : 0 < b i := hpd.inv.eigenvalues_pos i
    have h := one_div_le_one_div_of_le hbi (hmax i)
    simpa only [one_div] using sub_le_sub_right h ε
  rw [sigmaMin_transpose_sq]
  exact lamMin_eq_of_orthogonal_diagonalization (G * Gᵀ) U hU
    (fun i => (b i)⁻¹ - ε) hdiag i₀ hmin

/-- The squared smallest singular value of the transposed rectangular matrix
is bounded by its squared Frobenius size. Source: spectral versus Frobenius
norm comparison; atlas wishart-lambda-min-tail (dominated limit helper). -/
theorem sigmaMin_transpose_sq_le_frobSq {κ : Type*} [Fintype κ] [DecidableEq κ]
    [Nonempty ι] (G : Matrix ι κ ℝ) : sigmaMin Gᵀ ^ 2 ≤ frobSq G := by
  have h : sigmaMin Gᵀ ≤ frobNorm G := calc
    _ ≤ specNorm Gᵀ := sigmaMin_le_specNorm Gᵀ
    _ = specNorm G := specNorm_transpose G
    _ ≤ frobNorm G := specNorm_le_frobNorm G
  simpa only [frobNorm_sq] using pow_le_pow_left₀ (sigmaMin_nonneg Gᵀ) h 2

end NLAlib
