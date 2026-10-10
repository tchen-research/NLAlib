import NLAlib.Gaussian.Moments
import NLAlib.Matrix.Gram
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.Separable
import NLAlib.Matrix.GramSoftMinSpectral

/-!
# Almost-sure simple spectrum of a Gaussian Gram matrix

The characteristic polynomial and its derivative have nonzero resultant
almost surely. The resultant is a polynomial in the Gaussian entries, and
one rectangular diagonal matrix witnesses that this polynomial is nonzero.
No joint eigenvalue density is used.

Source: the generic polynomial-zero-set argument; operator hard-edge proof.
Atlas: `gaussian-simple-spectrum`, helper of `wishart-lambda-min-tail`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

private lemma eval_resultant_charpoly_self_mul_transpose (r k : ℕ)
    (G : Fin r → Fin k → ℝ) :
    MvPolynomial.eval (fun ab : Fin r × Fin k => G ab.1 ab.2)
      (Polynomial.resultant
        (Matrix.mvPolynomialX (Fin r) (Fin k) ℝ *
          (Matrix.mvPolynomialX (Fin r) (Fin k) ℝ)ᵀ).charpoly
        (Matrix.mvPolynomialX (Fin r) (Fin k) ℝ *
          (Matrix.mvPolynomialX (Fin r) (Fin k) ℝ)ᵀ).charpoly.derivative r (r - 1))
      = Polynomial.resultant (Matrix.of G * (Matrix.of G)ᵀ).charpoly
        (Matrix.of G * (Matrix.of G)ᵀ).charpoly.derivative r (r - 1) := by
  let ev : MvPolynomial (Fin r × Fin k) ℝ →+* ℝ :=
    MvPolynomial.eval fun ab : Fin r × Fin k => G ab.1 ab.2
  have hX : (Matrix.mvPolynomialX (Fin r) (Fin k) ℝ).map ev = Matrix.of G := by
    ext i j
    simp [ev]
  have hp : (Matrix.mvPolynomialX (Fin r) (Fin k) ℝ *
      (Matrix.mvPolynomialX (Fin r) (Fin k) ℝ)ᵀ).charpoly.map ev
      = (Matrix.of G * (Matrix.of G)ᵀ).charpoly := by
    rw [← Matrix.charpoly_map, Matrix.map_mul, Matrix.transpose_map, hX]
  change ev _ = _
  rw [← Polynomial.resultant_map_map, ← Polynomial.derivative_map, hp]

/-- A wide Gaussian Gram matrix has separable characteristic polynomial
almost surely. Source: nonzero resultant polynomial and Gaussian polynomial
zero sets; atlas `gaussian-simple-spectrum`. Includes the empty row dimension.
atlas: gaussian-simple-spectrum -/
theorem ae_charpoly_separable_self_mul_transpose_gaussianMatrix {r k : ℕ} (hrk : r ≤ k) :
    ∀ᵐ G ∂(gaussianMatrix r k), (Matrix.of G * (Matrix.of G)ᵀ).charpoly.Separable := by
  classical
  let P : Polynomial (MvPolynomial (Fin r × Fin k) ℝ) :=
    (Matrix.mvPolynomialX (Fin r) (Fin k) ℝ *
      (Matrix.mvPolynomialX (Fin r) (Fin k) ℝ)ᵀ).charpoly
  let f : MvPolynomial (Fin r × Fin k) ℝ :=
    Polynomial.resultant P P.derivative r (r - 1)
  have hf : f ≠ 0 := by
    let G0 : Fin r → Fin k → ℝ := fun i j =>
      if j = Fin.castLE hrk i then (i.val : ℝ) + 1 else 0
    let d : Fin r → ℝ := fun i => ((i.val : ℝ) + 1) ^ 2
    have hdiag : Matrix.of G0 * (Matrix.of G0)ᵀ = Matrix.diagonal d := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [G0, d, Matrix.mul_apply, sq]
      · simp [G0, d, Matrix.mul_apply, Fin.castLE_inj, hij, eq_comm]
    have hd : Function.Injective d := by
      intro i j hij
      apply Fin.ext
      have hi : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
      have hj : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
      have heq : (i.val : ℝ) = j.val := by
        dsimp [d] at hij
        nlinarith
      exact_mod_cast heq
    have hsep : (Matrix.diagonal d).charpoly.Separable := by
      rw [Matrix.charpoly_diagonal]
      exact Polynomial.separable_prod_X_sub_C_iff.2 hd
    have hres : Polynomial.resultant (Matrix.diagonal d).charpoly
        (Matrix.diagonal d).charpoly.derivative r (r - 1) ≠ 0 := by
      have hn : (Matrix.diagonal d).charpoly.natDegree = r := by simp
      have hnd : (Matrix.diagonal d).charpoly.derivative.natDegree = r - 1 := by
        rw [Polynomial.natDegree_derivative, hn]
      simpa only [hn, hnd] using
        Polynomial.resultant_ne_zero _ _ ((Polynomial.separable_def _).1 hsep)
    intro hzero
    have heval := eval_resultant_charpoly_self_mul_transpose r k G0
    change MvPolynomial.eval (fun ab : Fin r × Fin k => G0 ab.1 ab.2) f = _ at heval
    rw [hzero, map_zero, hdiag] at heval
    exact hres heval.symm
  filter_upwards [gaussianMatrix_ae_eval_ne_zero r k f hf] with G hG
  change MvPolynomial.eval (fun ab : Fin r × Fin k => G ab.1 ab.2)
    (Polynomial.resultant
      (Matrix.mvPolynomialX (Fin r) (Fin k) ℝ *
        (Matrix.mvPolynomialX (Fin r) (Fin k) ℝ)ᵀ).charpoly
      (Matrix.mvPolynomialX (Fin r) (Fin k) ℝ *
        (Matrix.mvPolynomialX (Fin r) (Fin k) ℝ)ᵀ).charpoly.derivative r (r - 1)) ≠ 0 at hG
  rw [eval_resultant_charpoly_self_mul_transpose] at hG
  have hn : (Matrix.of G * (Matrix.of G)ᵀ).charpoly.natDegree = r := by simp
  have hnd : (Matrix.of G * (Matrix.of G)ᵀ).charpoly.derivative.natDegree = r - 1 := by
    rw [Polynomial.natDegree_derivative, hn]
  have hG' : Polynomial.resultant (Matrix.of G * (Matrix.of G)ᵀ).charpoly
      (Matrix.of G * (Matrix.of G)ᵀ).charpoly.derivative ≠ 0 := by
    simpa only [hn, hnd] using hG
  apply (Polynomial.separable_def _).2
  exact (Polynomial.isUnit_resultant_iff_isCoprime (Matrix.charpoly_monic _)).1
    (isUnit_iff_ne_zero.mpr hG')

/-- The eigenvalues of a wide Gaussian Gram matrix are pairwise distinct
almost surely. Source: separable characteristic polynomial and the finite
spectral theorem; atlas `gaussian-simple-spectrum`. No density formula is used.
atlas: gaussian-simple-spectrum -/
theorem ae_injective_eigenvalues_self_mul_transpose_gaussianMatrix {r k : ℕ} (hrk : r ≤ k) :
    ∀ᵐ G ∂(gaussianMatrix r k), Function.Injective
      ((Matrix.posSemidef_self_mul_conjTranspose (Matrix.of G)).isHermitian.eigenvalues) := by
  filter_upwards [ae_charpoly_separable_self_mul_transpose_gaussianMatrix hrk] with G hG
  have hG' : (Matrix.of G * (Matrix.of G)ᴴ).charpoly.Separable := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hG
  rw [(Matrix.posSemidef_self_mul_conjTranspose (Matrix.of G)).isHermitian.charpoly_eq] at hG'
  intro i j hij
  apply (Polynomial.separable_prod_X_sub_C_iff.1 hG')
  simpa using hij

/-- The sorted eigenvalue list of a wide Gaussian Gram matrix is injective
almost surely. Source: simple characteristic polynomial and reindexing of
the Hermitian eigenvalues; atlas `gaussian-simple-spectrum`.
This is the sorted-list interface used by the soft minimum limit. -/
theorem ae_injective_eigenvalues₀_self_mul_transpose_gaussianMatrix {r k : ℕ} (hrk : r ≤ k) :
    ∀ᵐ G ∂(gaussianMatrix r k), Function.Injective
      ((Matrix.posSemidef_self_mul_conjTranspose (Matrix.of G)).isHermitian.eigenvalues₀) := by
  filter_upwards [ae_injective_eigenvalues_self_mul_transpose_gaussianMatrix hrk] with G hG
  let e : Fin (Fintype.card (Fin r)) ≃ Fin r :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  intro i j hij
  apply e.injective
  apply hG
  simpa only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply] using hij

/-- The inverse of a positively regularized wide Gaussian Gram matrix
has distinct eigenvalues almost surely. Source: polynomial simple spectrum
and simultaneous diagonalization of the inverse Gram matrix;
atlas `gaussian-simple-spectrum` (resolvent interface). -/
theorem ae_injective_eigenvalues_inv_regularizedGram_gaussianMatrix
    {r k : ℕ} (hrk : r ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ G ∂(gaussianMatrix r k), Function.Injective
      ((regularizedGram_posDef hε (Matrix.of G)).inv.isHermitian.eigenvalues) := by
  filter_upwards [ae_charpoly_separable_self_mul_transpose_gaussianMatrix hrk] with G hG
  let hpd := regularizedGram_posDef hε (Matrix.of G)
  let hR := hpd.inv.isHermitian
  let b := hR.eigenvalues
  let U := star hR.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ (Matrix (Fin r) (Fin r) ℝ) U
  have hdiag : φ (Matrix.of G * (Matrix.of G)ᵀ) =
      Matrix.diagonal (fun i => (b i)⁻¹ - ε) :=
    regularizedGram_inv_basis_conj_eq ε (Matrix.of G) hpd
  have hchar : (φ (Matrix.of G * (Matrix.of G)ᵀ)).charpoly =
      (Matrix.of G * (Matrix.of G)ᵀ).charpoly := by
    dsimp only [φ]
    rw [Unitary.conjStarAlgAut_apply, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      Unitary.coe_star_mul_self, Matrix.one_mul]
  have hsep : (Matrix.diagonal (fun i => (b i)⁻¹ - ε)).charpoly.Separable := by
    rw [← hdiag, hchar]
    exact hG
  rw [Matrix.charpoly_diagonal] at hsep
  have hinj := Polynomial.separable_prod_X_sub_C_iff.1 hsep
  intro i j hij
  change b i = b j at hij
  apply hinj
  change (b i)⁻¹ - ε = (b j)⁻¹ - ε
  rw [hij]

/-- Positive regularization supplies a unique maximal inverse eigenvalue
almost surely for every nonzero wide Gaussian row dimension. Source:
simple spectrum and attainment of the finite spectral maximum; atlas
`gaussian-simple-spectrum` (soft minimum limit interface). -/
theorem ae_exists_unique_max_eigenvalues_inv_regularizedGram_gaussianMatrix
    {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ G ∂(gaussianMatrix r k), ∃ i₀ : Fin r, ∀ i, i ≠ i₀ →
      (regularizedGram_posDef hε (Matrix.of G)).inv.isHermitian.eigenvalues i <
        (regularizedGram_posDef hε (Matrix.of G)).inv.isHermitian.eigenvalues i₀ := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  filter_upwards [ae_injective_eigenvalues_inv_regularizedGram_gaussianMatrix hrk ε hε]
    with G hG
  let hpd := regularizedGram_posDef hε (Matrix.of G)
  let b := hpd.inv.isHermitian.eigenvalues
  obtain ⟨i₀, hi₀⟩ := (IsGreatest.pi_norm b).1
  have hle (i : Fin r) : b i ≤ b i₀ := by
    have hn := norm_le_pi_norm b i
    change ‖b i₀‖ = ‖b‖ at hi₀
    rw [← hi₀] at hn
    have hb (j : Fin r) : 0 ≤ b j := (hpd.inv.eigenvalues_pos j).le
    rw [Real.norm_of_nonneg (hb i), Real.norm_of_nonneg (hb i₀)] at hn
    exact hn
  refine ⟨i₀, fun i hi => ?_⟩
  exact lt_of_le_of_ne (hle i) (fun h => hi (hG h))

end NLAlib
