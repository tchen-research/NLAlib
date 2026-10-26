import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import NLAlib.ForMathlib.Analysis.SpecialFunctions.LogDefectSum
import NLAlib.Matrix.Norms.Frobenius

/-!
# Determinant-to-balance certificate

A real or complex positive definite matrix with trace equal to its dimension
and determinant at least `exp (-eps)`, where `eps ≤ 1 / 6`, satisfies
`frobSq (A - 1) ≤ 6 * eps`.

The proof applies the scalar logarithmic-defect certificate to the eigenvalues.
It includes empty matrices and `eps = 0`. This is a quantitative spectral
certificate; the existence of approximately balancing operator scalings and
capacity tensor multiplicativity are separate results.
-/

noncomputable section

open scoped BigOperators ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- A positive definite matrix with trace equal to its dimension and determinant
at least `exp (-eps)`, for `eps ≤ 1 / 6`, has squared Frobenius distance from
the identity at most `6 * eps`. The trace and determinant are real; their real
parts express the statement uniformly over `ℝ` and `ℂ`. -/
theorem _root_.Matrix.PosDef.frobSq_sub_one_le_six_mul_of_exp_neg_le_det
    {A : Matrix n n 𝕜} (hA : A.PosDef) (eps : ℝ)
    (htr : RCLike.re A.trace = (Fintype.card n : ℝ))
    (heps : eps ≤ 1 / 6) (hdet : Real.exp (-eps) ≤ RCLike.re A.det) :
    frobSq (A - 1) ≤ 6 * eps := by
  let eig : n → ℝ := hA.isHermitian.eigenvalues
  have heig_pos : ∀ i, 0 < eig i := hA.eigenvalues_pos
  have htr_sum : ∑ i, eig i = (Fintype.card n : ℝ) := by
    have hre : RCLike.re A.trace = ∑ i, eig i := by
      rw [hA.isHermitian.trace_eq_sum_eigenvalues]
      simp [eig]
    rwa [hre] at htr
  have hdet_prod : RCLike.re A.det = ∏ i, eig i := by
    rw [hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod,
      RCLike.ofReal_re]
  have hscalar := Real.sum_sq_sub_one_le_six_mul_of_exp_neg_le_prod
    eig eps heig_pos htr_sum heps (hdet_prod ▸ hdet)
  have hsum : (∑ i, (eig i - 1) ^ 2) =
      (∑ i, eig i ^ 2) - 2 * (∑ i, eig i) + (Fintype.card n : ℝ) := by
    calc
      (∑ i, (eig i - 1) ^ 2) = ∑ i, (eig i ^ 2 - 2 * eig i + 1) :=
        Finset.sum_congr rfl fun i _ => by ring
      _ = (∑ i, eig i ^ 2) - 2 * (∑ i, eig i) + (Fintype.card n : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp
  have hA2 : frobSq A = ∑ i, eig i ^ 2 := by
    rw [frobSq_eq_re_trace_conjTranspose_mul_self, hA.isHermitian.eq, ← pow_two]
    conv_lhs => rw [hA.isHermitian.spectral_theorem, ← map_pow]
    rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, one_mul, Matrix.diagonal_pow, Matrix.trace_diagonal]
    simp [eig]
  have htr1 : frobInner A (1 : Matrix n n 𝕜) = (Fintype.card n : ℝ) := by
    rw [frobInner_eq_trace, Matrix.mul_one, hA.isHermitian.eq]
    exact htr
  have h1 : frobSq (1 : Matrix n n 𝕜) = (Fintype.card n : ℝ) := by
    simpa only [frobNorm_sq] using (frobNorm_one_sq (n := n) (𝕜 := 𝕜))
  calc
    frobSq (A - 1) = (∑ i, eig i ^ 2) -
        2 * (Fintype.card n : ℝ) + (Fintype.card n : ℝ) := by
      rw [frobSq_sub, hA2, htr1, h1]
    _ = ∑ i, (eig i - 1) ^ 2 := by rw [hsum, htr_sum]
    _ ≤ 6 * eps := hscalar

end NLAlib
