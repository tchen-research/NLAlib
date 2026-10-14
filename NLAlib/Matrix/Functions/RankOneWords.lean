import NLAlib.ForMathlib.Analysis.WeightedPowerProducts
import NLAlib.Matrix.Functions.CFCQuadratic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Cyclic words with rank-one insertions

A cyclic word in powers of a symmetric matrix and a single rank-one
positive matrix reduces to a product of scalar spectral moments. Weighted
Chebyshev then keeps the rank-one direction in its trace bound.
Source: Khatri--Rao Embeddings and Approximation, Lemma `closed:lem:step`;
https://github.com/DiarHaidary/Results/blob/main/manuscripts/08-Khatri-Rao-Embeddings-and-Approximation/Khatri_Rao_Embeddings_and_Approximation_Focused.pdf
-/

noncomputable section

open Matrix
open scoped Matrix

namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Sandwiching a matrix by one real rank-one matrix gives its quadratic
form times that same rank-one matrix. -/
theorem vecMulVec_mul_mul_vecMulVec (y : ι → ℝ) (B : Matrix ι ι ℝ) :
    vecMulVec y y * B * vecMulVec y y =
      (y ⬝ᵥ (B *ᵥ y)) • vecMulVec y y := by
  rw [vecMulVec_mul, vecMulVec_mul_vecMulVec, vecMulVec_smul,
    ← dotProduct_mulVec]

/-- A positive natural power of a real rank-one matrix is the same
rank-one matrix times a power of its trace. -/
theorem vecMulVec_pow_succ (y : ι → ℝ) (p : ℕ) :
    vecMulVec y y ^ (p + 1) = (y ⬝ᵥ y) ^ p • vecMulVec y y := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [pow_succ, ih, smul_mul_assoc, vecMulVec_mul_vecMulVec, vecMulVec_smul,
      smul_smul, pow_succ]

/-- Pairing a rank-one power with a matrix gives its directional moment. -/
theorem trace_mul_vecMulVec_pow_succ (C : Matrix ι ι ℝ) (y : ι → ℝ) (p : ℕ) :
    (C * vecMulVec y y ^ (p + 1)).trace =
      (y ⬝ᵥ y) ^ p * (y ⬝ᵥ (C *ᵥ y)) := by
  rw [vecMulVec_pow_succ, Matrix.mul_smul, Matrix.trace_smul, mul_vecMulVec,
    trace_vecMulVec, smul_eq_mul]
  rw [dotProduct_comm (C *ᵥ y) y]

/-- Multiplying rank-one-separated factors after an initial rank-one
matrix contracts each factor to a scalar quadratic form. -/
theorem vecMulVec_mul_prod_map_mul_vecMulVec (y : ι → ℝ)
    (Bs : List (Matrix ι ι ℝ)) :
    vecMulVec y y * (Bs.map fun B => B * vecMulVec y y).prod =
      (Bs.map fun B => y ⬝ᵥ (B *ᵥ y)).prod • vecMulVec y y := by
  induction Bs with
  | nil => simp
  | cons B Bs ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, vecMulVec_mul_mul_vecMulVec,
      smul_mul_assoc, ih, smul_smul]

/-- The trace of a nonempty cyclic rank-one word is exactly the product
of its scalar quadratic forms. -/
theorem trace_prod_map_mul_vecMulVec (y : ι → ℝ)
    (Bs : List (Matrix ι ι ℝ)) (hne : Bs ≠ []) :
    (Bs.map fun B => B * vecMulVec y y).prod.trace =
      (Bs.map fun B => y ⬝ᵥ (B *ᵥ y)).prod := by
  cases Bs with
  | nil => exact (hne rfl).elim
  | cons B Bs =>
    simp only [List.map_cons, List.prod_cons]
    rw [Matrix.mul_assoc, vecMulVec_mul_prod_map_mul_vecMulVec,
      Matrix.mul_smul, Matrix.trace_smul, mul_vecMulVec, trace_vecMulVec,
      dotProduct_comm]
    exact mul_comm _ _

/-- Absolute quadratic forms of powers are bounded by the corresponding
moments of the absolute eigenvalues, retaining the test vector weights. -/
theorem abs_dotProduct_pow_mulVec_le_sum_abs_eigenvalues_pow
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (y : ι → ℝ) (k : ℕ) :
    |y ⬝ᵥ (A ^ k *ᵥ y)| ≤
      ∑ i, ((hA.eigenvectorBasis i : ι → ℝ) ⬝ᵥ y) ^ 2 * |hA.eigenvalues i| ^ k := by
  have he := dotProduct_cfc_mulVec_eq_sum hA (fun x => x ^ k) y
  rw [cfc_pow_id (ha := hA.isSelfAdjoint)] at he
  rw [he]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  simp only [abs_mul, abs_pow, sq_abs, mul_comm]
  exact le_rfl

/-- A nonempty cyclic word with real rank-one insertions is bounded by
one absolute spectral moment and a power of the rank-one trace.
This is the direction-preserving estimate for higher insertions in the
finite-moment Khatri--Rao covariance proof. -/
theorem abs_trace_prod_pow_mul_vecMulVec_le
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (y : ι → ℝ)
    (ks : List ℕ) (hne : ks ≠ []) :
    |(ks.map fun k => A ^ k * vecMulVec y y).prod.trace| ≤
      (y ⬝ᵥ y) ^ (ks.length - 1) *
        (y ⬝ᵥ (cfc (fun x : ℝ => |x| ^ ks.sum) A *ᵥ y)) := by
  let w (i : ι) := ((hA.eigenvectorBasis i : ι → ℝ) ⬝ᵥ y) ^ 2
  have hw (i : ι) : 0 ≤ w i := sq_nonneg _
  have htrace : (ks.map fun k => A ^ k * vecMulVec y y).prod.trace =
      (ks.map fun k => y ⬝ᵥ (A ^ k *ᵥ y)).prod := by
    simpa only [List.map_map, Function.comp_def] using
      trace_prod_map_mul_vecMulVec y (ks.map fun k => A ^ k) (by simpa using hne)
  have hprod : ∀ ls : List ℕ, |(ls.map fun k => y ⬝ᵥ (A ^ k *ᵥ y)).prod| ≤
      (ls.map fun k => ∑ i, w i * |hA.eigenvalues i| ^ k).prod := by
    intro ls
    induction ls with
    | nil => simp
    | cons k ks ih =>
      simp only [List.map_cons, List.prod_cons, abs_mul]
      exact mul_le_mul (abs_dotProduct_pow_mulVec_le_sum_abs_eigenvalues_pow hA y k)
        ih (abs_nonneg _) (Finset.sum_nonneg fun i _ => mul_nonneg (hw i)
          (pow_nonneg (abs_nonneg _) _))
  rw [htrace]
  refine (hprod ks).trans ?_
  have hb := prod_list_sum_mul_pow_le w (fun i => |hA.eigenvalues i|) hw
    (fun i => abs_nonneg _) ks hne
  have hsum : (∑ i, w i) = y ⬝ᵥ y := sum_sq_eigenvectorBasis_dotProduct hA y
  rw [hsum] at hb
  rw [dotProduct_cfc_mulVec_eq_sum hA]
  simpa only [w, mul_comm] using hb

end NLAlib
