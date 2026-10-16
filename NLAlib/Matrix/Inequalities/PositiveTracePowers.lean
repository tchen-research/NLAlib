import NLAlib.Matrix.Spectral.GramSpectralSums
import NLAlib.Matrix.Spectral.SpectralGramFactor
import NLAlib.Matrix.Inequalities.Schur
import NLAlib.Matrix.Norms.SchattenNorms
import NLAlib.Matrix.Functions.FunctionalCalculusEigenvalues
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Superadditivity of positive trace powers

Stacking spectral Gram factors realizes the two separate eigenvalue lists
as the diagonal of a single Gram matrix. Schur majorization then proves
McCarthy's trace inequality without any operator-convexity assumption.
Source: matrix_toolkit_open_routes_2026_10_15, F8; pmm25, Lemma 2.3.
-/

noncomputable section
open Matrix
open scoped MatrixOrder ComplexOrder
namespace NLAlib
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- Positive trace powers are superadditive, including singular matrices,
empty dimensions, and every real exponent at least one.
atlas: ordered-schatten-trace-deficit (partial) -/
theorem sum_eigenvalues_rpow_add_le {X Y : Matrix n n 𝕜}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i, hX.isHermitian.eigenvalues i ^ p) +
      (∑ i, hY.isHermitian.eigenvalues i ^ p) ≤
        ∑ i, (hX.add hY).isHermitian.eigenvalues i ^ p := by
  let G := Matrix.fromRows (spectralGramRows hX) (spectralGramRows hY)
  have hG : G.conjTranspose * G = X + Y := by
    dsimp only [G]
    rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows, spectralGramRows_adjoint_mul,
      spectralGramRows_adjoint_mul]
  have hd : (fun i => RCLike.re ((G * G.conjTranspose) i i)) =
      Sum.elim hX.isHermitian.eigenvalues hY.isHermitian.eigenvalues := by
    funext i
    cases i with
    | inl i =>
      have h := congrArg (fun M : Matrix n n 𝕜 => RCLike.re (M i i))
        (spectralGramRows_mul_adjoint hX)
      simpa [G, Matrix.mul_apply, Matrix.conjTranspose_apply] using h
    | inr i =>
      have h := congrArg (fun M : Matrix n n 𝕜 => RCLike.re (M i i))
        (spectralGramRows_mul_adjoint hY)
      simpa [G, Matrix.mul_apply, Matrix.conjTranspose_apply] using h
  have hm := (majorized_diagonal_eigenvalues
    (Matrix.isHermitian_mul_conjTranspose_self G)).1
  rw [hd] at hm
  have hs := hm.sum_rpow_le
    (by intro i; cases i <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
      first | exact hX.eigenvalues_nonneg _ | exact hY.eigenvalues_nonneg _)
    (Matrix.posSemidef_self_mul_conjTranspose G).eigenvalues_nonneg hp
  rw [Fintype.sum_sum_type] at hs
  rw [sum_eigenvalues_mul_adjoint_eq_adjoint_mul G (fun x => x ^ p)
    (Real.zero_rpow (by linarith : p ≠ 0))] at hs
  simpa only [hG, Sum.elim_inl, Sum.elim_inr] using hs

/-- The positive-matrix Schatten power sum is its eigenvalue power sum. -/
theorem schattenNormReal_rpow_eq_sum_eigenvalues {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {p : ℝ} (hp : 0 < p) :
    schattenNormReal A p ^ p = ∑ i, hA.isHermitian.eigenvalues i ^ p := by
  rw [schattenNormReal, one_div, Real.rpow_inv_rpow
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValues_nonneg A i) p) hp.ne']
  rw [min_self, ← Fin.sum_univ_eq_sum_range]
  simp_rw [singularValues_eq_eigenvalues₀_of_posSemidef hA]
  exact (sum_eigenvalues_eq_sum_sorted hA.isHermitian (fun x => x ^ p)).symm

open scoped Matrix.Norms.L2Operator in
/-- McCarthy trace superadditivity in functional-calculus notation.
atlas: ordered-schatten-trace-deficit (partial) -/
theorem re_trace_rpow_add_le {X Y : Matrix n n 𝕜}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) {p : ℝ} (hp : 1 ≤ p) :
    RCLike.re (cfc (fun x : ℝ => x ^ p) X).trace +
      RCLike.re (cfc (fun x : ℝ => x ^ p) Y).trace ≤
        RCLike.re (cfc (fun x : ℝ => x ^ p) (X + Y)).trace := by
  simpa only [re_trace_cfc_eq_sum_eigenvalues hX.isHermitian,
    re_trace_cfc_eq_sum_eigenvalues hY.isHermitian,
    re_trace_cfc_eq_sum_eigenvalues (hX.add hY).isHermitian] using
    sum_eigenvalues_rpow_add_le hX hY hp

/-- Ordered PSD differences are bounded by the sharp Schatten trace deficit.
The field is real or complex and the index type may be empty.
atlas: ordered-schatten-trace-deficit (partial) -/
theorem schattenNormReal_sub_rpow_le {A B : Matrix n n 𝕜}
    (hB : B.PosSemidef) (hAB : B ≤ A) {p : ℝ} (hp : 1 ≤ p) :
    schattenNormReal (A-B) p ^ p ≤ schattenNormReal A p ^ p - schattenNormReal B p ^ p := by
  have hD : (A-B).PosSemidef := Matrix.le_iff.mp hAB
  have hA : A.PosSemidef := by simpa using hD.add hB
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  rw [schattenNormReal_rpow_eq_sum_eigenvalues hD hp0,
    schattenNormReal_rpow_eq_sum_eigenvalues hA hp0,
    schattenNormReal_rpow_eq_sum_eigenvalues hB hp0]
  have h := sum_eigenvalues_rpow_add_le hD hB hp
  simp only [sub_add_cancel] at h
  linarith

open scoped Matrix.Norms.L2Operator in
/-- At exponent one the ordered PSD Schatten deficit is an equality.
atlas: ordered-schatten-trace-deficit (partial) -/
theorem schattenNormReal_sub_one {A B : Matrix n n 𝕜}
    (hB : B.PosSemidef) (hAB : B ≤ A) :
    schattenNormReal (A-B) 1 = schattenNormReal A 1 - schattenNormReal B 1 := by
  have hD : (A-B).PosSemidef := Matrix.le_iff.mp hAB
  have hA : A.PosSemidef := by simpa using hD.add hB
  have ht (M : Matrix n n 𝕜) (hM : M.PosSemidef) :
      schattenNormReal M 1 = RCLike.re M.trace := by
    have h := schattenNormReal_rpow_eq_sum_eigenvalues hM (p := 1) zero_lt_one
    have ht := re_trace_cfc_eq_sum_eigenvalues hM.isHermitian (fun x => x)
    have hc : cfc (fun x : ℝ => x) M = M := cfc_id ℝ M hM.isHermitian
    rw [hc] at ht
    simpa only [Real.rpow_one, ← ht] using h
  rw [ht _ hD, ht _ hA, ht _ hB, Matrix.trace_sub, map_sub]

end NLAlib
