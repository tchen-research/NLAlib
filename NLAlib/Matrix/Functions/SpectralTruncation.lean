import NLAlib.Matrix.Functions.DiagonalCalculus
import NLAlib.Matrix.Norms.SchattenDiagonal
import NLAlib.Matrix.Inequalities.TraceTail
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-!
# Spectral function truncation in a fixed ordered eigenbasis

An orthogonal basis and its ordered coefficient list determine a spectral matrix.
`spectralFunctionTruncation` evaluates the scalar function before retaining the prefix.
All reconstruction, order and Schatten formulas hold for every supplied orthogonal
basis, so choices within repeated eigenspaces are part of the construction rather than
an implicit SVD selector. Canonical Hermitian eigenbases supply an unconditional instance.

Source: Persson–Meyer–Musco 2025, Theorem 2.6; the finite spectral theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Reconstruct a real spectral matrix in a supplied square basis. Coordinates are
indexed by `Fin (card n)` and transported to the matrix index type by the standard
equivalence. The definition itself does not require coefficients to be sorted. -/
def spectralBasisMatrix (U : Matrix n n ℝ) (a : Fin (Fintype.card n) → ℝ) : Matrix n n ℝ :=
  U * Matrix.diagonal (fun i => a ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)) * Uᵀ

/-- Apply `f` to the coefficients and then retain the first `k` basis directions.
For a sorted eigendecomposition this is `f(A)_k`; positive `f(0)` is retained in
selected zero-eigenvalue directions and discarded outside the selected prefix. -/
def spectralFunctionTruncation (U : Matrix n n ℝ) (a : Fin (Fintype.card n) → ℝ)
    (f : ℝ → ℝ) (k : ℕ) : Matrix n n ℝ :=
  spectralBasisMatrix U (fun i => if i.val < k then f (a i) else 0)

/-- The actual transformed prefix has rank at most its cutoff, for every basis
and every coefficient function. The zero and oversized cutoff cases are included. -/
theorem rank_spectralFunctionTruncation_le (U : Matrix n n ℝ)
    (a : Fin (Fintype.card n) → ℝ) (f : ℝ → ℝ) (k : ℕ) :
    (spectralFunctionTruncation U a f k).rank ≤ k := by
  classical
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  let H := Finset.univ.filter (fun i : n => (e.symm i).val < k)
  let d := fun i : n => if (e.symm i).val < k then f (a (e.symm i)) else 0
  have hsupport : Function.support (Matrix.diagonal d).row ⊆ H := by
    rw [Function.support_subset_iff']
    intro i hi
    change i ∉ H at hi
    have hik : ¬ (e.symm i).val < k := by
      intro hh
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hh⟩)
    ext j
    change Matrix.diagonal d i j = 0
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, d, if_neg hik]
    · exact Matrix.diagonal_apply_ne _ hij
  have hcard : H.card ≤ k := by
    have h := Finset.card_le_card_of_injOn (s := H) (t := Finset.range k)
      (fun i : n => (e.symm i).val)
      (fun i hi => Finset.mem_range.mpr (Finset.mem_filter.mp hi).2)
      (fun i _ j _ hij => e.symm.injective (Fin.ext hij))
    simpa only [Finset.card_range] using h
  have hD := Matrix.rank_le_card_of_support_subset (Matrix.diagonal d) H hsupport
  change (U * Matrix.diagonal d * Uᵀ).rank ≤ k
  exact ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans (hD.trans hcard)

/-- Coordinate subtraction commutes with spectral reconstruction in a fixed basis. -/
theorem spectralBasisMatrix_sub (U : Matrix n n ℝ) (a b : Fin (Fintype.card n) → ℝ) :
    spectralBasisMatrix U a - spectralBasisMatrix U b = spectralBasisMatrix U (a - b) := by
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  have hd : Matrix.diagonal (fun i : n => (a - b) (e.symm i)) =
      Matrix.diagonal (fun i : n => a (e.symm i)) - Matrix.diagonal (fun i : n => b (e.symm i)) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij, Pi.sub_apply]
  change U * Matrix.diagonal (fun i => a (e.symm i)) * Uᵀ -
    U * Matrix.diagonal (fun i => b (e.symm i)) * Uᵀ =
    U * Matrix.diagonal (fun i => (a - b) (e.symm i)) * Uᵀ
  rw [hd, Matrix.mul_sub, Matrix.sub_mul]

/-- Nonnegative spectral coefficients give a PSD matrix in any supplied basis. -/
theorem posSemidef_spectralBasisMatrix (U : Matrix n n ℝ) (a : Fin (Fintype.card n) → ℝ)
    (ha : ∀ i, 0 ≤ a i) : (spectralBasisMatrix U a).PosSemidef := by
  have hd := Matrix.posSemidef_diagonal_iff.mpr
    (fun i : n => ha ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i))
  exact hd.mul_mul_conjTranspose_same U

/-- Coordinatewise order is preserved by spectral reconstruction in a fixed basis. -/
theorem spectralBasisMatrix_mono (U : Matrix n n ℝ) {a b : Fin (Fintype.card n) → ℝ}
    (hab : ∀ i, a i ≤ b i) : spectralBasisMatrix U a ≤ spectralBasisMatrix U b := by
  apply Matrix.le_iff.mpr
  rw [spectralBasisMatrix_sub]
  exact posSemidef_spectralBasisMatrix U _ (fun i => sub_nonneg.mpr (hab i))

open scoped Matrix.Norms.L2Operator in
/-- Every scalar function on the finite spectrum acts coefficientwise in any
orthogonal spectral basis. No global continuity of the function is needed. -/
theorem cfc_spectralBasisMatrix (U : Matrix n n ℝ) (hU : HasOrthonormalCols U)
    (a : Fin (Fintype.card n) → ℝ) (f : ℝ → ℝ) :
    cfc f (spectralBasisMatrix U a) = spectralBasisMatrix U (f ∘ a) := by
  cases isEmpty_or_nonempty n with
  | inl h => exact Subsingleton.elim _ _
  | inr h =>
    let := h
    let V : unitary (Matrix n n ℝ) := ⟨U, ⟨hU, mul_eq_one_comm.mp hU⟩⟩
    let E := Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) V
    let d := fun i : n => a ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)
    have hD : (Matrix.diagonal d).IsHermitian := Matrix.isHermitian_diagonal d
    have hC : (E (Matrix.diagonal d)).IsHermitian :=
      Matrix.isHermitian_mul_mul_conjTranspose U hD
    have he := StarAlgHomClass.map_cfc E f (Matrix.diagonal d)
      ((Matrix.diagonal d).finite_real_spectrum.continuousOn f)
      E.toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional hD hC
    have hDcalc : cfc f (Matrix.diagonal d) = Matrix.diagonal (fun i => f (d i)) := cfc_diagonal f d
    rw [hDcalc] at he
    change cfc f (E (Matrix.diagonal d)) = E (Matrix.diagonal (fun i => f (d i)))
    exact he.symm

open scoped Matrix.Norms.L2Operator in
/-- The exact finite Schatten power sum in any orthogonal spectral basis is the
power sum of its nonnegative coefficients, including zeros and repeated values. -/
theorem schattenNormReal_spectralBasisMatrix_rpow (U : Matrix n n ℝ)
    (hU : HasOrthonormalCols U) (a : Fin (Fintype.card n) → ℝ) (ha : ∀ i, 0 ≤ a i)
    {p : ℝ} (hp : 0 < p) :
    schattenNormReal (spectralBasisMatrix U a) p ^ p = ∑ i, a i ^ p := by
  have hUt : HasOrthonormalCols Uᵀ := by
    change Uᵀᵀ * Uᵀ = 1
    rw [Matrix.transpose_transpose]
    exact mul_eq_one_comm.mp hU
  rw [spectralBasisMatrix, schattenNormReal_mul_orthogonal _ hUt,
    schattenNormReal_orthogonal_mul _ hU, schattenNormReal_diagonal_real]
  simp_rw [abs_of_nonneg (ha _)]
  rw [one_div, Real.rpow_inv_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (ha _) _) hp.ne']
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  rw [← e.sum_comp (fun i : n => a (e.symm i) ^ p)]
  simp only [Equiv.symm_apply_apply]

/-- The residual after applying a function and retaining a prefix is reconstructed
from the complementary transformed coefficients. In particular this keeps `f(0)`
on every unselected zero-eigenvalue direction. -/
theorem cfc_sub_spectralFunctionTruncation_eq (U : Matrix n n ℝ)
    (hU : HasOrthonormalCols U) (a : Fin (Fintype.card n) → ℝ) (f : ℝ → ℝ) (k : ℕ) :
    cfc f (spectralBasisMatrix U a) - spectralFunctionTruncation U a f k =
      spectralBasisMatrix U (fun i => if k ≤ i.val then f (a i) else 0) := by
  rw [cfc_spectralBasisMatrix U hU, spectralFunctionTruncation, spectralBasisMatrix_sub]
  congr 1
  funext i
  simp only [Pi.sub_apply, Function.comp_apply]
  by_cases hi : i.val < k
  · simp only [if_pos hi, if_neg (not_le.mpr hi), sub_self]
  · simp only [if_neg hi, if_pos (not_lt.mp hi), sub_zero]

/-- A truncated nonnegative spectral function is PSD, including an empty prefix. -/
theorem posSemidef_spectralFunctionTruncation (U : Matrix n n ℝ)
    (a : Fin (Fintype.card n) → ℝ) (f : ℝ → ℝ) (k : ℕ) (hf : ∀ i, 0 ≤ f (a i)) :
    (spectralFunctionTruncation U a f k).PosSemidef :=
  posSemidef_spectralBasisMatrix U _ (fun i => by split_ifs; exacts [hf i, le_rfl])

/-- Prefix truncation of a nonnegative spectral function lies below the full
function matrix in Loewner order, in the same supplied orthogonal basis. -/
theorem spectralFunctionTruncation_le_cfc (U : Matrix n n ℝ) (hU : HasOrthonormalCols U)
    (a : Fin (Fintype.card n) → ℝ) (f : ℝ → ℝ) (k : ℕ) (hf : ∀ i, 0 ≤ f (a i)) :
    spectralFunctionTruncation U a f k ≤ cfc f (spectralBasisMatrix U a) := by
  rw [cfc_spectralBasisMatrix U hU]
  apply spectralBasisMatrix_mono
  intro i
  change (if i.val < k then f (a i) else 0) ≤ f (a i)
  split_ifs
  · exact le_rfl
  · exact hf i

/-- The exact Schatten power of a truncated nonnegative spectral function is its
transformed head sum. This formula holds for every orthogonal choice within ties. -/
theorem schattenNormReal_spectralFunctionTruncation_rpow (U : Matrix n n ℝ)
    (hU : HasOrthonormalCols U) (a : Fin (Fintype.card n) → ℝ) (f : ℝ → ℝ) (k : ℕ)
    (hf : ∀ i, 0 ≤ f (a i)) {p : ℝ} (hp : 0 < p) :
    schattenNormReal (spectralFunctionTruncation U a f k) p ^ p =
      ∑ i, if i.val < k then f (a i) ^ p else 0 := by
  rw [spectralFunctionTruncation, schattenNormReal_spectralBasisMatrix_rpow U hU _
    (fun i => by split_ifs; exacts [hf i, le_rfl]) hp]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp only [Real.zero_rpow hp.ne']

/-- The exact Schatten residual power after truncating a nonnegative spectral
function is the transformed tail sum, including the positive `f(0)` terms. -/
theorem schattenNormReal_cfc_sub_spectralFunctionTruncation_rpow (U : Matrix n n ℝ)
    (hU : HasOrthonormalCols U) (a : Fin (Fintype.card n) → ℝ) (f : ℝ → ℝ) (k : ℕ)
    (hf : ∀ i, 0 ≤ f (a i)) {p : ℝ} (hp : 0 < p) :
    schattenNormReal (cfc f (spectralBasisMatrix U a) - spectralFunctionTruncation U a f k) p ^ p =
      ∑ i, if k ≤ i.val then f (a i) ^ p else 0 := by
  rw [cfc_sub_spectralFunctionTruncation_eq U hU a f k, schattenNormReal_spectralBasisMatrix_rpow U hU _
    (fun i => by split_ifs; exacts [hf i, le_rfl]) hp]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp only [Real.zero_rpow hp.ne']

/-- The canonical spectral eigenbasis reconstructs the matrix using its actual
decreasing eigenvalue list. It is one instance of the basis-explicit construction. -/
theorem spectralBasisMatrix_eigenvectorUnitary {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    spectralBasisMatrix (hA.eigenvectorUnitary : Matrix n n ℝ) hA.eigenvalues₀ = A := by
  exact (eq_eigenvectorUnitary_mul_diagonal_mul_transpose hA).symm

/-- Canonical truncation after applying `f`, using the fixed sorted spectral
eigenbasis of the original Hermitian matrix. The basis-explicit API also allows
any other ordered orthogonal diagonalization. -/
def _root_.Matrix.IsHermitian.spectralFunctionTruncation {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) (k : ℕ) : Matrix n n ℝ :=
  NLAlib.spectralFunctionTruncation (hA.eigenvectorUnitary : Matrix n n ℝ) hA.eigenvalues₀ f k

/-- Truncation at rank zero returns the zero matrix after any scalar function,
including a function that is positive at the origin. -/
@[simp] theorem spectralFunctionTruncation_zero (U : Matrix n n ℝ)
    (a : Fin (Fintype.card n) → ℝ) (f : ℝ → ℝ) : spectralFunctionTruncation U a f 0 = 0 := by
  simp [spectralFunctionTruncation, spectralBasisMatrix]

end NLAlib
