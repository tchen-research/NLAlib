import NLAlib.Matrix.Norms.Core
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import NLAlib.ForMathlib.LinearAlgebra.Matrix.TraceWords
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Rotate
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Cyclic cuts of actual alternating trace words

The cut identity uses only finite list/trace algebra. A bound on the
coefficient norms also gives a sharp bound on the actual middle matrix,
including zero radii and empty dimensions.

The word has m+2 alternating pairs. Rotating just after slot j leaves
  Z_(j+1) [Y_(j+1) product_(m interior slots) (Z_l Y_l)] Z_j Y_j.
The m interior indices retain their cyclic order. The entire rotated index
list is a permutation of Fin(m+2), so the middle contains exactly m Z factors
and every Y factor except Y_j, each once. The case m=0 is the two-pair word.

Source: the cyclic trace reduction in Brailovskaya–van Handel,
arXiv:2201.05142v3, Proposition 5.1, q=infinity endpoint.
Supports `independent-sum-spectrum-universality`.
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix

namespace NLAlib

/-- Ordered indices after rotating a word immediately after its selected slot.
The m+2 parametrization keeps the two-pair boundary explicit. -/
private def cyclicTraceCutIndices {m : ℕ} (j : Fin (m + 2)) : List (Fin (m + 2)) :=
  (List.finRange (m + 2)).rotate (j.val + 1)

/-- The strict interior of the cyclic cut: omit its first and last indices. -/
private def cyclicTraceCutMiddle {m : ℕ} (j : Fin (m + 2)) : List (Fin (m + 2)) :=
  ((cyclicTraceCutIndices j).drop 1).take m

@[simp]
private theorem length_cyclicTraceCutIndices {m : ℕ} (j : Fin (m + 2)) :
    (cyclicTraceCutIndices j).length = m + 2 := by
  simp [cyclicTraceCutIndices]

@[simp]
private theorem length_cyclicTraceCutMiddle {m : ℕ} (j : Fin (m + 2)) :
    (cyclicTraceCutMiddle j).length = m := by
  rw [cyclicTraceCutMiddle, List.length_take, List.length_drop, length_cyclicTraceCutIndices]
  omega

private theorem cyclicTraceCutIndices_first {m : ℕ} (j : Fin (m + 2)) :
    (cyclicTraceCutIndices j)[0]'(by simp) = finRotate (m + 2) j := by
  simp only [cyclicTraceCutIndices, List.getElem_rotate]
  apply Fin.ext
  rw [finRotate_apply]
  simp [Fin.add_def, Nat.mod_eq_of_lt (show 1 < m + 2 by omega)]

private theorem cyclicTraceCutIndices_last {m : ℕ} (j : Fin (m + 2)) :
    (cyclicTraceCutIndices j)[m + 1]'(by simp) = j := by
  simp only [cyclicTraceCutIndices, List.getElem_rotate]
  apply Fin.ext
  have h : m + 1 + (j.val + 1) = (m + 2) + j.val := by omega
  simp [h, Nat.add_mod_left, Nat.mod_eq_of_lt j.isLt]

/-- The cyclically rotated list has precisely the successor and selected slot
as its two ends, with exactly m ordered interior slots. -/
private theorem cyclicTraceCutIndices_eq {m : ℕ} (j : Fin (m + 2)) :
    cyclicTraceCutIndices j =
      finRotate (m + 2) j :: (cyclicTraceCutMiddle j ++ [j]) := by
  let L := cyclicTraceCutIndices j
  have hlen : L.length = m + 2 := length_cyclicTraceCutIndices j
  have hfirst : L[0]'(by omega) = finRotate (m + 2) j :=
    cyclicTraceCutIndices_first j
  have hlast : L[m + 1]'(by omega) = j := cyclicTraceCutIndices_last j
  have hdrop : (L.drop 1).drop m = [j] := by
    rw [List.drop_drop, Nat.add_comm 1 m,
      List.drop_eq_getElem_cons (show m + 1 < L.length by omega), hlast]
    simp [hlen]
  have htail : L.drop 1 = cyclicTraceCutMiddle j ++ [j] := by
    simpa only [cyclicTraceCutMiddle, ← hdrop] using
      (List.take_append_drop m (L.drop 1)).symm
  calc
    L = L[0]'(by omega) :: L.drop 1 := by
      simpa using (List.drop_eq_getElem_cons (show 0 < L.length by omega))
    _ = _ := by rw [hfirst, htail]

/-- The cut preserves every index exactly once; this also identifies the
noncommutative middle factors without any permutation of matrix products. -/
private theorem cyclicTraceCutIndices_perm {m : ℕ} (j : Fin (m + 2)) :
    (finRotate (m + 2) j :: (cyclicTraceCutMiddle j ++ [j])).Perm
      (List.finRange (m + 2)) := by
  rw [← cyclicTraceCutIndices_eq]
  exact List.rotate_perm _ _

private theorem prod_cyclicTraceCutMiddle {S : Type*} [CommMonoid S] {m : ℕ}
    (f : Fin (m + 2) → S) (j : Fin (m + 2)) :
    f (finRotate (m + 2) j) * ((cyclicTraceCutMiddle j).map f).prod =
      ∏ l ∈ Finset.univ.erase j, f l := by
  let T := finRotate (m + 2) j :: cyclicTraceCutMiddle j
  have hp : (j :: T).Perm (List.finRange (m + 2)) := by
    have hc : ([j] ++ T).Perm (T ++ [j]) := List.perm_append_comm
    exact hc.trans (by simpa only [T, List.cons_append] using cyclicTraceCutIndices_perm j)
  have he := hp.trans (List.perm_cons_erase (by simp : j ∈ List.finRange (m + 2)))
  have ht : T.Perm ((List.finRange (m + 2)).erase j) := he.cons_inv
  calc
    _ = (T.map f).prod := rfl
    _ = (((List.finRange (m + 2)).erase j).map f).prod := (ht.map f).prod_eq
    _ = _ := by
      rw [← List.prod_toFinset f (List.Nodup.erase j (List.nodup_finRange _))]
      congr 1
      ext l
      simp [(List.nodup_finRange (m + 2)).mem_erase_iff]

/-- The actual matrix-valued middle obtained by cutting an alternating trace
word immediately after its selected deterministic factor. It retains the
original cyclic factor order. -/
def cyclicTraceWordMiddle {S n : Type*} [CommSemiring S] [Fintype n] [DecidableEq n]
    {m : ℕ} (Z Y : Fin (m + 2) → Matrix n n S) (j : Fin (m + 2)) : Matrix n n S :=
  Y (finRotate (m + 2) j) * ((cyclicTraceCutMiddle j).map (fun l => Z l * Y l)).prod

open scoped Matrix.Norms.L2Operator in
private theorem specNorm_list_alternating_prod_le {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    {m : ℕ} (Z Y : Fin (m + 2) → Matrix n n 𝕜) {R : ℝ} (hR : 0 ≤ R)
    (hZ : ∀ l, NLAlib.specNorm (Z l) ≤ R) (L : List (Fin (m + 2))) :
    NLAlib.specNorm ((L.map (fun l => Z l * Y l)).prod) ≤
      R ^ L.length * ((L.map (fun l => NLAlib.specNorm (Y l))).prod) := by
  induction L with
  | nil => simpa only [List.map_nil, List.prod_nil, List.length_nil, pow_zero, one_mul] using
      (specNorm_one_le (𝕜 := 𝕜) (n := n))
  | cons l L ih =>
    simp only [List.map_cons, List.prod_cons]
    have hfac : specNorm (Z l * Y l) ≤ R * specNorm (Y l) :=
      (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hZ l) (specNorm_nonneg _))
    calc
      _ ≤ specNorm (Z l * Y l) * specNorm ((L.map (fun a => Z a * Y a)).prod) :=
        specNorm_mul_le _ _
      _ ≤ (R * specNorm (Y l)) *
          (R ^ L.length * (L.map (fun a => specNorm (Y a))).prod) :=
        mul_le_mul hfac ih (specNorm_nonneg _) (mul_nonneg hR (specNorm_nonneg _))
      _ = _ := by simp only [List.length_cons, pow_succ]; ring

open scoped Matrix.Norms.L2Operator in
/-- The actual cyclic middle contains k-2 bounded random coefficients and all
other deterministic factors, with sharp constant one and no division by any
norm. Includes zero radius and empty matrix dimensions. -/
theorem specNorm_cyclicTraceWordMiddle_le {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    {m : ℕ} (Z Y : Fin (m + 2) → Matrix n n 𝕜) {R : ℝ} (hR : 0 ≤ R)
    (hZ : ∀ l, specNorm (Z l) ≤ R) (j : Fin (m + 2)) :
    specNorm (cyclicTraceWordMiddle Z Y j) ≤
      R ^ m * ∏ l ∈ Finset.univ.erase j, specNorm (Y l) := by
  have hp := specNorm_list_alternating_prod_le Z Y hR hZ (cyclicTraceCutMiddle j)
  rw [length_cyclicTraceCutMiddle] at hp
  calc
    _ ≤ specNorm (Y (finRotate (m + 2) j)) *
        specNorm (((cyclicTraceCutMiddle j).map (fun l => Z l * Y l)).prod) :=
      specNorm_mul_le _ _
    _ ≤ specNorm (Y (finRotate (m + 2) j)) *
        (R ^ m * ((cyclicTraceCutMiddle j).map (fun l => specNorm (Y l))).prod) :=
      mul_le_mul_of_nonneg_left hp (specNorm_nonneg _)
    _ = R ^ m * (specNorm (Y (finRotate (m + 2) j)) *
        ((cyclicTraceCutMiddle j).map (fun l => specNorm (Y l))).prod) := by ring
    _ = _ := by rw [prod_cyclicTraceCutMiddle (fun l => specNorm (Y l)) j]

open scoped Matrix.Norms.L2Operator in
/-- The cyclic matrix middle is continuous in its coefficient array. -/
theorem continuous_cyclicTraceWordMiddle {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    {m : ℕ} (Y : Fin (m + 2) → Matrix n n 𝕜) (j : Fin (m + 2)) :
    Continuous (fun Z => cyclicTraceWordMiddle Z Y j) := by
  have hprod (L : List (Fin (m + 2))) :
      Continuous (fun Z : Fin (m + 2) → Matrix n n 𝕜 =>
        (L.map (fun l => Z l * Y l)).prod) := by
    induction L with
    | nil => simpa only [List.map_nil, List.prod_nil] using continuous_const
    | cons l L ih =>
      change Continuous (fun Z : Fin (m + 2) → Matrix n n 𝕜 =>
        (Z l * Y l) * (L.map (fun a => Z a * Y a)).prod)
      exact Continuous.mul (f := fun Z : Fin (m + 2) → Matrix n n 𝕜 => Z l * Y l)
        (g := fun Z => (L.map (fun a => Z a * Y a)).prod)
        ((continuous_apply l).mul continuous_const) ih
  exact continuous_const.mul (hprod (cyclicTraceCutMiddle j))

/-- Cutting after Y_j restores the two actual endpoint copies Z_(j+1), Z_j.
The middle contains m other Z factors and every deterministic Y except Y_j.
This identity includes two-pair words and empty matrix dimensions.
Source: Brailovskaya–van Handel, arXiv:2201.05142v3, Proposition 5.1. -/
private theorem trace_alternating_word_eq_cyclic_cut_aux
    {R n : Type*} [CommSemiring R] [Fintype n] [DecidableEq n] {m : ℕ}
    (Z Y : Fin (m + 2) → Matrix n n R) (j : Fin (m + 2)) :
    (List.ofFn (fun l => Z l * Y l)).prod.trace =
      (Z (finRotate (m + 2) j) *
        (Y (finRotate (m + 2) j) *
          ((cyclicTraceCutMiddle j).map (fun l => Z l * Y l)).prod) * Z j * Y j).trace := by
  let f : Fin (m + 2) → Matrix n n R := fun l => Z l * Y l
  calc
    (List.ofFn f).prod.trace =
        (((cyclicTraceCutIndices j).map f).prod).trace := by
      rw [cyclicTraceCutIndices, List.map_rotate, ← List.ofFn_eq_map]
      exact (Matrix.trace_list_prod_rotate _ _).symm
    _ = _ := by
      rw [cyclicTraceCutIndices_eq]
      simp only [List.map_cons, List.map_append, List.map_nil,
        List.prod_cons, List.prod_append, List.prod_nil, Matrix.mul_one, f, Matrix.mul_assoc]

/-- The exact cyclic cut of the literal ordered alternating trace word. The
actual middle matrix is deterministic algebra and needs no norm, support,
Hermitian, or dimension assumption. -/
theorem trace_alternating_word_eq_cyclic_cut
    {S n : Type*} [CommSemiring S] [Fintype n] [DecidableEq n] {m : ℕ}
    (Z Y : Fin (m + 2) → Matrix n n S) (j : Fin (m + 2)) :
    (List.ofFn (fun l => Z l * Y l)).prod.trace =
      (Z (finRotate (m + 2) j) * cyclicTraceWordMiddle Z Y j * Z j * Y j).trace :=
  trace_alternating_word_eq_cyclic_cut_aux Z Y j

@[simp]
private theorem cyclicTraceCutMiddle_zero (j : Fin 2) : cyclicTraceCutMiddle j = [] := by
  simp [cyclicTraceCutMiddle]

/-- At the two-pair boundary, the exact middle is simply the other Y factor.
There is no scalar division or positive-radius assumption in the cut. -/
theorem trace_alternating_two_pairs_eq_cyclic_cut
    {R n : Type*} [CommSemiring R] [Fintype n] [DecidableEq n]
    (Z Y : Fin 2 → Matrix n n R) (j : Fin 2) :
    (List.ofFn (fun l => Z l * Y l)).prod.trace =
      (Z (finRotate 2 j) * Y (finRotate 2 j) * Z j * Y j).trace := by
  simpa only [cyclicTraceCutMiddle_zero, List.map_nil, List.prod_nil, Matrix.mul_one] using
    trace_alternating_word_eq_cyclic_cut_aux Z Y j

end NLAlib
