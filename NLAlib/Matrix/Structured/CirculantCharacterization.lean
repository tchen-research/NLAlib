import NLAlib.Matrix.Structured.StructuredMatrices
import Mathlib.LinearAlgebra.Matrix.Circulant

/-!
# Circulants are precisely the cyclic-shift commutant

Commutation forces each column to be the cyclic shift of the first. Every
circulant is Toeplitz with its wrap-around diagonal parameters. The empty
case is included separately. Horn–Johnson 2013, §0.9.7.
-/

noncomputable section
open scoped Matrix Fin.NatCast Fin.IntCast
namespace NLAlib

/-- The cyclic shift sends coordinate `j` to `j+1` modulo the positive
dimension. This uses Mathlib's native circulant convention.
Horn–Johnson 2013, §0.9.7; structured-matrices-def helper. -/
def cyclicShiftMatrix (n : ℕ) [NeZero n] : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.circulant (Pi.single (1 : Fin n) 1)

private theorem mul_cyclicShiftMatrix_apply {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (A * cyclicShiftMatrix n) i j = A i (j + 1) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (j + 1)]
  · simp [cyclicShiftMatrix, Matrix.circulant_apply]
  · intro k _ hkj
    have h : (1 : Fin n) ≠ k - j := by
      intro hk
      apply hkj
      have h' := sub_eq_iff_eq_add.mp hk.symm
      simpa only [add_comm] using h'
    simp [cyclicShiftMatrix, Matrix.circulant_apply, h]
  · simp

private theorem cyclicShiftMatrix_mul_apply {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (cyclicShiftMatrix n * A) i j = A (i - 1) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (i - 1)]
  · simp [cyclicShiftMatrix, Matrix.circulant_apply]
  · intro k _ hki
    have h : (1 : Fin n) ≠ i - k := by
      intro hk
      apply hki
      have h' : k = i - 1 := by rw [hk]; abel
      exact h'
    simp [cyclicShiftMatrix, Matrix.circulant_apply, h]
  · simp

/-- Commutation with the cyclic shift forces the Mathlib circulant formula,
with the original first column as generator. No Toeplitz assumption is
needed. Horn–Johnson 2013, §0.9.7.
atlas: structured-matrices-def (partial) -/
theorem eq_circulant_of_commute_cyclicShift {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A * cyclicShiftMatrix n = cyclicShiftMatrix n * A) :
    A = Matrix.circulant (fun i => A i 0) := by
  have hStep (i j : Fin n) : A i (j + 1) = A (i - 1) j := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hA
    simpa only [mul_cyclicShiftMatrix_apply, cyclicShiftMatrix_mul_apply] using h
  have hNat (j : ℕ) : ∀ i : Fin n, A i (j : Fin n) = A (i - (j : Fin n)) 0 := by
    induction j with
    | zero => intro i; simp
    | succ j ih =>
      intro i
      rw [Nat.cast_succ, hStep, ih]
      congr 1
      abel
  ext i j
  have h := hNat j.val i
  simpa only [Fin.cast_val_eq_self, Matrix.circulant_apply] using h

/-- A matrix commutes with the cyclic shift exactly when it is a circulant.
Horn–Johnson 2013, §0.9.7.
atlas: structured-matrices-def (partial) -/
theorem commute_cyclicShift_iff_exists_circulant {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℝ) :
    A * cyclicShiftMatrix n = cyclicShiftMatrix n * A ↔
      ∃ v : Fin n → ℝ, A = Matrix.circulant v := by
  constructor
  · intro h; exact ⟨_, eq_circulant_of_commute_cyclicShift A h⟩
  · rintro ⟨v, rfl⟩
    exact Matrix.circulant_mul_comm v _

/-- Every positive-dimensional circulant is an ordinary Toeplitz matrix;
the diagonal parameters implement only the necessary wrap-around
identifications. Horn–Johnson 2013, §0.9.7.
atlas: structured-matrices-def (partial) -/
theorem exists_toeplitzMatrix_eq_circulant {n : ℕ} [NeZero n] (v : Fin n → ℝ) :
    ∃ t : ℤ → ℝ, toeplitzMatrix t = Matrix.circulant v := by
  classical
  let t : ℤ → ℝ := fun d => if h : ∃ i j : Fin n, (j.val : ℤ) - (i.val : ℤ) = d then
    v (h.choose - h.choose_spec.choose) else 0
  refine ⟨t, ?_⟩
  ext i j
  have h : ∃ a b : Fin n, (b.val : ℤ) - (a.val : ℤ) = (j.val : ℤ) - (i.val : ℤ) :=
    ⟨i, j, rfl⟩
  change (if h : ∃ a b : Fin n, (b.val : ℤ) - (a.val : ℤ) = (j.val : ℤ) - (i.val : ℤ) then
    v (h.choose - h.choose_spec.choose) else 0) = v (i - j)
  rw [dif_pos h]
  apply congrArg v
  have hDiff := h.choose_spec.choose_spec
  have hSum : h.choose.val + j.val = i.val + h.choose_spec.choose.val := by omega
  have hG := congrArg (fun k : ℕ => (k : Fin n)) hSum
  simp only [Nat.cast_add, Fin.cast_val_eq_self] at hG
  exact sub_eq_sub_iff_add_eq_add.mpr hG

/-- In dimension zero the unique matrix is both Toeplitz and circulant.
This endpoint needs no named coordinate zero or cyclic group instance.
Horn–Johnson 2013, §0.9.7.
atlas: structured-matrices-def -/
theorem exists_toeplitz_circulant_of_empty (A : Matrix (Fin 0) (Fin 0) ℝ) :
    (∃ t : ℤ → ℝ, A = toeplitzMatrix t) ∧
      (∃ v : Fin 0 → ℝ, A = Matrix.circulant v) := by
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;> ext i <;> exact i.elim0

/-- Circulants are exactly the ordinary Toeplitz matrices commuting with the
cyclic shift. Commutation alone already forces the circulant formula.
Horn–Johnson 2013, §0.9.7.
atlas: structured-matrices-def -/
theorem exists_circulant_iff_toeplitz_and_commute {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (∃ v : Fin n → ℝ, A = Matrix.circulant v) ↔
      (∃ t : ℤ → ℝ, A = toeplitzMatrix t) ∧
        A * cyclicShiftMatrix n = cyclicShiftMatrix n * A := by
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨t, ht⟩ := exists_toeplitzMatrix_eq_circulant v
    exact ⟨⟨t, ht.symm⟩, Matrix.circulant_mul_comm v _⟩
  · rintro ⟨_, hComm⟩
    exact (commute_cyclicShift_iff_exists_circulant A).mp hComm

end NLAlib
