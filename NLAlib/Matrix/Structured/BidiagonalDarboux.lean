import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Finite bidiagonal Darboux factors

Monic Jacobi matrices use a unit superdiagonal. Their finite lower/upper
bidiagonal factors have an exact terminal-coordinate correction after reversing
the factors. This correction is necessary even when all pivots are nonzero.
Source: Gautschi (2004), Theorem 1.33; operator derivations OP20--OP24.
-/

noncomputable section
open Matrix Finset
open scoped Matrix
namespace NLAlib
variable {𝕜 : Type*} [CommRing 𝕜]

/-- The unit lower bidiagonal factor with subdiagonal `e_j`.
Source: finite monic Darboux factorization, OP24. -/
def darbouxLowerMatrix (n : ℕ) (e : ℕ → 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  1 + Matrix.of (fun (i j : Fin n) => if j.val+1 = i.val then e j.val else 0)

/-- The upper bidiagonal factor with diagonal `q_j` and unit superdiagonal.
Source: finite monic Darboux factorization, OP24. -/
def darbouxUpperMatrix (n : ℕ) (q : ℕ → 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  diagonal (fun i : Fin n => q i.val) +
    Matrix.of (fun (i j : Fin n) => if i.val+1 = j.val then 1 else 0)

/-- The nonsymmetric monic Jacobi matrix: diagonal `a_j`, unit superdiagonal,
and subdiagonal `b_j` at row `j`. Source: monic recurrence, OP24. -/
def monicJacobiMatrix (n : ℕ) (a b : ℕ → 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  diagonal (fun i : Fin n => a i.val) +
    Matrix.of (fun (i j : Fin n) => if i.val+1 = j.val then 1 else 0) +
    Matrix.of (fun (i j : Fin n) => if j.val+1 = i.val then b i.val else 0)

/-- The last-coordinate diagonal projector, also defined in empty dimension.
Source: finite Darboux boundary correction, OP24. -/
def terminalCoordinateMatrix (n : ℕ) : Matrix (Fin n) (Fin n) 𝕜 :=
  diagonal (fun i => if i.val+1 = n then 1 else 0)

/-- Left multiplication by a unit lower bidiagonal matrix uses only the current
row and its immediate predecessor, including the first-row boundary. -/
theorem darbouxLowerMatrix_mul_apply {n : ℕ} (e : ℕ → 𝕜)
    (B : Matrix (Fin n) (Fin n) 𝕜) (i j : Fin n) :
    (darbouxLowerMatrix n e * B) i j = B i j +
      if hi : 0 < i.val then e (i.val-1) * B ⟨i.val-1, by omega⟩ j else 0 := by
  rw [darbouxLowerMatrix, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  by_cases hi : 0 < i.val
  · rw [dif_pos hi]
    let k : Fin n := ⟨i.val-1, by omega⟩
    rw [sum_eq_single k]
    · simp [k, show i.val-1+1 = i.val by omega]
    · intro l _ hlk
      have hne : l.val+1 ≠ i.val := by intro h; apply hlk; apply Fin.ext; simp [k]; omega
      simp [hne]
    · simp
  · rw [dif_neg hi]
    apply sum_eq_zero
    intro k _
    have hne : k.val+1 ≠ i.val := by omega
    simp [hne]

private theorem darbouxUpperMatrix_mul_apply {n : ℕ} (q : ℕ → 𝕜)
    (B : Matrix (Fin n) (Fin n) 𝕜) (i j : Fin n) :
    (darbouxUpperMatrix n q * B) i j = q i.val * B i j +
      if hi : i.val+1 < n then B ⟨i.val+1, hi⟩ j else 0 := by
  rw [darbouxUpperMatrix, Matrix.add_mul, Matrix.add_apply, diagonal_mul, Matrix.mul_apply]
  congr 1
  by_cases hi : i.val+1 < n
  · rw [dif_pos hi]
    let k : Fin n := ⟨i.val+1, hi⟩
    rw [sum_eq_single k]
    · simp [k]
    · intro l _ hlk
      have hne : i.val+1 ≠ l.val := by intro h; apply hlk; apply Fin.ext; exact h.symm
      simp [hne]
    · simp
  · rw [dif_neg hi]
    apply sum_eq_zero
    intro k _
    have hne : i.val+1 ≠ k.val := by omega
    simp [hne]

/-- The lower/upper factors give the monic Jacobi entries `q_j+e_(j-1)`
and `q_(j-1)e_(j-1)`, with zero elimination term in the first row.
Source: finite Darboux factorization, OP24. -/
theorem darbouxLowerMatrix_mul_darbouxUpperMatrix (n : ℕ) (q e : ℕ → 𝕜) :
    darbouxLowerMatrix n e * darbouxUpperMatrix n q =
      monicJacobiMatrix n (fun i => q i + if i=0 then 0 else e (i-1))
        (fun i => q (i-1) * e (i-1)) := by
  ext i j
  rw [darbouxLowerMatrix_mul_apply]
  simp only [darbouxUpperMatrix, monicJacobiMatrix, Matrix.add_apply, diagonal_apply]
  split_ifs <;> simp_all [Fin.ext_iff] <;> try omega
  all_goals split_ifs
  all_goals try simp_all
  all_goals try omega
  all_goals ring

/-- Reversing finite bidiagonal factors gives diagonal `q_j+e_j` except at
the last row, where the absent next coordinate removes `e_j`.
Source: finite Darboux factorization, OP24. -/
theorem darbouxUpperMatrix_mul_darbouxLowerMatrix (n : ℕ) (q e : ℕ → 𝕜) :
    darbouxUpperMatrix n q * darbouxLowerMatrix n e =
      monicJacobiMatrix n
        (fun i => q i + if i+1<n then e i else 0)
        (fun i => q i * e (i-1)) := by
  ext i j
  rw [darbouxUpperMatrix_mul_apply]
  simp only [darbouxLowerMatrix, monicJacobiMatrix, Matrix.add_apply, diagonal_apply,
    Matrix.one_apply]
  split_ifs <;> simp_all [Fin.ext_iff] <;> try omega
  all_goals split_ifs
  all_goals try simp_all
  all_goals try omega
  all_goals have hidx : i.val-1 = j.val := by omega
  all_goals simp only [hidx]

/-- The finite monic Darboux reversal has its exact last-coordinate correction.
The formula also includes empty dimension, where both sides are empty matrices.
Source: Gautschi (2004), Theorem 1.33; operator derivations OP24.
atlas: kernel-polynomials-christoffel (partial) -/
theorem monicJacobiMatrix_eq_darbouxUpperMatrix_mul_darbouxLowerMatrix_add_boundary
    (n : ℕ) (q e : ℕ → 𝕜) :
    monicJacobiMatrix n (fun i => q i + e i) (fun i => q i * e (i-1)) =
      darbouxUpperMatrix n q * darbouxLowerMatrix n e +
        e (n-1) • terminalCoordinateMatrix n := by
  rw [darbouxUpperMatrix_mul_darbouxLowerMatrix]
  ext i j
  simp only [monicJacobiMatrix, terminalCoordinateMatrix, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, diagonal_apply]
  split_ifs <;> simp_all [Fin.ext_iff] <;> try omega
  all_goals split_ifs
  all_goals try simp_all
  all_goals have hidx : n-1 = j.val := by omega
  all_goals rw [hidx]

end NLAlib
