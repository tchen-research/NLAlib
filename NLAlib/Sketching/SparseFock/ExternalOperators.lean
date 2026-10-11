/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.FiniteSiteOperators
import Mathlib.Tactic

set_option autoImplicit false

/-!
# External sparse-Fock tensor operators

Literal external rank-one factors and finite pattern kernels form the physical matrices and their grade-homogeneity API.
Ported from `SparseFockFormal.ExternalOperators` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock

namespace ExternalOperator

open BandInventory FiniteOperator

variable {d m n : ℕ}

/-- A matrix on the external row leg tensored with the finite sparse-Fock basis.

Source: ported from `SparseFockFormal.ExternalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
abbrev FullOp (d m n : ℕ) :=
  Matrix (Fin d × Pattern m n) (Fin d × Pattern m n) ℝ

/-- Entrywise tensor product of an external matrix and a sparse-Fock matrix.

Source: ported from `SparseFockFormal.ExternalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def externalTensor (M : Matrix (Fin d) (Fin d) ℝ) (K : FockOp m n) :
    FullOp d m n := fun out inp => M out.1 inp.1 * K out.2 inp.2

/-- Transposing an external tensor transposes both its external and Fock factors.
Source: ported from `SparseFockFormal.ExternalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem transpose_externalTensor
    (M : Matrix (Fin d) (Fin d) ℝ) (K : FockOp m n) :
    (externalTensor M K).transpose = externalTensor M.transpose K.transpose := by
  ext out inp
  rfl

/-- The external rank-one coefficient `|u><v|`.

Source: ported from `SparseFockFormal.ExternalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def outer (u v : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun a b => u a * v b

/-- Transposing an external rank-one matrix exchanges its two vectors.
Source: ported from `SparseFockFormal.ExternalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem transpose_outer (u v : Fin d → ℝ) :
    (outer u v).transpose = outer v u := by
  ext a b
  simp [outer, Matrix.transpose_apply, mul_comm]

/-- One ordered, externally weighted word at the two sites `(r,i)` and `(r,j)`.

Source: ported from `SparseFockFormal.ExternalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def orderedWordTerm
    (u : Fin n → Fin d → ℝ) (r : Fin m) (i j : Fin n) (w : Word) :
    FullOp d m n :=
  externalTensor (outer (u i) (u j)) (wordKernel (r, i) (r, j) w)

/-- Transposition swaps the external vectors and the two sites and reverses both
local arrows.  This is the precise ordered-word adjoint convention.

Source: ported from `SparseFockFormal.ExternalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem transpose_orderedWordTerm
    (u : Fin n → Fin d → ℝ) (r : Fin m) (i j : Fin n) (w : Word) :
    (orderedWordTerm u r i j w).transpose =
      orderedWordTerm u r j i w.orderedAdjoint := by
  rw [orderedWordTerm, transpose_externalTensor, transpose_outer,
    transpose_wordKernel]
  rfl

/-- The external-coordinate grade is the integer occupation grade of its Fock pattern.
Source: ported from `SparseFockFormal.ExternalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def gradeZ (x : Fin d × Pattern m n) : ℤ := FiniteOperator.gradeZ x.2

/-- Grade homogeneity on the full external/Fock matrix; the external leg has
grade zero.

Source: ported from `SparseFockFormal.ExternalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def Homogeneous (delta : ℤ) (T : FullOp d m n) : Prop :=
  ∀ ⦃out inp⦄, T out inp ≠ 0 → gradeZ out = gradeZ inp + delta

/-- An external tensor inherits its Fock factor's grade shift.
Source: ported from `SparseFockFormal.ExternalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem externalTensor_homogeneous {delta : ℤ}
    {M : Matrix (Fin d) (Fin d) ℝ} {K : FockOp m n}
    (hK : FiniteOperator.Homogeneous delta K) :
    Homogeneous delta (externalTensor M K) := by
  intro out inp hnonzero
  have hKnonzero : K out.2 inp.2 ≠ 0 := (mul_ne_zero_iff.mp hnonzero).2
  exact hK hKnonzero

/-- A physical distinct-site word term has its two-leg word's grade shift.
Source: ported from `SparseFockFormal.ExternalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem orderedWordTerm_homogeneous
    (u : Fin n → Fin d → ℝ) (r : Fin m) {i j : Fin n} (hij : i ≠ j)
    (w : Word) :
    Homogeneous w.degree (orderedWordTerm u r i j w) := by
  apply externalTensor_homogeneous
  apply wordKernel_homogeneous
  intro hsite
  exact hij (congrArg Prod.snd hsite)

end ExternalOperator

end NLAlib.SparseFock
