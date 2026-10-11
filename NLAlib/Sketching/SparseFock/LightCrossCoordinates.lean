/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.LightLabelledSlots

/-!
# Common spectator coordinates for two particle slots

Partition of the literal shared-leg proof from sparse-Fock commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`.
The original `LightSectorConcrete` import re-exports this unchanged namespace.
Supports the `sparse-ose` moment proof.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
namespace NLAlib.SparseFock.LightSectorConcrete
open ParsevalFrame LocalOperator FiniteOperator ExternalOperator FiniteHilbert
variable {d m n ell : ℕ}

/-! ### Explicit typing of the off-diagonal cross maps -/

/-- The common spectator slots omit two distinguished particle slots.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
abbrev RestParticle (ell : ℕ) (k l : Fin ell) :=
  {j : Fin ell // j ≠ k ∧ j ≠ l}

/-- A cross fiber retains the two row registers and all common spectators.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
abbrev CrossFiberIndex (m n ell : ℕ) (k l : Fin ell) :=
  (Fin m × Fin m) × (RestParticle ell k l → Site m n)

/-- A sum over three product coordinates is the corresponding iterated finite sum.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem sum_prod3 {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : A × B × C → ℝ) :
    (∑ t, f t) = ∑ a, ∑ b, ∑ c, f (a, b, c) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Fintype.sum_prod_type]

/-- Coordinates on `D_k`: extra row of `k`, row and column of particle `l`,
and all remaining spectator particles.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def domainKToFiber (k l : Fin ell) (hkl : k ≠ l)
    (z : ParticleDomainIndex m n ell k) :
    CrossFiberIndex m n ell k l × Fin n :=
  (((z.1, (z.2 ⟨l, Ne.symm hkl⟩).1),
      fun j ↦ z.2 ⟨j.1, j.2.1⟩),
    (z.2 ⟨l, Ne.symm hkl⟩).2)

/-- A common fiber and column reconstruct the first distinguished particle domain.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
def fiberToDomainK (k l : Fin ell) (_hkl : k ≠ l)
    (z : CrossFiberIndex m n ell k l × Fin n) :
    ParticleDomainIndex m n ell k :=
  (z.1.1.1, fun j ↦
    if hjl : j.1 = l then (z.1.1.2, z.2)
    else z.1.2 ⟨j.1, j.2, hjl⟩)

/-- The first particle domain is equivalent to its common fiber and one column coordinate.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
def domainKEquiv (k l : Fin ell) (hkl : k ≠ l) :
    ParticleDomainIndex m n ell k ≃
      (CrossFiberIndex m n ell k l × Fin n) where
  toFun := domainKToFiber k l hkl
  invFun := fiberToDomainK k l hkl
  left_inv z := by
    apply Prod.ext
    · rfl
    · funext j
      by_cases hjl : j.1 = l
      · subst l
        simp [fiberToDomainK, domainKToFiber]
      · simp [fiberToDomainK, domainKToFiber, hjl]
  right_inv z := by
    rcases z with ⟨⟨⟨r, s⟩, rest⟩, i⟩
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext <;> simp [domainKToFiber, fiberToDomainK]
      · funext j
        simp [domainKToFiber, fiberToDomainK, j.2.2]
    · simp [domainKToFiber, fiberToDomainK]

/-- Extracting the common fiber after reconstruction recovers its original coordinates.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem domainKToFiber_fiberToDomainK (k l : Fin ell)
    (hkl : k ≠ l) (z : CrossFiberIndex m n ell k l × Fin n) :
    domainKToFiber k l hkl (fiberToDomainK k l hkl z) = z :=
  (domainKEquiv k l hkl).apply_symm_apply z

/-- Coordinates on `D_l`, ordered in the same cross-fiber convention:
particle-`k` row, extra row of `l`, remaining spectators, particle-`k` column.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def domainLToFiber (k l : Fin ell) (hkl : k ≠ l)
    (z : ParticleDomainIndex m n ell l) :
    CrossFiberIndex m n ell k l × Fin n :=
  ((((z.2 ⟨k, hkl⟩).1, z.1),
      fun j ↦ z.2 ⟨j.1, j.2.2⟩),
    (z.2 ⟨k, hkl⟩).2)

/-- A common fiber and column reconstruct the second distinguished particle domain.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
def fiberToDomainL (k l : Fin ell) (_hkl : k ≠ l)
    (z : CrossFiberIndex m n ell k l × Fin n) :
    ParticleDomainIndex m n ell l :=
  (z.1.1.2, fun j ↦
    if hjk : j.1 = k then (z.1.1.1, z.2)
    else z.1.2 ⟨j.1, hjk, j.2⟩)

/-- The second particle domain is equivalent to its common fiber and one column coordinate.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
def domainLEquiv (k l : Fin ell) (hkl : k ≠ l) :
    ParticleDomainIndex m n ell l ≃
      (CrossFiberIndex m n ell k l × Fin n) where
  toFun := domainLToFiber k l hkl
  invFun := fiberToDomainL k l hkl
  left_inv z := by
    apply Prod.ext
    · rfl
    · funext j
      by_cases hjk : j.1 = k
      · subst k
        simp [fiberToDomainL, domainLToFiber]
      · simp [fiberToDomainL, domainLToFiber, hjk]
  right_inv z := by
    rcases z with ⟨⟨⟨r, s⟩, rest⟩, i⟩
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext <;> simp [domainLToFiber, fiberToDomainL]
      · funext j
        simp [domainLToFiber, fiberToDomainL, j.2.1]
    · simp [domainLToFiber, fiberToDomainL]

/-- Extracting the second common fiber after reconstruction recovers its original coordinates.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem domainLToFiber_fiberToDomainL (k l : Fin ell)
    (hkl : k ≠ l) (z : CrossFiberIndex m n ell k l × Fin n) :
    domainLToFiber k l hkl (fiberToDomainL k l hkl z) = z :=
  (domainLEquiv k l hkl).apply_symm_apply z

/-- The explicitly typed cross-map matrix.  It is a row-register permutation,
a copy of the concrete column Gram matrix, and identity on all spectators.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def crossMatrix (F : Frame n d) (k l : Fin ell) (hkl : k ≠ l) :
    Matrix (ParticleDomainIndex m n ell k)
      (ParticleDomainIndex m n ell l) ℝ :=
  fun zk zl ↦
    let xk := domainKToFiber k l hkl zk
    let xl := domainLToFiber k l hkl zl
    if xk.1 = xl.1 then columnGram F xk.2 xl.2 else 0

/-- Squared coordinate energy on any finite real coordinate space.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def coordinateEnergy {I : Type*} [Fintype I] (x : I → ℝ) : ℝ :=
  ∑ i, x i ^ 2

/-- Euclidean squared norm agrees with the sum of squared coordinate entries.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem normSq_eq_coordinateEnergy (x : EVec n) :
    ParsevalFrame.normSq x = coordinateEnergy (fun i ↦ x i) := by
  rw [ParsevalFrame.normSq_eq_norm_sq, EuclideanSpace.norm_sq_eq]
  simp [coordinateEnergy, Real.norm_eq_abs, pow_two]

end NLAlib.SparseFock.LightSectorConcrete
