/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.LightCrossCoordinates

/-!
# Concrete cross-map contractions on common spectator fibers

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

/-- One column-register slice of a vector on `D_l`.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def domainLSlice (k l : Fin ell) (hkl : k ≠ l)
    (y : ParticleDomainIndex m n ell l → ℝ)
    (fiber : CrossFiberIndex m n ell k l) : EVec n :=
  WithLp.toLp 2 fun j ↦ y (fiberToDomainL k l hkl (fiber, j))

/-- A fiber slice evaluates the original vector at the reconstructed second domain.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem domainLSlice_apply (k l : Fin ell) (hkl : k ≠ l)
    (y : ParticleDomainIndex m n ell l → ℝ)
    (fiber : CrossFiberIndex m n ell k l) (j : Fin n) :
    domainLSlice k l hkl y fiber j =
      y (fiberToDomainL k l hkl (fiber, j)) := rfl

/-- Pointwise, the typed cross map is exactly `U Uᵀ` on one column slice.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem crossMatrix_mulVec_fiber (F : Frame n d)
    (k l : Fin ell) (hkl : k ≠ l)
    (y : ParticleDomainIndex m n ell l → ℝ)
    (fiber : CrossFiberIndex m n ell k l) (i : Fin n) :
    (crossMatrix F k l hkl).mulVec y
        (fiberToDomainK k l hkl (fiber, i)) =
      columnGramApply F (domainLSlice k l hkl y fiber) i := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  let f : ParticleDomainIndex m n ell l → ℝ := fun zl ↦
    crossMatrix F k l hkl (fiberToDomainK k l hkl (fiber, i)) zl * y zl
  calc
    (∑ zl, crossMatrix F k l hkl
        (fiberToDomainK k l hkl (fiber, i)) zl * y zl) = ∑ zl, f zl := rfl
    _ = ∑ t : CrossFiberIndex m n ell k l × Fin n,
        f ((domainLEquiv k l hkl).symm t) :=
      ((domainLEquiv k l hkl).symm.sum_comp f).symm
    _ = ∑ j : Fin n, columnGram F i j *
        y (fiberToDomainL k l hkl (fiber, j)) := by
      simp only [f, crossMatrix, Equiv.coe_fn_symm_mk,
        domainLEquiv, domainKToFiber_fiberToDomainK,
        domainLToFiber_fiberToDomainL]
      rw [Fintype.sum_prod_type]
      simp
    _ = columnGramApply F (domainLSlice k l hkl y fiber) i := by
      rfl

/-- The fully typed off-diagonal matrix is a contraction in literal coordinate
energy.  Row transfer and all spectator coordinates are accounted for by the
two proved equivalences above.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem crossMatrix_energy_le (F : Frame n d)
    (k l : Fin ell) (hkl : k ≠ l)
    (y : ParticleDomainIndex m n ell l → ℝ) :
    coordinateEnergy ((crossMatrix F k l hkl).mulVec y) ≤
      coordinateEnergy y := by
  classical
  let outEnergy : ParticleDomainIndex m n ell k → ℝ := fun zk ↦
    ((crossMatrix F k l hkl).mulVec y zk) ^ 2
  let inEnergy : ParticleDomainIndex m n ell l → ℝ := fun zl ↦ y zl ^ 2
  calc
    coordinateEnergy ((crossMatrix F k l hkl).mulVec y) =
        ∑ zk, outEnergy zk := rfl
    _ = ∑ t : CrossFiberIndex m n ell k l × Fin n,
        outEnergy ((domainKEquiv k l hkl).symm t) :=
      ((domainKEquiv k l hkl).symm.sum_comp outEnergy).symm
    _ = ∑ fiber : CrossFiberIndex m n ell k l,
        ∑ i : Fin n,
          (columnGramApply F (domainLSlice k l hkl y fiber) i) ^ 2 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro fiber _hfiber
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [outEnergy, domainKEquiv, Equiv.coe_fn_symm_mk]
      rw [crossMatrix_mulVec_fiber]
    _ ≤ ∑ fiber : CrossFiberIndex m n ell k l,
        ∑ j : Fin n, (domainLSlice k l hkl y fiber j) ^ 2 := by
      apply Finset.sum_le_sum
      intro fiber _hfiber
      have h := columnGram_energy_le F (domainLSlice k l hkl y fiber)
      rw [normSq_eq_coordinateEnergy, normSq_eq_coordinateEnergy] at h
      exact h
    _ = ∑ fiber : CrossFiberIndex m n ell k l, ∑ j : Fin n,
        inEnergy (fiberToDomainL k l hkl (fiber, j)) := by rfl
    _ = ∑ t : CrossFiberIndex m n ell k l × Fin n,
        inEnergy ((domainLEquiv k l hkl).symm t) := by
      exact (Fintype.sum_prod_type (fun t :
        CrossFiberIndex m n ell k l × Fin n ↦
          inEnergy ((domainLEquiv k l hkl).symm t))).symm
    _ = ∑ zl, inEnergy zl :=
      (domainLEquiv k l hkl).symm.sum_comp inEnergy
    _ = coordinateEnergy y := rfl

/-- Reconstruct a labelled word from a cross fiber and the two distinguished
column coordinates: `j` at particle `k` and `i` at particle `l`.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def wordOfCross (k l : Fin ell) (_hkl : k ≠ l)
    (fiber : CrossFiberIndex m n ell k l) (i j : Fin n) :
    Fin ell → Site m n :=
  fun t ↦ if htk : t = k then (fiber.1.1, j)
    else if htl : t = l then (fiber.1.2, i)
    else fiber.2 ⟨t, htk, htl⟩

/-- The cross word inserts the second column into its first distinguished slot.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem wordOfCross_at_k (k l : Fin ell) (hkl : k ≠ l)
    (fiber : CrossFiberIndex m n ell k l) (i j : Fin n) :
    wordOfCross k l hkl fiber i j k = (fiber.1.1, j) := by
  simp [wordOfCross]

/-- The cross word inserts the first column into its second distinguished slot.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem wordOfCross_at_l (k l : Fin ell) (hkl : k ≠ l)
    (fiber : CrossFiberIndex m n ell k l) (i j : Fin n) :
    wordOfCross k l hkl fiber i j l = (fiber.1.2, i) := by
  simp [wordOfCross,  Ne.symm hkl]

/-- The cross word retains every common spectator site.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem wordOfCross_off (k l : Fin ell) (hkl : k ≠ l)
    (fiber : CrossFiberIndex m n ell k l) (i j : Fin n)
    (t : Fin ell) (htk : t ≠ k) (htl : t ≠ l) :
    wordOfCross k l hkl fiber i j t = fiber.2 ⟨t, htk, htl⟩ := by
  simp [wordOfCross, htk, htl]

/-- Canonical decomposition of the labelled shared-leg space for a pair of
distinct particle labels.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def labelledCrossEquiv (k l : Fin ell) (hkl : k ≠ l) :
    LabelledIndex d m n ell ≃
      (CrossFiberIndex m n ell k l × Fin n × Fin n × Fin d) where
  toFun out :=
    ((((out.2 k).1, (out.2 l).1),
        fun t ↦ out.2 t.1),
      (out.2 l).2, (out.2 k).2, out.1)
  invFun z :=
    (z.2.2.2, wordOfCross k l hkl z.1 z.2.1 z.2.2.1)
  left_inv out := by
    apply Prod.ext
    · rfl
    · funext t
      by_cases htk : t = k
      · subst t
        simp
      · by_cases htl : t = l
        · subst t
          simp []
        · simp [wordOfCross, htk, htl]
  right_inv z := by
    rcases z with ⟨⟨⟨r, s⟩, rest⟩, i, j, a⟩
    simp only
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext <;> simp [wordOfCross,  Ne.symm hkl]
      · funext t
        simp [wordOfCross, t.2.1, t.2.2]
    · apply Prod.ext
      · simp [wordOfCross,  Ne.symm hkl]
      · apply Prod.ext <;> simp [wordOfCross]

/-- The first domain of a cross word has its stated fiber and column coordinates.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem domainKToFiber_domainOf_crossWord
    (k l : Fin ell) (hkl : k ≠ l)
    (fiber : CrossFiberIndex m n ell k l) (i j : Fin n) :
    domainKToFiber k l hkl (domainOfWord k (wordOfCross k l hkl fiber i j)) =
      (fiber, i) := by
  rw [← domainKToFiber_fiberToDomainK k l hkl (fiber, i)]
  congr 1
  apply Prod.ext
  · simp [domainOfWord, fiberToDomainK, wordOfCross]
  · funext t
    by_cases htl : t.1 = l
    · subst l
      simp [domainOfWord, fiberToDomainK, wordOfCross,  Ne.symm hkl]
    · simp [domainOfWord, fiberToDomainK, wordOfCross, t.2, htl
        ]

/-- The second domain of a cross word has its stated fiber and column coordinates.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem domainLToFiber_domainOf_crossWord
    (k l : Fin ell) (hkl : k ≠ l)
    (fiber : CrossFiberIndex m n ell k l) (i j : Fin n) :
    domainLToFiber k l hkl (domainOfWord l (wordOfCross k l hkl fiber i j)) =
      (fiber, j) := by
  rw [← domainLToFiber_fiberToDomainL k l hkl (fiber, j)]
  congr 1
  apply Prod.ext
  · simp [domainOfWord, fiberToDomainL, wordOfCross,  Ne.symm hkl]
  · funext t
    by_cases htk : t.1 = k
    · subst k
      simp [domainOfWord, fiberToDomainL, wordOfCross,  Ne.symm hkl]
    · simp [domainOfWord, fiberToDomainL, wordOfCross, t.2, htk,
        Ne.symm hkl]

/-- Equality with a cross word's first domain is equivalent to equality of fiber coordinates.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem eq_domainOf_crossWord_k_iff
    (k l : Fin ell) (hkl : k ≠ l)
    (zk : ParticleDomainIndex m n ell k)
    (fiber : CrossFiberIndex m n ell k l) (i j : Fin n) :
    zk = domainOfWord k (wordOfCross k l hkl fiber i j) ↔
      domainKToFiber k l hkl zk = (fiber, i) := by
  constructor
  · intro h
    rw [h]
    exact domainKToFiber_domainOf_crossWord k l hkl fiber i j
  · intro h
    apply (domainKEquiv k l hkl).injective
    change domainKToFiber k l hkl zk =
      domainKToFiber k l hkl
        (domainOfWord k (wordOfCross k l hkl fiber i j))
    simpa using h

/-- Equality with a cross word's second domain is equivalent to equality of fiber coordinates.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem eq_domainOf_crossWord_l_iff
    (k l : Fin ell) (hkl : k ≠ l)
    (zl : ParticleDomainIndex m n ell l)
    (fiber : CrossFiberIndex m n ell k l) (i j : Fin n) :
    zl = domainOfWord l (wordOfCross k l hkl fiber i j) ↔
      domainLToFiber k l hkl zl = (fiber, j) := by
  constructor
  · intro h
    rw [h]
    exact domainLToFiber_domainOf_crossWord k l hkl fiber i j
  · intro h
    apply (domainLEquiv k l hkl).injective
    change domainLToFiber k l hkl zl =
      domainLToFiber k l hkl
        (domainOfWord l (wordOfCross k l hkl fiber i j))
    simpa using h

set_option maxHeartbeats 1000000 in
/-- Direct substitution into the literal insertion matrices gives exactly the
typed row-transfer/column-projection cross map.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem transpose_VMatrix_mul_cross (F : Frame n d)
    (k l : Fin ell) (hkl : k ≠ l) :
    (VMatrix (m := m) F k).transpose * VMatrix (m := m) F l =
      crossMatrix F k l hkl := by
  classical
  ext zk zl
  simp only [Matrix.mul_apply, Matrix.transpose_apply, VMatrix]
  let f : LabelledIndex d m n ell → ℝ := fun out ↦
    (if zk = domainOfWord k out.2 then F.u (out.2 k).2 out.1 else 0) *
      (if zl = domainOfWord l out.2 then F.u (out.2 l).2 out.1 else 0)
  let xk := domainKToFiber k l hkl zk
  let xl := domainLToFiber k l hkl zl
  change (∑ out, f out) = if xk.1 = xl.1 then columnGram F xk.2 xl.2 else 0
  calc
    (∑ out, f out) =
        ∑ t : CrossFiberIndex m n ell k l × Fin n × Fin n × Fin d,
          f ((labelledCrossEquiv k l hkl).symm t) :=
      ((labelledCrossEquiv k l hkl).symm.sum_comp f).symm
    _ = if xk.1 = xl.1 then columnGram F xk.2 xl.2 else 0 := by
      simp only [f, xk, xl, labelledCrossEquiv, Equiv.coe_fn_symm_mk,
        wordOfCross_at_k, wordOfCross_at_l,
        eq_domainOf_crossWord_k_iff, eq_domainOf_crossWord_l_iff]
      rw [Fintype.sum_prod_type]
      simp_rw [sum_prod3]
      rcases hxk : domainKToFiber k l hkl zk with ⟨fk, ik⟩
      rcases hxl : domainLToFiber k l hkl zl with ⟨fl, jl⟩
      by_cases hf : fk = fl
      · subst fl
        simp [columnGram, PiLp.inner_apply, ite_and]
      · simp [hf, ite_and]

end NLAlib.SparseFock.LightSectorConcrete
