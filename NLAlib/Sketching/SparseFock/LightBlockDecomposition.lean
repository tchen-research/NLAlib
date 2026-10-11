/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.LightOrbitCompression

/-!
# The finite direct sum of exact heavy/light pattern blocks

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

/-! ### Finite direct sum of the concrete Pattern blocks -/

/-- The possible light counts range from zero to the total number of sites.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
abbrev LightCount (m n : ℕ) := Fin (Fintype.card (Site m n) + 1)

/-- A block key consists of a heavy support and a possible light count.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
abbrev FockBlockKey (m n : ℕ) := Finset (Site m n) × LightCount m n

/-- The actual light support cardinality defines a valid bounded light count.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
def patternLightCount (p : Pattern m n) : LightCount m n :=
  ⟨p.light.card, Nat.lt_succ_of_le (Finset.card_le_univ p.light)⟩

/-- A pattern determines its heavy-support and light-count block key.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
def patternBlockKey (p : Pattern m n) : FockBlockKey m n :=
  (p.heavy, patternLightCount p)

/-- The full coordinate fiber of one block key is equivalent to that block's coordinates.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
def fullKeyFiberEquiv (q : FockBlockKey m n) :
    {x : Fin d × Pattern m n // patternBlockKey x.2 = q} ≃
      BlockIndex d q.1 q.2.1 where
  toFun x :=
    (x.1.1, ⟨x.1.2,
      congrArg Prod.fst x.2,
      congrArg (fun z : FockBlockKey m n ↦ z.2.1) x.2⟩)
  invFun z :=
    ⟨(z.1, z.2.1), by
      apply Prod.ext
      · exact z.2.2.1
      · apply Fin.ext
        exact z.2.2.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl

/-- Every full external/Fock coordinate belongs to one and only one finite
fixed-heavy/fixed-light block.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def fullIndexBlockEquiv :
    (Fin d × Pattern m n) ≃
      Σ q : FockBlockKey m n, BlockIndex d q.1 q.2.1 :=
  (Equiv.sigmaFiberEquiv
    (fun x : Fin d × Pattern m n ↦ patternBlockKey x.2)).symm.trans
      (Equiv.sigmaCongrRight fun q ↦ fullKeyFiberEquiv (d := d) q)

/-- The inverse block decomposition reconstructs the full coordinate from its block coordinate.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem fullIndexBlockEquiv_symm_apply
    (q : FockBlockKey m n) (z : BlockIndex d q.1 q.2.1) :
    (fullIndexBlockEquiv (d := d) (m := m) (n := n)).symm ⟨q, z⟩ =
      (z.1, z.2.1) := rfl

/-- A full coordinate vector restricts to a vector on each exact pattern block.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
def blockFiber (x : Fin d × Pattern m n → ℝ) (q : FockBlockKey m n) :
    BlockIndex d q.1 q.2.1 → ℝ :=
  fun z ↦ x (z.1, z.2.1)

/-- Full squared norm is the sum of coordinate energies of the exact block fibers.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem normSq_eq_sum_blockFiber (x : Fin d × Pattern m n → ℝ) :
    FiniteHilbert.normSq x =
      ∑ q : FockBlockKey m n, coordinateEnergy (blockFiber x q) := by
  classical
  have h := Equiv.sum_comp (fullIndexBlockEquiv (d := d) (m := m) (n := n))
    (fun z : Σ q : FockBlockKey m n, BlockIndex d q.1 q.2.1 ↦
      x ((fullIndexBlockEquiv (d := d) (m := m) (n := n)).symm z) ^ 2)
  rw [Fintype.sum_sigma] at h
  simpa [FiniteHilbert.normSq, coordinateEnergy, blockFiber] using h

/-- A block's grade is its light count plus twice its heavy count.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
def blockGrade (q : FockBlockKey m n) : ℕ := q.2.1 + 2 * q.1.card

/-- Every pattern in an exact block has that block's grade.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem grade_eq_blockGrade {q : FockBlockKey m n}
    (p : BlockPattern q.1 q.2.1) : p.1.grade = blockGrade q := by
  rw [Pattern.grade_eq_card_light_add_two_mul_card_heavy]
  simp [blockGrade, p.2.1, p.2.2]

/-- Right grade projection retains precisely the shared-leg entries with the selected input grade.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem ghat_mul_gradeProjection_apply
    (F : Frame n d) (nu : ℕ)
    (out inp : Fin d × Pattern m n) :
    (ghat (m := m) F *
      gradeProjection (d := d) (m := m) (n := n) nu) out inp =
      if inp.2.grade = nu then ghat (m := m) F out inp else 0 := by
  classical
  rw [gradeProjection, Matrix.mul_diagonal]
  by_cases h : inp.2.grade = nu <;> simp [h]

/-- The shared-leg operator has zero entries between distinct pattern block keys.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem ghat_apply_eq_zero_of_key_ne
    (F : Frame n d) {q q' : FockBlockKey m n}
    (out : BlockIndex d q.1 q.2.1)
    (inp : BlockIndex d q'.1 q'.2.1) (hne : q ≠ q') :
    ghat (m := m) F (out.1, out.2.1) (inp.1, inp.2.1) = 0 := by
  apply ghat_apply_eq_zero_of_block_ne
  by_contra hsame
  push Not at hsame
  apply hne
  apply Prod.ext
  · exact out.2.2.1.symm.trans (hsame.1.trans inp.2.2.1)
  · apply Fin.ext
    exact out.2.2.2.symm.trans (hsame.2.trans inp.2.2.2)

set_option maxHeartbeats 1000000 in
/-- The grade-restricted shared-leg operator acts on each block fiber by its actual block matrix.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem blockFiber_ghat_gradeProjection_mulVec
    (F : Frame n d) (nu : ℕ) (x : Fin d × Pattern m n → ℝ)
    (q : FockBlockKey m n) :
    blockFiber
      (Matrix.mulVec
        (ghat (m := m) F *
          gradeProjection (d := d) (m := m) (n := n) nu) x) q =
      if blockGrade q = nu then
        Matrix.mulVec (ghatBlock F q.1 q.2.1) (blockFiber x q)
      else 0 := by
  classical
  funext out
  let e := fullIndexBlockEquiv (d := d) (m := m) (n := n)
  let A := ghat (m := m) F *
    gradeProjection (d := d) (m := m) (n := n) nu
  change Matrix.mulVec A x (out.1, out.2.1) = _
  simp only [Matrix.mulVec, dotProduct]
  calc
    (∑ inp : Fin d × Pattern m n,
      A (out.1, out.2.1) inp * x inp) =
        ∑ z : Σ q : FockBlockKey m n, BlockIndex d q.1 q.2.1,
          A (out.1, out.2.1) (e.symm z) * x (e.symm z) := by
            have h := Equiv.sum_comp e
              (fun z : Σ q : FockBlockKey m n, BlockIndex d q.1 q.2.1 ↦
                A (out.1, out.2.1) (e.symm z) * x (e.symm z))
            simpa using h
    _ = ∑ q' : FockBlockKey m n,
          ∑ inp : BlockIndex d q'.1 q'.2.1,
            A (out.1, out.2.1) (inp.1, inp.2.1) *
              x (inp.1, inp.2.1) := by
          rw [Fintype.sum_sigma]
          rfl
    _ = ∑ inp : BlockIndex d q.1 q.2.1,
            A (out.1, out.2.1) (inp.1, inp.2.1) *
            x (inp.1, inp.2.1) := by
          apply Finset.sum_eq_single q
          · intro q' _hq' hq'ne
            apply Finset.sum_eq_zero
            intro inp _hinp
            change
              (ghat (m := m) F *
                gradeProjection (d := d) (m := m) (n := n) nu)
                  (out.1, out.2.1) (inp.1, inp.2.1) *
                x (inp.1, inp.2.1) = 0
            rw [ghat_mul_gradeProjection_apply]
            by_cases hg : inp.2.1.grade = nu
            · rw [if_pos hg, ghat_apply_eq_zero_of_key_ne F out inp
                (Ne.symm hq'ne)]
              simp
            · simp [hg]
          · intro hq
            exact False.elim (hq (Finset.mem_univ q))
    _ = ∑ inp : BlockIndex d q.1 q.2.1,
          (if blockGrade q = nu then ghatBlock F q.1 q.2.1 out inp else 0) *
            blockFiber x q inp := by
          apply Finset.sum_congr rfl
          intro inp _hinp
          rw [show A (out.1, out.2.1) (inp.1, inp.2.1) =
              if inp.2.1.grade = nu then
                ghat (m := m) F (out.1, out.2.1) (inp.1, inp.2.1)
              else 0 by
                exact ghat_mul_gradeProjection_apply F nu _ _]
          rw [grade_eq_blockGrade inp.2]
          rfl
    _ = (if blockGrade q = nu then
          ∑ inp, ghatBlock F q.1 q.2.1 out inp * blockFiber x q inp
        else 0) := by
          by_cases hg : blockGrade q = nu <;> simp [hg]
    _ = (if blockGrade q = nu then
          Matrix.mulVec (ghatBlock F q.1 q.2.1) (blockFiber x q)
        else 0) out := by
          by_cases hg : blockGrade q = nu <;>
            simp [hg, Matrix.mulVec, dotProduct]

/-- The shared-leg block with no light particles is the zero matrix.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem ghatBlock_zero_light
    (F : Frame n d) (T : Finset (Site m n)) :
    ghatBlock F T 0 = 0 := by
  ext out inp
  rw [← orbit_sum_labelledG_eq_ghatBlock F T 0 out inp]
  simp [labelledG]

end NLAlib.SparseFock.LightSectorConcrete
