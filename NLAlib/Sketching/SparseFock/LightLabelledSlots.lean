/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.LightOperators

/-!
# Labelled particle slots and their individual synthesis matrices

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

/-! ## Labelled-particle realization -/

/-- The labelled-particle coordinates consist of an external leg and one site per particle slot.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
abbrev LabelledIndex (d m n ell : ℕ) :=
  Fin d × (Fin ell → Site m n)

/-- The spectator slots omit one distinguished particle slot.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
abbrev OtherParticle (ell : ℕ) (k : Fin ell) :=
  {j : Fin ell // j ≠ k}

/-- The domain of a particle map retains its row and all spectator sites.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
abbrev ParticleDomainIndex (m n ell : ℕ) (k : Fin ell) :=
  Fin m × (OtherParticle ell k → Site m n)

/-- Remove particle slot `k`, retaining its row in the extra row register.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def domainOfWord {ell : ℕ} (k : Fin ell) (w : Fin ell → Site m n) :
    ParticleDomainIndex m n ell k :=
  ((w k).1, fun j ↦ w j.1)

/-- Two particle domains agree exactly when their retained row and spectator sites agree.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem domainOfWord_eq_iff {ell : ℕ} (k : Fin ell)
    (w v : Fin ell → Site m n) :
    domainOfWord k w = domainOfWord k v ↔
      (w k).1 = (v k).1 ∧ ∀ j, j ≠ k → w j = v j := by
  constructor
  · intro h
    constructor
    · exact congrArg
        (fun z : ParticleDomainIndex m n ell k ↦ z.1) h
    · intro j hj
      have hfun := congrArg
        (fun z : ParticleDomainIndex m n ell k ↦ z.2) h
      exact congrFun hfun ⟨j, hj⟩
  · rintro ⟨hrow, hoff⟩
    apply Prod.ext
    · exact hrow
    · funext j
      exact hoff j.1 j.2

/-- Reinsert a column coordinate into the omitted particle slot.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def wordOfDomain {ell : ℕ} (k : Fin ell)
    (z : ParticleDomainIndex m n ell k) (i : Fin n) :
    Fin ell → Site m n :=
  fun j ↦ if h : j = k then (z.1, i) else z.2 ⟨j, h⟩

/-- Reconstructing a word inserts the selected column into its distinguished slot.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem wordOfDomain_at {ell : ℕ} (k : Fin ell)
    (z : ParticleDomainIndex m n ell k) (i : Fin n) :
    wordOfDomain k z i k = (z.1, i) := by
  simp [wordOfDomain]

/-- Reconstructing a word retains every spectator site.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem wordOfDomain_off {ell : ℕ} (k : Fin ell)
    (z : ParticleDomainIndex m n ell k) (i : Fin n)
    (j : Fin ell) (hjk : j ≠ k) :
    wordOfDomain k z i j = z.2 ⟨j, hjk⟩ := by
  simp [wordOfDomain, hjk]

/-- Extracting the domain of a reconstructed word recovers the original domain.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem domainOfWord_wordOfDomain {ell : ℕ} (k : Fin ell)
    (z : ParticleDomainIndex m n ell k) (i : Fin n) :
    domainOfWord k (wordOfDomain k z i) = z := by
  apply Prod.ext
  · simp [domainOfWord]
  · funext j
    simp [domainOfWord, wordOfDomain, j.2]

/-- Reconstructing a word with its original distinguished column recovers the word.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
@[simp] theorem wordOfDomain_domainOfWord {ell : ℕ} (k : Fin ell)
    (w : Fin ell → Site m n) :
    wordOfDomain k (domainOfWord k w) (w k).2 = w := by
  funext j
  by_cases hjk : j = k
  · subst j
    simp [domainOfWord]
  · simp [wordOfDomain, domainOfWord, hjk]

/-- `H_ell` is exactly domain data, the omitted column, and the external
coordinate.  This equivalence is used to evaluate all finite sums without a
dimension-counting assumption.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def labelledIndexEquiv (k : Fin ell) :
    LabelledIndex d m n ell ≃
      (ParticleDomainIndex m n ell k × Fin n × Fin d) where
  toFun out := (domainOfWord k out.2, (out.2 k).2, out.1)
  invFun z := (z.2.2, wordOfDomain k z.1 z.2.1)
  left_inv out := by
    apply Prod.ext
    · rfl
    · exact wordOfDomain_domainOfWord k out.2
  right_inv z := by
    rcases z with ⟨domain, i, a⟩
    simp

/-- The insertion matrix `V_k` from the exact typed particle domain into the
labelled shared-leg space.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def VMatrix (F : Frame n d) (k : Fin ell) :
    Matrix (LabelledIndex d m n ell) (ParticleDomainIndex m n ell k) ℝ :=
  fun out z ↦
    if z = domainOfWord k out.2 then F.u (out.2 k).2 out.1 else 0

/-- `Q_k = V_k V_kᵀ`, written as a literal labelled-coordinate matrix.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def qSlot (F : Frame n d) (k : Fin ell) :
    Matrix (LabelledIndex d m n ell) (LabelledIndex d m n ell) ℝ :=
  fun out inp ↦
    if domainOfWord k out.2 = domainOfWord k inp.2 then
      F.u (out.2 k).2 out.1 * F.u (inp.2 k).2 inp.1
    else 0

/-- A slot permutation relabels the particle coordinates and preserves the external leg.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
def relabelSlots (pi : Equiv.Perm (Fin ell))
    (out : LabelledIndex d m n ell) : LabelledIndex d m n ell :=
  (out.1, fun k ↦ out.2 (pi k))

/-- Relabelling slots moves the one-slot operator to the permuted slot.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem qSlot_relabelSlots (F : Frame n d) (k : Fin ell)
    (pi : Equiv.Perm (Fin ell))
    (out inp : LabelledIndex d m n ell) :
    qSlot F k (relabelSlots pi out) (relabelSlots pi inp) =
      qSlot F (pi k) out inp := by
  classical
  have hdomain :
      domainOfWord k (relabelSlots pi out).2 =
          domainOfWord k (relabelSlots pi inp).2 ↔
        domainOfWord (pi k) out.2 = domainOfWord (pi k) inp.2 := by
    rw [domainOfWord_eq_iff, domainOfWord_eq_iff]
    constructor
    · rintro ⟨hrow, hoff⟩
      refine ⟨hrow, ?_⟩
      intro j hj
      have hj' : pi.symm j ≠ k := by
        intro heq
        apply hj
        simpa using congrArg pi heq
      simpa [relabelSlots] using hoff (pi.symm j) hj'
    · rintro ⟨hrow, hoff⟩
      refine ⟨hrow, ?_⟩
      intro j hj
      have hpij : pi j ≠ pi k := fun h ↦ hj (pi.injective h)
      simpa [relabelSlots] using hoff (pi j) hpij
  simp only [qSlot]
  rw [if_congr hdomain rfl rfl]
  rfl

/-- A particle synthesis matrix times its transpose is the one-slot shared-leg operator.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem VMatrix_mul_transpose (F : Frame n d) (k : Fin ell) :
    VMatrix (m := m) F k * (VMatrix (m := m) F k).transpose =
      qSlot (m := m) F k := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.transpose_apply, VMatrix, qSlot]
  by_cases hdom : domainOfWord k out.2 = domainOfWord k inp.2
  · rw [if_pos hdom]
    rw [hdom]
    simp
  · rw [if_neg hdom]
    apply Finset.sum_eq_zero
    intro z _hz
    by_cases hzout : z = domainOfWord k out.2
    · have hzinp : z ≠ domainOfWord k inp.2 := by
        intro heq
        exact hdom (hzout.symm.trans heq)
      rw [if_pos hzout, if_neg hzinp]
      simp
    · rw [if_neg hzout]
      simp

/-- Exact diagonal block `V_kᵀ V_k = d I`, evaluated in coordinates.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem transpose_VMatrix_mul_apply (F : Frame n d) (k : Fin ell)
    (z z' : ParticleDomainIndex m n ell k) :
    ((VMatrix (m := m) F k).transpose * VMatrix (m := m) F k) z z' =
      if z = z' then (d : ℝ) else 0 := by
  classical
  simp only [Matrix.mul_apply, Matrix.transpose_apply, VMatrix]
  by_cases hzz : z = z'
  · subst z'
    rw [if_pos rfl]
    let f : LabelledIndex d m n ell → ℝ := fun out ↦
      (if z = domainOfWord k out.2 then F.u (out.2 k).2 out.1 else 0) *
        (if z = domainOfWord k out.2 then F.u (out.2 k).2 out.1 else 0)
    calc
      (∑ out : LabelledIndex d m n ell,
        (if z = domainOfWord k out.2 then
          F.u (out.2 k).2 out.1 else 0) *
        (if z = domainOfWord k out.2 then
          F.u (out.2 k).2 out.1 else 0)) = ∑ out, f out := rfl
      _ = ∑ t : ParticleDomainIndex m n ell k × Fin n × Fin d,
          f ((labelledIndexEquiv (d := d) k).symm t) :=
        ((labelledIndexEquiv (d := d) k).symm.sum_comp f).symm
      _ = ∑ i : Fin n, ∑ a : Fin d, F.u i a * F.u i a := by
        simp only [f, labelledIndexEquiv, Equiv.coe_fn_symm_mk,
          domainOfWord_wordOfDomain, wordOfDomain_at]
        rw [Fintype.sum_prod_type]
        simp
        rw [Fintype.sum_prod_type]
      _ = (d : ℝ) := by
        rw [Finset.sum_comm]
        exact sum_frame_coordinate_sq_eq_dim F
  · rw [if_neg hzz]
    apply Finset.sum_eq_zero
    intro out _hout
    by_cases hz : z = domainOfWord k out.2
    · have hz' : z' ≠ domainOfWord k out.2 := by
        intro heq
        exact hzz (hz.trans heq.symm)
      simp [hz, hz']
    · simp [hz]

/-- The reverse particle Gram matrix is the retained-row identity times the frame column Gram.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem transpose_VMatrix_mul (F : Frame n d) (k : Fin ell) :
    (VMatrix (m := m) F k).transpose * VMatrix (m := m) F k =
      (d : ℝ) • (1 : Matrix (ParticleDomainIndex m n ell k)
        (ParticleDomainIndex m n ell k) ℝ) := by
  classical
  ext z z'
  rw [transpose_VMatrix_mul_apply F k z z']
  by_cases hzz : z = z'
  · subst z'
    simp
  · simp [hzz]

end NLAlib.SparseFock.LightSectorConcrete
