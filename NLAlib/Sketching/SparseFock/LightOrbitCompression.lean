/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.LightMoveOrbits

/-!
# The exact orbit-sum and physical compression identity

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

/-- An unfiltered labelled move consists of a particle slot and a slot permutation.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
abbrev OrbitRaw (ell : ℕ) := Fin ell × Equiv.Perm (Fin ell)
/-- An unfiltered physical move consists of a row, target column, and source column.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
abbrev MoveRaw (m n : ℕ) := Fin m × (Fin n × Fin n)

/-- A labelled move is compatible when its omitted-slot domains match.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
def OrbitCompatible (T : Finset (Site m n)) (ell : ℕ)
    (out inp : BlockPattern T ell) (z : OrbitRaw ell) : Prop :=
  domainOfWord z.1 (canonicalLightWord T ell out) =
    domainOfWord z.1 (permutedLightWord T ell inp z.2)

/-- Compatibility of a labelled move is decidable.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
instance instDecidableOrbitCompatible (T : Finset (Site m n)) (ell : ℕ)
    (out inp : BlockPattern T ell) (z : OrbitRaw ell) :
    Decidable (OrbitCompatible T ell out inp z) := Classical.propDecidable _

/-- A physical move is legal when its source, target, and resulting pattern obey the creation and annihilation rules.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
def LegalLightMove (out inp : Pattern m n) (z : MoveRaw m n) : Prop :=
  inp (z.1, z.2.2) = .one ∧
    ((z.1, z.2.1) = (z.1, z.2.2) ∨ inp (z.1, z.2.1) = .zero) ∧
    out = lightMove inp (z.1, z.2.2) (z.1, z.2.1)

/-- Legality of a physical light move is decidable.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
instance instDecidableLegalLightMove (out inp : Pattern m n) (z : MoveRaw m n) :
    Decidable (LegalLightMove out inp z) := Classical.propDecidable _

/-- Forget labels from one compatible omitted-slot configuration, retaining
the target and source columns of the induced Pattern move.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def orbitToLegalMove (T : Finset (Site m n)) (ell : ℕ)
    (out inp : BlockPattern T ell)
    (z : {z : OrbitRaw ell // OrbitCompatible T ell out inp z}) :
    {z : MoveRaw m n // LegalLightMove out.1 inp.1 z} := by
  let k := z.1.1
  let tau := z.1.2
  let target := canonicalLightWord T ell out k
  let source := permutedLightWord T ell inp tau k
  have hdom : domainOfWord k (canonicalLightWord T ell out) =
      domainOfWord k (permutedLightWord T ell inp tau) := z.2
  have hlegal := lightMove_legal_of_domain_eq T ell out inp
    (Equiv.refl (Fin ell)) tau k (by simpa using hdom)
  have hrow : target.1 = source.1 :=
    (domainOfWord_eq_iff k _ _).1 hdom |>.1
  have hsourceSite : (target.1, source.2) = source := Prod.ext hrow rfl
  refine ⟨(target.1, (target.2, source.2)), ?_⟩
  simpa [LegalLightMove, target, source, hsourceSite] using hlegal

/-- Forgetting the labels of a compatible move is injective.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem orbitToLegalMove_injective
    (T : Finset (Site m n)) (ell : ℕ)
    (out inp : BlockPattern T ell) :
    Function.Injective (orbitToLegalMove T ell out inp) := by
  intro x y hxy
  apply Subtype.ext
  rcases x with ⟨⟨kx, taux⟩, hx⟩
  rcases y with ⟨⟨ky, tauy⟩, hy⟩
  have hval := congrArg Subtype.val hxy
  change
    ((canonicalLightWord T ell out kx).1,
      ((canonicalLightWord T ell out kx).2,
        (permutedLightWord T ell inp taux kx).2)) =
    ((canonicalLightWord T ell out ky).1,
      ((canonicalLightWord T ell out ky).2,
        (permutedLightWord T ell inp tauy ky).2)) at hval
  have htarget : canonicalLightWord T ell out kx =
      canonicalLightWord T ell out ky := by
    have hr := congrArg (fun z : MoveRaw m n ↦ z.1) hval
    have hi := congrArg (fun z : MoveRaw m n ↦ z.2.1) hval
    exact Prod.ext hr hi
  have hk : kx = ky :=
    (canonicalLightWord_injective T ell out) htarget
  subst ky
  have hsource : permutedLightWord T ell inp taux kx =
      permutedLightWord T ell inp tauy kx := by
    have hj := congrArg (fun z : MoveRaw m n ↦ z.2.2) hval
    have hrowx := (domainOfWord_eq_iff kx _ _).1 hx |>.1
    have hrowy := (domainOfWord_eq_iff kx _ _).1 hy |>.1
    exact Prod.ext (hrowx.symm.trans hrowy) hj
  have hword : permutedLightWord T ell inp taux =
      permutedLightWord T ell inp tauy := by
    funext l
    by_cases hl : l = kx
    · subst l
      exact hsource
    · exact ((domainOfWord_eq_iff kx _ _).1 hx |>.2 l hl).symm.trans
        ((domainOfWord_eq_iff kx _ _).1 hy |>.2 l hl)
  have htau : taux = tauy :=
    (permutedLightWord_eq_iff T ell inp inp taux tauy).1 hword |>.2
  subst tauy
  rfl

/-- Every legal physical light move is represented by a compatible labelled move.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem orbitToLegalMove_surjective
    (T : Finset (Site m n)) (ell : ℕ)
    (out inp : BlockPattern T ell) :
    Function.Surjective (orbitToLegalMove T ell out inp) := by
  intro y
  rcases y with ⟨⟨r, i, j⟩, hy⟩
  have hsource := hy.1
  have havailable := hy.2.1
  have hmove := hy.2.2
  have htone : out.1 (r, i) = .one := by
    rw [hmove]
    simp [lightMove]
  have htMem : (r, i) ∈ out.1.light := Pattern.mem_light.mpr htone
  obtain ⟨k, hk⟩ :=
    (canonicalLightWord_surjective T ell out (r, i)).1 htMem
  obtain ⟨tau, hdom, hsrc⟩ := exists_permutation_of_legal_move
    T ell out inp k r i j hk hsource havailable hmove
  let x : {z : OrbitRaw ell // OrbitCompatible T ell out inp z} :=
    ⟨(k, tau), hdom⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  change
    ((canonicalLightWord T ell out k).1,
      ((canonicalLightWord T ell out k).2,
        (permutedLightWord T ell inp tau k).2)) = (r, (i, j))
  simp [hk, hsrc]

/-- Weighted finite-sum form of the exact orbit/legal-move bijection.  The
weights depend only on the target and source columns, as in the frame Gram
entry.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem orbit_legal_weighted_sum
    (T : Finset (Site m n)) (ell : ℕ)
    (out inp : BlockPattern T ell) (a b : Fin n → ℝ) :
    (∑ k, ∑ tau,
      if OrbitCompatible T ell out inp (k, tau) then
        a (canonicalLightWord T ell out k).2 *
          b (permutedLightWord T ell inp tau k).2
      else 0) =
    ∑ r, ∑ i, ∑ j,
      if LegalLightMove out.1 inp.1 (r, (i, j)) then a i * b j else 0 := by
  classical
  let orbitSet : Finset (OrbitRaw ell) :=
    Finset.univ.filter (OrbitCompatible T ell out inp)
  let moveSet : Finset (MoveRaw m n) :=
    Finset.univ.filter (LegalLightMove out.1 inp.1)
  let e : {z : OrbitRaw ell // OrbitCompatible T ell out inp z} ≃
      {z : MoveRaw m n // LegalLightMove out.1 inp.1 z} :=
    Equiv.ofBijective (orbitToLegalMove T ell out inp)
      ⟨orbitToLegalMove_injective T ell out inp,
        orbitToLegalMove_surjective T ell out inp⟩
  have horbitSubtype :
      (∑ z : OrbitRaw ell,
        if OrbitCompatible T ell out inp z then
          a (canonicalLightWord T ell out z.1).2 *
            b (permutedLightWord T ell inp z.2 z.1).2
        else 0) =
      ∑ z : {z : OrbitRaw ell // OrbitCompatible T ell out inp z},
        a (canonicalLightWord T ell out z.1.1).2 *
          b (permutedLightWord T ell inp z.1.2 z.1.1).2 := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype orbitSet (by simp [orbitSet])
      (fun z : OrbitRaw ell ↦
        a (canonicalLightWord T ell out z.1).2 *
          b (permutedLightWord T ell inp z.2 z.1).2)
  have hmoveSubtype :
      (∑ z : MoveRaw m n,
        if LegalLightMove out.1 inp.1 z then a z.2.1 * b z.2.2 else 0) =
      ∑ z : {z : MoveRaw m n // LegalLightMove out.1 inp.1 z},
        a z.1.2.1 * b z.1.2.2 := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype moveSet (by simp [moveSet])
      (fun z : MoveRaw m n ↦ a z.2.1 * b z.2.2)
  have hequiv :
      (∑ z : {z : OrbitRaw ell // OrbitCompatible T ell out inp z},
        a (canonicalLightWord T ell out z.1.1).2 *
          b (permutedLightWord T ell inp z.1.2 z.1.1).2) =
      ∑ z : {z : MoveRaw m n // LegalLightMove out.1 inp.1 z},
        a z.1.2.1 * b z.1.2.2 := by
    have h := Equiv.sum_comp e
      (fun z : {z : MoveRaw m n // LegalLightMove out.1 inp.1 z} ↦
        a z.1.2.1 * b z.1.2.2)
    calc
      (∑ z : {z : OrbitRaw ell // OrbitCompatible T ell out inp z},
        a (canonicalLightWord T ell out z.1.1).2 *
          b (permutedLightWord T ell inp z.1.2 z.1.1).2) =
          ∑ z : {z : OrbitRaw ell // OrbitCompatible T ell out inp z},
            a (e z).1.2.1 * b (e z).1.2.2 := by
              apply Finset.sum_congr rfl
              intro z _hz
              rfl
      _ = _ := h
  calc
    (∑ k, ∑ tau,
      if OrbitCompatible T ell out inp (k, tau) then
        a (canonicalLightWord T ell out k).2 *
          b (permutedLightWord T ell inp tau k).2 else 0) =
        ∑ z : OrbitRaw ell,
          if OrbitCompatible T ell out inp z then
            a (canonicalLightWord T ell out z.1).2 *
              b (permutedLightWord T ell inp z.2 z.1).2 else 0 := by
          rw [Fintype.sum_prod_type]
    _ = _ := horbitSubtype
    _ = _ := hequiv
    _ = (∑ z : MoveRaw m n,
          if LegalLightMove out.1 inp.1 z then a z.2.1 * b z.2.2 else 0) :=
      hmoveSubtype.symm
    _ = ∑ r, ∑ i, ∑ j,
        if LegalLightMove out.1 inp.1 (r, (i, j)) then a i * b j else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro r _hr
      rw [Fintype.sum_prod_type]

set_option maxHeartbeats 1000000 in
/-- The labelled orbit sum is exactly the physical shared-leg block entry.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem orbit_sum_labelledG_eq_ghatBlock
    (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ)
    (out inp : BlockIndex d T ell) :
    (∑ tau : Equiv.Perm (Fin ell), labelledG F ell
      (blockLabel T ell out (Equiv.refl (Fin ell)))
      (blockLabel T ell inp tau)) = ghatBlock F T ell out inp := by
  classical
  rw [ghatBlock, ghat_apply]
  simp only [labelledG, Matrix.sum_apply, qSlot, blockLabel,
    permutedLightWord, Equiv.refl_apply]
  rw [Finset.sum_comm]
  simp_rw [pDagAt_mul_pAt_apply]
  have h := orbit_legal_weighted_sum T ell out.2 inp.2
    (fun i ↦ F.u i out.1) (fun j ↦ F.u j inp.1)
  convert h using 1 <;>
    simp [OrbitCompatible, LegalLightMove, permutedLightWord, mul_ite]
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro tau _htau
  by_cases hp : domainOfWord k (canonicalLightWord T ell out.2) =
      domainOfWord k (permutedLightWord T ell inp.2 tau)
  · simp only [hp, if_pos]
  · simp only [hp]

/-- The unnormalized symmetrization produces exactly one factorial copy of
the literal fixed-heavy/fixed-light `G-hat` block.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem hardCoreLift_labelledG_compression
    (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ) :
    (hardCoreLift (d := d) T ell).transpose * labelledG F ell *
        hardCoreLift T ell =
      (permutationCount ell : ℝ) • ghatBlock F T ell := by
  ext out inp
  rw [hardCoreLift_compression_apply,
    sum_sum_labelledG_blockLabel,
    orbit_sum_labelledG_eq_ghatBlock]
  rfl

/-- Exact concrete compression identity: normalized hard-core
symmetrization of the labelled Gram matrix is the actual Pattern/Fock
`G-hat` block, with no relaxation or comparison premise.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem hardCoreCompressedG_eq_ghatBlock
    (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ) :
    hardCoreCompressedG F T ell = ghatBlock F T ell := by
  have hNnat : 0 < permutationCount ell := permutationCount_pos ell
  have hN : (0 : ℝ) < (permutationCount ell : ℝ) := by exact_mod_cast hNnat
  have hsqrt : Real.sqrt (permutationCount ell : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hN)
  have hscalar :
      (1 / Real.sqrt (permutationCount ell : ℝ)) *
          (1 / Real.sqrt (permutationCount ell : ℝ)) *
            (permutationCount ell : ℝ) = 1 := by
    field_simp [hsqrt]
    nlinarith [Real.sq_sqrt hN.le]
  rw [hardCoreCompressedG, hardCoreEmbedding, Matrix.transpose_smul,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    hardCoreLift_labelledG_compression]
  rw [smul_smul, smul_smul, hscalar, one_smul]

/-- Sharp Euclidean operator norm of the actual fixed-heavy/fixed-light
Pattern block.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem ghatBlock_norm_le
    (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ) (hell : 1 ≤ ell) :
    ‖ghatBlock F T ell‖ ≤ (d : ℝ) + (ell : ℝ) - 1 := by
  rw [← hardCoreCompressedG_eq_ghatBlock F T ell]
  exact hardCoreCompressedG_norm_le F T ell hell

/-- A positive-light shared-leg block has norm at most dimension plus grade minus one.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem ghatBlock_norm_le_grade
    (F : Frame n d) (T : Finset (Site m n)) (ell nu : ℕ)
    (hell : 1 ≤ ell) (hle : ell ≤ nu) :
    ‖ghatBlock F T ell‖ ≤ (d : ℝ) + (nu : ℝ) - 1 := by
  calc
    ‖ghatBlock F T ell‖ ≤ (d : ℝ) + (ell : ℝ) - 1 :=
      ghatBlock_norm_le F T ell hell
    _ ≤ (d : ℝ) + (nu : ℝ) - 1 := by
      have hleR : (ell : ℝ) ≤ (nu : ℝ) := by exact_mod_cast hle
      linarith

end NLAlib.SparseFock.LightSectorConcrete
