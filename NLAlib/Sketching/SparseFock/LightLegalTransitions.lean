/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.LightHardCoreEmbedding

/-!
# Legal physical light moves and fixed-block preservation

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

/-- The literal Pattern-level `G-hat` submatrix on one fixed-heavy,
fixed-light block.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def ghatBlock (F : Frame n d) (T : Finset (Site m n)) (ell : ℕ) :
    Matrix (BlockIndex d T ell) (BlockIndex d T ell) ℝ :=
  fun out inp ↦ ghat F (out.1, out.2.1) (inp.1, inp.2.1)

/-- An updated pattern is characterized by its value at the updated site and agreement elsewhere.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem eq_update_iff (s : Site m n) (v : Level)
    (out inp : Pattern m n) :
    out = Function.update inp s v ↔
      out s = v ∧ agreesOutsideSite s out inp := by
  constructor
  · rintro rfl
    constructor
    · simp
    · intro x hx
      simp [Function.update, hx]
  · rintro ⟨hs, hoff⟩
    funext x
    by_cases hx : x = s
    · subst x
      simp [hs]
    · simp [Function.update, hx, hoff x hx]

/-- An annihilation entry is one exactly for its legal occupied-to-empty transition.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem pAt_apply_characterization (r : Fin m) (i : Fin n)
    (out inp : Pattern m n) :
    pAt r i out inp =
      if inp (r, i) = .one ∧
          out = Function.update inp (r, i) .zero then 1 else 0 := by
  classical
  by_cases hoff : agreesOutsideSite (r, i) out inp
  · by_cases hout : out (r, i) = .zero
    · by_cases hin : inp (r, i) = .one
      · have heq : out = Function.update inp (r, i) .zero :=
          (eq_update_iff (r, i) .zero out inp).2 ⟨hout, hoff⟩
        have hoffUpdate : agreesOutsideSite (r, i)
            (Function.update inp (r, i) .zero) inp :=
          (eq_update_iff (r, i) .zero
            (Function.update inp (r, i) .zero) inp).1 rfl |>.2
        simp [pAt, siteKernel, pDestroy, ketBra, hin, heq,
          hoffUpdate]
      · simp [pAt, siteKernel, pDestroy, ketBra, hoff, hout, hin]
    · have hne : out ≠ Function.update inp (r, i) .zero := by
        intro heq
        apply hout
        simp [heq]
      simp [pAt, siteKernel, pDestroy, ketBra, hoff, hout, hne]
  · have hne : out ≠ Function.update inp (r, i) .zero := by
      intro heq
      apply hoff
      exact (eq_update_iff (r, i) .zero out inp).1 heq |>.2
    simp [pAt, siteKernel, hoff, hne]

/-- A creation entry is one exactly for its legal empty-to-occupied transition.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem pDagAt_apply_characterization (r : Fin m) (i : Fin n)
    (out inp : Pattern m n) :
    pDagAt r i out inp =
      if inp (r, i) = .zero ∧
          out = Function.update inp (r, i) .one then 1 else 0 := by
  classical
  by_cases hoff : agreesOutsideSite (r, i) out inp
  · by_cases hout : out (r, i) = .one
    · by_cases hin : inp (r, i) = .zero
      · have heq : out = Function.update inp (r, i) .one :=
          (eq_update_iff (r, i) .one out inp).2 ⟨hout, hoff⟩
        have hoffUpdate : agreesOutsideSite (r, i)
            (Function.update inp (r, i) .one) inp :=
          (eq_update_iff (r, i) .one
            (Function.update inp (r, i) .one) inp).1 rfl |>.2
        simp [pDagAt, siteKernel, pCreate, ketBra, hin, heq,
          hoffUpdate]
      · simp [pDagAt, siteKernel, pCreate, ketBra, hoff, hout, hin]
    · have hne : out ≠ Function.update inp (r, i) .one := by
        intro heq
        apply hout
        simp [heq]
      simp [pDagAt, siteKernel, pCreate, ketBra, hoff, hout, hne]
  · have hne : out ≠ Function.update inp (r, i) .one := by
      intro heq
      apply hoff
      exact (eq_update_iff (r, i) .one out inp).1 heq |>.2
    simp [pDagAt, siteKernel, hoff, hne]

/-- A light move empties its source site and occupies its target site.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
def lightMove (inp : Pattern m n) (source target : Site m n) : Pattern m n :=
  Function.update (Function.update inp source .zero) target .one

/-- A source-clearing update is zero at the target exactly when the target is the source or was already empty.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem update_source_zero_apply_eq_zero_iff
    (inp : Pattern m n) (source target : Site m n) :
    Function.update inp source .zero target = .zero ↔
      target = source ∨ inp target = .zero := by
  by_cases h : target = source
  · subst target
    simp
  · simp [Function.update, h]

/-- A creation-after-annihilation entry is the indicator of a legal light move.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem pDagAt_mul_pAt_apply (r : Fin m) (i j : Fin n)
    (out inp : Pattern m n) :
    (pDagAt r i * pAt r j) out inp =
      if inp (r, j) = .one ∧
          ((r, i) = (r, j) ∨ inp (r, i) = .zero) ∧
          out = lightMove inp (r, j) (r, i) then 1 else 0 := by
  classical
  rw [Matrix.mul_apply]
  simp_rw [pDagAt_apply_characterization, pAt_apply_characterization]
  by_cases hsource : inp (r, j) = .one
  · simp only [hsource, true_and]
    simp_rw [mul_ite, mul_one, mul_zero]
    rw [Fintype.sum_ite_eq']
    simp [update_source_zero_apply_eq_zero_iff, lightMove]
  · simp [hsource]

/-- A legal light move preserves the heavy support.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem heavy_lightMove_of_legal (inp : Pattern m n) (source target : Site m n)
    (hsource : inp source = .one)
    (havailable : target = source ∨ inp target = .zero) :
    (lightMove inp source target).heavy = inp.heavy := by
  classical
  ext x
  simp only [Pattern.mem_heavy]
  by_cases hxt : x = target
  · subst x
    have htNotTwo : inp target ≠ .two := by
      intro htwo
      rcases havailable with hts | htzero
      · subst target
        exact Level.noConfusion (hsource.symm.trans htwo)
      · exact Level.noConfusion (htzero.symm.trans htwo)
    simp [lightMove, htNotTwo]
  · by_cases hxs : x = source
    · subst x
      simp [lightMove, Function.update, hxt, hsource]
    · simp [lightMove, Function.update, hxt, hxs]

/-- A legal light move replaces its source in the light support by its target.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem light_lightMove_of_legal (inp : Pattern m n) (source target : Site m n)
    (_hsource : inp source = .one)
    (_havailable : target = source ∨ inp target = .zero) :
    (lightMove inp source target).light = insert target (inp.light.erase source) := by
  classical
  ext x
  simp only [Pattern.mem_light, Finset.mem_insert, Finset.mem_erase]
  by_cases hxt : x = target
  · subst x
    simp [lightMove]
  · by_cases hxs : x = source
    · subst x
      simp [lightMove, Function.update, hxt]
    · simp [lightMove, Function.update, hxt, hxs]

/-- A legal light move preserves the number of light sites.
Source: ported sparse-Fock shared-leg/vacuum proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem card_light_lightMove_of_legal
    (inp : Pattern m n) (source target : Site m n)
    (hsource : inp source = .one)
    (havailable : target = source ∨ inp target = .zero) :
    (lightMove inp source target).light.card = inp.light.card := by
  classical
  rw [light_lightMove_of_legal inp source target hsource havailable]
  have hsMem : source ∈ inp.light := Pattern.mem_light.mpr hsource
  rcases havailable with rfl | htarget
  · simp [hsMem]
  · have htNotMem : target ∉ inp.light := by
      simp [Pattern.mem_light, htarget]
    rw [Finset.card_insert_of_notMem (by simp [htNotMem]),
      Finset.card_erase_of_mem hsMem]
    have hcardpos : 0 < inp.light.card := Finset.card_pos.mpr ⟨source, hsMem⟩
    omega

/-- `G-hat` has no matrix entries between distinct fixed-heavy/fixed-light
blocks.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem ghat_apply_eq_zero_of_block_ne
    (F : Frame n d) (out inp : Fin d × Pattern m n)
    (hne : out.2.heavy ≠ inp.2.heavy ∨
      out.2.light.card ≠ inp.2.light.card) :
    ghat (m := m) F out inp = 0 := by
  classical
  rw [ghat_apply]
  apply Finset.sum_eq_zero
  intro r _hr
  apply Finset.sum_eq_zero
  intro i _hi
  apply Finset.sum_eq_zero
  intro j _hj
  rw [pDagAt_mul_pAt_apply]
  by_cases hlegal : inp.2 (r, j) = .one ∧
      ((r, i) = (r, j) ∨ inp.2 (r, i) = .zero) ∧
      out.2 = lightMove inp.2 (r, j) (r, i)
  · rcases hlegal with ⟨hsource, havailable, hmove⟩
    have hheavy : out.2.heavy = inp.2.heavy := by
      rw [hmove]
      exact heavy_lightMove_of_legal inp.2 (r, j) (r, i)
        hsource havailable
    have hlight : out.2.light.card = inp.2.light.card := by
      rw [hmove]
      exact card_light_lightMove_of_legal inp.2 (r, j) (r, i)
        hsource havailable
    exact False.elim (hne.elim (fun h ↦ h hheavy) (fun h ↦ h hlight))
  · rw [if_neg hlegal]
    ring

end NLAlib.SparseFock.LightSectorConcrete
