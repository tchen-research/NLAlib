/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.LightLegalTransitions

/-!
# Correspondence between labelled spectators and legal physical moves

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

/-- A matching labelled spectator configuration is exactly a legal hard-core
light move on the underlying Pattern block.  This is the pointwise
combinatorial content of the bosonic compression.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem lightMove_legal_of_domain_eq
    (T : Finset (Site m n)) (ell : ℕ)
    (out inp : BlockPattern T ell)
    (pi sigma : Equiv.Perm (Fin ell)) (k : Fin ell)
    (hdom : domainOfWord k (permutedLightWord T ell out pi) =
      domainOfWord k (permutedLightWord T ell inp sigma)) :
    let O := permutedLightWord T ell out pi
    let I := permutedLightWord T ell inp sigma
    inp.1 (I k) = .one ∧
      (O k = I k ∨ inp.1 (O k) = .zero) ∧
      out.1 = lightMove inp.1 (I k) (O k) := by
  classical
  let O := permutedLightWord T ell out pi
  let I := permutedLightWord T ell inp sigma
  have hmatch := (domainOfWord_eq_iff k O I).1 hdom
  have hrow : (O k).1 = (I k).1 := hmatch.1
  have hoff : ∀ l, l ≠ k → O l = I l := hmatch.2
  have htone : out.1 (O k) = .one := by
    apply Pattern.mem_light.mp
    exact permutedLightWord_mem T ell out pi k
  have hsone : inp.1 (I k) = .one := by
    apply Pattern.mem_light.mp
    exact permutedLightWord_mem T ell inp sigma k
  have hheavy : out.1.heavy = inp.1.heavy := out.2.1.trans inp.2.1.symm
  by_cases hsame : O k = I k
  · have hword : O = I := by
      funext l
      by_cases hlk : l = k
      · subst l
        exact hsame
      · exact hoff l hlk
    have houtinp : out = inp :=
      (permutedLightWord_eq_iff T ell out inp pi sigma).1 hword |>.1
    have hmove : lightMove inp.1 (I k) (O k) = inp.1 := by
      rw [hsame]
      funext x
      by_cases hx : x = I k
      · subst x
        simp [lightMove, hsone]
      · simp [lightMove, Function.update, hx]
    exact ⟨hsone, Or.inl hsame,
      congrArg Subtype.val houtinp |>.trans hmove.symm⟩
  · have htNotOne : inp.1 (O k) ≠ .one := by
      intro htInp
      have htMem : O k ∈ inp.1.light := Pattern.mem_light.mpr htInp
      obtain ⟨l, hl⟩ :=
        (permutedLightWord_surjective T ell inp sigma (O k)).1 htMem
      have hlk : l ≠ k := by
        intro hlk
        subst l
        exact hsame hl.symm
      have hOl : O l = O k := (hoff l hlk).trans hl
      exact hlk ((permutedLightWord_injective T ell out pi) hOl)
    have htNotTwo : inp.1 (O k) ≠ .two := by
      intro htInp
      have htMem : O k ∈ inp.1.heavy := Pattern.mem_heavy.mpr htInp
      have htOutMem : O k ∈ out.1.heavy := by simpa [hheavy] using htMem
      have htOut := Pattern.mem_heavy.mp htOutMem
      exact Level.noConfusion (htone.symm.trans htOut)
    have htzero : inp.1 (O k) = .zero := by
      cases h : inp.1 (O k) with
      | zero => rfl
      | one => exact False.elim (htNotOne h)
      | two => exact False.elim (htNotTwo h)
    have hsNotOne : out.1 (I k) ≠ .one := by
      intro hsOut
      have hsMem : I k ∈ out.1.light := Pattern.mem_light.mpr hsOut
      obtain ⟨l, hl⟩ :=
        (permutedLightWord_surjective T ell out pi (I k)).1 hsMem
      have hlk : l ≠ k := by
        intro hlk
        subst l
        exact hsame hl
      have hIl : I l = I k := (hoff l hlk).symm.trans hl
      exact hlk ((permutedLightWord_injective T ell inp sigma) hIl)
    have hsNotTwo : out.1 (I k) ≠ .two := by
      intro hsOut
      have hsMem : I k ∈ out.1.heavy := Pattern.mem_heavy.mpr hsOut
      have hsInpMem : I k ∈ inp.1.heavy := by simpa [hheavy] using hsMem
      have hsInp := Pattern.mem_heavy.mp hsInpMem
      exact Level.noConfusion (hsone.symm.trans hsInp)
    have hszero : out.1 (I k) = .zero := by
      cases h : out.1 (I k) with
      | zero => rfl
      | one => exact False.elim (hsNotOne h)
      | two => exact False.elim (hsNotTwo h)
    have houtMove : out.1 = lightMove inp.1 (I k) (O k) := by
      funext x
      by_cases hxt : x = O k
      · subst x
        simp [lightMove, htone]
      · by_cases hxs : x = I k
        · subst x
          simp [lightMove, Function.update, Ne.symm hsame, hszero]
        · have hone : out.1 x = .one ↔ inp.1 x = .one := by
            constructor
            · intro hxOut
              have hxMem : x ∈ out.1.light := Pattern.mem_light.mpr hxOut
              obtain ⟨l, hl⟩ :=
                (permutedLightWord_surjective T ell out pi x).1 hxMem
              have hlk : l ≠ k := by
                intro hlk
                subst l
                exact hxt hl.symm
              have : I l = x := (hoff l hlk).symm.trans hl
              exact Pattern.mem_light.mp
                ((permutedLightWord_surjective T ell inp sigma x).2 ⟨l, this⟩)
            · intro hxInp
              have hxMem : x ∈ inp.1.light := Pattern.mem_light.mpr hxInp
              obtain ⟨l, hl⟩ :=
                (permutedLightWord_surjective T ell inp sigma x).1 hxMem
              have hlk : l ≠ k := by
                intro hlk
                subst l
                exact hxs hl.symm
              have : O l = x := (hoff l hlk).trans hl
              exact Pattern.mem_light.mp
                ((permutedLightWord_surjective T ell out pi x).2 ⟨l, this⟩)
          have htwo : out.1 x = .two ↔ inp.1 x = .two := by
            rw [← Pattern.mem_heavy, ← Pattern.mem_heavy, hheavy]
          have hval : out.1 x = inp.1 x := by
            cases ho : out.1 x <;> cases hi : inp.1 x <;> simp_all
          simpa [lightMove, Function.update, hxt, hxs] using hval
    exact ⟨hsone, Or.inr htzero, houtMove⟩

/-- Conversely, every legal Pattern-level move admits the unique labelled
ordering whose spectators coincide with the canonical output ordering.

Source: ported from `SparseFockFormal.LightSectorConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem exists_permutation_of_legal_move
    (T : Finset (Site m n)) (ell : ℕ)
    (out inp : BlockPattern T ell) (k : Fin ell)
    (r : Fin m) (i j : Fin n)
    (htarget : canonicalLightWord T ell out k = (r, i))
    (hsource : inp.1 (r, j) = .one)
    (_havailable : (r, i) = (r, j) ∨ inp.1 (r, i) = .zero)
    (hmove : out.1 = lightMove inp.1 (r, j) (r, i)) :
    ∃ tau : Equiv.Perm (Fin ell),
      domainOfWord k (canonicalLightWord T ell out) =
          domainOfWord k (permutedLightWord T ell inp tau) ∧
        permutedLightWord T ell inp tau k = (r, j) := by
  classical
  let O := canonicalLightWord T ell out
  let source : Site m n := (r, j)
  let target : Site m n := (r, i)
  let w : Fin ell → Site m n := Function.update O k source
  have hOinj : Function.Injective O :=
    canonicalLightWord_injective T ell out
  have htargetO : O k = target := by simpa [O, target] using htarget
  have hsMem : source ∈ inp.1.light := by
    exact Pattern.mem_light.mpr hsource
  have hOffTarget (l : Fin ell) (hlk : l ≠ k) : O l ≠ target := by
    intro hlt
    apply hlk
    apply hOinj
    exact hlt.trans htargetO.symm
  have hsOutZero : target ≠ source → out.1 source = .zero := by
    intro hne
    rw [hmove]
    change lightMove inp.1 source target source = .zero
    simp [lightMove, Function.update, Ne.symm hne]
  have hOffSource (l : Fin ell) (hlk : l ≠ k) : O l ≠ source := by
    intro hls
    by_cases hts : target = source
    · exact hOffTarget l hlk (hls.trans hts.symm)
    · have hOlOne : out.1 (O l) = .one := by
        apply Pattern.mem_light.mp
        exact canonicalLightWord_mem T ell out l
      have : out.1 source = .one := by simpa [hls] using hOlOne
      exact Level.noConfusion (this.symm.trans (hsOutZero hts))
  have hmem : ∀ l, w l ∈ inp.1.light := by
    intro l
    by_cases hlk : l = k
    · subst l
      simpa [w, source] using hsMem
    · have hOlOne : out.1 (O l) = .one := by
        apply Pattern.mem_light.mp
        exact canonicalLightWord_mem T ell out l
      have hInpOne : inp.1 (O l) = .one := by
        rw [hmove] at hOlOne
        change lightMove inp.1 source target (O l) = .one at hOlOne
        simpa [lightMove, Function.update, hOffTarget l hlk,
          hOffSource l hlk] using hOlOne
      apply Pattern.mem_light.mpr
      simpa [w, Function.update, hlk] using hInpOne
  have hinj : Function.Injective w := by
    intro a b hab
    by_cases ha : a = k
    · subst a
      by_cases hb : b = k
      · exact hb.symm
      · exfalso
        apply hOffSource b hb
        simpa [w, Function.update, hb] using hab.symm
    · by_cases hb : b = k
      · subst b
        exfalso
        apply hOffSource a ha
        simpa [w, Function.update, ha] using hab
      · apply hOinj
        simpa [w, Function.update, ha, hb] using hab
  let tau := permutationOfLightWord T ell inp w hmem hinj
  have hword : permutedLightWord T ell inp tau = w := by
    exact permutedLightWord_permutationOfLightWord T ell inp w hmem hinj
  refine ⟨tau, ?_, ?_⟩
  · rw [hword]
    apply (domainOfWord_eq_iff k _ _).2
    constructor
    · simp [w, O, source, target, htargetO]
    · intro l hlk
      change O l = w l
      simp [w, hlk]
  · rw [hword]
    simp [w, source]

end NLAlib.SparseFock.LightSectorConcrete
