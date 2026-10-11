/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.NamedBands
import NLAlib.Sketching.SparseFock.FiniteHilbert
import NLAlib.Sketching.SparseFock.DirectionalBounds
import NLAlib.Sketching.SparseFock.ParsevalFrame
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Directional two-site transitions

Literal pair updates, typed word kernels, and their matrix actions.
Ported from `SparseFockFormal.DirectionalConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock

namespace DirectionalConcrete

open ParsevalFrame LocalOperator BandInventory FiniteOperator ExternalOperator
  GlobalBands NamedBands FiniteHilbert
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

variable {d m n : ℕ}

/-- Forget only the Euclidean wrapper on the vectors of a Parseval frame.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def frameRows (F : Frame n d) : Fin n → Fin d → ℝ :=
  fun i k ↦ F.u i k

/-- The exposed frame-row coordinates are the original Euclidean frame coordinates.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem frameRows_apply (F : Frame n d) (i : Fin n) (k : Fin d) :
    frameRows F i k = F.u i k := rfl

/-- Update two distinct sites of a pattern.  The second update is written
last; all uses below prove the sites distinct.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def setPair (p : Pattern m n) (s : Site m n) (a : Level)
    (t : Site m n) (b : Level) : Pattern m n :=
  Function.update (Function.update p s a) t b

/-- Updating two distinct sites assigns the first specified level at the first site.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem setPair_apply_left (p : Pattern m n) {s t : Site m n}
    (hst : s ≠ t) (a b : Level) :
    setPair p s a t b s = a := by
  simp [setPair, hst]

/-- A two-site update assigns the second specified level at the second site.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem setPair_apply_right (p : Pattern m n) (s t : Site m n)
    (a b : Level) :
    setPair p s a t b t = b := by
  simp [setPair]

/-- A two-site update leaves every other site unchanged.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem setPair_apply_of_ne (p : Pattern m n) {s t x : Site m n}
    (hxs : x ≠ s) (hxt : x ≠ t) (a b : Level) :
    setPair p s a t b x = p x := by
  simp [setPair, hxs, hxt]

/-- A two-site update agrees with the original pattern outside the marked pair.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem agreesOutsidePair_setPair (p : Pattern m n) (s t : Site m n)
    (a b : Level) :
    agreesOutsidePair s t p (setPair p s a t b) := by
  intro x hxs hxt
  symm
  exact setPair_apply_of_ne p hxs hxt a b

/-- Outside-pair agreement plus the two local values determines the input
pattern uniquely.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem eq_setPair_iff {out inp : Pattern m n} {s t : Site m n}
    (hst : s ≠ t) (a b : Level) :
    inp = setPair out s a t b ↔
      agreesOutsidePair s t out inp ∧ inp s = a ∧ inp t = b := by
  constructor
  · rintro rfl
    exact ⟨agreesOutsidePair_setPair out s t a b,
      setPair_apply_left out hst a b, setPair_apply_right out s t a b⟩
  · rintro ⟨hout, hs, ht⟩
    funext x
    by_cases hxs : x = s
    · subst x
      simpa [setPair_apply_left out hst a b] using hs
    · by_cases hxt : x = t
      · subst x
        simpa using ht
      · rw [setPair_apply_of_ne out hxs hxt]
        exact (hout x hxs hxt).symm

/-- Exact matrix entry of a lifted pair of local rank-one transitions.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem pairKernel_ketBra_apply {s t : Site m n} (hst : s ≠ t)
    (os is ot it : Level) (out inp : Pattern m n) :
    pairKernel s t (ketBra os is) (ketBra ot it) out inp =
      if out s = os ∧ out t = ot ∧ inp = setPair out s is t it then 1 else 0 := by
  classical
  simp only [pairKernel, ketBra]
  by_cases hoff : agreesOutsidePair s t out inp
  · rw [if_pos hoff]
    by_cases hos : out s = os
    · by_cases hot : out t = ot
      · simp only [hos, hot, true_and]
        have heqiff : inp = setPair out s is t it ↔ inp s = is ∧ inp t = it := by
          rw [eq_setPair_iff hst]
          simp [hoff]
        by_cases his : inp s = is
        · by_cases hit : inp t = it
          · have heq := heqiff.mpr ⟨his, hit⟩
            rw [if_pos his, if_pos hit, if_pos heq]
            norm_num
          · have hne : inp ≠ setPair out s is t it := by
              intro heq
              exact hit (heqiff.mp heq).2
            simp [his, hit, hne]
        · have hne : inp ≠ setPair out s is t it := by
            intro heq
            exact his (heqiff.mp heq).1
          simp [his, hne]
      · simp [hos, hot]
    · simp [hos]
  · rw [if_neg hoff]
    have hne : inp ≠ setPair out s is t it := by
      intro h
      apply hoff
      rw [h]
      exact agreesOutsidePair_setPair out s t is it
    simp [hne]

/-- The transpose light hop `H'` from the paper.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def Hprime (m : ℕ) (u : Fin n → Fin d → ℝ) : FullOp d m n :=
  wordSum m u .pDown .pUp

/-- Swapping both ordered indices does not change a sum over `i ≠ j`.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sum_ordered_swap {A : Type*} [AddCommMonoid A]
    (f : Fin n → Fin n → A) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, f j i) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, f i j := by
  classical
  have expand (g : Fin n → Fin n → A) :
      (∑ i, ∑ j ∈ Finset.univ.erase i, g i j) =
        ∑ i, ∑ j, if j ≠ i then g i j else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.filter_ne' Finset.univ i, Finset.sum_filter]
  rw [expand (fun i j ↦ f j i), expand f, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j <;> simp [hij, Ne.symm]

/-- Transposition of a physical word sum is its ordered adjoint word sum.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem transpose_physicalWordSum (u : Fin n → Fin d → ℝ) (w : Word) :
    (physicalWordSum m u w).transpose =
      physicalWordSum m u w.orderedAdjoint := by
  classical
  ext out inp
  simp only [Matrix.transpose_apply, physicalWordSum, Matrix.sum_apply]
  have hterm (r : Fin m) (i j : Fin n) :
      orderedWordTerm u r i j w inp out =
        orderedWordTerm u r j i w.orderedAdjoint out inp := by
    have h := congrArg
      (fun M : FullOp d m n ↦ M out inp)
      (transpose_orderedWordTerm u r i j w)
    simpa [Matrix.transpose_apply] using h
  simp_rw [hterm]
  apply Finset.sum_congr rfl
  intro r _
  exact sum_ordered_swap
    (fun i j ↦ orderedWordTerm u r i j w.orderedAdjoint out inp)

/-- Ordered-index relabeling makes the transpose light hop symmetric.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hprime_transpose (u : Fin n → Fin d → ℝ) :
    (Hprime m u).transpose = Hprime m u := by
  rw [Hprime, wordSum, transpose_physicalWordSum]
  rfl

/-- The mixed directional raising word kernel has exactly the prescribed pair-transition coefficient.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem yPlus_wordKernel_apply {r : Fin m} {i j : Fin n} (hij : i ≠ j)
    (out inp : Pattern m n) :
    wordKernel (r, i) (r, j) (.rUp, .pUp) out inp =
      if out (r, i) = .two ∧ out (r, j) = .one ∧
          inp = setPair out (r, i) .one (r, j) .zero then 1 else 0 := by
  have hsite : (r, i) ≠ (r, j) := by
    intro h
    exact hij (congrArg Prod.snd h)
  simpa [wordKernel, Leg.op, rPromote, pCreate] using
    pairKernel_ketBra_apply hsite .two .one .one .zero out inp

/-- The mixed directional preserving word kernel has exactly the prescribed pair-transition coefficient.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem yZero_wordKernel_apply {r : Fin m} {i j : Fin n} (hij : i ≠ j)
    (out inp : Pattern m n) :
    wordKernel (r, i) (r, j) (.rDown, .pUp) out inp =
      if out (r, i) = .one ∧ out (r, j) = .one ∧
          inp = setPair out (r, i) .two (r, j) .zero then 1 else 0 := by
  have hsite : (r, i) ≠ (r, j) := by
    intro h
    exact hij (congrArg Prod.snd h)
  simpa [wordKernel, Leg.op, rDemote, pCreate] using
    pairKernel_ketBra_apply hsite .one .two .one .zero out inp

/-- The heavy correction word kernel has exactly the prescribed pair-transition coefficient.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem hprime_wordKernel_apply {r : Fin m} {i j : Fin n} (hij : i ≠ j)
    (out inp : Pattern m n) :
    wordKernel (r, i) (r, j) (.pDown, .pUp) out inp =
      if out (r, i) = .zero ∧ out (r, j) = .one ∧
          inp = setPair out (r, i) .one (r, j) .zero then 1 else 0 := by
  have hsite : (r, i) ≠ (r, j) := by
    intro h
    exact hij (congrArg Prod.snd h)
  simpa [wordKernel, Leg.op, pDestroy, pCreate] using
    pairKernel_ketBra_apply hsite .zero .one .one .zero out inp

/-- One ordered `Y₊` word has exactly the marked-pattern coefficient claimed
in the paper.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem orderedYplus_mulVec (u : Fin n → Fin d → ℝ)
    (x : Fin d × Pattern m n → ℝ) (r : Fin m) {i j : Fin n}
    (hij : i ≠ j) (k : Fin d) (σ : Pattern m n) :
    Matrix.mulVec (orderedWordTerm u r i j (.rUp, .pUp)) x (k, σ) =
      if σ (r, i) = .two ∧ σ (r, j) = .one then
        ∑ l, u i k * u j l *
          x (l, setPair σ (r, i) .one (r, j) .zero)
      else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  simp only [orderedWordTerm, externalTensor, ExternalOperator.outer]
  simp_rw [yPlus_wordKernel_apply hij]
  by_cases hout : σ (r, i) = .two ∧ σ (r, j) = .one
  · simp [hout]
  · have hz (τ : Pattern m n) :
        ¬(σ (r, i) = .two ∧ σ (r, j) = .one ∧
          τ = setPair σ (r, i) .one (r, j) .zero) := by
      intro h
      exact hout ⟨h.1, h.2.1⟩
    simp [hz, hout]

/-- One ordered `Y₀` word has exactly its marked-pattern coefficient.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem orderedYzero_mulVec (u : Fin n → Fin d → ℝ)
    (x : Fin d × Pattern m n → ℝ) (r : Fin m) {i j : Fin n}
    (hij : i ≠ j) (k : Fin d) (σ : Pattern m n) :
    Matrix.mulVec (orderedWordTerm u r i j (.rDown, .pUp)) x (k, σ) =
      if σ (r, i) = .one ∧ σ (r, j) = .one then
        ∑ l, u i k * u j l *
          x (l, setPair σ (r, i) .two (r, j) .zero)
      else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  simp only [orderedWordTerm, externalTensor, ExternalOperator.outer]
  simp_rw [yZero_wordKernel_apply hij]
  by_cases hout : σ (r, i) = .one ∧ σ (r, j) = .one
  · simp [hout]
  · have hz (τ : Pattern m n) :
        ¬(σ (r, i) = .one ∧ σ (r, j) = .one ∧
          τ = setPair σ (r, i) .two (r, j) .zero) := by
      intro h
      exact hout ⟨h.1, h.2.1⟩
    simp [hz, hout]

/-- One ordered transpose-light-hop word has exactly its marked coefficient.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem orderedHprime_mulVec (u : Fin n → Fin d → ℝ)
    (x : Fin d × Pattern m n → ℝ) (r : Fin m) {i j : Fin n}
    (hij : i ≠ j) (k : Fin d) (σ : Pattern m n) :
    Matrix.mulVec (orderedWordTerm u r i j (.pDown, .pUp)) x (k, σ) =
      if σ (r, i) = .zero ∧ σ (r, j) = .one then
        ∑ l, u i k * u j l *
          x (l, setPair σ (r, i) .one (r, j) .zero)
      else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  simp only [orderedWordTerm, externalTensor, ExternalOperator.outer]
  simp_rw [hprime_wordKernel_apply hij]
  by_cases hout : σ (r, i) = .zero ∧ σ (r, j) = .one
  · simp [hout]
  · have hz (τ : Pattern m n) :
        ¬(σ (r, i) = .zero ∧ σ (r, j) = .one ∧
          τ = setPair σ (r, i) .one (r, j) .zero) := by
      intro h
      exact hout ⟨h.1, h.2.1⟩
    simp [hz, hout]

end

end DirectionalConcrete

end NLAlib.SparseFock
