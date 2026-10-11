/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.DirectionalSiteTransitions

set_option autoImplicit false

/-!
# Directional marked coefficient formulas

Pair-counting coefficient identities and the marked Parseval analysis formulas.
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

/-- Ordered distinct pairs whose two output levels are different are exactly
the product of the two corresponding row-local occupation sets.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sum_distinct_level_pairs (σ : Pattern m n) (r : Fin m)
    {a b : Level} (hab : a ≠ b) (f : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i,
        if σ (r, i) = a ∧ σ (r, j) = b then f i j else 0) =
      ∑ i ∈ Finset.univ.filter (fun i ↦ σ (r, i) = a),
        ∑ j ∈ Finset.univ.filter (fun j ↦ σ (r, j) = b), f i j := by
  classical
  have hexpand (i : Fin n) :
      (∑ j ∈ Finset.univ.erase i,
          if σ (r, i) = a ∧ σ (r, j) = b then f i j else 0) =
        ∑ j, if j ≠ i then
          (if σ (r, i) = a ∧ σ (r, j) = b then f i j else 0) else 0 := by
    rw [← Finset.filter_ne' Finset.univ i, Finset.sum_filter]
  rw [show (∑ i ∈ Finset.univ.filter (fun i ↦ σ (r, i) = a),
        ∑ j ∈ Finset.univ.filter (fun j ↦ σ (r, j) = b), f i j) =
      ∑ i, if σ (r, i) = a then
        (∑ j, if σ (r, j) = b then f i j else 0) else 0 by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    rw [Finset.sum_filter]]
  simp_rw [hexpand]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : σ (r, i) = a
  · simp only [hi, true_and, if_true]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : σ (r, j) = b
    · have hji : j ≠ i := by
        intro h
        subst j
        exact hab (hi.symm.trans hj)
      simp [hj, hji]
    · simp [hj]
  · simp [hi]

/-- When both local levels are the same, the ordered-pair restriction is the
erase of the marked source from the same row-local set.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sum_same_level_pairs (σ : Pattern m n) (r : Fin m)
    (a : Level) (f : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i,
        if σ (r, i) = a ∧ σ (r, j) = a then f i j else 0) =
      ∑ i ∈ Finset.univ.filter (fun i ↦ σ (r, i) = a),
        ∑ j ∈ (Finset.univ.filter (fun j ↦ σ (r, j) = a)).erase i, f i j := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : σ (r, i) = a
  · simp only [hi, true_and, if_true]
    rw [← Finset.filter_erase, Finset.sum_filter]
  · simp [hi]

/-- Exact coefficient formula for the concrete named `Y₊` matrix.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Yplus_mulVec_coeff (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (k : Fin d) (σ : Pattern m n) :
    Matrix.mulVec (Yplus m (frameRows F)) x (k, σ) =
      ∑ r, ∑ a ∈ σ.heavyInRow r, ∑ c ∈ σ.lightInRow r,
        ∑ l, F.u a k * F.u c l *
          x (l, setPair σ (r, a) .one (r, c) .zero) := by
  classical
  simp only [Yplus, wordSum, physicalWordSum, Matrix.sum_mulVec,
    Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro r _
  calc
    (∑ i, ∑ j ∈ Finset.univ.erase i,
        Matrix.mulVec (orderedWordTerm (frameRows F) r i j (.rUp, .pUp)) x (k, σ)) =
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          if σ (r, i) = .two ∧ σ (r, j) = .one then
            ∑ l, F.u i k * F.u j l *
              x (l, setPair σ (r, i) .one (r, j) .zero)
          else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j hj
      exact orderedYplus_mulVec (frameRows F) x r
        (Ne.symm (Finset.mem_erase.mp hj).1) k σ
    _ = ∑ a ∈ σ.heavyInRow r, ∑ c ∈ σ.lightInRow r,
          ∑ l, F.u a k * F.u c l *
            x (l, setPair σ (r, a) .one (r, c) .zero) := by
      simpa only [Pattern.heavyInRow, Pattern.lightInRow] using
        sum_distinct_level_pairs σ r (a := .two) (b := .one) (by decide)
          (fun a c ↦ ∑ l, F.u a k * F.u c l *
            x (l, setPair σ (r, a) .one (r, c) .zero))

/-- Exact coefficient formula for the concrete named `Y₀` matrix.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Yzero_mulVec_coeff (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (k : Fin d) (σ : Pattern m n) :
    Matrix.mulVec (Yzero m (frameRows F)) x (k, σ) =
      ∑ r, ∑ a ∈ σ.lightInRow r,
        ∑ c ∈ (σ.lightInRow r).erase a,
          ∑ l, F.u a k * F.u c l *
            x (l, setPair σ (r, a) .two (r, c) .zero) := by
  classical
  simp only [Yzero, wordSum, physicalWordSum, Matrix.sum_mulVec,
    Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro r _
  calc
    (∑ i, ∑ j ∈ Finset.univ.erase i,
        Matrix.mulVec (orderedWordTerm (frameRows F) r i j (.rDown, .pUp)) x (k, σ)) =
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          if σ (r, i) = .one ∧ σ (r, j) = .one then
            ∑ l, F.u i k * F.u j l *
              x (l, setPair σ (r, i) .two (r, j) .zero)
          else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j hj
      exact orderedYzero_mulVec (frameRows F) x r
        (Ne.symm (Finset.mem_erase.mp hj).1) k σ
    _ = ∑ a ∈ σ.lightInRow r,
          ∑ c ∈ (σ.lightInRow r).erase a,
            ∑ l, F.u a k * F.u c l *
              x (l, setPair σ (r, a) .two (r, c) .zero) := by
      simpa only [Pattern.lightInRow] using
        sum_same_level_pairs σ r .one
          (fun a c ↦ ∑ l, F.u a k * F.u c l *
            x (l, setPair σ (r, a) .two (r, c) .zero))

/-- Exact coefficient formula for the transpose light hop `H'`.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hprime_mulVec_coeff (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (k : Fin d) (σ : Pattern m n) :
    Matrix.mulVec (Hprime m (frameRows F)) x (k, σ) =
      ∑ r, ∑ a ∈ σ.freshInRow r, ∑ c ∈ σ.lightInRow r,
        ∑ l, F.u a k * F.u c l *
          x (l, setPair σ (r, a) .one (r, c) .zero) := by
  classical
  simp only [Hprime, wordSum, physicalWordSum, Matrix.sum_mulVec,
    Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro r _
  calc
    (∑ i, ∑ j ∈ Finset.univ.erase i,
        Matrix.mulVec (orderedWordTerm (frameRows F) r i j (.pDown, .pUp)) x (k, σ)) =
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          if σ (r, i) = .zero ∧ σ (r, j) = .one then
            ∑ l, F.u i k * F.u j l *
              x (l, setPair σ (r, i) .one (r, j) .zero)
          else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j hj
      exact orderedHprime_mulVec (frameRows F) x r
        (Ne.symm (Finset.mem_erase.mp hj).1) k σ
    _ = ∑ a ∈ σ.freshInRow r, ∑ c ∈ σ.lightInRow r,
          ∑ l, F.u a k * F.u c l *
            x (l, setPair σ (r, a) .one (r, c) .zero) := by
      simpa only [Pattern.freshInRow, Pattern.lightInRow] using
        sum_distinct_level_pairs σ r (a := .zero) (b := .one) (by decide)
          (fun a c ↦ ∑ l, F.u a k * F.u c l *
            x (l, setPair σ (r, a) .one (r, c) .zero))

/-- External coefficient vector attached to one pattern.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def fiber (x : Fin d × Pattern m n → ℝ) (τ : Pattern m n) : EVec d :=
  WithLp.toLp 2 (fun k ↦ x (k, τ))

/-- An external fiber reads the vector coordinates at its chosen Fock pattern.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem fiber_apply (x : Fin d × Pattern m n → ℝ)
    (τ : Pattern m n) (k : Fin d) : fiber x τ k = x (k, τ) := rfl

/-- The scalar `u_cᵀ x_τ`.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def contract (F : Frame n d) (c : Fin n)
    (x : Fin d × Pattern m n → ℝ) (τ : Pattern m n) : ℝ :=
  ∑ l, F.u c l * x (l, τ)

/-- Contracting a fiber with a frame vector equals the corresponding Parseval analysis coefficient.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem contract_eq_analyze (F : Frame n d) (c : Fin n)
    (x : Fin d × Pattern m n → ℝ) (τ : Pattern m n) :
    contract F c x τ = analyze F (fiber x τ) c := by
  simp only [contract, analyze, PiLp.inner_apply, Real.inner_apply, fiber_apply]

/-- The marked output vector `z⁺_{σ,r,c}`.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def yPlusMarked (F : Frame n d) (x : Fin d × Pattern m n → ℝ)
    (σ : Pattern m n) (r : Fin m) (c : Fin n) : EVec d :=
  synthesize F (σ.heavyInRow r) (fun a ↦
    contract F c x (setPair σ (r, a) .one (r, c) .zero))

/-- The marked output vector `z⁰_{σ,r,c}`.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def yZeroMarked (F : Frame n d) (x : Fin d × Pattern m n → ℝ)
    (σ : Pattern m n) (r : Fin m) (c : Fin n) : EVec d :=
  synthesize F ((σ.lightInRow r).erase c) (fun a ↦
    contract F c x (setPair σ (r, a) .two (r, c) .zero))

/-- The marked output vector `z'_{σ,r,c}`.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def hprimeMarked (F : Frame n d) (x : Fin d × Pattern m n → ℝ)
    (σ : Pattern m n) (r : Fin m) (c : Fin n) : EVec d :=
  synthesize F (σ.freshInRow r) (fun a ↦
    contract F c x (setPair σ (r, a) .one (r, c) .zero))

/-- The marked mixed raising coefficient evaluates its transitioned input fiber.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem yPlusMarked_apply (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (σ : Pattern m n)
    (r : Fin m) (c : Fin n) (k : Fin d) :
    yPlusMarked F x σ r c k =
      ∑ a ∈ σ.heavyInRow r, F.u a k *
        contract F c x (setPair σ (r, a) .one (r, c) .zero) := by
  simp [yPlusMarked, synthesize, mul_comm]

/-- The marked mixed preserving coefficient evaluates its transitioned input fiber.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem yZeroMarked_apply (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (σ : Pattern m n)
    (r : Fin m) (c : Fin n) (k : Fin d) :
    yZeroMarked F x σ r c k =
      ∑ a ∈ (σ.lightInRow r).erase c, F.u a k *
        contract F c x (setPair σ (r, a) .two (r, c) .zero) := by
  simp [yZeroMarked, synthesize, mul_comm]

/-- The marked heavy correction coefficient evaluates its transitioned input fiber.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem hprimeMarked_apply (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (σ : Pattern m n)
    (r : Fin m) (c : Fin n) (k : Fin d) :
    hprimeMarked F x σ r c k =
      ∑ a ∈ σ.freshInRow r, F.u a k *
        contract F c x (setPair σ (r, a) .one (r, c) .zero) := by
  simp [hprimeMarked, synthesize, mul_comm]

/-- Reversing the two marked indices in an ordered sum over a single finite
set preserves multiplicity exactly.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sum_erase_comm {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → α → ℝ) :
    (∑ a ∈ s, ∑ c ∈ s.erase a, f a c) =
      ∑ c ∈ s, ∑ a ∈ s.erase c, f a c := by
  classical
  have hexpand (g : α → α → ℝ) :
      (∑ a ∈ s, ∑ c ∈ s.erase a, g a c) =
        ∑ a ∈ s, ∑ c ∈ s, if c ≠ a then g a c else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.filter_ne' s a, Finset.sum_filter]
  rw [hexpand f, hexpand (fun c a ↦ f a c)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro c hc
  by_cases h : c = a <;> simp [h, Ne.symm]

/-- Paper equation `(Yplus-coeff)` on the actual finite pattern basis.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Yplus_mulVec_marked (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (k : Fin d) (σ : Pattern m n) :
    Matrix.mulVec (Yplus m (frameRows F)) x (k, σ) =
      ∑ r, ∑ c ∈ σ.lightInRow r, yPlusMarked F x σ r c k := by
  rw [Yplus_mulVec_coeff]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  rw [yPlusMarked_apply]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [contract]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- Paper equation `(Yzero-coeff)` on the actual finite pattern basis.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Yzero_mulVec_marked (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (k : Fin d) (σ : Pattern m n) :
    Matrix.mulVec (Yzero m (frameRows F)) x (k, σ) =
      ∑ r, ∑ c ∈ σ.lightInRow r, yZeroMarked F x σ r c k := by
  rw [Yzero_mulVec_coeff]
  apply Finset.sum_congr rfl
  intro r _
  rw [sum_erase_comm]
  apply Finset.sum_congr rfl
  intro c hc
  rw [yZeroMarked_apply]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [contract]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- Paper equation `(Hprime-coeff)` on the actual finite pattern basis.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hprime_mulVec_marked (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (k : Fin d) (σ : Pattern m n) :
    Matrix.mulVec (Hprime m (frameRows F)) x (k, σ) =
      ∑ r, ∑ c ∈ σ.lightInRow r, hprimeMarked F x σ r c k := by
  rw [Hprime_mulVec_coeff]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  rw [hprimeMarked_apply]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [contract]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- The marked mixed raising energy is bounded by its input contraction energy.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem yPlusMarked_normSq_le (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (σ : Pattern m n)
    (r : Fin m) (c : Fin n) :
    ParsevalFrame.normSq (yPlusMarked F x σ r c) ≤
      ∑ a ∈ σ.heavyInRow r,
        (contract F c x (setPair σ (r, a) .one (r, c) .zero)) ^ 2 := by
  calc
    ParsevalFrame.normSq (yPlusMarked F x σ r c) ≤
        ∑ a ∈ σ.heavyInRow r,
          |contract F c x (setPair σ (r, a) .one (r, c) .zero)| ^ 2 := by
      exact subset_synthesis F (σ.heavyInRow r)
        (fun a ↦ contract F c x (setPair σ (r, a) .one (r, c) .zero))
    _ = _ := by simp only [sq_abs]

/-- The marked mixed preserving energy is bounded by its input contraction energy.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem yZeroMarked_normSq_le (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (σ : Pattern m n)
    (r : Fin m) (c : Fin n) :
    ParsevalFrame.normSq (yZeroMarked F x σ r c) ≤
      ∑ a ∈ (σ.lightInRow r).erase c,
        (contract F c x (setPair σ (r, a) .two (r, c) .zero)) ^ 2 := by
  calc
    ParsevalFrame.normSq (yZeroMarked F x σ r c) ≤
        ∑ a ∈ (σ.lightInRow r).erase c,
          |contract F c x (setPair σ (r, a) .two (r, c) .zero)| ^ 2 := by
      exact subset_synthesis F ((σ.lightInRow r).erase c)
        (fun a ↦ contract F c x (setPair σ (r, a) .two (r, c) .zero))
    _ = _ := by simp only [sq_abs]

/-- The marked heavy correction energy is bounded by its input contraction energy.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem hprimeMarked_normSq_le (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (σ : Pattern m n)
    (r : Fin m) (c : Fin n) :
    ParsevalFrame.normSq (hprimeMarked F x σ r c) ≤
      ∑ a ∈ σ.freshInRow r,
        (contract F c x (setPair σ (r, a) .one (r, c) .zero)) ^ 2 := by
  calc
    ParsevalFrame.normSq (hprimeMarked F x σ r c) ≤
        ∑ a ∈ σ.freshInRow r,
          |contract F c x (setPair σ (r, a) .one (r, c) .zero)| ^ 2 := by
      exact subset_synthesis F (σ.freshInRow r)
        (fun a ↦ contract F c x (setPair σ (r, a) .one (r, c) .zero))
    _ = _ := by simp only [sq_abs]

end

end DirectionalConcrete

end NLAlib.SparseFock
