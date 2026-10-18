import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.Abel

/-! # Filling a finite rectangular edge cycle

Horizontal edges point east and vertical edges point north. At a vertex the
outgoing minus incoming coefficient is zero. Edges leaving the finite grid
are absent; perimeter edges themselves may have nonzero coefficients.

Finite prefix sums construct the cell coefficients. The horizontal and
vertical differences recover every edge, and pairing with arbitrary edge
values telescopes to the weighted counterclockwise cell boundaries.

Ported from the local deferred Jordan-contour development of 2026-10-14.
The coefficients are constructed explicitly; no filling or cancellation
identity is an assumption of the resulting theorem.
-/

noncomputable section
open Finset

namespace Fin

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] {n : ℕ}

/-- The finite difference of a tuple, extended by zero at both ends. -/
def edgeBoundary (c : Fin n → A) (i : Fin (n + 1)) : A :=
  snoc (α := fun _ => A) c 0 i - cons (α := fun _ => A) 0 c i

/-- Finite differences commute with additive homomorphisms. -/
theorem map_edgeBoundary (f : A →+ B) (c : Fin n → A) (i : Fin (n + 1)) :
    f (edgeBoundary c i) = edgeBoundary (fun k => f (c k)) i := by
  have hs : f (snoc (α := fun _ => A) c 0 i) = snoc (α := fun _ => B) (fun k => f (c k)) 0 i := by
    refine Fin.lastCases ?_ (fun k => ?_) i <;> simp
  have hc : f (cons (α := fun _ => A) 0 c i) = cons (α := fun _ => B) 0 (fun k => f (c k)) i := by
    refine Fin.cases ?_ (fun k => ?_) i <;> simp
  simp only [edgeBoundary, map_sub, hs, hc]

/-- The finite difference map is additive. -/
def edgeBoundaryHom (n : ℕ) : (Fin n → A) →+ (Fin (n + 1) → A) where
  toFun := edgeBoundary
  map_zero' := by
    ext i
    simp only [edgeBoundary, Pi.zero_apply]
    have hs : snoc (α := fun _ => A) (0 : Fin n → A) 0 i = 0 := by
      refine Fin.lastCases ?_ (fun k => ?_) i <;> simp
    have hc : cons (α := fun _ => A) 0 (0 : Fin n → A) i = 0 := by
      refine Fin.cases ?_ (fun k => ?_) i <;> simp
    rw [hs, hc, sub_self]
  map_add' c d := by
    ext i
    have hs : snoc (α := fun _ => A) (c + d) 0 i = snoc (α := fun _ => A) c 0 i + snoc (α := fun _ => A) d 0 i := by
      refine Fin.lastCases ?_ (fun k => ?_) i <;> simp
    have hc : cons (α := fun _ => A) 0 (c + d) i = cons (α := fun _ => A) 0 c i + cons (α := fun _ => A) 0 d i := by
      refine Fin.cases ?_ (fun k => ?_) i <;> simp
    simp only [edgeBoundary, Pi.add_apply, hs, hc]
    abel

/-- The total of a finite boundary is zero. -/
theorem sum_edgeBoundary (c : Fin n → A) : ∑ i, edgeBoundary c i = 0 := by
  simp only [edgeBoundary]
  rw [sum_sub_distrib, Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  simp

/-- A finite tuple with zero boundary is zero. -/
theorem eq_zero_of_edgeBoundary_eq_zero (c : Fin n → A)
    (h : ∀ i, edgeBoundary c i = 0) : c = 0 := by
  cases n with
  | zero => ext i; exact i.elim0
  | succ n =>
    ext i
    induction i using Fin.induction with
    | zero => simpa [edgeBoundary] using h 0
    | succ i hi =>
      have hh := h i.succ.castSucc
      rw [edgeBoundary, Fin.snoc_castSucc, Fin.castSucc_succ, Fin.cons_succ] at hh
      simpa only [sub_eq_zero, hi, Pi.zero_apply] using hh

/-- The cell primitive is the inclusive prefix sum of the edge tuple. -/
def edgePrefix (h : Fin (n + 1) → A) (i : Fin n) : A :=
  partialSum h i.castSucc.succ

/-- The final partial sum is the full finite sum. -/
theorem partialSum_last_eq_sum (h : Fin n → A) :
    partialSum h (last n) = ∑ i, h i := by
  unfold partialSum
  change (List.take n (List.ofFn h)).sum = _
  rw [List.take_of_length_le (by simp)]
  exact Fin.sum_ofFn h

/-- Prefix sums recover a tuple of total zero as a finite boundary. -/
theorem edgeBoundary_edgePrefix (h : Fin (n + 1) → A) (hsum : ∑ i, h i = 0)
    (j : Fin (n + 1)) : edgeBoundary (edgePrefix h) j = h j := by
  have hlo : snoc (α := fun _ => A) (edgePrefix h) 0 j = partialSum h j.succ := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [partialSum_last_eq_sum, hsum]
    · simp [edgePrefix]
  have hhi : cons (α := fun _ => A) 0 (edgePrefix h) j = partialSum h j.castSucc := by
    refine Fin.cases ?_ (fun i => ?_) j
    · simp
    · simp [edgePrefix, Fin.castSucc_succ]
  rw [edgeBoundary, hlo, hhi]
  rw [partialSum_succ]
  abel

end Fin

namespace RectangularChain

variable {A : Type*} [AddCommGroup A] {m n : ℕ}

/-- A signed edge cycle on the rectangular grid with `(m+1)(n+1)` vertices.
The finite difference pads absent outgoing and incoming edges with zero. -/
def IsCycle (horizontal : Fin m → Fin (n + 1) → A)
    (vertical : Fin (m + 1) → Fin n → A) : Prop :=
  ∀ i j, Fin.edgeBoundary horizontal i j + Fin.edgeBoundary (vertical i) j = 0

/-- The explicit coefficient of each cell, obtained by horizontal prefix sums. -/
def cellCoefficients (horizontal : Fin m → Fin (n + 1) → A) : Fin m → Fin n → A :=
  fun i => Fin.edgePrefix (horizontal i)

/-- Conservation forces the total of each horizontal column to be zero. -/
theorem sum_horizontal_eq_zero
    (horizontal : Fin m → Fin (n + 1) → A)
    (vertical : Fin (m + 1) → Fin n → A) (hcycle : IsCycle horizontal vertical)
    (i : Fin m) : ∑ j, horizontal i j = 0 := by
  let s : (Fin (n + 1) → A) →+ A :=
    { toFun := fun f => ∑ j, f j
      map_zero' := by simp
      map_add' := by intro f g; simp [sum_add_distrib] }
  have hb : ∀ k, Fin.edgeBoundary (fun i => ∑ j, horizontal i j) k = 0 := by
    intro k
    have hh : (∑ j, Fin.edgeBoundary horizontal k j) =
        Fin.edgeBoundary (fun i => ∑ j, horizontal i j) k :=
      Fin.map_edgeBoundary s horizontal k
    have hz : (∑ j, (Fin.edgeBoundary horizontal k j +
        Fin.edgeBoundary (vertical k) j)) = 0 := by
      exact sum_eq_zero (fun j _ => hcycle k j)
    rw [sum_add_distrib, Fin.sum_edgeBoundary, add_zero, hh] at hz
    exact hz
  exact congrFun (Fin.eq_zero_of_edgeBoundary_eq_zero _ hb) i

/-- The horizontal differences of the prefix coefficients recover every
horizontal edge, including both sides of the rectangle. -/
theorem horizontal_eq_cell_boundary
    (horizontal : Fin m → Fin (n + 1) → A)
    (vertical : Fin (m + 1) → Fin n → A) (hcycle : IsCycle horizontal vertical)
    (i : Fin m) (j : Fin (n + 1)) :
    horizontal i j = Fin.edgeBoundary (cellCoefficients horizontal i) j := by
  exact (Fin.edgeBoundary_edgePrefix (horizontal i)
    (sum_horizontal_eq_zero horizontal vertical hcycle i) j).symm

/-- The vertical differences of the same coefficients recover every vertical
edge. No additional condition on interior edges is assumed. -/
theorem vertical_eq_cell_boundary
    (horizontal : Fin m → Fin (n + 1) → A)
    (vertical : Fin (m + 1) → Fin n → A) (hcycle : IsCycle horizontal vertical)
    (i : Fin (m + 1)) (j : Fin n) :
    vertical i j = -Fin.edgeBoundary (cellCoefficients horizontal) i j := by
  let c := cellCoefficients horizontal
  have hh : (fun k => Fin.edgeBoundary (c k)) = horizontal := by
    ext k l
    exact (horizontal_eq_cell_boundary horizontal vertical hcycle k l).symm
  have hcomm : Fin.edgeBoundary (Fin.edgeBoundary c i) =
      Fin.edgeBoundary horizontal i := by
    have h := Fin.map_edgeBoundary (Fin.edgeBoundaryHom n) c i
    change Fin.edgeBoundary (Fin.edgeBoundary c i) =
      Fin.edgeBoundary (fun k => Fin.edgeBoundary (c k)) i at h
    rwa [hh] at h
  have hz : Fin.edgeBoundary (vertical i + Fin.edgeBoundary c i) = 0 := by
    have ha := (Fin.edgeBoundaryHom n).map_add (vertical i) (Fin.edgeBoundary c i)
    change Fin.edgeBoundary (vertical i + Fin.edgeBoundary c i) =
      Fin.edgeBoundary (vertical i) + Fin.edgeBoundary (Fin.edgeBoundary c i) at ha
    rw [ha, hcomm]
    ext l
    simpa only [Pi.add_apply, Pi.zero_apply, add_comm] using hcycle i l
  have hv := Fin.eq_zero_of_edgeBoundary_eq_zero
    (vertical i + Fin.edgeBoundary c i) (fun l => congrFun hz l)
  have hp := congrFun hv j
  exact eq_neg_of_add_eq_zero_left hp

end RectangularChain

namespace Fin

variable {R B : Type*} [Ring R] [AddCommGroup B] [Module R B] {n : ℕ}

/-- Summation by parts for a finite coefficient boundary and arbitrary edge
values. The end coefficients are padded by zero. -/
theorem sum_edgeBoundary_smul (c : Fin n → R) (e : Fin (n + 1) → B) :
    (∑ j, edgeBoundary c j • e j) =
      ∑ i, c i • (e i.castSucc - e i.succ) := by
  simp only [edgeBoundary, sub_smul]
  rw [sum_sub_distrib]
  have hlo : (∑ j, snoc (α := fun _ => R) c 0 j • e j) =
      ∑ i, c i • e i.castSucc := by
    rw [Fin.sum_univ_castSucc]
    simp
  have hhi : (∑ j, cons (α := fun _ => R) 0 c j • e j) =
      ∑ i, c i • e i.succ := by
    rw [Fin.sum_univ_succ]
    simp
  rw [hlo, hhi, ← sum_sub_distrib]
  simp only [smul_sub]

end Fin

namespace RectangularChain

variable {R B : Type*} [Ring R] [AddCommGroup B] [Module R B] {m n : ℕ}

/-- Pairing a finite signed grid cycle with arbitrary edge values equals the
sum of its prefix coefficients times counterclockwise cell boundaries.
In particular, this applies to integer traversal counts and complex periods. -/
theorem sum_edges_eq_sum_cell_boundaries
    (horizontal : Fin m → Fin (n + 1) → R)
    (vertical : Fin (m + 1) → Fin n → R) (hcycle : IsCycle horizontal vertical)
    (h : Fin m → Fin (n + 1) → B) (v : Fin (m + 1) → Fin n → B) :
    (∑ i, ∑ j, horizontal i j • h i j) + (∑ i, ∑ j, vertical i j • v i j) =
      ∑ i, ∑ j, cellCoefficients horizontal i j •
        (h i j.castSucc + v i.succ j - h i j.succ - v i.castSucc j) := by
  have hh : (∑ i, ∑ j, horizontal i j • h i j) =
      ∑ i, ∑ j, cellCoefficients horizontal i j • (h i j.castSucc - h i j.succ) := by
    apply sum_congr rfl
    intro i _
    simp_rw [horizontal_eq_cell_boundary horizontal vertical hcycle]
    exact Fin.sum_edgeBoundary_smul _ _
  have hv : (∑ i, ∑ j, vertical i j • v i j) =
      ∑ i, ∑ j, cellCoefficients horizontal i j • (v i.succ j - v i.castSucc j) := by
    rw [sum_comm]
    conv_rhs => rw [sum_comm]
    apply sum_congr rfl
    intro j _
    simp_rw [vertical_eq_cell_boundary horizontal vertical hcycle, neg_smul]
    rw [sum_neg_distrib]
    have hs := Fin.sum_edgeBoundary_smul
      (fun i => cellCoefficients horizontal i j) (fun i => v i j)
    have he : (fun i => Fin.edgeBoundary (cellCoefficients horizontal) i j) =
        Fin.edgeBoundary (fun i => cellCoefficients horizontal i j) := by
      ext i
      exact Fin.map_edgeBoundary (Pi.evalAddMonoidHom (fun _ : Fin n => R) j) _ i
    simp_rw [← he] at hs
    rw [hs, ← sum_neg_distrib]
    simp only [← smul_neg, neg_sub]
  rw [hh, hv, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  rw [← smul_add]
  congr 1
  abel

end RectangularChain
