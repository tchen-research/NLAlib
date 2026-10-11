/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.HeavyLoweringBound

set_option autoImplicit false

/-!
# Heavy preserving Gram factorization

Heavy hopping Gram matrices and their same-site diagonal corrections.
Ported from `SparseFockFormal.HeavyBandsConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock.HeavyBandsConcrete

open ParsevalFrame LocalOperator FiniteOperator ExternalOperator GlobalBands BandInventory
  NamedBands FiniteHilbert TypedBlockCS ConcreteLadder
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

variable {d m n : ℕ}

/-- A one-site heavy annihilation analysis summand is expressed on the concrete finite basis.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def ADownOne (F : Frame n d) (r : Fin m) (i : Fin n) :
    Matrix (Pattern m n) (Fin d × Pattern m n) ℝ :=
  fun p inp ↦ F.u i inp.1 * rDownAt r i p inp.2

/-- The heavy annihilation analysis matrix is the sum of its one-site summands.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem ADownMatrix_eq_sum_one (F : Frame n d) (r : Fin m) :
    ADownMatrix F r = ∑ i, ADownOne F r i := by
  ext p inp
  simp [ADownMatrix, ADownOne, Matrix.sum_apply]

/-- Annihilation followed by creation at distinct sites is its two-leg word kernel.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rDownAt_mul_rUpAt_of_ne (r : Fin m) {i j : Fin n} (hij : i ≠ j) :
    rDownAt r i * rUpAt r j = wordKernel (r, i) (r, j) (.rDown, .rUp) := by
  simpa [rDownAt, rUpAt, wordKernel, Leg.op] using
    siteKernel_mul_siteKernel_of_ne (m := m) (n := n)
      (r, i) (r, j) (by
        intro h
        exact hij (congrArg Prod.snd h)) rDemote rPromote

/-- Creation followed by annihilation at distinct sites is its two-leg word kernel.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rUpAt_mul_rDownAt_of_ne (r : Fin m) {i j : Fin n} (hij : i ≠ j) :
    rUpAt r i * rDownAt r j = wordKernel (r, i) (r, j) (.rUp, .rDown) := by
  simpa [rDownAt, rUpAt, wordKernel, Leg.op] using
    siteKernel_mul_siteKernel_of_ne (m := m) (n := n)
      (r, i) (r, j) (by
        intro h
        exact hij (congrArg Prod.snd h)) rPromote rDemote

/-- Distinct creation-analysis Gram terms equal the corresponding physical heavy hopping word.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem AUpOne_transpose_mul_AUpOne_of_ne (F : Frame n d) (r : Fin m)
    {i j : Fin n} (hij : i ≠ j) :
    (AUpOne F r i).transpose * AUpOne F r j =
      orderedWordTerm (frameRows F) r i j (.rDown, .rUp) := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.transpose_apply, AUpOne, orderedWordTerm,
    externalTensor, ExternalOperator.outer]
  calc
    (∑ p, (F.u i out.1 * rUpAt r i p out.2) *
        (F.u j inp.1 * rUpAt r j p inp.2)) =
      (F.u i out.1 * F.u j inp.1) *
        ∑ p, rDownAt r i out.2 p * rUpAt r j p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      have ht := congrArg (fun K : FockOp m n ↦ K out.2 p)
        (rUpAt_transpose r i)
      simp only [Matrix.transpose_apply] at ht
      rw [← ht]
      ring
    _ = (F.u i out.1 * F.u j inp.1) *
        wordKernel (r, i) (r, j) (.rDown, .rUp) out.2 inp.2 := by
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (rDownAt_mul_rUpAt_of_ne r hij)
      simpa [Matrix.mul_apply] using congrArg
        (fun t : ℝ ↦ (F.u i out.1 * F.u j inp.1) * t) h

/-- Distinct annihilation-analysis Gram terms equal the corresponding physical heavy hopping word.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem ADownOne_transpose_mul_ADownOne_of_ne (F : Frame n d) (r : Fin m)
    {i j : Fin n} (hij : i ≠ j) :
    (ADownOne F r i).transpose * ADownOne F r j =
      orderedWordTerm (frameRows F) r i j (.rUp, .rDown) := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.transpose_apply, ADownOne, orderedWordTerm,
    externalTensor, ExternalOperator.outer]
  calc
    (∑ p, (F.u i out.1 * rDownAt r i p out.2) *
        (F.u j inp.1 * rDownAt r j p inp.2)) =
      (F.u i out.1 * F.u j inp.1) *
        ∑ p, rUpAt r i out.2 p * rDownAt r j p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      have ht := congrArg (fun K : FockOp m n ↦ K out.2 p)
        (rDownAt_transpose r i)
      simp only [Matrix.transpose_apply] at ht
      rw [← ht]
      ring
    _ = (F.u i out.1 * F.u j inp.1) *
        wordKernel (r, i) (r, j) (.rUp, .rDown) out.2 inp.2 := by
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (rUpAt_mul_rDownAt_of_ne r hij)
      simpa [Matrix.mul_apply] using congrArg
        (fun t : ℝ ↦ (F.u i out.1 * F.u j inp.1) * t) h

/-- The creation diagonal correction sums the same-site creation-analysis Gram terms.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def DUp (F : Frame n d) : FullOp d m n :=
  ∑ r, ∑ i, (AUpOne F r i).transpose * AUpOne F r i

/-- The annihilation diagonal correction sums the same-site annihilation-analysis Gram terms.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def DDown (F : Frame n d) : FullOp d m n :=
  ∑ r, ∑ i, (ADownOne F r i).transpose * ADownOne F r i

/-- A row creation Gram matrix splits into distinct-site words and its same-site diagonal correction.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem AUpMatrix_gram_row (F : Frame n d) (r : Fin m) :
    (AUpMatrix F r).transpose * AUpMatrix F r =
      (∑ i, ∑ j ∈ Finset.univ.erase i,
        orderedWordTerm (frameRows F) r i j (.rDown, .rUp)) +
      ∑ i, (AUpOne F r i).transpose * AUpOne F r i := by
  classical
  rw [AUpMatrix_eq_sum_one, Matrix.transpose_sum, Matrix.sum_mul]
  simp_rw [Matrix.mul_sum]
  calc
    (∑ i, ∑ j, (AUpOne F r i).transpose * AUpOne F r j) =
      ∑ i, ((∑ j ∈ Finset.univ.erase i,
        (AUpOne F r i).transpose * AUpOne F r j) +
          (AUpOne F r i).transpose * AUpOne F r i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
    _ = (∑ i, ∑ j ∈ Finset.univ.erase i,
        (AUpOne F r i).transpose * AUpOne F r j) +
        ∑ i, (AUpOne F r i).transpose * AUpOne F r i := by
      rw [Finset.sum_add_distrib]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j hj
      exact AUpOne_transpose_mul_AUpOne_of_ne F r
        (Ne.symm (Finset.mem_erase.mp hj).1)

/-- A row annihilation Gram matrix splits into distinct-site words and its same-site diagonal correction.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem ADownMatrix_gram_row (F : Frame n d) (r : Fin m) :
    (ADownMatrix F r).transpose * ADownMatrix F r =
      (∑ i, ∑ j ∈ Finset.univ.erase i,
        orderedWordTerm (frameRows F) r i j (.rUp, .rDown)) +
      ∑ i, (ADownOne F r i).transpose * ADownOne F r i := by
  classical
  rw [ADownMatrix_eq_sum_one, Matrix.transpose_sum, Matrix.sum_mul]
  simp_rw [Matrix.mul_sum]
  calc
    (∑ i, ∑ j, (ADownOne F r i).transpose * ADownOne F r j) =
      ∑ i, ((∑ j ∈ Finset.univ.erase i,
        (ADownOne F r i).transpose * ADownOne F r j) +
          (ADownOne F r i).transpose * ADownOne F r i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
    _ = (∑ i, ∑ j ∈ Finset.univ.erase i,
        (ADownOne F r i).transpose * ADownOne F r j) +
        ∑ i, (ADownOne F r i).transpose * ADownOne F r i := by
      rw [Finset.sum_add_distrib]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j hj
      exact ADownOne_transpose_mul_ADownOne_of_ne F r
        (Ne.symm (Finset.mem_erase.mp hj).1)

/-- The creation stack Gram matrix splits into its heavy hopping word and diagonal correction.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem AUpStack_gram (F : Frame n d) :
    (AUpStack (m := m) F).transpose * AUpStack (m := m) F =
      wordSum m (frameRows F) .rDown .rUp + DUp (m := m) F := by
  classical
  calc
    (AUpStack (m := m) F).transpose * AUpStack (m := m) F =
        ∑ r, (AUpMatrix F r).transpose * AUpMatrix F r := by
      ext out inp
      simp only [Matrix.mul_apply, Matrix.transpose_apply, AUpStack,
        Matrix.sum_apply]
      rw [Fintype.sum_prod_type]
    _ = ∑ r, ((∑ i, ∑ j ∈ Finset.univ.erase i,
          orderedWordTerm (frameRows F) r i j (.rDown, .rUp)) +
        ∑ i, (AUpOne F r i).transpose * AUpOne F r i) := by
      apply Finset.sum_congr rfl
      intro r _
      exact AUpMatrix_gram_row F r
    _ = (∑ r, ∑ i, ∑ j ∈ Finset.univ.erase i,
          orderedWordTerm (frameRows F) r i j (.rDown, .rUp)) +
        ∑ r, ∑ i, (AUpOne F r i).transpose * AUpOne F r i := by
      rw [Finset.sum_add_distrib]
    _ = wordSum m (frameRows F) .rDown .rUp + DUp (m := m) F := by
      rfl

/-- The annihilation stack Gram matrix splits into its heavy hopping word and diagonal correction.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem ADownStack_gram (F : Frame n d) :
    (ADownStack (m := m) F).transpose * ADownStack (m := m) F =
      wordSum m (frameRows F) .rUp .rDown + DDown (m := m) F := by
  classical
  calc
    (ADownStack (m := m) F).transpose * ADownStack (m := m) F =
        ∑ r, (ADownMatrix F r).transpose * ADownMatrix F r := by
      ext out inp
      simp only [Matrix.mul_apply, Matrix.transpose_apply, ADownStack,
        Matrix.sum_apply]
      rw [Fintype.sum_prod_type]
    _ = ∑ r, ((∑ i, ∑ j ∈ Finset.univ.erase i,
          orderedWordTerm (frameRows F) r i j (.rUp, .rDown)) +
        ∑ i, (ADownOne F r i).transpose * ADownOne F r i) := by
      apply Finset.sum_congr rfl
      intro r _
      exact ADownMatrix_gram_row F r
    _ = (∑ r, ∑ i, ∑ j ∈ Finset.univ.erase i,
          orderedWordTerm (frameRows F) r i j (.rUp, .rDown)) +
        ∑ r, ∑ i, (ADownOne F r i).transpose * ADownOne F r i := by
      rw [Finset.sum_add_distrib]
    _ = wordSum m (frameRows F) .rUp .rDown + DDown (m := m) F := by
      rfl

end

end NLAlib.SparseFock.HeavyBandsConcrete
