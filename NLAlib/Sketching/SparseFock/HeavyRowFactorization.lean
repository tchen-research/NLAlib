/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.HeavyDemotionEnergy

set_option autoImplicit false

/-!
# Heavy raising row factorization

The literal typed row and column factors of the heavy raising band.
Ported from `SparseFockFormal.HeavyBandsConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock.HeavyBandsConcrete

open ParsevalFrame LocalOperator FiniteOperator ExternalOperator GlobalBands BandInventory
  NamedBands FiniteHilbert TypedBlockCS ConcreteLadder
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

variable {d m n : ℕ}

/-- Row-indexed scalar Fock output space for the block analysis operator.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
abbrev RowFock (m n : ℕ) := Fin m × Pattern m n

/-- The block column stacks the heavy creation analysis matrices over physical rows.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def AUpStack (F : Frame n d) :
    Matrix (RowFock m n) (Fin d × Pattern m n) ℝ :=
  fun out inp ↦ AUpMatrix F out.1 out.2 inp

/-- The block column stacks the heavy annihilation analysis matrices over physical rows.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def ADownStack (F : Frame n d) :
    Matrix (RowFock m n) (Fin d × Pattern m n) ℝ :=
  fun out inp ↦ ADownMatrix F out.1 out.2 inp

/-- The block row concatenates the heavy synthesis matrices over physical rows.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def BUpStack (F : Frame n d) :
    Matrix (Fin d × Pattern m n) (RowFock m n) ℝ :=
  fun out inp ↦ BUpMatrix F inp.1 out inp.2

/-- Transposing the heavy synthesis block row gives the annihilation analysis block column.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem BUpStack_transpose (F : Frame n d) :
    (BUpStack (m := m) F).transpose = ADownStack (m := m) F := by
  ext out inp
  simp only [BUpStack, ADownStack, Matrix.transpose_apply]
  simp only [BUpMatrix, ADownMatrix]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
    (rUpAt_transpose out.1 i)
  simpa [Matrix.transpose_apply] using h

/-- Creating heavy occupation twice at the same site gives the zero operator.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rUpAt_sq_zero (r : Fin m) (i : Fin n) :
    rUpAt r i * rUpAt r i = 0 := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  by_cases hout : out (r, i) = .two
  · simp only [rUpAt_apply, hout, true_and]
    rw [Finset.sum_eq_single (setSite out (r, i) .one)]
    · simp [setSite]
    · intro other _ hne
      simp [hne]
    · simp
  · simp [rUpAt_apply, hout]

/-- The external frame vectors are exposed in the coordinate form used by named bands.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def frameRows (F : Frame n d) : Fin n → Fin d → ℝ :=
  fun i k ↦ F.u i k

/-- A one-site heavy synthesis summand combines the frame coordinate with heavy creation.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def BUpOne (F : Frame n d) (r : Fin m) (i : Fin n) :
    Matrix (Fin d × Pattern m n) (Pattern m n) ℝ :=
  fun out p ↦ F.u i out.1 * rUpAt r i out.2 p

/-- A one-site heavy analysis summand combines the frame coordinate with heavy creation.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def AUpOne (F : Frame n d) (r : Fin m) (i : Fin n) :
    Matrix (Pattern m n) (Fin d × Pattern m n) ℝ :=
  fun p inp ↦ F.u i inp.1 * rUpAt r i p inp.2

/-- The heavy synthesis matrix is the sum of its one-site summands.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem BUpMatrix_eq_sum_one (F : Frame n d) (r : Fin m) :
    BUpMatrix F r = ∑ i, BUpOne F r i := by
  ext out p
  simp [BUpMatrix, BUpOne, Matrix.sum_apply]

/-- The heavy creation analysis matrix is the sum of its one-site summands.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem AUpMatrix_eq_sum_one (F : Frame n d) (r : Fin m) :
    AUpMatrix F r = ∑ i, AUpOne F r i := by
  ext p inp
  simp [AUpMatrix, AUpOne, Matrix.sum_apply]

/-- Heavy creation on distinct sites is the corresponding two-leg word kernel.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rUpAt_mul_rUpAt_of_ne (r : Fin m) {i j : Fin n} (hij : i ≠ j) :
    rUpAt r i * rUpAt r j = wordKernel (r, i) (r, j) (.rUp, .rUp) := by
  simpa [rUpAt, wordKernel, Leg.op] using
    siteKernel_mul_siteKernel_of_ne (m := m) (n := n)
      (r, i) (r, j) (by
        intro h
        exact hij (congrArg Prod.snd h)) rPromote rPromote

/-- Distinct-site heavy synthesis-analysis products are the external heavy raising word terms.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem BUpOne_mul_AUpOne_of_ne (F : Frame n d) (r : Fin m)
    {i j : Fin n} (hij : i ≠ j) :
    BUpOne F r i * AUpOne F r j =
      orderedWordTerm (frameRows F) r i j (.rUp, .rUp) := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, BUpOne, AUpOne, orderedWordTerm,
    externalTensor, ExternalOperator.outer]
  calc
    (∑ p, (F.u i out.1 * rUpAt r i out.2 p) *
        (F.u j inp.1 * rUpAt r j p inp.2)) =
        (F.u i out.1 * F.u j inp.1) *
          ∑ p, rUpAt r i out.2 p * rUpAt r j p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = (F.u i out.1 * F.u j inp.1) *
        wordKernel (r, i) (r, j) (.rUp, .rUp) out.2 inp.2 := by
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (rUpAt_mul_rUpAt_of_ne r hij)
      simpa [Matrix.mul_apply] using congrArg
        (fun t : ℝ ↦ (F.u i out.1 * F.u j inp.1) * t) h

/-- A same-site heavy synthesis-analysis product vanishes by nilpotence.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem BUpOne_mul_AUpOne_self (F : Frame n d) (r : Fin m) (i : Fin n) :
    BUpOne F r i * AUpOne F r i = 0 := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, BUpOne, AUpOne, Matrix.zero_apply]
  calc
    (∑ p, (F.u i out.1 * rUpAt r i out.2 p) *
        (F.u i inp.1 * rUpAt r i p inp.2)) =
        (F.u i out.1 * F.u i inp.1) *
          ∑ p, rUpAt r i out.2 p * rUpAt r i p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = 0 := by
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (rUpAt_sq_zero r i)
      simp only [Matrix.mul_apply, Matrix.zero_apply] at h
      rw [h, mul_zero]

/-- Exact nilpotent row-leg factorization of one physical heavy `+2` row.
The diagonal terms disappear because `R² = 0`, leaving precisely `i ≠ j`.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem BUpMatrix_mul_AUpMatrix (F : Frame n d) (r : Fin m) :
    BUpMatrix F r * AUpMatrix F r =
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        orderedWordTerm (frameRows F) r i j (.rUp, .rUp) := by
  classical
  rw [BUpMatrix_eq_sum_one, AUpMatrix_eq_sum_one, Matrix.sum_mul]
  simp_rw [Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [BUpOne_mul_AUpOne_self]
  simp only [add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  exact BUpOne_mul_AUpOne_of_ne F r (Ne.symm (Finset.mem_erase.mp hj).1)

/-- The named concrete `H₊` is exactly the product of the typed row
synthesis and analysis matrices.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hplus_eq_BUpStack_mul_AUpStack (F : Frame n d) :
    Hplus m (frameRows F) = BUpStack (m := m) F * AUpStack (m := m) F := by
  classical
  ext out inp
  simp only [Hplus, wordSum, physicalWordSum, Matrix.sum_apply,
    Matrix.mul_apply, BUpStack, AUpStack]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  have h := congrArg
    (fun M : FullOp d m n ↦ M out inp) (BUpMatrix_mul_AUpMatrix F r)
  simpa [Matrix.mul_apply, Matrix.sum_apply] using h.symm

/-- Every nonzero heavy creation analysis entry raises the pattern grade by one.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem AUpMatrix_grade_relation (F : Frame n d) (r : Fin m)
    {out : Pattern m n} {inp : Fin d × Pattern m n}
    (hentry : AUpMatrix F r out inp ≠ 0) :
    (out.grade : ℤ) = (inp.2.grade : ℤ) + 1 := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hentry
  have hk : rUpAt r i out inp.2 ≠ 0 := (mul_ne_zero_iff.mp hi).2
  have hh := siteKernel_homogeneous rPromote_homogeneous (r, i) hk
  simpa [rUpAt, gradeZ_eq_cast_grade] using hh

/-- Every nonzero heavy annihilation analysis entry lowers the pattern grade by one.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem ADownMatrix_grade_relation (F : Frame n d) (r : Fin m)
    {out : Pattern m n} {inp : Fin d × Pattern m n}
    (hentry : ADownMatrix F r out inp ≠ 0) :
    (out.grade : ℤ) + 1 = (inp.2.grade : ℤ) := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hentry
  have hk : rDownAt r i out inp.2 ≠ 0 := (mul_ne_zero_iff.mp hi).2
  have hh := siteKernel_homogeneous rDemote_homogeneous (r, i) hk
  have hz : (out.grade : ℤ) = (inp.2.grade : ℤ) - 1 := by
    simpa [rDownAt, gradeZ_eq_cast_grade, sub_eq_add_neg] using hh
  omega

end

end NLAlib.SparseFock.HeavyBandsConcrete
