/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.LightBandsConcrete
import NLAlib.Sketching.SparseFock.HeavyBandsConcrete
import NLAlib.Sketching.SparseFock.DirectionalNormalized
import NLAlib.Sketching.SparseFock.BandCoefficientBounds
import NLAlib.Sketching.SparseFock.BandEnvelope
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Mixed light-heavy row factorizations

Same-site nilpotence and exact typed factorizations of the physical mixed bands.
Ported from `SparseFockFormal.MixedBandsConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock.MixedBandsConcrete

open ParsevalFrame LocalOperator FiniteOperator ExternalOperator GlobalBands
  BandInventory NamedBands FiniteHilbert ConcreteLadder
  HeavyBandsConcrete LightBandsConcrete DirectionalConcrete
  DirectionalNormalized BandCoefficientBounds BandEnvelope
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

set_option maxHeartbeats 1000000

variable {d m n : ℕ}

/-- The lifted same-site product `P† R` vanishes in literal pattern
coordinates.

Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem pDagAt_mul_rUpAt_self (r : Fin m) (i : Fin n) :
    LightSectorConcrete.pDagAt r i * rUpAt r i = 0 := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  by_cases hout : out (r, i) = .one
  · simp only [LightBandsConcrete.pDagAt_apply, hout, true_and]
    rw [Finset.sum_eq_single (setSite out (r, i) .zero)]
    · simp [rUpAt_apply, setSite]
    · intro other _ hne
      simp [hne]
    · simp
  · simp [LightBandsConcrete.pDagAt_apply, hout]

/-- The lifted same-site product `P† R†` also vanishes.

Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem pDagAt_mul_rDownAt_self (r : Fin m) (i : Fin n) :
    LightSectorConcrete.pDagAt r i * rDownAt r i = 0 := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  by_cases hout : out (r, i) = .one
  · simp only [LightBandsConcrete.pDagAt_apply, hout, true_and]
    rw [Finset.sum_eq_single (setSite out (r, i) .zero)]
    · simp [rDownAt_apply, setSite]
    · intro other _ hne
      simp [hne]
    · simp
  · simp [LightBandsConcrete.pDagAt_apply, hout]

/-- Light creation and heavy creation at distinct sites form their mixed word kernel.
Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem pDagAt_mul_rUpAt_of_ne (r : Fin m) {i j : Fin n} (hij : i ≠ j) :
    LightSectorConcrete.pDagAt r i * rUpAt r j =
      wordKernel (r, i) (r, j) (.pUp, .rUp) := by
  simpa [LightSectorConcrete.pDagAt, rUpAt, wordKernel, Leg.op] using
    siteKernel_mul_siteKernel_of_ne (m := m) (n := n)
      (r, i) (r, j) (by
        intro h
        exact hij (congrArg Prod.snd h)) pCreate rPromote

/-- Light creation and heavy annihilation at distinct sites form their mixed word kernel.
Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem pDagAt_mul_rDownAt_of_ne (r : Fin m) {i j : Fin n} (hij : i ≠ j) :
    LightSectorConcrete.pDagAt r i * rDownAt r j =
      wordKernel (r, i) (r, j) (.pUp, .rDown) := by
  simpa [LightSectorConcrete.pDagAt, rDownAt, wordKernel, Leg.op] using
    siteKernel_mul_siteKernel_of_ne (m := m) (n := n)
      (r, i) (r, j) (by
        intro h
        exact hij (congrArg Prod.snd h)) pCreate rDemote

/-- Distinct-site light synthesis/heavy creation analysis equals the physical mixed raising term.
Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem COne_mul_AUpOne_of_ne (F : Frame n d) (r : Fin m)
    {i j : Fin n} (hij : i ≠ j) :
    LightBandsConcrete.COne F r i * HeavyBandsConcrete.AUpOne F r j =
      orderedWordTerm (DirectionalConcrete.frameRows F) r i j (.pUp, .rUp) := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, LightBandsConcrete.COne,
    HeavyBandsConcrete.AUpOne, orderedWordTerm, externalTensor,
    ExternalOperator.outer]
  calc
    (∑ p, (F.u i out.1 * LightSectorConcrete.pDagAt r i out.2 p) *
        (F.u j inp.1 * rUpAt r j p inp.2)) =
        (F.u i out.1 * F.u j inp.1) *
          ∑ p, LightSectorConcrete.pDagAt r i out.2 p *
            rUpAt r j p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = (F.u i out.1 * F.u j inp.1) *
        wordKernel (r, i) (r, j) (.pUp, .rUp) out.2 inp.2 := by
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (pDagAt_mul_rUpAt_of_ne r hij)
      simpa [Matrix.mul_apply] using congrArg
        (fun t : ℝ ↦ (F.u i out.1 * F.u j inp.1) * t) h

/-- Same-site light synthesis/heavy creation analysis has zero product.
Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem COne_mul_AUpOne_self (F : Frame n d) (r : Fin m) (i : Fin n) :
    LightBandsConcrete.COne F r i * HeavyBandsConcrete.AUpOne F r i = 0 := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, LightBandsConcrete.COne,
    HeavyBandsConcrete.AUpOne, Matrix.zero_apply]
  calc
    (∑ p, (F.u i out.1 * LightSectorConcrete.pDagAt r i out.2 p) *
        (F.u i inp.1 * rUpAt r i p inp.2)) =
        (F.u i out.1 * F.u i inp.1) *
          ∑ p, LightSectorConcrete.pDagAt r i out.2 p *
            rUpAt r i p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = 0 := by
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (pDagAt_mul_rUpAt_self r i)
      simp only [Matrix.mul_apply, Matrix.zero_apply] at h
      rw [h, mul_zero]

/-- Distinct-site light synthesis/heavy annihilation analysis equals the physical mixed preserving term.
Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem COne_mul_ADownOne_of_ne (F : Frame n d) (r : Fin m)
    {i j : Fin n} (hij : i ≠ j) :
    LightBandsConcrete.COne F r i * HeavyBandsConcrete.ADownOne F r j =
      orderedWordTerm (DirectionalConcrete.frameRows F) r i j (.pUp, .rDown) := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, LightBandsConcrete.COne,
    HeavyBandsConcrete.ADownOne, orderedWordTerm, externalTensor,
    ExternalOperator.outer]
  calc
    (∑ p, (F.u i out.1 * LightSectorConcrete.pDagAt r i out.2 p) *
        (F.u j inp.1 * rDownAt r j p inp.2)) =
        (F.u i out.1 * F.u j inp.1) *
          ∑ p, LightSectorConcrete.pDagAt r i out.2 p *
            rDownAt r j p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = (F.u i out.1 * F.u j inp.1) *
        wordKernel (r, i) (r, j) (.pUp, .rDown) out.2 inp.2 := by
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (pDagAt_mul_rDownAt_of_ne r hij)
      simpa [Matrix.mul_apply] using congrArg
        (fun t : ℝ ↦ (F.u i out.1 * F.u j inp.1) * t) h

/-- Same-site light synthesis/heavy annihilation analysis has zero product.
Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem COne_mul_ADownOne_self (F : Frame n d) (r : Fin m) (i : Fin n) :
    LightBandsConcrete.COne F r i * HeavyBandsConcrete.ADownOne F r i = 0 := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, LightBandsConcrete.COne,
    HeavyBandsConcrete.ADownOne, Matrix.zero_apply]
  calc
    (∑ p, (F.u i out.1 * LightSectorConcrete.pDagAt r i out.2 p) *
        (F.u i inp.1 * rDownAt r i p inp.2)) =
        (F.u i out.1 * F.u i inp.1) *
          ∑ p, LightSectorConcrete.pDagAt r i out.2 p *
            rDownAt r i p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = 0 := by
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (pDagAt_mul_rDownAt_self r i)
      simp only [Matrix.mul_apply, Matrix.zero_apply] at h
      rw [h, mul_zero]

/-- Exact row-local mixed raising factorization; the diagonal terms vanish.

Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem CMatrix_mul_AUpMatrix (F : Frame n d) (r : Fin m) :
    LightSectorConcrete.CMatrix F r * HeavyBandsConcrete.AUpMatrix F r =
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        orderedWordTerm (DirectionalConcrete.frameRows F) r i j (.pUp, .rUp) := by
  classical
  rw [LightBandsConcrete.CMatrix_eq_sum_COne,
    HeavyBandsConcrete.AUpMatrix_eq_sum_one, Matrix.sum_mul]
  simp_rw [Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [COne_mul_AUpOne_self]
  simp only [add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  exact COne_mul_AUpOne_of_ne F r (Ne.symm (Finset.mem_erase.mp hj).1)

/-- Exact row-local grade-preserving mixed factorization.

Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem CMatrix_mul_ADownMatrix (F : Frame n d) (r : Fin m) :
    LightSectorConcrete.CMatrix F r * HeavyBandsConcrete.ADownMatrix F r =
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        orderedWordTerm (DirectionalConcrete.frameRows F) r i j (.pUp, .rDown) := by
  classical
  rw [LightBandsConcrete.CMatrix_eq_sum_COne,
    HeavyBandsConcrete.ADownMatrix_eq_sum_one, Matrix.sum_mul]
  simp_rw [Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [COne_mul_ADownOne_self]
  simp only [add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  exact COne_mul_ADownOne_of_ne F r (Ne.symm (Finset.mem_erase.mp hj).1)

/-- The physical `X₊` word sum is literally `CStack * AUpStack`.

Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Xplus_eq_CStack_mul_AUpStack (F : Frame n d) :
    Xplus m (DirectionalConcrete.frameRows F) =
      LightBandsConcrete.CStack (m := m) F *
        HeavyBandsConcrete.AUpStack (m := m) F := by
  classical
  ext out inp
  simp only [Xplus, NamedBands.wordSum, physicalWordSum, Matrix.sum_apply,
    Matrix.mul_apply, LightBandsConcrete.CStack,
    HeavyBandsConcrete.AUpStack]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  have h := congrArg (fun M : FullOp d m n ↦ M out inp)
    (CMatrix_mul_AUpMatrix F r)
  simpa [Matrix.mul_apply, Matrix.sum_apply] using h.symm

/-- The physical `X₀` word sum is literally `CStack * ADownStack`.

Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Xzero_eq_CStack_mul_ADownStack (F : Frame n d) :
    Xzero m (DirectionalConcrete.frameRows F) =
      LightBandsConcrete.CStack (m := m) F *
        HeavyBandsConcrete.ADownStack (m := m) F := by
  classical
  ext out inp
  simp only [Xzero, NamedBands.wordSum, physicalWordSum, Matrix.sum_apply,
    Matrix.mul_apply, LightBandsConcrete.CStack,
    HeavyBandsConcrete.ADownStack]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  have h := congrArg (fun M : FullOp d m n ↦ M out inp)
    (CMatrix_mul_ADownMatrix F r)
  simpa [Matrix.mul_apply, Matrix.sum_apply] using h.symm

/-- Fully projected typed factorization of `X₊` on input grade `nu`.

Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Xplus_grade_factor (F : Frame n d) (nu : ℕ) :
    Xplus m (DirectionalConcrete.frameRows F) *
        gradeProjection (d := d) (m := m) (n := n) nu =
      (gradeProjection (d := d) (m := m) (n := n) (nu + 2) *
          LightBandsConcrete.CStack (m := m) F *
          HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) (nu + 1)) *
        (HeavyBandsConcrete.AUpStack (m := m) F *
          gradeProjection (d := d) (m := m) (n := n) nu) := by
  rw [Xplus_eq_CStack_mul_AUpStack]
  have hins := HeavyBandsConcrete.rowProjection_AUpStack_gradeProjection
    (m := m) F nu
  have hout := LightBandsConcrete.gradeProjection_CStack_rowProjection
    (m := m) F (nu + 1)
  have hout' :
      gradeProjection (d := d) (m := m) (n := n) (nu + 2) *
          LightBandsConcrete.CStack (m := m) F *
          HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) (nu + 1) =
        LightBandsConcrete.CStack (m := m) F *
          HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) (nu + 1) := by
    convert hout using 1
  calc
    (LightBandsConcrete.CStack (m := m) F *
        HeavyBandsConcrete.AUpStack (m := m) F) * gradeProjection (d := d) nu =
      LightBandsConcrete.CStack (m := m) F *
        (HeavyBandsConcrete.AUpStack (m := m) F * gradeProjection (d := d) nu) := by
      rw [Matrix.mul_assoc]
    _ = LightBandsConcrete.CStack (m := m) F *
        (HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) (nu + 1) *
          HeavyBandsConcrete.AUpStack (m := m) F * gradeProjection (d := d) nu) := by
      rw [hins]
    _ = (LightBandsConcrete.CStack (m := m) F *
          HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) (nu + 1)) *
        (HeavyBandsConcrete.AUpStack (m := m) F * gradeProjection (d := d) nu) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hout']

/-- Fully projected typed factorization of `X₀` on positive input grade.

Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Xzero_grade_factor_add_one (F : Frame n d) (k : ℕ) :
    Xzero m (DirectionalConcrete.frameRows F) *
        gradeProjection (d := d) (m := m) (n := n) (k + 1) =
      (gradeProjection (d := d) (m := m) (n := n) (k + 1) *
          LightBandsConcrete.CStack (m := m) F *
          HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) k) *
        (HeavyBandsConcrete.ADownStack (m := m) F *
          gradeProjection (d := d) (m := m) (n := n) (k + 1)) := by
  rw [Xzero_eq_CStack_mul_ADownStack]
  have hins := HeavyBandsConcrete.rowProjection_ADownStack_output
    (m := m) F k
  have hout := LightBandsConcrete.gradeProjection_CStack_rowProjection
    (m := m) F k
  calc
    (LightBandsConcrete.CStack (m := m) F *
        HeavyBandsConcrete.ADownStack (m := m) F) *
          gradeProjection (d := d) (k + 1) =
      LightBandsConcrete.CStack (m := m) F *
        (HeavyBandsConcrete.ADownStack (m := m) F *
          gradeProjection (d := d) (k + 1)) := by
      rw [Matrix.mul_assoc]
    _ = LightBandsConcrete.CStack (m := m) F *
        (HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) k *
          HeavyBandsConcrete.ADownStack (m := m) F *
            gradeProjection (d := d) (k + 1)) := by
      rw [hins]
    _ = (LightBandsConcrete.CStack (m := m) F *
          HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) k) *
        (HeavyBandsConcrete.ADownStack (m := m) F *
          gradeProjection (d := d) (k + 1)) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hout]

/-- The mixed preserving analysis band vanishes on grade-zero input.
Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Xzero_gradeProjection_zero (F : Frame n d) :
    Xzero m (DirectionalConcrete.frameRows F) *
      gradeProjection (d := d) (m := m) (n := n) 0 = 0 := by
  rw [Xzero_eq_CStack_mul_ADownStack, Matrix.mul_assoc,
    HeavyBandsConcrete.ADownStack_gradeProjection_zero, Matrix.mul_zero]

/-- Transposing the mixed raising band gives its named adjoint band.
Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem transpose_Xplus (u : Fin n → Fin d → ℝ) :
    (Xplus m u).transpose = XplusAdj m u := by
  simpa [Xplus, XplusAdj, NamedBands.wordSum, Word.orderedAdjoint,
    Leg.adjoint] using
    DirectionalConcrete.transpose_physicalWordSum (m := m) u (.pUp, .rUp)

/-- Transposing the named mixed raising adjoint returns the raising band.
Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem transpose_XplusAdj (u : Fin n → Fin d → ℝ) :
    (XplusAdj m u).transpose = Xplus m u := by
  rw [← transpose_Xplus (m := m) u, Matrix.transpose_transpose]

/-- Transposing the mixed preserving band gives its named adjoint band.
Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem transpose_Xzero (u : Fin n → Fin d → ℝ) :
    (Xzero m u).transpose = XzeroAdj m u := by
  simpa [Xzero, XzeroAdj, NamedBands.wordSum, Word.orderedAdjoint,
    Leg.adjoint] using
    DirectionalConcrete.transpose_physicalWordSum (m := m) u (.pUp, .rDown)

/-- Transposing the named mixed preserving adjoint returns the preserving band.
Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem transpose_XzeroAdj (u : Fin n → Fin d → ℝ) :
    (XzeroAdj m u).transpose = Xzero m u := by
  rw [← transpose_Xzero (m := m) u, Matrix.transpose_transpose]

/-- The mixed raising band has grade shift two.
Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Xplus_homogeneous (F : Frame n d) :
    ExternalOperator.Homogeneous 2
      (Xplus m (DirectionalConcrete.frameRows F)) := by
  simpa [Xplus, NamedBands.wordSum, Word.degree, Leg.degree] using
    DirectionalConcrete.physicalWordSum_homogeneous
      (m := m) (DirectionalConcrete.frameRows F) (.pUp, .rUp)

/-- The mixed preserving band has grade shift zero.
Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Xzero_homogeneous (F : Frame n d) :
    ExternalOperator.Homogeneous 0
      (Xzero m (DirectionalConcrete.frameRows F)) := by
  simpa [Xzero, NamedBands.wordSum, Word.degree, Leg.degree] using
    DirectionalConcrete.physicalWordSum_homogeneous
      (m := m) (DirectionalConcrete.frameRows F) (.pUp, .rDown)

/-- The mixed raising adjoint has grade shift minus two.
Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem XplusAdj_homogeneous (F : Frame n d) :
    ExternalOperator.Homogeneous (-2)
      (XplusAdj m (DirectionalConcrete.frameRows F)) := by
  simpa [XplusAdj, NamedBands.wordSum, Word.degree, Leg.degree] using
    DirectionalConcrete.physicalWordSum_homogeneous
      (m := m) (DirectionalConcrete.frameRows F) (.rDown, .pDown)

/-- The mixed preserving adjoint has grade shift zero.
Source: ported from `SparseFockFormal.MixedBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem XzeroAdj_homogeneous (F : Frame n d) :
    ExternalOperator.Homogeneous 0
      (XzeroAdj m (DirectionalConcrete.frameRows F)) := by
  simpa [XzeroAdj, NamedBands.wordSum, Word.degree, Leg.degree] using
    DirectionalConcrete.physicalWordSum_homogeneous
      (m := m) (DirectionalConcrete.frameRows F) (.rUp, .pDown)

end

end NLAlib.SparseFock.MixedBandsConcrete
