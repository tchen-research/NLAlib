/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.LightSectorConcrete
import NLAlib.Sketching.SparseFock.DirectionalNormalized
import NLAlib.Sketching.SparseFock.HeavyBandsConcrete
import NLAlib.Sketching.SparseFock.ConcreteLadder
import NLAlib.Sketching.SparseFock.TypedBlockCS
import NLAlib.Sketching.SparseFock.BandEnvelope
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Light raising row factorization

Literal creation analysis and synthesis matrices and their exact middle-grade factorization.
Ported from `SparseFockFormal.LightBandsConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace NLAlib.SparseFock.LightBandsConcrete

open ParsevalFrame LocalOperator FiniteOperator ExternalOperator FiniteHilbert
open NamedBands ConcreteLadder DirectionalConcrete DirectionalNormalized
open LightSectorConcrete
open BandInventory GlobalBands

noncomputable section

variable {d m n : ℕ}

/-- The common middle space: one scalar Fock copy for every physical row.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
abbrev RowFock (m n : ℕ) := HeavyBandsConcrete.RowFock m n

/-- One creation-synthesis summand `u_i ⊗ P†_(r,i)`.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def COne (F : Frame n d) (r : Fin m) (i : Fin n) :
    Matrix (Fin d × Pattern m n) (Pattern m n) ℝ :=
  fun out inp ↦ F.u i out.1 * pDagAt r i out.2 inp

/-- One creation-analysis summand.  Its external index is on the input side.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def cOne (F : Frame n d) (r : Fin m) (i : Fin n) :
    Matrix (Pattern m n) (Fin d × Pattern m n) ℝ :=
  fun out inp ↦ F.u i inp.1 * pDagAt r i out inp.2

/-- The row-local creation-analysis operator `c_r`.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def cMatrix (F : Frame n d) (r : Fin m) :
    Matrix (Pattern m n) (Fin d × Pattern m n) ℝ :=
  ∑ i, cOne F r i

/-- Row-stacked creation synthesis.  This is reusable in the mixed bands.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def CStack (F : Frame n d) :
    Matrix (Fin d × Pattern m n) (RowFock m n) ℝ :=
  fun out inp ↦ CMatrix F inp.1 out inp.2

/-- Row-stacked creation analysis.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def CreateAnalysisStack (F : Frame n d) :
    Matrix (RowFock m n) (Fin d × Pattern m n) ℝ :=
  fun out inp ↦ cMatrix F out.1 out.2 inp

/-- The row light creation synthesis matrix is the sum of its one-site summands.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem CMatrix_eq_sum_COne (F : Frame n d) (r : Fin m) :
    CMatrix F r = ∑ i, COne F r i := by
  ext out inp
  simp [CMatrix, COne, Matrix.sum_apply]

/-- The row light creation analysis matrix is the sum of its one-site summands.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem cMatrix_eq_sum_cOne (F : Frame n d) (r : Fin m) :
    cMatrix F r = ∑ i, cOne F r i := by
  rfl

/-- The stacked synthesis cogram is exactly the concrete shared-leg operator.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem CStack_mul_transpose (F : Frame n d) :
    CStack (m := m) F * (CStack (m := m) F).transpose = ghat F := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, CStack, Matrix.transpose_apply, ghat,
    Matrix.sum_apply]
  rw [Fintype.sum_prod_type]

/-- The transposed light synthesis stack evaluates the corresponding row matrix coefficient.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem CStack_transpose_apply (F : Frame n d)
    (out : RowFock m n) (inp : Fin d × Pattern m n) :
    (CStack F).transpose out inp = (CMatrix F out.1).transpose out.2 inp := by
  rfl

/-- The row-local creation synthesis is grade `+1`.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem CMatrix_grade_relation (F : Frame n d) (r : Fin m)
    {out : Fin d × Pattern m n} {inp : Pattern m n}
    (hentry : CMatrix F r out inp ≠ 0) :
    (out.2.grade : ℤ) = (inp.grade : ℤ) + 1 := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hentry
  have hk : pDagAt r i out.2 inp ≠ 0 := (mul_ne_zero_iff.mp hi).2
  have hh := siteKernel_homogeneous pCreate_homogeneous (r, i) hk
  simpa [pDagAt, gradeZ_eq_cast_grade] using hh

/-- The row-local creation analysis is also grade `+1`.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem cMatrix_grade_relation (F : Frame n d) (r : Fin m)
    {out : Pattern m n} {inp : Fin d × Pattern m n}
    (hentry : cMatrix F r out inp ≠ 0) :
    (out.grade : ℤ) = (inp.2.grade : ℤ) + 1 := by
  classical
  rw [cMatrix_eq_sum_cOne] at hentry
  simp only [Matrix.sum_apply, cOne] at hentry
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hentry
  have hk : pDagAt r i out inp.2 ≠ 0 := (mul_ne_zero_iff.mp hi).2
  have hh := siteKernel_homogeneous pCreate_homogeneous (r, i) hk
  simpa [cOne, pDagAt, gradeZ_eq_cast_grade] using hh

/-- One-site light creation has coefficient one precisely at the matching marked transition.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem pDagAt_apply (r : Fin m) (i : Fin n)
    (out inp : Pattern m n) :
    pDagAt r i out inp =
      if out (r, i) = .one ∧
          inp = HeavyBandsConcrete.setSite out (r, i) .zero then 1 else 0 := by
  simpa [pDagAt, pCreate] using
    HeavyBandsConcrete.siteKernel_ketBra_apply
      (m := m) (n := n) (r, i) .one .zero out inp

/-- Two light creation steps at the same site give the zero matrix.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem pDagAt_sq_zero (r : Fin m) (i : Fin n) :
    pDagAt r i * pDagAt r i = 0 := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  by_cases hout : out (r, i) = .one
  · simp only [pDagAt_apply, hout, true_and]
    rw [Finset.sum_eq_single (HeavyBandsConcrete.setSite out (r, i) .zero)]
    · simp [HeavyBandsConcrete.setSite]
    · intro other _ hne
      simp [hne]
    · simp
  · simp [pDagAt_apply, hout]

/-- Light creation at distinct sites is the associated two-leg word kernel.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem pDagAt_mul_pDagAt_of_ne (r : Fin m) {i j : Fin n}
    (hij : i ≠ j) :
    pDagAt r i * pDagAt r j =
      wordKernel (r, i) (r, j) (.pUp, .pUp) := by
  simpa [pDagAt, wordKernel, BandInventory.Leg.op] using
    siteKernel_mul_siteKernel_of_ne (m := m) (n := n)
      (r, i) (r, j) (by
        intro h
        exact hij (congrArg Prod.snd h)) pCreate pCreate

/-- Distinct-site light synthesis-analysis products are the physical light raising terms.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem COne_mul_cOne_of_ne (F : Frame n d) (r : Fin m)
    {i j : Fin n} (hij : i ≠ j) :
    COne F r i * cOne F r j =
      orderedWordTerm (DirectionalConcrete.frameRows F) r i j (.pUp, .pUp) := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, COne, cOne, orderedWordTerm,
    externalTensor, ExternalOperator.outer]
  calc
    (∑ p, (F.u i out.1 * pDagAt r i out.2 p) *
        (F.u j inp.1 * pDagAt r j p inp.2)) =
        (F.u i out.1 * F.u j inp.1) *
          ∑ p, pDagAt r i out.2 p * pDagAt r j p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = (F.u i out.1 * F.u j inp.1) *
        wordKernel (r, i) (r, j) (.pUp, .pUp) out.2 inp.2 := by
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (pDagAt_mul_pDagAt_of_ne r hij)
      simpa [Matrix.mul_apply] using congrArg
        (fun t : ℝ ↦ (F.u i out.1 * F.u j inp.1) * t) h

/-- Same-site light synthesis-analysis products vanish by creation nilpotence.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem COne_mul_cOne_self (F : Frame n d) (r : Fin m) (i : Fin n) :
    COne F r i * cOne F r i = 0 := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, COne, cOne, Matrix.zero_apply]
  calc
    (∑ p, (F.u i out.1 * pDagAt r i out.2 p) *
        (F.u i inp.1 * pDagAt r i p inp.2)) =
        (F.u i out.1 * F.u i inp.1) *
          ∑ p, pDagAt r i out.2 p * pDagAt r i p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = 0 := by
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (pDagAt_sq_zero r i)
      simp only [Matrix.mul_apply, Matrix.zero_apply] at h
      rw [h, mul_zero]

/-- Exact row-local factorization: the diagonal terms vanish by `P†²=0`.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem CMatrix_mul_cMatrix (F : Frame n d) (r : Fin m) :
    CMatrix F r * cMatrix F r =
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        orderedWordTerm (DirectionalConcrete.frameRows F) r i j (.pUp, .pUp) := by
  classical
  rw [CMatrix_eq_sum_COne, cMatrix_eq_sum_cOne, Matrix.sum_mul]
  simp_rw [Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [COne_mul_cOne_self]
  simp only [add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  exact COne_mul_cOne_of_ne F r (Ne.symm (Finset.mem_erase.mp hj).1)

/-- The named light raising band is the row synthesis times row analysis.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Lplus_eq_CStack_mul_CreateAnalysisStack (F : Frame n d) :
    Lplus m (DirectionalConcrete.frameRows F) =
      CStack (m := m) F * CreateAnalysisStack (m := m) F := by
  classical
  ext out inp
  simp only [Lplus, NamedBands.wordSum, physicalWordSum, Matrix.sum_apply,
    Matrix.mul_apply, CStack, CreateAnalysisStack]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  have h := congrArg
    (fun M : FullOp d m n ↦ M out inp) (CMatrix_mul_cMatrix F r)
  simpa [Matrix.mul_apply, Matrix.sum_apply] using h.symm

/-- Fixing the input at grade `nu` forces the creation-analysis stack to land
in row grade `nu+1`.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rowProjection_CreateAnalysisStack_gradeProjection
    (F : Frame n d) (nu : ℕ) :
    HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) (nu + 1) *
        CreateAnalysisStack (m := m) F *
          gradeProjection (d := d) (m := m) (n := n) nu =
      CreateAnalysisStack (m := m) F *
        gradeProjection (d := d) (m := m) (n := n) nu := by
  classical
  ext out inp
  simp only [HeavyBandsConcrete.rowGradeProjection, gradeProjection,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hin : inp.2.grade = nu
  · by_cases hentry : CreateAnalysisStack F out inp = 0
    · simp [hin, hentry]
    · have hrel := cMatrix_grade_relation F out.1 hentry
      have hout : out.2.grade = nu + 1 := by
        rw [hin] at hrel
        exact_mod_cast hrel
      simp [hin, hout]
  · simp [hin]

/-- On row grade `mu`, the synthesis stack lands at full grade `mu+1`.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem gradeProjection_CStack_rowProjection (F : Frame n d) (mu : ℕ) :
    gradeProjection (d := d) (m := m) (n := n) (mu + 1) *
        CStack (m := m) F *
        HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) mu =
      CStack (m := m) F *
        HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) mu := by
  classical
  ext out inp
  simp only [HeavyBandsConcrete.rowGradeProjection, gradeProjection,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hin : inp.2.grade = mu
  · by_cases hentry : CStack F out inp = 0
    · simp [hin, hentry]
    · have hrel := CMatrix_grade_relation F inp.1 hentry
      have hout : out.2.grade = mu + 1 := by
        rw [hin] at hrel
        exact_mod_cast hrel
      simp [hin, hout]
  · simp [hin]

/-- Fully typed projected factorization of the light `+2` band.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Lplus_grade_factor (F : Frame n d) (nu : ℕ) :
    Lplus m (DirectionalConcrete.frameRows F) *
        gradeProjection (d := d) (m := m) (n := n) nu =
      (gradeProjection (d := d) (m := m) (n := n) (nu + 2) *
          CStack (m := m) F *
          HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) (nu + 1)) *
        (CreateAnalysisStack (m := m) F *
          gradeProjection (d := d) (m := m) (n := n) nu) := by
  rw [Lplus_eq_CStack_mul_CreateAnalysisStack]
  have hins := rowProjection_CreateAnalysisStack_gradeProjection
    (m := m) F nu
  have hout := gradeProjection_CStack_rowProjection (m := m) F (nu + 1)
  calc
    (CStack (m := m) F * CreateAnalysisStack (m := m) F) *
        gradeProjection (d := d) (m := m) (n := n) nu =
        CStack (m := m) F *
          (CreateAnalysisStack (m := m) F *
            gradeProjection (d := d) (m := m) (n := n) nu) := by
      rw [Matrix.mul_assoc]
    _ = CStack (m := m) F *
        (HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) (nu + 1) *
          CreateAnalysisStack (m := m) F * gradeProjection (d := d) nu) := by
      rw [hins]
    _ = (CStack (m := m) F *
          HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) (nu + 1)) *
        (CreateAnalysisStack (m := m) F * gradeProjection (d := d) nu) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hout]

/-- The transpose of one-site light creation is light annihilation.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem pDagAt_transpose (r : Fin m) (i : Fin n) :
    (pDagAt r i).transpose = pAt r i := by
  simp [pDagAt, pAt, transpose_siteKernel]

end

end NLAlib.SparseFock.LightBandsConcrete
