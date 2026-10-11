/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.LightPreservingDiagonal

set_option autoImplicit false

/-!
# Light synthesis and mixed row factors

Restricted light synthesis norms and its exact factorization with heavy analysis.
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

/-- The transpose synthesis stack sends full grade `mu+1` exactly to row
grade `mu`.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rowProjection_CStackTranspose_gradeProjection
    (F : Frame n d) (mu : ℕ) :
    HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) mu *
        (CStack (m := m) F).transpose *
          gradeProjection (d := d) (m := m) (n := n) (mu + 1) =
      (CStack (m := m) F).transpose *
        gradeProjection (d := d) (m := m) (n := n) (mu + 1) := by
  classical
  ext out inp
  simp only [HeavyBandsConcrete.rowGradeProjection, gradeProjection,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hin : inp.2.grade = mu + 1
  · by_cases hentry : (CStack F).transpose out inp = 0
    · have hz : CStack F inp out = 0 := by
        simpa [Matrix.transpose_apply] using hentry
      simp [hin, hz]
    · have hentry' : CStack F inp out ≠ 0 := by
        simpa [Matrix.transpose_apply] using hentry
      have hrel := CMatrix_grade_relation F out.1 hentry'
      have hout : out.2.grade = mu := by
        rw [hin] at hrel
        push_cast at hrel
        have hz : (out.2.grade : ℤ) = (mu : ℤ) := by omega
        exact_mod_cast hz
      simp [hin, hout]
  · simp [hin]

/-- Exact cogram of the projected synthesis factor.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem CStack_restricted_cogram (F : Frame n d) (mu : ℕ) :
    let P := gradeProjection (d := d) (m := m) (n := n) (mu + 1)
    let R := HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) mu
    let B := P * CStack (m := m) F * R
    B * B.transpose = P * ghat F * P := by
  dsimp
  rw [Matrix.transpose_mul, Matrix.transpose_mul,
    HeavyBandsConcrete.rowGradeProjection_transpose, gradeProjection_transpose]
  have hins := rowProjection_CStackTranspose_gradeProjection
    (m := m) F mu
  have hins' :
      HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) mu *
        ((CStack (m := m) F).transpose *
          gradeProjection (d := d) (m := m) (n := n) (mu + 1)) =
      (CStack (m := m) F).transpose *
        gradeProjection (d := d) (m := m) (n := n) (mu + 1) := by
    rw [← Matrix.mul_assoc, hins]
  calc
    (gradeProjection (d := d) (m := m) (n := n) (mu + 1) *
        CStack (m := m) F *
        HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) mu) *
      (HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) mu *
        ((CStack (m := m) F).transpose *
          gradeProjection (d := d) (m := m) (n := n) (mu + 1))) =
      (gradeProjection (d := d) (m := m) (n := n) (mu + 1) *
          CStack (m := m) F *
        HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) mu) *
          ((CStack (m := m) F).transpose *
            gradeProjection (d := d) (m := m) (n := n) (mu + 1)) := by
      rw [hins']
    _ = gradeProjection (d := d) (m := m) (n := n) (mu + 1) *
        CStack (m := m) F *
          (HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) mu *
            ((CStack (m := m) F).transpose *
              gradeProjection (d := d) (m := m) (n := n) (mu + 1))) := by
      simp only [Matrix.mul_assoc]
    _ = gradeProjection (d := d) (m := m) (n := n) (mu + 1) *
        CStack (m := m) F *
        ((CStack (m := m) F).transpose *
          gradeProjection (d := d) (m := m) (n := n) (mu + 1)) := by
      rw [hins']
    _ = gradeProjection (d := d) (m := m) (n := n) (mu + 1) *
        (CStack (m := m) F * (CStack (m := m) F).transpose) *
          gradeProjection (d := d) (m := m) (n := n) (mu + 1) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [CStack_mul_transpose]

/-- Sharp restricted synthesis-stack bound.  The output projection is one
grade above the row input projection, exactly as required by the light and
mixed factorizations.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem CStack_restricted_norm (F : Frame n d) (mu : ℕ) :
    ‖gradeProjection (d := d) (m := m) (n := n) (mu + 1) *
        CStack (m := m) F *
        HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) mu‖ ≤
      Real.sqrt ((d : ℝ) + (mu : ℝ)) := by
  let P := gradeProjection (d := d) (m := m) (n := n) (mu + 1)
  let R := HeavyBandsConcrete.rowGradeProjection (m := m) (n := n) mu
  let B := P * CStack (m := m) F * R
  have hP : ‖P‖ ≤ 1 := gradeProjection_norm_le_one (mu + 1)
  have hG :
      ‖ghat (m := m) F * P‖ ≤ (d : ℝ) + (mu : ℝ) := by
    have hsharp := LightSectorConcrete.ghat_gradeProjection_norm_le
      (m := m) F (mu + 1) (Nat.succ_le_succ (Nat.zero_le mu))
    dsimp [P]
    (convert hsharp using 1; push_cast; ring)
  have hcogram : ‖B * B.transpose‖ ≤ (d : ℝ) + (mu : ℝ) := by
    rw [show B * B.transpose = P * ghat (m := m) F * P by
      simpa [B, P, R] using CStack_restricted_cogram (m := m) F mu]
    calc
      ‖P * ghat (m := m) F * P‖ ≤ ‖P‖ * ‖ghat (m := m) F * P‖ := by
        rw [Matrix.mul_assoc]
        exact Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * ((d : ℝ) + (mu : ℝ)) := by
        exact mul_le_mul hP hG (norm_nonneg _) (by positivity)
      _ = (d : ℝ) + (mu : ℝ) := one_mul _
  have hBconj : B.transpose.conjTranspose = B := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hsquare : ‖B * B.transpose‖ = ‖B‖ * ‖B‖ := by
    calc
      ‖B * B.transpose‖ =
          ‖B.transpose.conjTranspose * B.transpose‖ := by rw [hBconj]
      _ = ‖B.transpose‖ * ‖B.transpose‖ :=
        Matrix.l2_opNorm_conjTranspose_mul_self B.transpose
      _ = ‖B‖ * ‖B‖ := by
        rw [HeavyBandsConcrete.norm_transpose_real]
  have hdm : 0 ≤ (d : ℝ) + (mu : ℝ) := by positivity
  have hsqrt := Real.sq_sqrt hdm
  change ‖B‖ ≤ Real.sqrt ((d : ℝ) + (mu : ℝ))
  rw [hsquare] at hcogram
  nlinarith [norm_nonneg B, Real.sqrt_nonneg ((d : ℝ) + (mu : ℝ))]

/-- Light creation and heavy creation at distinct sites give the mixed raising word.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem pDagAt_mul_rUpAt_of_ne (r : Fin m) {i j : Fin n}
    (hij : i ≠ j) :
    pDagAt r i * HeavyBandsConcrete.rUpAt r j =
      wordKernel (r, i) (r, j) (.pUp, .rUp) := by
  simpa [pDagAt, HeavyBandsConcrete.rUpAt, wordKernel,
    BandInventory.Leg.op] using
    siteKernel_mul_siteKernel_of_ne (m := m) (n := n)
      (r, i) (r, j) (by
        intro h
        exact hij (congrArg Prod.snd h)) pCreate rPromote

/-- Light creation and heavy annihilation at distinct sites give the mixed preserving word.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem pDagAt_mul_rDownAt_of_ne (r : Fin m) {i j : Fin n}
    (hij : i ≠ j) :
    pDagAt r i * HeavyBandsConcrete.rDownAt r j =
      wordKernel (r, i) (r, j) (.pUp, .rDown) := by
  simpa [pDagAt, HeavyBandsConcrete.rDownAt, wordKernel,
    BandInventory.Leg.op] using
    siteKernel_mul_siteKernel_of_ne (m := m) (n := n)
      (r, i) (r, j) (by
        intro h
        exact hij (congrArg Prod.snd h)) pCreate rDemote

/-- Light creation composed with heavy creation at the same site vanishes.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem pDagAt_mul_rUpAt_self (r : Fin m) (i : Fin n) :
    pDagAt r i * HeavyBandsConcrete.rUpAt r i = 0 := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  by_cases hout : out (r, i) = .one
  · simp only [pDagAt_apply, hout, true_and]
    rw [Finset.sum_eq_single
      (HeavyBandsConcrete.setSite out (r, i) .zero)]
    · simp [HeavyBandsConcrete.rUpAt_apply, HeavyBandsConcrete.setSite]
    · intro other _ hne
      simp [hne]
    · simp
  · simp [pDagAt_apply, hout]

/-- Light creation composed with heavy annihilation at the same site vanishes.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem pDagAt_mul_rDownAt_self (r : Fin m) (i : Fin n) :
    pDagAt r i * HeavyBandsConcrete.rDownAt r i = 0 := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  by_cases hout : out (r, i) = .one
  · simp only [pDagAt_apply, hout, true_and]
    rw [Finset.sum_eq_single
      (HeavyBandsConcrete.setSite out (r, i) .zero)]
    · simp [HeavyBandsConcrete.rDownAt_apply, HeavyBandsConcrete.setSite]
    · intro other _ hne
      simp [hne]
    · simp
  · simp [pDagAt_apply, hout]

/-- Distinct-site light synthesis and heavy creation analysis give the mixed raising term.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem COne_mul_AUpOne_of_ne (F : Frame n d) (r : Fin m)
    {i j : Fin n} (hij : i ≠ j) :
    COne F r i * HeavyBandsConcrete.AUpOne F r j =
      orderedWordTerm (DirectionalConcrete.frameRows F) r i j
        (.pUp, .rUp) := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, COne, HeavyBandsConcrete.AUpOne,
    orderedWordTerm, externalTensor, ExternalOperator.outer]
  calc
    (∑ p, (F.u i out.1 * pDagAt r i out.2 p) *
        (F.u j inp.1 * HeavyBandsConcrete.rUpAt r j p inp.2)) =
        (F.u i out.1 * F.u j inp.1) *
          ∑ p, pDagAt r i out.2 p *
            HeavyBandsConcrete.rUpAt r j p inp.2 := by
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

/-- Distinct-site light synthesis and heavy annihilation analysis give the mixed preserving term.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem COne_mul_ADownOne_of_ne (F : Frame n d) (r : Fin m)
    {i j : Fin n} (hij : i ≠ j) :
    COne F r i * HeavyBandsConcrete.ADownOne F r j =
      orderedWordTerm (DirectionalConcrete.frameRows F) r i j
        (.pUp, .rDown) := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, COne, HeavyBandsConcrete.ADownOne,
    orderedWordTerm, externalTensor, ExternalOperator.outer]
  calc
    (∑ p, (F.u i out.1 * pDagAt r i out.2 p) *
        (F.u j inp.1 * HeavyBandsConcrete.rDownAt r j p inp.2)) =
        (F.u i out.1 * F.u j inp.1) *
          ∑ p, pDagAt r i out.2 p *
            HeavyBandsConcrete.rDownAt r j p inp.2 := by
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

/-- Same-site light synthesis and heavy creation analysis have zero product.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem COne_mul_AUpOne_self (F : Frame n d) (r : Fin m) (i : Fin n) :
    COne F r i * HeavyBandsConcrete.AUpOne F r i = 0 := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, COne, HeavyBandsConcrete.AUpOne,
    Matrix.zero_apply]
  calc
    (∑ p, (F.u i out.1 * pDagAt r i out.2 p) *
        (F.u i inp.1 * HeavyBandsConcrete.rUpAt r i p inp.2)) =
        (F.u i out.1 * F.u i inp.1) *
          ∑ p, pDagAt r i out.2 p *
            HeavyBandsConcrete.rUpAt r i p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = 0 := by
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (pDagAt_mul_rUpAt_self r i)
      simp only [Matrix.mul_apply, Matrix.zero_apply] at h
      rw [h, mul_zero]

/-- Same-site light synthesis and heavy annihilation analysis have zero product.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem COne_mul_ADownOne_self (F : Frame n d) (r : Fin m) (i : Fin n) :
    COne F r i * HeavyBandsConcrete.ADownOne F r i = 0 := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, COne, HeavyBandsConcrete.ADownOne,
    Matrix.zero_apply]
  calc
    (∑ p, (F.u i out.1 * pDagAt r i out.2 p) *
        (F.u i inp.1 * HeavyBandsConcrete.rDownAt r i p inp.2)) =
        (F.u i out.1 * F.u i inp.1) *
          ∑ p, pDagAt r i out.2 p *
            HeavyBandsConcrete.rDownAt r i p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = 0 := by
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (pDagAt_mul_rDownAt_self r i)
      simp only [Matrix.mul_apply, Matrix.zero_apply] at h
      rw [h, mul_zero]

/-- The light synthesis/heavy creation product equals its physical mixed raising word sum.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem CMatrix_mul_AUpMatrix (F : Frame n d) (r : Fin m) :
    CMatrix F r * HeavyBandsConcrete.AUpMatrix F r =
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        orderedWordTerm (DirectionalConcrete.frameRows F) r i j
          (.pUp, .rUp) := by
  classical
  rw [CMatrix_eq_sum_COne, HeavyBandsConcrete.AUpMatrix_eq_sum_one,
    Matrix.sum_mul]
  simp_rw [Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    COne_mul_AUpOne_self, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  exact COne_mul_AUpOne_of_ne F r
    (Ne.symm (Finset.mem_erase.mp hj).1)

/-- The light synthesis/heavy annihilation product equals its physical mixed preserving word sum.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem CMatrix_mul_ADownMatrix (F : Frame n d) (r : Fin m) :
    CMatrix F r * HeavyBandsConcrete.ADownMatrix F r =
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        orderedWordTerm (DirectionalConcrete.frameRows F) r i j
          (.pUp, .rDown) := by
  classical
  rw [CMatrix_eq_sum_COne, HeavyBandsConcrete.ADownMatrix_eq_sum_one,
    Matrix.sum_mul]
  simp_rw [Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    COne_mul_ADownOne_self, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  exact COne_mul_ADownOne_of_ne F r
    (Ne.symm (Finset.mem_erase.mp hj).1)

/-- Reusable exact mixed-band factorization requested downstream.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Xplus_eq_CStack_mul_AUpStack (F : Frame n d) :
    Xplus m (DirectionalConcrete.frameRows F) =
      CStack (m := m) F * HeavyBandsConcrete.AUpStack (m := m) F := by
  classical
  ext out inp
  simp only [Xplus, NamedBands.wordSum, physicalWordSum, Matrix.sum_apply,
    Matrix.mul_apply, CStack, HeavyBandsConcrete.AUpStack]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  have h := congrArg (fun M : FullOp d m n ↦ M out inp)
    (CMatrix_mul_AUpMatrix F r)
  simpa [Matrix.mul_apply, Matrix.sum_apply] using h.symm

/-- Reusable exact mixed grade-zero factorization requested downstream.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Xzero_eq_CStack_mul_ADownStack (F : Frame n d) :
    Xzero m (DirectionalConcrete.frameRows F) =
      CStack (m := m) F * HeavyBandsConcrete.ADownStack (m := m) F := by
  classical
  ext out inp
  simp only [Xzero, NamedBands.wordSum, physicalWordSum, Matrix.sum_apply,
    Matrix.mul_apply, CStack, HeavyBandsConcrete.ADownStack]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  have h := congrArg (fun M : FullOp d m n ↦ M out inp)
    (CMatrix_mul_ADownMatrix F r)
  simpa [Matrix.mul_apply, Matrix.sum_apply] using h.symm

end

end NLAlib.SparseFock.LightBandsConcrete
