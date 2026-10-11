/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.LightRowFactorization

set_option autoImplicit false

/-!
# Light creation analysis Gram estimates

Same-site fresh corrections, the analysis Gram factorization, and restricted analysis norms.
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

/-- Light annihilation and creation at distinct sites form the corresponding word kernel.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem pAt_mul_pDagAt_of_ne (r : Fin m) {i j : Fin n}
    (hij : i ≠ j) :
    pAt r i * pDagAt r j =
      wordKernel (r, i) (r, j) (.pDown, .pUp) := by
  simpa [pAt, pDagAt, wordKernel, BandInventory.Leg.op] using
    siteKernel_mul_siteKernel_of_ne (m := m) (n := n)
      (r, i) (r, j) (by
        intro h
        exact hij (congrArg Prod.snd h)) pDestroy pCreate

/-- Distinct-site light creation-analysis Gram terms are physical preserving-word terms.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem cOne_transpose_mul_cOne_of_ne (F : Frame n d) (r : Fin m)
    {i j : Fin n} (hij : i ≠ j) :
    (cOne F r i).transpose * cOne F r j =
      orderedWordTerm (DirectionalConcrete.frameRows F) r i j
        (.pDown, .pUp) := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.transpose_apply, cOne, orderedWordTerm,
    externalTensor, ExternalOperator.outer]
  calc
    (∑ p, (F.u i out.1 * pDagAt r i p out.2) *
        (F.u j inp.1 * pDagAt r j p inp.2)) =
        (F.u i out.1 * F.u j inp.1) *
          ∑ p, (pDagAt r i).transpose out.2 p * pDagAt r j p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      simp only [Matrix.transpose_apply]
      ring
    _ = (F.u i out.1 * F.u j inp.1) *
        wordKernel (r, i) (r, j) (.pDown, .pUp) out.2 inp.2 := by
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (pAt_mul_pDagAt_of_ne r hij)
      rw [pDagAt_transpose]
      change (F.u i out.1 * F.u j inp.1) *
        ((pAt r i * pDagAt r j) out.2 inp.2) = _
      rw [h]

/-- The same-site, fresh-site diagonal part of one analysis Gram.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def D0Row (F : Frame n d) (r : Fin m) : FullOp d m n :=
  ∑ i, (cOne F r i).transpose * cOne F r i

/-- The global fresh-site diagonal Gram term.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def D0 (F : Frame n d) : FullOp d m n :=
  ∑ r, D0Row F r

/-- A light creation-analysis Gram matrix splits into hopping and same-site diagonal terms.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem cMatrix_transpose_mul_cMatrix (F : Frame n d) (r : Fin m) :
    (cMatrix F r).transpose * cMatrix F r =
      D0Row F r +
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          orderedWordTerm (DirectionalConcrete.frameRows F) r i j
            (.pDown, .pUp) := by
  classical
  rw [cMatrix_eq_sum_cOne, Matrix.transpose_sum, Matrix.sum_mul]
  simp_rw [Matrix.mul_sum]
  rw [D0Row]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ j, (cOne F r i).transpose * cOne F r j) =
        (∑ j ∈ Finset.univ.erase i,
          (cOne F r i).transpose * cOne F r j) +
          (cOne F r i).transpose * cOne F r i := by
      rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    _ = (cOne F r i).transpose * cOne F r i +
        ∑ j ∈ Finset.univ.erase i,
          (cOne F r i).transpose * cOne F r j := add_comm _ _
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact cOne_transpose_mul_cOne_of_ne F r
        (Ne.symm (Finset.mem_erase.mp hj).1)

/-- The full creation-analysis Gram is the fresh diagonal plus the exact
light transpose hop `H'`.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem CreateAnalysisStack_transpose_mul_self (F : Frame n d) :
    (CreateAnalysisStack (m := m) F).transpose * CreateAnalysisStack F =
      D0 F + Hprime m (DirectionalConcrete.frameRows F) := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.transpose_apply, CreateAnalysisStack]
  rw [Fintype.sum_prod_type]
  simp only [D0, Matrix.sum_apply, Hprime, NamedBands.wordSum,
    physicalWordSum, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  have h := congrArg (fun M : FullOp d m n ↦ M out inp)
    (cMatrix_transpose_mul_cMatrix F r)
  simpa [Matrix.mul_apply, Matrix.sum_apply] using h

/-- The same-site creation column has exactly the fresh-site projection as
its scalar Gram.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem pDagAt_column_inner (r : Fin m) (i : Fin n)
    (a b : Pattern m n) :
    (∑ p, pDagAt r i p a * pDagAt r i p b) =
      if a = b ∧ a (r, i) = .zero then 1 else 0 := by
  classical
  let s : Site m n := (r, i)
  let marked := HeavyBandsConcrete.setSite a s .one
  by_cases ha : a s = .zero
  · have hrestore : HeavyBandsConcrete.setSite marked s .zero = a := by
      simpa [marked, s] using
        HeavyBandsConcrete.setSite_restore (b := .one) a s ha
    rw [Finset.sum_eq_single marked]
    · simp only [pDagAt_apply]
      simp [marked, s, hrestore, ha, eq_comm]
    · intro p _ hpne
      by_cases hp : p s = .one
      · by_cases heq : a = HeavyBandsConcrete.setSite p s .zero
        · have hpmark : p = marked := by
            calc
              p = HeavyBandsConcrete.setSite
                    (HeavyBandsConcrete.setSite p s .zero) s .one := by
                symm
                exact HeavyBandsConcrete.setSite_restore (b := .zero) p s hp
              _ = marked := by rw [← heq]
          exact (hpne hpmark).elim
        · simp [pDagAt_apply, s, hp, heq]
      · simp [pDagAt_apply, s, hp]
    · simp
  · have hzero (p : Pattern m n) : pDagAt r i p a = 0 := by
      rw [pDagAt_apply]
      by_cases hp : p s = .one
      · by_cases heq : a = HeavyBandsConcrete.setSite p s .zero
        · exfalso
          apply ha
          rw [heq]
          exact HeavyBandsConcrete.setSite_apply_self _ _ _
        · simp [s, hp, heq]
      · simp [s, hp]
    have hane : a (r, i) ≠ .zero := by simpa [s] using ha
    simp [hzero, hane]

/-- Entrywise form of the fresh-site diagonal Gram: on each Fock pattern it
is precisely the partial frame operator over the currently fresh columns.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem D0Row_apply (F : Frame n d) (r : Fin m)
    (out inp : Fin d × Pattern m n) :
    D0Row F r out inp =
      if out.2 = inp.2 then
        partialFrameOperator F (out.2.freshInRow r) out.1 inp.1 else 0 := by
  classical
  simp only [D0Row, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.transpose_apply, cOne]
  calc
    (∑ i, ∑ p,
        (F.u i out.1 * pDagAt r i p out.2) *
          (F.u i inp.1 * pDagAt r i p inp.2)) =
        ∑ i, (F.u i out.1 * F.u i inp.1) *
          ∑ p, pDagAt r i p out.2 * pDagAt r i p inp.2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = ∑ i, (F.u i out.1 * F.u i inp.1) *
        (if out.2 = inp.2 ∧ out.2 (r, i) = .zero then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [pDagAt_column_inner]
    _ = _ := by
      by_cases hp : out.2 = inp.2
      · simp only [hp, true_and, if_true]
        simp [partialFrameOperator, Pattern.freshInRow, Finset.sum_filter]
      · simp [hp]

/-- The row fresh-site diagonal correction acts through its selected frame-fiber contributions.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem D0Row_fullFiber (F : Frame n d) (r : Fin m)
    (x : Fin d × Pattern m n → ℝ) (p : Pattern m n) :
    fullFiber (Matrix.mulVec (D0Row F r) x) p =
      applyMatrix (partialFrameOperator F (p.freshInRow r)) (fullFiber x p) := by
  classical
  ext k
  simp only [fullFiber, Matrix.mulVec, dotProduct, D0Row_apply, applyMatrix,
    PiLp.toLp_apply]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro l _
  simp

/-- One row's fresh-site diagonal is a Euclidean contraction.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem D0Row_norm_le_one (F : Frame n d) (r : Fin m) :
    ‖D0Row F r‖ ≤ 1 := by
  apply FiniteHilbert.norm_le_of_normSq_mulVec_le (by norm_num)
  intro x
  rw [DirectionalConcrete.full_normSq_eq_sum_fiber]
  calc
    (∑ p, ParsevalFrame.normSq
        (fullFiber (Matrix.mulVec (D0Row F r) x) p)) =
        ∑ p, ParsevalFrame.normSq
          (applyMatrix (partialFrameOperator F (p.freshInRow r))
            (fullFiber x p)) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [D0Row_fullFiber]
    _ ≤ ∑ p, ParsevalFrame.normSq (fullFiber x p) := by
      apply Finset.sum_le_sum
      intro p _
      exact partialFrameOperator_contraction F (p.freshInRow r) (fullFiber x p)
    _ = 1 ^ 2 * FiniteHilbert.normSq x := by
      rw [DirectionalConcrete.full_normSq_eq_sum_fiber]
      ring

/-- Summing the row contractions gives the exact paper bound `D₀ ≼ m I`.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem D0_norm_le (F : Frame n d) :
    ‖D0 (m := m) F‖ ≤ (m : ℝ) := by
  rw [D0]
  calc
    ‖∑ r, D0Row F r‖ ≤ ∑ r, ‖D0Row F r‖ := norm_sum_le _ _
    _ ≤ ∑ _r : Fin m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro r _
      exact D0Row_norm_le_one F r
    _ = (m : ℝ) := by simp

/-- Finite-matrix specialization of typed block Cauchy--Schwarz.  The middle
index type is genuine and may differ from both endpoint types.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem matrix_typed_block_cs
    {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (B : Matrix K J ℝ) (A : Matrix J I ℝ) :
    ‖B * A‖ ^ 2 ≤ ‖A.transpose * A‖ * ‖B * B.transpose‖ := by
  have hmul : ‖B * A‖ ≤ ‖B‖ * ‖A‖ := Matrix.l2_opNorm_mul B A
  have hAconj : A.conjTranspose = A.transpose := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hBconj : B.transpose.conjTranspose = B := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hAgram : ‖A.transpose * A‖ = ‖A‖ * ‖A‖ := by
    rw [← hAconj, Matrix.l2_opNorm_conjTranspose_mul_self]
  have hBcogram : ‖B * B.transpose‖ = ‖B‖ * ‖B‖ := by
    calc
      ‖B * B.transpose‖ =
          ‖B.transpose.conjTranspose * B.transpose‖ := by rw [hBconj]
      _ = ‖B.transpose‖ * ‖B.transpose‖ :=
        Matrix.l2_opNorm_conjTranspose_mul_self B.transpose
      _ = ‖B‖ * ‖B‖ := by
        rw [HeavyBandsConcrete.norm_transpose_real]
  calc
    ‖B * A‖ ^ 2 ≤ (‖B‖ * ‖A‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hmul 2
    _ = (‖A‖ * ‖A‖) * (‖B‖ * ‖B‖) := by ring
    _ = ‖A.transpose * A‖ * ‖B * B.transpose‖ := by rw [hAgram, hBcogram]

/-- The light creation stack's restricted Gram matrix splits into the projected diagonal and light-band terms.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem CreateAnalysisStack_restricted_gram (F : Frame n d) (nu : ℕ) :
    (CreateAnalysisStack (m := m) F *
        gradeProjection (d := d) (m := m) (n := n) nu).transpose *
      (CreateAnalysisStack (m := m) F * gradeProjection (d := d) nu) =
        gradeProjection (d := d) (m := m) (n := n) nu *
          (D0 F + Hprime m (DirectionalConcrete.frameRows F)) *
            gradeProjection (d := d) (m := m) (n := n) nu := by
  rw [Matrix.transpose_mul, gradeProjection_transpose]
  calc
    (gradeProjection (d := d) (m := m) (n := n) nu *
        (CreateAnalysisStack (m := m) F).transpose) *
        (CreateAnalysisStack (m := m) F *
          gradeProjection (d := d) (m := m) (n := n) nu) =
      gradeProjection (d := d) (m := m) (n := n) nu *
        ((CreateAnalysisStack (m := m) F).transpose *
          CreateAnalysisStack (m := m) F) *
            gradeProjection (d := d) (m := m) (n := n) nu := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [CreateAnalysisStack_transpose_mul_self]

/-- The analysis Gram bound `m+ν`, obtained from the fresh diagonal and the
concrete directional estimate for `H'`.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem CreateAnalysisStack_gradeProjection_norm
    (F : Frame n d) (nu : ℕ) :
    ‖CreateAnalysisStack (m := m) F *
        gradeProjection (d := d) (m := m) (n := n) nu‖ ≤
      Real.sqrt ((m : ℝ) + (nu : ℝ)) := by
  let A := CreateAnalysisStack (m := m) F *
    gradeProjection (d := d) (m := m) (n := n) nu
  let P := gradeProjection (d := d) (m := m) (n := n) nu
  have hP : ‖P‖ ≤ 1 := gradeProjection_norm_le_one nu
  have hD0P : ‖D0 F * P‖ ≤ (m : ℝ) := by
    calc
      ‖D0 F * P‖ ≤ ‖D0 F‖ * ‖P‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (m : ℝ) * 1 := mul_le_mul (D0_norm_le F) hP
        (norm_nonneg _) (Nat.cast_nonneg _)
      _ = (m : ℝ) := mul_one _
  have hHP :
      ‖Hprime m (DirectionalConcrete.frameRows F) * P‖ ≤ (nu : ℝ) := by
    simpa [P] using DirectionalConcrete.norm_Hprime_restricted_le
      (m := m) F nu
  have hgram : ‖A.transpose * A‖ ≤ (m : ℝ) + (nu : ℝ) := by
    rw [show A.transpose * A = P *
        (D0 F + Hprime m (DirectionalConcrete.frameRows F)) * P by
      simpa [A, P] using CreateAnalysisStack_restricted_gram
        (m := m) F nu]
    calc
      ‖P * (D0 F + Hprime m (DirectionalConcrete.frameRows F)) * P‖ ≤
          ‖P‖ * ‖(D0 F + Hprime m
            (DirectionalConcrete.frameRows F)) * P‖ := by
        rw [Matrix.mul_assoc]
        exact Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * ‖(D0 F + Hprime m
            (DirectionalConcrete.frameRows F)) * P‖ := by
        exact mul_le_mul_of_nonneg_right hP (norm_nonneg _)
      _ = ‖D0 F * P + Hprime m
            (DirectionalConcrete.frameRows F) * P‖ := by
        rw [one_mul, Matrix.add_mul]
      _ ≤ ‖D0 F * P‖ +
          ‖Hprime m (DirectionalConcrete.frameRows F) * P‖ := norm_add_le _ _
      _ ≤ (m : ℝ) + (nu : ℝ) := add_le_add hD0P hHP
  have hconj : A.conjTranspose = A.transpose := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hsquare : ‖A‖ * ‖A‖ = ‖A.transpose * A‖ := by
    rw [← hconj, Matrix.l2_opNorm_conjTranspose_mul_self]
  have hmn : 0 ≤ (m : ℝ) + (nu : ℝ) := by positivity
  have hsqrt := Real.sq_sqrt hmn
  change ‖A‖ ≤ Real.sqrt ((m : ℝ) + (nu : ℝ))
  nlinarith [norm_nonneg A, Real.sqrt_nonneg ((m : ℝ) + (nu : ℝ))]

end

end NLAlib.SparseFock.LightBandsConcrete
