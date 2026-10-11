/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.LightAnalysisGram

set_option autoImplicit false

/-!
# Light preserving diagonal energy

The preserving-band decomposition and occupied-site diagonal correction energy.
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

/-- Light creation and annihilation at distinct sites form the corresponding word kernel.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem pDagAt_mul_pAt_of_ne (r : Fin m) {i j : Fin n}
    (hij : i ≠ j) :
    pDagAt r i * pAt r j =
      wordKernel (r, i) (r, j) (.pUp, .pDown) := by
  simpa [pAt, pDagAt, wordKernel, BandInventory.Leg.op] using
    siteKernel_mul_siteKernel_of_ne (m := m) (n := n)
      (r, i) (r, j) (by
        intro h
        exact hij (congrArg Prod.snd h)) pCreate pDestroy

/-- Distinct-site light synthesis co-Gram terms are physical light hopping terms.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem COne_mul_COne_transpose_of_ne (F : Frame n d) (r : Fin m)
    {i j : Fin n} (hij : i ≠ j) :
    COne F r i * (COne F r j).transpose =
      orderedWordTerm (DirectionalConcrete.frameRows F) r i j
        (.pUp, .pDown) := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.transpose_apply, COne, orderedWordTerm,
    externalTensor, ExternalOperator.outer]
  calc
    (∑ p, (F.u i out.1 * pDagAt r i out.2 p) *
        (F.u j inp.1 * pDagAt r j inp.2 p)) =
        (F.u i out.1 * F.u j inp.1) *
          ∑ p, pDagAt r i out.2 p *
            (pDagAt r j).transpose p inp.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      simp only [Matrix.transpose_apply]
      ring
    _ = (F.u i out.1 * F.u j inp.1) *
        wordKernel (r, i) (r, j) (.pUp, .pDown) out.2 inp.2 := by
      rw [pDagAt_transpose]
      have h := congrArg (fun K : FockOp m n ↦ K out.2 inp.2)
        (pDagAt_mul_pAt_of_ne r hij)
      change (F.u i out.1 * F.u j inp.1) *
        ((pDagAt r i * pAt r j) out.2 inp.2) = _
      rw [h]

/-- Same-site part of the shared-leg cogram.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def D1Row (F : Frame n d) (r : Fin m) : FullOp d m n :=
  ∑ i, COne F r i * (COne F r i).transpose

/-- Global same-site light-occupancy diagonal.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def D1 (F : Frame n d) : FullOp d m n :=
  ∑ r, D1Row F r

/-- A light synthesis co-Gram matrix splits into hopping and same-site diagonal corrections.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem CMatrix_mul_transpose_decomposition (F : Frame n d) (r : Fin m) :
    CMatrix F r * (CMatrix F r).transpose =
      D1Row F r +
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          orderedWordTerm (DirectionalConcrete.frameRows F) r i j
            (.pUp, .pDown) := by
  classical
  rw [CMatrix_eq_sum_COne, Matrix.transpose_sum, Matrix.sum_mul]
  simp_rw [Matrix.mul_sum]
  rw [D1Row, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ j, COne F r i * (COne F r j).transpose) =
        (∑ j ∈ Finset.univ.erase i,
          COne F r i * (COne F r j).transpose) +
          COne F r i * (COne F r i).transpose := by
      rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    _ = COne F r i * (COne F r i).transpose +
        ∑ j ∈ Finset.univ.erase i,
          COne F r i * (COne F r j).transpose := add_comm _ _
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact COne_mul_COne_transpose_of_ne F r
        (Ne.symm (Finset.mem_erase.mp hj).1)

/-- The light-sector comparison operator is its diagonal correction plus light hopping.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem ghat_eq_D1_add_lightHop (F : Frame n d) :
    ghat (m := m) F = D1 F +
      NamedBands.wordSum m (DirectionalConcrete.frameRows F) .pUp .pDown := by
  classical
  rw [ghat]
  simp only [D1, NamedBands.wordSum, physicalWordSum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  exact CMatrix_mul_transpose_decomposition F r

/-- Exact grade-zero light-band identity from the two diagonal/cross Grams.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Lzero_eq_ghat_sub_D1_add_Hprime (F : Frame n d) :
    Lzero m (DirectionalConcrete.frameRows F) =
      (ghat F - D1 F) + Hprime m (DirectionalConcrete.frameRows F) := by
  rw [Lzero, Hprime]
  have h := ghat_eq_D1_add_lightHop (m := m) F
  rw [h]
  abel

/-- The scalar row kernel `P†P` is exactly the indicator of a light site.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem pDagAt_row_inner (r : Fin m) (i : Fin n)
    (a b : Pattern m n) :
    (∑ p, pDagAt r i a p * pDagAt r i b p) =
      if a = b ∧ a (r, i) = .one then 1 else 0 := by
  classical
  let s : Site m n := (r, i)
  let erased := HeavyBandsConcrete.setSite a s .zero
  by_cases ha : a s = .one
  · rw [Finset.sum_eq_single erased]
    · have hfirst : a (r, i) = .one ∧
          erased = HeavyBandsConcrete.setSite a (r, i) .zero := by
        constructor
        · simpa [s] using ha
        · rfl
      have hsecond :
          (b (r, i) = .one ∧
            erased = HeavyBandsConcrete.setSite b (r, i) .zero) ↔ b = a := by
        constructor
        · rintro ⟨hb, heq⟩
          calc
            b = HeavyBandsConcrete.setSite
                (HeavyBandsConcrete.setSite b (r, i) .zero) (r, i) .one := by
              symm
              exact HeavyBandsConcrete.setSite_restore (b := .zero) b (r, i) hb
            _ = HeavyBandsConcrete.setSite erased (r, i) .one := by rw [← heq]
            _ = a := by
              exact HeavyBandsConcrete.setSite_restore
                (b := .zero) a (r, i) (by simpa [s] using ha)
        · rintro rfl
          exact hfirst
      simp only [pDagAt_apply, if_pos hfirst]
      by_cases hab : b = a
      · subst b
        simp [hfirst]
      · have hn : ¬(b (r, i) = .one ∧
            erased = HeavyBandsConcrete.setSite b (r, i) .zero) :=
          fun hb ↦ hab (hsecond.mp hb)
        have hab' : a ≠ b := Ne.symm hab
        simp [hn, hab']
    · intro p _ hpne
      have hz : pDagAt r i a p = 0 := by
        rw [pDagAt_apply]
        simp [s, erased, ha, hpne]
      rw [hz, zero_mul]
    · simp
  · have hzero (p : Pattern m n) : pDagAt r i a p = 0 := by
      rw [pDagAt_apply]
      simp [s, ha]
    have hane : a (r, i) ≠ .one := by simpa [s] using ha
    simp [hzero, hane]

/-- The occupied-site row diagonal correction is supported on identical patterns with light marked sites.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem D1Row_apply (F : Frame n d) (r : Fin m)
    (out inp : Fin d × Pattern m n) :
    D1Row F r out inp =
      if out.2 = inp.2 then
        partialFrameOperator F (out.2.lightInRow r) out.1 inp.1 else 0 := by
  classical
  simp only [D1Row, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.transpose_apply, COne]
  calc
    (∑ i, ∑ p,
        (F.u i out.1 * pDagAt r i out.2 p) *
          (F.u i inp.1 * pDagAt r i inp.2 p)) =
        ∑ i, (F.u i out.1 * F.u i inp.1) *
          ∑ p, pDagAt r i out.2 p * pDagAt r i inp.2 p := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = ∑ i, (F.u i out.1 * F.u i inp.1) *
        (if out.2 = inp.2 ∧ out.2 (r, i) = .one then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [pDagAt_row_inner]
    _ = _ := by
      by_cases hp : out.2 = inp.2
      · simp only [hp, true_and, if_true]
        simp [partialFrameOperator, Pattern.lightInRow, Finset.sum_filter]
      · simp [hp]

/-- The total occupied-site diagonal correction sums the row corrections.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem D1_apply (F : Frame n d) (out inp : Fin d × Pattern m n) :
    D1 (m := m) F out inp =
      if out.2 = inp.2 then
        ∑ r, partialFrameOperator F (out.2.lightInRow r) out.1 inp.1
      else 0 := by
  classical
  simp only [D1, Matrix.sum_apply, D1Row_apply]
  by_cases hp : out.2 = inp.2
  · simp [hp]
  · simp [hp]

/-- The occupied-site diagonal correction acts on each fiber as a sum over rows.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem D1_fullFiber_rows (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (p : Pattern m n) :
    fullFiber (Matrix.mulVec (D1 (m := m) F) x) p =
      ∑ r, applyMatrix (partialFrameOperator F (p.lightInRow r))
        (fullFiber x p) := by
  classical
  ext k
  simp only [fullFiber, PiLp.toLp_apply, Matrix.mulVec, dotProduct,
    applyMatrix, WithLp.ofLp_sum, Finset.sum_apply]
  change (∑ inp : Fin d × Pattern m n,
      D1 (m := m) F (k, p) inp * x inp) =
    ∑ r, ∑ l, (partialFrameOperator F (p.lightInRow r)) k l * x (l, p)
  rw [Fintype.sum_prod_type]
  simp_rw [D1_apply]
  calc
    (∑ l, ∑ q,
        (if p = q then
          ∑ r, (partialFrameOperator F (p.lightInRow r)) k l else 0) *
            x (l, q)) =
        ∑ l, (∑ r, (partialFrameOperator F (p.lightInRow r)) k l) *
          x (l, p) := by
      apply Finset.sum_congr rfl
      intro l _
      simp
    _ = ∑ l, ∑ r,
        (partialFrameOperator F (p.lightInRow r)) k l * x (l, p) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_mul]
    _ = _ := by rw [Finset.sum_comm]

/-- The occupied-site diagonal correction acts on each fiber as a sum over occupied sites.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem D1_fullFiber_sites (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (p : Pattern m n) :
    fullFiber (Matrix.mulVec (D1 (m := m) F) x) p =
      ∑ s ∈ p.light,
        (analyze F (fullFiber x p) s.2) • F.u s.2 := by
  rw [D1_fullFiber_rows]
  simp_rw [partialFrameOperator_mulVec]
  ext k
  simp only [synthesize, WithLp.ofLp_sum, Finset.sum_apply,
    WithLp.ofLp_smul, Pi.smul_apply]
  exact DirectionalConcrete.sum_rows_light_eq_sum_light p
    (fun s ↦ analyze F (fullFiber x p) s.2 * F.u s.2 k)

/-- A scaled frame-vector analysis energy is bounded by its scalar energy.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem analyze_smul_frame_normSq_le (F : Frame n d)
    (v : EVec d) (i : Fin n) :
    ParsevalFrame.normSq ((analyze F v i) • F.u i) ≤
      ParsevalFrame.normSq v := by
  have ha : (analyze F v i) ^ 2 ≤ ParsevalFrame.normSq v := by
    have h := subset_analysis F ({i} : Finset (Fin n)) v
    simpa using h
  have hu := vector_normSq_le_one F i
  have hscale :
      ParsevalFrame.normSq ((analyze F v i) • F.u i) =
        (analyze F v i) ^ 2 * ParsevalFrame.normSq (F.u i) := by
    simp only [ParsevalFrame.normSq, PiLp.inner_apply, Real.inner_apply,
      WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hscale]
  calc
    (analyze F v i) ^ 2 * ParsevalFrame.normSq (F.u i) ≤
        (analyze F v i) ^ 2 * 1 := by
      exact mul_le_mul_of_nonneg_left hu (sq_nonneg _)
    _ ≤ ParsevalFrame.normSq v := by simpa using ha

/-- Occupied-site diagonal output-fiber energy is controlled by the light occupation count.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem D1_output_fiber_energy_le (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (p : Pattern m n) :
    ParsevalFrame.normSq
        (fullFiber (Matrix.mulVec (D1 (m := m) F) x) p) ≤
      (p.light.card : ℝ) ^ 2 *
        ParsevalFrame.normSq (fullFiber x p) := by
  rw [D1_fullFiber_sites]
  calc
    ParsevalFrame.normSq
        (∑ s ∈ p.light, (analyze F (fullFiber x p) s.2) • F.u s.2) ≤
        (p.light.card : ℝ) * ∑ s ∈ p.light,
          ParsevalFrame.normSq
            ((analyze F (fullFiber x p) s.2) • F.u s.2) :=
      DirectionalConcrete.normSq_sum_le_card p.light
        (fun s ↦ (analyze F (fullFiber x p) s.2) • F.u s.2)
    _ ≤ (p.light.card : ℝ) * ∑ _s ∈ p.light,
          ParsevalFrame.normSq (fullFiber x p) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro s _
      exact analyze_smul_frame_normSq_le F (fullFiber x p) s.2
    _ = (p.light.card : ℝ) ^ 2 *
          ParsevalFrame.normSq (fullFiber x p) := by
      simp
      ring

/-- The occupied-site diagonal correction obeys the stated exact-grade energy bound on supported vectors.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem D1_supported_energy_le (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ}
    (hx : DirectionalConcrete.SupportedAtGrade nu x) :
    FiniteHilbert.normSq (Matrix.mulVec (D1 (m := m) F) x) ≤
      (nu : ℝ) ^ 2 * FiniteHilbert.normSq x := by
  rw [DirectionalConcrete.full_normSq_eq_sum_fiber]
  calc
    (∑ p, ParsevalFrame.normSq
        (fullFiber (Matrix.mulVec (D1 (m := m) F) x) p)) ≤
        ∑ p, (nu : ℝ) ^ 2 *
          ParsevalFrame.normSq (fullFiber x p) := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hp : p.grade = nu
      · have hcardNat : p.light.card ≤ nu := by
          simpa [hp] using p.card_light_le_grade
        have hcard : (p.light.card : ℝ) ≤ (nu : ℝ) := by
          exact_mod_cast hcardNat
        have hsquare : (p.light.card : ℝ) ^ 2 ≤ (nu : ℝ) ^ 2 := by
          have hc0 : 0 ≤ (p.light.card : ℝ) := Nat.cast_nonneg _
          have hn0 : 0 ≤ (nu : ℝ) := Nat.cast_nonneg _
          nlinarith
        exact (D1_output_fiber_energy_le F x p).trans
          (mul_le_mul_of_nonneg_right hsquare real_inner_self_nonneg)
      · have hz : fullFiber x p = 0 := by
          ext k
          exact hx k p hp
        have hlocal := D1_output_fiber_energy_le (m := m) F x p
        rw [hz] at hlocal ⊢
        simpa [ParsevalFrame.normSq] using hlocal
    _ = (nu : ℝ) ^ 2 * FiniteHilbert.normSq x := by
      rw [DirectionalConcrete.full_normSq_eq_sum_fiber, Finset.mul_sum]

/-- The occupied-site diagonal correction obeys the stated energy bound after grade projection.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem D1_restricted_energy (F : Frame n d) (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    FiniteHilbert.normSq
        (Matrix.mulVec
          (D1 (m := m) F * gradeProjection (d := d) nu) x) ≤
      (nu : ℝ) ^ 2 * FiniteHilbert.normSq x := by
  rw [← Matrix.mulVec_mulVec]
  calc
    FiniteHilbert.normSq
        (Matrix.mulVec (D1 (m := m) F)
          (Matrix.mulVec (gradeProjection (d := d) nu) x)) ≤
        (nu : ℝ) ^ 2 * FiniteHilbert.normSq
          (Matrix.mulVec (gradeProjection (d := d) nu) x) :=
      D1_supported_energy_le F (DirectionalConcrete.gradeProjection_supported nu x)
    _ ≤ (nu : ℝ) ^ 2 * FiniteHilbert.normSq x := by
      exact mul_le_mul_of_nonneg_left (gradeProjection_normSq_le nu x)
        (sq_nonneg (nu : ℝ))

/-- The light-occupancy diagonal has restricted norm at most the input grade.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem D1_gradeProjection_norm (F : Frame n d) (nu : ℕ) :
    ‖D1 (m := m) F * gradeProjection (d := d) nu‖ ≤ (nu : ℝ) := by
  exact FiniteHilbert.norm_le_of_normSq_mulVec_le (Nat.cast_nonneg nu)
    (D1_restricted_energy (m := m) F nu)

end

end NLAlib.SparseFock.LightBandsConcrete
