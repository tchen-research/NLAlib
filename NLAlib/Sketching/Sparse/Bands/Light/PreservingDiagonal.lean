/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.Sparse.Bands.Light.AnalysisGram

/-!
# Light preserving diagonal energy

The preserving-band decomposition and occupied-site diagonal correction energy.
Ported from `SparseFockFormal.LightBandsConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace NLAlib.SparseSketch.Light

open SparseSketch.Directional

noncomputable section

variable {d m n : ℕ}

/-- Light creation and annihilation at distinct sites form the corresponding word kernel.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem pDagAt_mul_pAt_of_ne (r : Fin m) {i j : Fin n}
    (hij : i ≠ j) :
    pDagAt r i * pAt r j =
      wordKernel (r, i) (r, j) (.pUp, .pDown) := by
  simpa [pAt, pDagAt, wordKernel, Leg.op] using
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
      orderedWordTerm (Frame.rows F) r i j
        (.pUp, .pDown) := by
  classical
  ext out inp
  simp only [Matrix.mul_apply, Matrix.transpose_apply, COne, orderedWordTerm,
    externalTensor, Matrix.vecMulVec_apply]
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
          orderedWordTerm (Frame.rows F) r i j
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
      wordSum m (Frame.rows F) .pUp .pDown := by
  classical
  rw [ghat]
  simp only [D1, wordSum, physicalWordSum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  exact CMatrix_mul_transpose_decomposition F r

/-- Exact grade-zero light-band identity from the two diagonal/cross Grams.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Lzero_eq_ghat_sub_D1_add_Hprime (F : Frame n d) :
    Lzero m (Frame.rows F) =
      (ghat F - D1 F) + Hprime m (Frame.rows F) := by
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
  let erased := Heavy.setSite a s .zero
  by_cases ha : a s = .one
  · rw [Finset.sum_eq_single erased]
    · have hfirst : a (r, i) = .one ∧
          erased = Heavy.setSite a (r, i) .zero := by
        constructor
        · simpa [s] using ha
        · rfl
      have hsecond :
          (b (r, i) = .one ∧
            erased = Heavy.setSite b (r, i) .zero) ↔ b = a := by
        constructor
        · rintro ⟨hb, heq⟩
          calc
            b = Heavy.setSite
                (Heavy.setSite b (r, i) .zero) (r, i) .one := by
              symm
              exact Heavy.setSite_restore (b := .zero) b (r, i) hb
            _ = Heavy.setSite erased (r, i) .one := by rw [← heq]
            _ = a := by
              exact Heavy.setSite_restore
                (b := .zero) a (r, i) (by simpa [s] using ha)
        · rintro rfl
          exact hfirst
      simp only [pDagAt_apply, if_pos hfirst]
      by_cases hab : b = a
      · subst b
        simp [hfirst]
      · have hn : ¬(b (r, i) = .one ∧
            erased = Heavy.setSite b (r, i) .zero) :=
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
    fiber (Matrix.mulVec (D1 (m := m) F) x) p =
      ∑ r, applyMatrix (partialFrameOperator F (p.lightInRow r))
        (fiber x p) := by
  classical
  ext k
  simp only [fiber, PiLp.toLp_apply, Matrix.mulVec, dotProduct,
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
    fiber (Matrix.mulVec (D1 (m := m) F) x) p =
      ∑ s ∈ p.light,
        (analyze F (fiber x p) s.2) • F.u s.2 := by
  rw [D1_fullFiber_rows]
  simp_rw [partialFrameOperator_mulVec]
  ext k
  simp only [synthesize, WithLp.ofLp_sum, Finset.sum_apply,
    WithLp.ofLp_smul, Pi.smul_apply]
  exact sum_rows_light_eq_sum_light p
    (fun s ↦ analyze F (fiber x p) s.2 * F.u s.2 k)

/-- A scaled frame-vector analysis energy is bounded by its scalar energy.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem analyze_smul_frame_normSq_le (F : Frame n d)
    (v : EVec d) (i : Fin n) :
    euclideanNormSq ((analyze F v i) • F.u i) ≤
      euclideanNormSq v := by
  have ha : (analyze F v i) ^ 2 ≤ euclideanNormSq v := by
    have h := subset_analysis F ({i} : Finset (Fin n)) v
    simpa using h
  have hu := vector_normSq_le_one F i
  have hscale :
      euclideanNormSq ((analyze F v i) • F.u i) =
        (analyze F v i) ^ 2 * euclideanNormSq (F.u i) := by
    simp only [euclideanNormSq, PiLp.inner_apply, Real.inner_apply,
      WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hscale]
  calc
    (analyze F v i) ^ 2 * euclideanNormSq (F.u i) ≤
        (analyze F v i) ^ 2 * 1 := by
      exact mul_le_mul_of_nonneg_left hu (sq_nonneg _)
    _ ≤ euclideanNormSq v := by simpa using ha

/-- Occupied-site diagonal output-fiber energy is controlled by the light occupation count.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem D1_output_fiber_energy_le (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) (p : Pattern m n) :
    euclideanNormSq
        (fiber (Matrix.mulVec (D1 (m := m) F) x) p) ≤
      (p.light.card : ℝ) ^ 2 *
        euclideanNormSq (fiber x p) := by
  rw [D1_fullFiber_sites]
  calc
    euclideanNormSq
        (∑ s ∈ p.light, (analyze F (fiber x p) s.2) • F.u s.2) ≤
        (p.light.card : ℝ) * ∑ s ∈ p.light,
          euclideanNormSq
            ((analyze F (fiber x p) s.2) • F.u s.2) :=
      normSq_sum_le_card p.light
        (fun s ↦ (analyze F (fiber x p) s.2) • F.u s.2)
    _ ≤ (p.light.card : ℝ) * ∑ _s ∈ p.light,
          euclideanNormSq (fiber x p) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro s _
      exact analyze_smul_frame_normSq_le F (fiber x p) s.2
    _ = (p.light.card : ℝ) ^ 2 *
          euclideanNormSq (fiber x p) := by
      simp
      ring

/-- The occupied-site diagonal correction obeys the stated exact-grade energy bound on supported vectors.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem D1_supported_energy_le (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ}
    (hx : SupportedAtGrade nu x) :
    sumSq (Matrix.mulVec (D1 (m := m) F) x) ≤
      (nu : ℝ) ^ 2 * sumSq x := by
  rw [full_normSq_eq_sum_fiber]
  calc
    (∑ p, euclideanNormSq
        (fiber (Matrix.mulVec (D1 (m := m) F) x) p)) ≤
        ∑ p, (nu : ℝ) ^ 2 *
          euclideanNormSq (fiber x p) := by
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
      · have hz : fiber x p = 0 := by
          ext k
          exact hx k p hp
        have hlocal := D1_output_fiber_energy_le (m := m) F x p
        rw [hz] at hlocal ⊢
        simpa [euclideanNormSq] using hlocal
    _ = (nu : ℝ) ^ 2 * sumSq x := by
      rw [full_normSq_eq_sum_fiber, Finset.mul_sum]

/-- The occupied-site diagonal correction obeys the stated energy bound after grade projection.
Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem D1_restricted_energy (F : Frame n d) (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    sumSq
        (Matrix.mulVec
          (D1 (m := m) F * gradeProjection (d := d) nu) x) ≤
      (nu : ℝ) ^ 2 * sumSq x := by
  rw [← Matrix.mulVec_mulVec]
  calc
    sumSq
        (Matrix.mulVec (D1 (m := m) F)
          (Matrix.mulVec (gradeProjection (d := d) nu) x)) ≤
        (nu : ℝ) ^ 2 * sumSq
          (Matrix.mulVec (gradeProjection (d := d) nu) x) :=
      D1_supported_energy_le F (gradeProjection_supported nu x)
    _ ≤ (nu : ℝ) ^ 2 * sumSq x := by
      exact mul_le_mul_of_nonneg_left (gradeProjection_normSq_le nu x)
        (sq_nonneg (nu : ℝ))

/-- The light-occupancy diagonal has restricted norm at most the input grade.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem D1_gradeProjection_norm (F : Frame n d) (nu : ℕ) :
    ‖D1 (m := m) F * gradeProjection (d := d) nu‖ ≤ (nu : ℝ) := by
  exact norm_le_of_normSq_mulVec_le (Nat.cast_nonneg nu)
    (D1_restricted_energy (m := m) F nu)

end

end NLAlib.SparseSketch.Light
