import NLAlib.ForMathlib.Analysis.Complex.PrimitiveHomotopyGrid

/-!
# Holomorphic contour integrals under free loop homotopies

A continuous homotopy of loops preserves the integral of a holomorphic
function, even when the loops have different base points. The proof constructs
actual local primitives on a finite grid and cancels its boundary sides.
The grid and primitive transport infrastructure is ported from the local
deferred Jordan-contour development; the free-loop boundary cancellation is
new. Only the two endpoint loops need to be continuously differentiable.
-/

noncomputable section

open Set Finset MeasureTheory
open scoped unitInterval

namespace Complex

private theorem freeHomotopy_node_mem_Icc {n i : ℕ} (hn : 0 < n) (hi : i ≤ n) :
    (i : ℝ) / n ∈ Icc (0 : ℝ) 1 := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  exact ⟨div_nonneg (Nat.cast_nonneg i) hn'.le,
    (div_le_one hn').mpr (by exact_mod_cast hi)⟩

/-- A continuous free homotopy of loops in an open holomorphy domain preserves
their native contour integrals. Opposite boundary sides are the same path;
their primitive transports cancel even though the charts may differ. -/
theorem curveIntegral_eq_of_differentiableOn_of_freeHomotopy
    {a b : ℂ} (γ₀ : Path a a) (γ₁ : Path b b)
    {ψ : ℝ × ℝ → ℂ} (hψ : Continuous ψ) {Ω : Set ℂ} {g : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω)
    (hψΩ : ∀ t ∈ Icc (0 : ℝ × ℝ) 1, ψ t ∈ Ω)
    (hleft : ∀ t ∈ Icc (0 : ℝ) 1, γ₀.extend t = ψ (0, t))
    (hright : ∀ t ∈ Icc (0 : ℝ) 1, γ₁.extend t = ψ (1, t))
    (hloop : ∀ t ∈ Icc (0 : ℝ) 1, ψ (t, 0) = ψ (t, 1))
    (hγ₀ : ContDiffOn ℝ 1 γ₀.extend I) (hγ₁ : ContDiffOn ℝ 1 γ₁.extend I) :
    curveIntegral (fun z => g z • ContinuousLinearMap.id ℂ ℂ) γ₀ =
      curveIntegral (fun z => g z • ContinuousLinearMap.id ℂ ℂ) γ₁ := by
  classical
  let D := Classical.choice (nonempty_primitiveHomotopyGrid_of_differentiableOn
    hψ hΩ hg hψΩ)
  have hn : 0 < (D.size : ℝ) := by exact_mod_cast D.size_pos
  have hlast : D.size - 1 < D.size := Nat.sub_lt D.size_pos (by decide)
  have hlastadd : D.size - 1 + 1 = D.size := Nat.sub_add_cancel (Nat.succ_le_of_lt D.size_pos)
  have hend : ((D.size - 1 : ℕ) : ℝ) + 1 = D.size := by exact_mod_cast hlastadd
  have hlastnode : (((D.size - 1 : ℕ) : ℝ) + 1) / D.size = 1 := by
    rw [hend, div_self hn.ne']
  have hnode (i : ℕ) (hi : i ≤ D.size) : (i : ℝ) / D.size ∈ Icc (0 : ℝ) 1 :=
    freeHomotopy_node_mem_Icc D.size_pos hi
  have hcellI (i : ℕ) (hi : i < D.size) {t : ℝ}
      (ht : t ∈ Icc ((i : ℝ) / D.size) ((i + 1 : ℝ) / D.size)) : t ∈ Icc (0 : ℝ) 1 := by
    have hnext : (i + 1 : ℝ) / D.size ∈ Icc (0 : ℝ) 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hnode (i + 1) hi
    exact ⟨(hnode i hi.le).1.trans ht.1, ht.2.trans hnext.2⟩
  have hp (i : ℕ) (_hi : i < D.size) :
      (i : ℝ) / D.size ≤ ((i + 1 : ℕ) : ℝ) / D.size := by
    apply div_le_div_of_nonneg_right _ hn.le
    exact_mod_cast Nat.le_succ i
  have hleftChart : ∀ j < D.size,
      ∀ t ∈ Icc ((j : ℝ) / D.size) (((j + 1 : ℕ) : ℝ) / D.size),
        γ₀.extend t ∈ D.chart 0 j := by
    intro j hj t ht
    have ht' : t ∈ Icc ((j : ℝ) / D.size) ((j + 1 : ℝ) / D.size) := by
      simpa only [Nat.cast_add, Nat.cast_one] using ht
    rw [hleft t (hcellI j hj ht')]
    apply D.mapsTo_chart 0 D.size_pos j hj
    exact ⟨⟨by simp, ht'.1⟩, ⟨by positivity, ht'.2⟩⟩
  have hrightChart : ∀ j < D.size,
      ∀ t ∈ Icc ((j : ℝ) / D.size) (((j + 1 : ℕ) : ℝ) / D.size),
        γ₁.extend t ∈ D.chart (D.size - 1) j := by
    intro j hj t ht
    have ht' : t ∈ Icc ((j : ℝ) / D.size) ((j + 1 : ℝ) / D.size) := by
      simpa only [Nat.cast_add, Nat.cast_one] using ht
    rw [hright t (hcellI j hj ht')]
    apply D.mapsTo_chart _ hlast j hj
    exact ⟨⟨(hnode _ hlast.le).2, ht'.1⟩, ⟨hlastnode.symm.le, ht'.2⟩⟩
  have hL := primitiveSubdivisionTransport_eq_curveIntegral_of_hasDerivAt γ₀ hγ₀
    hp (by simp) (by simp [D.size_pos.ne']) hnode
    (fun j hj => D.hasDerivAt_primitive 0 D.size_pos j hj)
    (fun j hj => D.continuousOn 0 D.size_pos j hj) hleftChart
  have hR := primitiveSubdivisionTransport_eq_curveIntegral_of_hasDerivAt γ₁ hγ₁
    hp (by simp) (by simp [D.size_pos.ne']) hnode
    (fun j hj => D.hasDerivAt_primitive _ hlast j hj)
    (fun j hj => D.continuousOn _ hlast j hj) hrightChart
  have hsumL : (∑ j ∈ range D.size, D.left 0 j) =
      curveIntegral (fun z => g z • ContinuousLinearMap.id ℂ ℂ) γ₀ := by
    rw [← hL]
    unfold primitiveSubdivisionTransport
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    have hnext := hnode (j + 1) hj'
    simp only [PrimitiveHomotopyGrid.left, Nat.cast_zero, zero_div]
    rw [hleft _ hnext, hleft _ (hnode j hj'.le)]
    simp only [Nat.cast_add, Nat.cast_one]
  have hsumR : (∑ j ∈ range D.size, D.right (D.size - 1) j) =
      curveIntegral (fun z => g z • ContinuousLinearMap.id ℂ ℂ) γ₁ := by
    rw [← hR]
    unfold primitiveSubdivisionTransport
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    have hnext := hnode (j + 1) hj'
    simp only [PrimitiveHomotopyGrid.right, hlastnode]
    rw [hright _ hnext, hright _ (hnode j hj'.le)]
    simp only [Nat.cast_add, Nat.cast_one]
  have htopBottom (i : ℕ) (hi : i < D.size) :
      D.top i (D.size - 1) = D.bottom i 0 := by
    have h := sub_eq_sub_of_hasDerivAt_of_continuous
      (γ := fun t => ψ (t, 0)) (hψ.comp (continuous_id.prodMk continuous_const))
      (hp i hi) (D.isOpen_chart i hi _ hlast) (D.isOpen_chart i hi 0 D.size_pos)
      (D.hasDerivAt_primitive i hi _ hlast) (D.hasDerivAt_primitive i hi 0 D.size_pos)
      (fun t ht => by
        have ht' : t ∈ Icc ((i : ℝ) / D.size) ((i + 1 : ℝ) / D.size) := by
          simpa only [Nat.cast_add, Nat.cast_one] using ht
        rw [hloop t (hcellI i hi ht')]
        apply D.mapsTo_chart i hi _ hlast
        exact ⟨⟨ht'.1, (hnode _ hlast.le).2⟩, ⟨ht'.2, hlastnode.symm.le⟩⟩)
      (fun t ht => by
        apply D.mapsTo_chart i hi 0 D.size_pos
        exact ⟨⟨ht.1, by simp⟩, ⟨by simpa only [Nat.cast_add, Nat.cast_one] using ht.2,
          by positivity⟩⟩)
    have hnext := hnode (i + 1) hi
    have hcur := hnode i hi.le
    have hnext' : (i + 1 : ℝ) / D.size ∈ Icc (0 : ℝ) 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hnext
    simpa only [PrimitiveHomotopyGrid.top, PrimitiveHomotopyGrid.bottom,
      Nat.cast_zero, zero_div, hlastnode, Nat.cast_add, Nat.cast_one,
      ← hloop _ hnext', ← hloop _ hcur] using h
  have hboundary := D.sum_right_sub_sum_left_eq_sum_top_sub_sum_bottom hψ
  have hsum : (∑ i ∈ range D.size, D.top i (D.size - 1)) =
      ∑ i ∈ range D.size, D.bottom i 0 := by
    exact sum_congr rfl (fun i hi => htopBottom i (mem_range.mp hi))
  rw [hsum, sub_self, hsumL, hsumR] at hboundary
  exact (sub_eq_zero.mp hboundary).symm

end Complex
