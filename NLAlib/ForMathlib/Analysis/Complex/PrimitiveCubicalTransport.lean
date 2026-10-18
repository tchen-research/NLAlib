import NLAlib.ForMathlib.Analysis.Complex.PrimitivePathIntegral
import NLAlib.ForMathlib.Analysis.Complex.PrimitiveHomotopyGrid

/-! # Holomorphic transport around continuous singular squares

The four actual continuous boundary paths of a singular square have zero
alternating primitive transport. Only local holomorphy is used; the interior
and boundary need not be smooth. This is the analytic step for cancellation
on finite singular cubical two-chains.
-/

noncomputable section
open Set Finset Metric
open scoped unitInterval
namespace Complex

/-- The four boundary transports of an actual continuous primitive-charted
square cancel. The edge subdivisions and their agreement with the intrinsic
continuous-path integrals are constructed from the grid. -/
theorem primitivePathIntegral_boundary_eq_zero_of_grid
    {a b c d : ℂ} {g : ℂ → ℂ}
    (L : Path a b) (R : Path c d) (B : Path a c) (T : Path b d)
    (hL : Nonempty (PrimitivePathSubdivision g L.extend))
    (hR : Nonempty (PrimitivePathSubdivision g R.extend))
    (hB : Nonempty (PrimitivePathSubdivision g B.extend))
    (hT : Nonempty (PrimitivePathSubdivision g T.extend))
    {ψ : ℝ × ℝ → ℂ} (hψ : Continuous ψ) (D : PrimitiveHomotopyGrid g ψ)
    (hleft : ∀ t ∈ Icc (0 : ℝ) 1, L.extend t = ψ (0, t))
    (hright : ∀ t ∈ Icc (0 : ℝ) 1, R.extend t = ψ (1, t))
    (hbottom : ∀ t ∈ Icc (0 : ℝ) 1, B.extend t = ψ (t, 0))
    (htop : ∀ t ∈ Icc (0 : ℝ) 1, T.extend t = ψ (t, 1)) :
    primitivePathIntegral g R hR - primitivePathIntegral g L hL -
      primitivePathIntegral g T hT + primitivePathIntegral g B hB = 0 := by
  have hn : 0 < (D.size : ℝ) := by exact_mod_cast D.size_pos
  have hlast : D.size - 1 < D.size := Nat.sub_lt D.size_pos (by decide)
  have hend : ((D.size - 1 : ℕ) : ℝ) + 1 = D.size := by
    exact_mod_cast Nat.sub_add_cancel (Nat.succ_le_of_lt D.size_pos)
  have hlastnode : (((D.size - 1 : ℕ) : ℝ) + 1) / D.size = 1 := by
    rw [hend, div_self hn.ne']
  have hnode (i : ℕ) (hi : i ≤ D.size) : (i : ℝ) / D.size ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (Nat.cast_nonneg i) hn.le, (div_le_one hn).mpr (by exact_mod_cast hi)⟩
  have hcell (i : ℕ) (hi : i < D.size) {t : ℝ}
      (ht : t ∈ Icc ((i : ℝ) / D.size) ((i + 1 : ℝ) / D.size)) : t ∈ Icc (0 : ℝ) 1 := by
    have hnext : (i + 1 : ℝ) / D.size ∈ Icc (0 : ℝ) 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hnode (i + 1) hi
    exact ⟨(hnode i hi.le).1.trans ht.1, ht.2.trans hnext.2⟩
  let DL : PrimitivePathSubdivision g L.extend :=
    ⟨D.size, D.size_pos, D.chart 0, D.primitive 0,
      fun j hj => D.isOpen_chart 0 D.size_pos j hj,
      fun j hj => D.hasDerivAt_primitive 0 D.size_pos j hj,
      fun j hj => D.continuousOn 0 D.size_pos j hj,
      fun j hj t ht => by
        rw [hleft t (hcell j hj ht)]
        apply D.mapsTo_chart 0 D.size_pos j hj
        exact ⟨⟨by simp, ht.1⟩, ⟨by positivity, ht.2⟩⟩⟩
  let DR : PrimitivePathSubdivision g R.extend :=
    ⟨D.size, D.size_pos, D.chart (D.size - 1), D.primitive (D.size - 1),
      fun j hj => D.isOpen_chart _ hlast j hj,
      fun j hj => D.hasDerivAt_primitive _ hlast j hj,
      fun j hj => D.continuousOn _ hlast j hj,
      fun j hj t ht => by
        rw [hright t (hcell j hj ht)]
        apply D.mapsTo_chart _ hlast j hj
        exact ⟨⟨(hnode _ hlast.le).2, ht.1⟩, ⟨hlastnode.symm.le, ht.2⟩⟩⟩
  let DB : PrimitivePathSubdivision g B.extend :=
    ⟨D.size, D.size_pos, fun i => D.chart i 0, fun i => D.primitive i 0,
      fun i hi => D.isOpen_chart i hi 0 D.size_pos,
      fun i hi => D.hasDerivAt_primitive i hi 0 D.size_pos,
      fun i hi => D.continuousOn i hi 0 D.size_pos,
      fun i hi t ht => by
        rw [hbottom t (hcell i hi ht)]
        apply D.mapsTo_chart i hi 0 D.size_pos
        exact ⟨⟨ht.1, by simp⟩, ⟨ht.2, by positivity⟩⟩⟩
  let DT : PrimitivePathSubdivision g T.extend :=
    ⟨D.size, D.size_pos, fun i => D.chart i (D.size - 1), fun i => D.primitive i (D.size - 1),
      fun i hi => D.isOpen_chart i hi _ hlast,
      fun i hi => D.hasDerivAt_primitive i hi _ hlast,
      fun i hi => D.continuousOn i hi _ hlast,
      fun i hi t ht => by
        rw [htop t (hcell i hi ht)]
        apply D.mapsTo_chart i hi _ hlast
        exact ⟨⟨ht.1, (hnode _ hlast.le).2⟩, ⟨ht.2, hlastnode.symm.le⟩⟩⟩
  have hLi : primitivePathIntegral g L hL = ∑ j ∈ range D.size, D.left 0 j := by
    rw [primitivePathIntegral_eq_transport L hL DL]
    unfold PrimitivePathSubdivision.transport primitiveSubdivisionTransport
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    rw [hleft _ (hnode (j + 1) hj'), hleft _ (hnode j hj'.le)]
    simp only [DL, PrimitiveHomotopyGrid.left, Nat.cast_zero, zero_div, Nat.cast_add, Nat.cast_one]
  have hRi : primitivePathIntegral g R hR = ∑ j ∈ range D.size, D.right (D.size - 1) j := by
    rw [primitivePathIntegral_eq_transport R hR DR]
    unfold PrimitivePathSubdivision.transport primitiveSubdivisionTransport
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    rw [hright _ (hnode (j + 1) hj'), hright _ (hnode j hj'.le)]
    simp only [DR, PrimitiveHomotopyGrid.right, Nat.cast_add, Nat.cast_one, hlastnode]
  have hBi : primitivePathIntegral g B hB = ∑ i ∈ range D.size, D.bottom i 0 := by
    rw [primitivePathIntegral_eq_transport B hB DB]
    unfold PrimitivePathSubdivision.transport primitiveSubdivisionTransport
    apply sum_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    rw [hbottom _ (hnode (i + 1) hi'), hbottom _ (hnode i hi'.le)]
    simp only [DB, PrimitiveHomotopyGrid.bottom, Nat.cast_zero, zero_div, Nat.cast_add, Nat.cast_one]
  have hTi : primitivePathIntegral g T hT = ∑ i ∈ range D.size, D.top i (D.size - 1) := by
    rw [primitivePathIntegral_eq_transport T hT DT]
    unfold PrimitivePathSubdivision.transport primitiveSubdivisionTransport
    apply sum_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    rw [htop _ (hnode (i + 1) hi'), htop _ (hnode i hi'.le)]
    simp only [DT, PrimitiveHomotopyGrid.top, Nat.cast_add, Nat.cast_one, hlastnode]
  rw [hRi, hLi, hTi, hBi, D.sum_right_sub_sum_left_eq_sum_top_sub_sum_bottom hψ]
  abel

end Complex
