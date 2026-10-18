import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Tactic.Linarith

/-! # Positive extensions with a prescribed value

A positive linear functional on an order-cofinal subspace can be extended with
a specified value at one additional vector precisely when that value respects
the lower and upper order bounds. This refines the one-vector step of the
M. Riesz extension theorem and supports compact transport duality.
-/

noncomputable section

open Set Submodule

namespace NLAlib

/-- The M. Riesz extension theorem with a prescribed value at one vector.
The two bounds are actual order constraints against the original domain. -/
theorem exists_extension_nonneg_apply_eq {E : Type*} [AddCommGroup E] [Module ℝ E]
    (s : PointedCone ℝ E) (f : E →ₗ.[ℝ] ℝ) (y : E) (v : ℝ)
    (hnonneg : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x)
    (hdense : ∀ z, ∃ x : f.domain, (x : E) + z ∈ s)
    (hlower : ∀ x : f.domain, y - (x : E) ∈ s → f x ≤ v)
    (hupper : ∀ x : f.domain, (x : E) - y ∈ s → v ≤ f x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧
      (∀ x ∈ s, 0 ≤ g x) ∧ g y = v := by
  by_cases hy : y ∈ f.domain
  · obtain ⟨g, hgf, hg⟩ := riesz_extension s f hnonneg hdense
    refine ⟨g, hgf, hg, ?_⟩
    have hzero : y - (⟨y, hy⟩ : f.domain) ∈ s := by simp
    exact (hgf ⟨y, hy⟩).trans (le_antisymm (hlower _ hzero) (hupper _ hzero))
  let c := -v
  have hneg (x : f.domain) (hx : -(x : E) - y ∈ s) : f x ≤ c := by
    have h := hupper (-x) hx
    rw [f.map_neg] at h
    dsimp [c]
    linarith
  have hpos (x : f.domain) (hx : (x : E) + y ∈ s) : c ≤ f x := by
    have h := hlower (-x) (by simpa [sub_neg_eq_add, add_comm] using hx)
    rw [f.map_neg] at h
    dsimp [c]
    linarith
  let q := f.supSpanSingleton y (-c) hy
  have hfq : f ≤ q := f.left_le_sup _ _
  have hq : ∀ z : q.domain, (z : E) ∈ s → 0 ≤ q z := by
    rintro ⟨z, hz⟩ hzs
    rcases mem_sup.1 hz with ⟨x, hx, y', hy', rfl⟩
    rcases mem_span_singleton.1 hy' with ⟨r, rfl⟩
    simp only at hzs
    rw [LinearPMap.supSpanSingleton_apply_mk _ _ _ _ _ hx, smul_neg,
      ← sub_eq_add_neg, sub_nonneg]
    rcases lt_trichotomy r 0 with hr | hr | hr
    · have h : -(r⁻¹ • x) - y ∈ s := by
        rwa [← s.smul_mem_iff (neg_pos.2 hr), smul_sub, smul_neg, neg_smul,
          neg_neg, smul_smul, mul_inv_cancel₀ hr.ne, one_smul, sub_eq_add_neg,
          neg_smul, neg_neg]
      have h' := hneg (r⁻¹ • ⟨x, hx⟩) h
      rwa [← mul_le_mul_iff_right₀ (neg_pos.2 hr), neg_mul, neg_mul,
        neg_le_neg_iff, f.map_smul, smul_eq_mul, ← mul_assoc,
        mul_inv_cancel₀ hr.ne, one_mul] at h'
    · subst r
      simp only [zero_smul, add_zero] at hzs ⊢
      rw [RingHom.id_apply, zero_smul]
      exact hnonneg _ hzs
    · have h : r⁻¹ • x + y ∈ s := by
        rwa [← s.smul_mem_iff hr, smul_add, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      have h' := hpos (r⁻¹ • ⟨x, hx⟩) h
      rwa [← mul_le_mul_iff_right₀ hr, f.map_smul, smul_eq_mul,
        ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at h'
  have hqdense : ∀ z, ∃ x : q.domain, (x : E) + z ∈ s := by
    intro z
    obtain ⟨x, hx⟩ := hdense z
    exact ⟨Submodule.inclusion hfq.1 x, hx⟩
  obtain ⟨g, hgq, hg⟩ := riesz_extension s q hq hqdense
  refine ⟨g, ?_, hg, ?_⟩
  · intro x
    exact (hgq (Submodule.inclusion hfq.1 x)).trans (hfq.2 rfl).symm
  · have hyq : y ∈ q.domain := mem_sup_right (mem_span_singleton_self y)
    calc
      g y = q ⟨y, hyq⟩ := hgq ⟨y, hyq⟩
      _ = -c := f.supSpanSingleton_apply_self (-c) hy
      _ = v := neg_neg v

/-- The least possible value of a positive extension at `y` is attained. It is
the supremum of the original functional evaluated on domain vectors below
`y`. Cofinality supplies both bounds, so this is a finite real supremum. -/
theorem exists_extension_nonneg_apply_eq_sSup {E : Type*}
    [AddCommGroup E] [Module ℝ E] (s : PointedCone ℝ E) (f : E →ₗ.[ℝ] ℝ) (y : E)
    (hnonneg : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x)
    (hdense : ∀ z, ∃ x : f.domain, (x : E) + z ∈ s) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧
      (∀ x ∈ s, 0 ≤ g x) ∧
      g y = sSup (f '' {x : f.domain | y - (x : E) ∈ s}) := by
  let S := f '' {x : f.domain | y - (x : E) ∈ s}
  have hS : S.Nonempty := by
    obtain ⟨x, hx⟩ := hdense y
    exact ⟨f (-x), -x, by simpa [sub_neg_eq_add, add_comm] using hx, rfl⟩
  have hcompare (x u : f.domain) (hx : y - (x : E) ∈ s)
      (hu : (u : E) - y ∈ s) : f x ≤ f u := by
    have hmem : ((u - x : f.domain) : E) ∈ s := by
      convert s.add_mem hu hx using 1
      simp only [AddSubgroupClass.coe_sub, sub_add_sub_cancel]
    have h := hnonneg (u - x) hmem
    rw [f.map_sub] at h
    exact sub_nonneg.mp h
  have hbdd : BddAbove S := by
    obtain ⟨u, hu⟩ := hdense (-y)
    refine ⟨f u, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hcompare x u hx (by simpa [sub_eq_add_neg] using hu)
  apply exists_extension_nonneg_apply_eq s f y (sSup S) hnonneg hdense
  · intro x hx
    exact le_csSup hbdd ⟨x, hx, rfl⟩
  · intro u hu
    apply csSup_le hS
    rintro _ ⟨x, hx, rfl⟩
    exact hcompare x u hx hu

end NLAlib
