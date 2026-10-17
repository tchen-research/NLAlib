import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Fine uniform subdivisions subordinate to compact path covers

An open cover of the image of a continuous path admits a uniform parameter
subdivision with each closed cell in one chart. The corresponding theorem for
a continuous map of the unit square supplies the finite grid needed for local
primitive homotopy arguments. Both mesh constructions follow from the native
compact Lebesgue-number theorem; no differentiability or smoothing is used.

Ported from the local deferred Jordan-contour development of 2026-10-14.
-/

noncomputable section
open Set Metric

private theorem uniformSubdivision_node_mem_Icc {n i : ℕ} (hn : 0 < n) (hi : i ≤ n) :
    (i : ℝ) / n ∈ Icc (0 : ℝ) 1 := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  exact ⟨div_nonneg (Nat.cast_nonneg i) hn'.le,
    (div_le_one hn').mpr (by exact_mod_cast hi)⟩

private theorem uniformSubdivision_cell_subset_ball {n i : ℕ} {δ : ℝ}
    (hδ : 1 / (n : ℝ) < δ) :
    Icc ((i : ℝ) / n) ((i + 1 : ℝ) / n) ⊆ ball ((i : ℝ) / n) δ := by
  intro t ht
  rw [mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
  apply lt_of_le_of_lt _ hδ
  have htop : t ≤ (i : ℝ) / n + 1 / n := by simpa only [add_div] using ht.2
  linarith

/-- Every open cover of a compact continuous path image admits a finite uniform
subdivision whose actual closed parameter cells map into individual charts. -/
theorem exists_uniform_subdivision_subordinate_open_cover
    {X : Type*} [TopologicalSpace X] {ι : Sort*} (γ : ℝ → X) (hγ : Continuous γ)
    (U : ι → Set X) (hU : ∀ j, IsOpen (U j))
    (hcover : γ '' Icc (0 : ℝ) 1 ⊆ ⋃ j, U j) :
    ∃ n : ℕ, 0 < n ∧ ∀ i < n, ∃ j, ∀ t ∈ Icc ((i : ℝ) / n) ((i + 1 : ℝ) / n),
      γ t ∈ U j := by
  have hpre : Icc (0 : ℝ) 1 ⊆ ⋃ j, γ ⁻¹' U j := by
    intro t ht
    simpa only [mem_iUnion, mem_preimage] using hcover (mem_image_of_mem γ ht)
  obtain ⟨δ, hδ, hmesh⟩ := lebesgue_number_lemma_of_metric isCompact_Icc
    (fun j => hγ.isOpen_preimage _ (hU j)) hpre
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  have hm' : 1 / ((m + 1 : ℕ) : ℝ) < δ := by simpa only [Nat.cast_add, Nat.cast_one] using hm
  refine ⟨m + 1, Nat.succ_pos m, ?_⟩
  intro i hi
  obtain ⟨j, hj⟩ := hmesh ((i : ℝ) / (m + 1 : ℕ))
    (uniformSubdivision_node_mem_Icc (Nat.succ_pos m) hi.le)
  exact ⟨j, fun t ht => hj (uniformSubdivision_cell_subset_ball hm' ht)⟩

/-- A compact continuous homotopy square has a uniform finite grid whose actual
closed cells each lie in one open chart of the image cover. This is the mesh
input for a local primitive telescoping argument, with no C² hypothesis. -/
theorem exists_uniform_grid_subordinate_open_cover
    {X : Type*} [TopologicalSpace X] {ι : Sort*} (ψ : ℝ × ℝ → X) (hψ : Continuous ψ)
    (U : ι → Set X) (hU : ∀ j, IsOpen (U j))
    (hcover : ψ '' Icc (0 : ℝ × ℝ) 1 ⊆ ⋃ j, U j) :
    ∃ n : ℕ, 0 < n ∧ ∀ i < n, ∀ k < n, ∃ j,
      ∀ t ∈ Icc (((i : ℝ) / n), ((k : ℝ) / n))
        (((i + 1 : ℝ) / n), ((k + 1 : ℝ) / n)), ψ t ∈ U j := by
  have hpre : Icc (0 : ℝ × ℝ) 1 ⊆ ⋃ j, ψ ⁻¹' U j := by
    intro t ht
    simpa only [mem_iUnion, mem_preimage] using hcover (mem_image_of_mem ψ ht)
  obtain ⟨δ, hδ, hmesh⟩ := lebesgue_number_lemma_of_metric isCompact_Icc
    (fun j => hψ.isOpen_preimage _ (hU j)) hpre
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  have hm' : 1 / ((m + 1 : ℕ) : ℝ) < δ := by simpa only [Nat.cast_add, Nat.cast_one] using hm
  refine ⟨m + 1, Nat.succ_pos m, ?_⟩
  intro i hi k hk
  have hi' := uniformSubdivision_node_mem_Icc (Nat.succ_pos m) hi.le
  have hk' := uniformSubdivision_node_mem_Icc (Nat.succ_pos m) hk.le
  obtain ⟨j, hj⟩ := hmesh (((i : ℝ) / (m + 1 : ℕ)), ((k : ℝ) / (m + 1 : ℕ)))
    ⟨⟨hi'.1, hk'.1⟩, ⟨hi'.2, hk'.2⟩⟩
  refine ⟨j, fun t ht => hj ?_⟩
  rw [mem_ball, Prod.dist_eq, max_lt_iff]
  exact ⟨mem_ball.mp (uniformSubdivision_cell_subset_ball hm' ⟨ht.1.1, ht.2.1⟩),
    mem_ball.mp (uniformSubdivision_cell_subset_ball hm' ⟨ht.1.2, ht.2.2⟩)⟩
