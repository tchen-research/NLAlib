import NLAlib.Matrix.MajorizationSupport
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Hardy–Littlewood–Pólya characterization

Majorization is membership in the convex hull of the permutation orbit, or
equivalently a doubly stochastic image. The hard implication uses the compact
convex-hull separation theorem and the proved finite support bound; no HLP
theorem is assumed. Source: Marshall–Olkin–Arnold (2011), Theorem 2.B.2.
Atlas: `majorization-def`.
-/

noncomputable section
open scoped BigOperators Matrix

namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A real linear functional on a finite coordinate space is its coordinate
pairing with the values on standard basis vectors. HLP support helper. -/
theorem apply_eq_sum_mul_single (f : (ι → ℝ) →ₗ[ℝ] ℝ) (x : ι → ℝ) :
    f x = ∑ i, f (Pi.single i 1) * x i := by
  conv_lhs => rw [← Finset.univ_sum_single x, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h : Pi.single i (x i) = x i • Pi.single i (1 : ℝ) := by
    ext j
    by_cases hij : j = i <;> simp [hij]
  rw [h, map_smul, smul_eq_mul, mul_comm]

/-- A majorized vector belongs to the convex hull of the comparator's actual
permutations. The proof separates the compact convex hull and contradicts the
signed support bound. Marshall–Olkin–Arnold (2011), Theorem 2.B.2.
atlas: majorization-def (partial) -/
theorem Majorized.mem_convexHull_permutations {x y : ι → ℝ} (hxy : Majorized x y) :
    x ∈ convexHull ℝ (Set.range fun σ : Equiv.Perm ι => y ∘ σ) := by
  by_contra hx
  have hclosed := (Set.finite_range (fun σ : Equiv.Perm ι => y ∘ σ)).isClosed_convexHull ℝ
  obtain ⟨f, u, hu, hux⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ _) hclosed hx
  obtain ⟨σ, hσ⟩ := hxy.exists_perm_sum_mul_le (fun i => f (Pi.single i 1))
  have hmem : y ∘ σ ∈ convexHull ℝ (Set.range fun σ : Equiv.Perm ι => y ∘ σ) :=
    subset_convexHull ℝ _ (Set.mem_range_self σ)
  have hle : f x ≤ f (y ∘ σ) := by
    change f.toLinearMap x ≤ f.toLinearMap (y ∘ σ)
    rw [apply_eq_sum_mul_single f.toLinearMap x, apply_eq_sum_mul_single f.toLinearMap (y ∘ σ)]
    exact hσ
  exact (hle.trans_lt (hu _ hmem)).not_gt hux

/-- Convex-hull membership in the permutation orbit is equivalent to being an
actual doubly stochastic image. This is Birkhoff transported by the linear map
`D ↦ D y`. Marshall–Olkin–Arnold (2011), Theorem 2.B.2. -/
theorem mem_convexHull_permutations_iff_exists_doublyStochastic (x y : ι → ℝ) :
    x ∈ convexHull ℝ (Set.range fun σ : Equiv.Perm ι => y ∘ σ) ↔
      ∃ D : Matrix ι ι ℝ, D ∈ doublyStochastic ℝ ι ∧ D *ᵥ y = x := by
  let F : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ) := (Matrix.mulVecBilin ℝ ℝ).flip y
  have him : F '' {σ.permMatrix ℝ | σ : Equiv.Perm ι} =
      Set.range (fun σ : Equiv.Perm ι => y ∘ σ) := by
    ext z
    constructor
    · rintro ⟨D, ⟨σ, rfl⟩, rfl⟩
      exact ⟨σ, by simp [F, LinearMap.flip_apply, Matrix.permMatrix_mulVec]⟩
    · rintro ⟨σ, rfl⟩
      exact ⟨σ.permMatrix ℝ, ⟨σ, rfl⟩,
        by simp [F, LinearMap.flip_apply, Matrix.permMatrix_mulVec]⟩
  rw [← him, ← F.image_convexHull, ← doublyStochastic_eq_convexHull_permMatrix]
  rfl

/-- Full HLP equivalence between ordinary majorization and the existence of an
actual doubly stochastic matrix, including empty index types and signed vectors.
Marshall–Olkin–Arnold (2011), Theorem 2.B.2.
atlas: majorization-def (partial) -/
theorem majorized_iff_exists_doublyStochastic (x y : ι → ℝ) :
    Majorized x y ↔ ∃ D : Matrix ι ι ℝ, D ∈ doublyStochastic ℝ ι ∧ D *ᵥ y = x := by
  constructor
  · intro hxy
    exact (mem_convexHull_permutations_iff_exists_doublyStochastic x y).mp
      hxy.mem_convexHull_permutations
  · rintro ⟨D, hD, rfl⟩
    exact majorized_mulVec_of_doublyStochastic y hD

/-- Full HLP equivalence with convex-hull membership in the permutation orbit.
Marshall–Olkin–Arnold (2011), Theorem 2.B.2.
atlas: majorization-def (partial) -/
theorem majorized_iff_mem_convexHull_permutations (x y : ι → ℝ) :
    Majorized x y ↔ x ∈ convexHull ℝ (Set.range fun σ : Equiv.Perm ι => y ∘ σ) := by
  rw [mem_convexHull_permutations_iff_exists_doublyStochastic,
    majorized_iff_exists_doublyStochastic]

/-- Majorization implies the sum inequality for every real convex function.
Marshall–Olkin–Arnold (2011), Propositions 4.B.1–4.B.2.
atlas: majorization-def (partial) -/
theorem Majorized.sum_convex_le {x y : ι → ℝ} (hxy : Majorized x y)
    {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) : (∑ i, φ (x i)) ≤ ∑ i, φ (y i) := by
  obtain ⟨D, hD, hDx⟩ := (majorized_iff_exists_doublyStochastic x y).mp hxy
  rw [← hDx]
  exact sum_convex_mulVec_le_of_doublyStochastic y hD hφ

end NLAlib
