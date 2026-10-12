import NLAlib.Matrix.GeneralizedEigenDecay
import NLAlib.ForMathlib.Analysis.PowerBoundedEigen

/-!
# Bounded power orbits from primary eigenspaces

The vectors with bounded power orbits form a subspace. All primary spaces
lie in it when eigenvalues are subunit or semisimple peripheral eigenvalues.
A finite basis then upgrades orbit bounds to one operator-norm bound.
Source: Horn–Johnson (2013), §5.6.
-/

noncomputable section
open Module Filter
open scoped Topology

namespace NLAlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- Spectral containment in the closed unit disk and semisimplicity on its
boundary make every power orbit bounded. Source: Horn–Johnson (2013), §5.6;
generalized eigenspaces span the finite-dimensional complex space. -/
theorem exists_bound_pow_orbit_of_eigenvalues_le_one_of_peripheral_semisimple
    (f : Module.End ℂ E)
    (hvalues : ∀ μ : ℂ, f.HasEigenvalue μ → ‖μ‖ ≤ 1)
    (hsemi : ∀ μ : ℂ, ‖μ‖ = 1 → f.maxGenEigenspace μ = f.eigenspace μ) :
    ∀ x : E, ∃ C : ℝ, ∀ k : ℕ, ‖(f ^ k) x‖ ≤ C := by
  let P : Submodule ℂ E :=
    { carrier := {x | ∃ C : ℝ, ∀ k : ℕ, ‖(f ^ k) x‖ ≤ C}
      zero_mem' := ⟨0, by intro k; simp⟩
      add_mem' := by
        rintro x y ⟨C, hC⟩ ⟨D, hD⟩
        exact ⟨C + D, fun k => by simpa only [map_add] using
          (norm_add_le ((f ^ k) x) ((f ^ k) y)).trans (add_le_add (hC k) (hD k))⟩
      smul_mem' := by
        rintro a x ⟨C, hC⟩
        exact ⟨‖a‖ * C, fun k => by
          simpa only [map_smul, norm_smul] using mul_le_mul_of_nonneg_left (hC k) (norm_nonneg a)⟩ }
  have hprimary (μ : ℂ) : f.maxGenEigenspace μ ≤ P := by
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      exact P.zero_mem
    have heigen : f.HasEigenvalue μ := by
      obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace f μ x).mp hx
      have hg : f.HasGenEigenvector μ k x := ⟨Module.End.mem_genEigenspace_nat.mpr hk, hx0⟩
      exact Module.End.hasEigenvalue_of_hasGenEigenvalue hg.hasUnifEigenvalue
    rcases (hvalues μ heigen).lt_or_eq with hlt | heq
    · obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _
        (tendsto_pow_apply_zero_of_mem_maxGenEigenspace f hlt hx)).exists_norm_le
      exact ⟨C, fun k => hC _ ⟨k, rfl⟩⟩
    · have hx' : x ∈ f.eigenspace μ := by rw [← hsemi μ heq]; exact hx
      have hxe : f.HasEigenvector μ x := ⟨hx', hx0⟩
      exact ⟨‖x‖, fun k => by simp only [hxe.pow_apply, norm_smul, norm_pow, heq, one_pow, one_mul, le_refl]⟩
  have htop : (⊤ : Submodule ℂ E) ≤ P := by
    rw [← Module.End.iSup_maxGenEigenspace_eq_top f]
    exact iSup_le hprimary
  exact fun x => htop (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ E))

/-- In finite dimension, bounded power orbits give a single bound on the
norms of all powers. Source: Horn–Johnson (2013), §5.6; the proof takes a
finite maximum over a basis and uses its explicit coordinate norm bound. -/
theorem exists_bound_norm_pow_of_bounded_pow_orbits (f : Module.End ℂ E)
    (hb : ∀ x : E, ∃ C : ℝ, ∀ k : ℕ, ‖(f ^ k) x‖ ≤ C) :
    ∃ C : ℝ, ∀ k : ℕ, ‖(LinearMap.toContinuousLinearMap (f ^ k))‖ ≤ C := by
  classical
  let b := Module.finBasis ℂ E
  choose C hC using fun i => hb (b i)
  let M : ℝ := ∑ i, max (C i) 0
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => le_max_right _ _
  refine ⟨Fintype.card (Fin (finrank ℂ E)) • ‖b.equivFunL.toContinuousLinearMap‖ * M, fun k => ?_⟩
  apply b.opNorm_le hM
  intro i
  exact (hC i k).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun j _ => le_max_right (C j) 0) (Finset.mem_univ i)))

/-- The finite-dimensional complex operator power-boundedness criterion:
all eigenvalues lie in the closed unit disk and every boundary generalized
eigenspace is already its ordinary eigenspace. Source: Horn–Johnson (2013),
§5.6; includes the zero-dimensional space. -/
theorem exists_bound_norm_pow_iff_eigenvalues_le_one_and_peripheral_semisimple
    (f : Module.End ℂ E) :
    (∃ C : ℝ, ∀ k : ℕ, ‖(LinearMap.toContinuousLinearMap (f ^ k))‖ ≤ C) ↔
      (∀ μ : ℂ, f.HasEigenvalue μ → ‖μ‖ ≤ 1) ∧
      (∀ μ : ℂ, ‖μ‖ = 1 → f.maxGenEigenspace μ = f.eigenspace μ) := by
  constructor
  · rintro ⟨C, hC⟩
    have hb (x : E) : ∃ D : ℝ, ∀ k : ℕ, ‖(f ^ k) x‖ ≤ D := by
      refine ⟨C * ‖x‖, fun k => ?_⟩
      exact ((LinearMap.toContinuousLinearMap (f ^ k)).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (hC k) (norm_nonneg x))
    refine ⟨?_, fun μ hμ => maxGenEigenspace_eq_eigenspace_of_bounded_pow_orbits f hb hμ⟩
    intro μ hμ
    obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
    exact norm_eigenvalue_le_one_of_bounded_pow_orbit f hx (hb x)
  · rintro ⟨hvalues, hsemi⟩
    exact exists_bound_norm_pow_of_bounded_pow_orbits f
      (exists_bound_pow_orbit_of_eigenvalues_le_one_of_peripheral_semisimple f hvalues hsemi)

end NLAlib
