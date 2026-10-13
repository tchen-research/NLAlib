import NLAlib.Polynomial.BestApproximation.Basic
import NLAlib.ForMathlib.Analysis.Normed.Approximation
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Best uniform polynomial approximation

Attainment and the basic algebraic properties of the minimax error. The only existence
argument is compactness of a ball in the finite dimensional polynomial subspace.
Source: Cheney (1966), Chapter 2, and Trefethen, ATAP, Chapter 10.
Atlas: `minimax-error-def`.
-/

noncomputable section

open Polynomial
open scoped Topology

namespace NLAlib

/-- The degree-bounded polynomial restriction space is finite dimensional.
Source: the coefficient coordinates of polynomials of bounded degree, ATAP, Chapter 10. -/
instance polynomialApproximationSpace_finiteDimensional (s : Set ℝ) (n : ℕ) :
    FiniteDimensional ℝ (polynomialApproximationSpace s n) := by
  have : FiniteDimensional ℝ (degreeLT ℝ (n + 1)) :=
    FiniteDimensional.of_injective (degreeLTEquiv ℝ (n + 1)).toLinearMap
      (degreeLTEquiv ℝ (n + 1)).injective
  unfold polynomialApproximationSpace
  rw [← degreeLT_succ_eq_degreeLE]
  infer_instance

/-- Increasing the degree enlarges the polynomial approximation space.
Source: ATAP, Chapter 10. -/
theorem polynomialApproximationSpace_mono {s : Set ℝ} {m n : ℕ} (hmn : m ≤ n) :
    polynomialApproximationSpace s m ≤ polynomialApproximationSpace s n := by
  exact Submodule.map_mono (degreeLE_mono (by exact_mod_cast hmn))

/-- The best uniform error is nonnegative. Source: ATAP, Chapter 10.
atlas: minimax-error-def (partial) -/
theorem minimaxError_nonneg {s : Set ℝ} [CompactSpace s] (n : ℕ) (f : C(s, ℝ)) :
    0 ≤ minimaxError n f := Metric.infDist_nonneg

/-- Any degree-bounded competitor gives an upper bound on best uniform error.
Source: ATAP, Chapter 10. -/
theorem minimaxError_le_norm_sub {s : Set ℝ} [CompactSpace s] {n : ℕ}
    (f : C(s, ℝ)) {p : C(s, ℝ)} (hp : p ∈ polynomialApproximationSpace s n) :
    minimaxError n f ≤ ‖f - p‖ := by
  simpa [minimaxError, dist_eq_norm] using (Metric.infDist_le_dist_of_mem (x := f) hp)

/-- The zero polynomial bounds best approximation by the norm of the function.
Source: ATAP, Chapter 10.
atlas: minimax-error-def (partial) -/
theorem minimaxError_le_norm {s : Set ℝ} [CompactSpace s] (n : ℕ) (f : C(s, ℝ)) :
    minimaxError n f ≤ ‖f‖ := by
  simpa using minimaxError_le_norm_sub f (polynomialApproximationSpace s n).zero_mem

/-- Best approximation error decreases with the allowed degree. Source: ATAP, Chapter 10.
atlas: minimax-error-def (partial) -/
theorem minimaxError_antitone {s : Set ℝ} [CompactSpace s] (f : C(s, ℝ)) :
    Antitone (fun n => minimaxError n f) := by
  intro m n hmn
  exact Metric.infDist_le_infDist_of_subset (polynomialApproximationSpace_mono hmn)
    ⟨0, (polynomialApproximationSpace s m).zero_mem⟩

/-- A polynomial of degree at most `n` attains the best uniform approximation error.
Source: Cheney (1966), Chapter 2; ATAP, Chapter 10. The compact set may be any compact
subset of the real line, including empty sets.
atlas: minimax-error-def (partial) -/
theorem exists_degree_le_norm_sub_eq_minimaxError {s : Set ℝ} [CompactSpace s]
    (n : ℕ) (f : C(s, ℝ)) :
    ∃ p : ℝ[X], p.degree ≤ n ∧ ‖f - p.toContinuousMapOn s‖ = minimaxError n f := by
  obtain ⟨g, hg, hbest⟩ := exists_norm_sub_eq_infDist_of_finiteDimensional
    (polynomialApproximationSpace s n) f
  obtain ⟨p, hp, rfl⟩ := mem_polynomialApproximationSpace_iff.mp hg
  exact ⟨p, hp, hbest⟩

/-- The minimax error is the least uniform bound attainable by a degree-bounded polynomial.
Source: Cheney (1966), Chapter 2; Trefethen, ATAP, Chapter 10.
atlas: minimax-error-def (partial) -/
theorem isLeast_minimaxError {s : Set ℝ} [CompactSpace s] (n : ℕ) (f : C(s, ℝ)) :
    IsLeast {E : ℝ | ∃ p : ℝ[X], p.degree ≤ n ∧ ‖f - p.toContinuousMapOn s‖ ≤ E}
      (minimaxError n f) := by
  obtain ⟨p, hp, hbest⟩ := exists_degree_le_norm_sub_eq_minimaxError n f
  refine ⟨⟨p, hp, hbest.le⟩, ?_⟩
  rintro E ⟨q, hq, hE⟩
  exact (minimaxError_le_norm_sub f
    (mem_polynomialApproximationSpace_iff.mpr ⟨q, hq, rfl⟩)).trans hE

/-- Distance to the polynomial space equals the infimum of its attainable uniform bounds.
Source: Trefethen, ATAP, Chapter 10. -/
theorem minimaxError_eq_sInf {s : Set ℝ} [CompactSpace s] (n : ℕ) (f : C(s, ℝ)) :
    minimaxError n f =
      sInf {E : ℝ | ∃ p : ℝ[X], p.degree ≤ n ∧ ‖f - p.toContinuousMapOn s‖ ≤ E} :=
  (isLeast_minimaxError n f).csInf_eq.symm

/-- The minimax error is the least pointwise uniform error bound attained by a polynomial.
Source: Trefethen, ATAP, Chapter 10, the existential uniform-bound convention.
atlas: minimax-error-def (partial) -/
theorem isLeast_minimaxError_pointwise {a b : ℝ} (hab : a ≤ b) (n : ℕ)
    (f : C(Set.Icc a b, ℝ)) :
    IsLeast {E : ℝ | ∃ p : ℝ[X], p.degree ≤ n ∧
      ∀ x : Set.Icc a b, |f x - p.eval (x : ℝ)| ≤ E} (minimaxError n f) := by
  have hset : {E : ℝ | ∃ p : ℝ[X], p.degree ≤ n ∧
      ∀ x : Set.Icc a b, |f x - p.eval (x : ℝ)| ≤ E} =
      {E : ℝ | ∃ p : ℝ[X], p.degree ≤ n ∧
        ‖f - p.toContinuousMapOn (Set.Icc a b)‖ ≤ E} := by
    ext E
    constructor
    · rintro ⟨p, hp, hpoint⟩
      have hEnonneg : 0 ≤ E := (abs_nonneg _).trans (hpoint ⟨a, le_rfl, hab⟩)
      exact ⟨p, hp, (ContinuousMap.norm_le _ hEnonneg).mpr hpoint⟩
    · rintro ⟨p, hp, hnorm⟩
      exact ⟨p, hp, fun x => ((f - p.toContinuousMapOn (Set.Icc a b)).norm_coe_le_norm x).trans hnorm⟩
  rw [hset]
  exact isLeast_minimaxError n f

/-- Adding a degree-bounded polynomial does not change the best approximation error.
Source: Cheney (1966), Chapter 2; ATAP, Chapter 10.
atlas: minimax-error-def (partial) -/
theorem minimaxError_add_of_mem {s : Set ℝ} [CompactSpace s] {n : ℕ}
    (f : C(s, ℝ)) {p : C(s, ℝ)} (hp : p ∈ polynomialApproximationSpace s n) :
    minimaxError n (f + p) = minimaxError n f := by
  let S := polynomialApproximationSpace s n
  apply le_antisymm
  · obtain ⟨q, hq, hbest⟩ := exists_norm_sub_eq_infDist_of_finiteDimensional S f
    have := minimaxError_le_norm_sub (f + p) (S.add_mem hq hp)
    simpa [S, minimaxError, hbest] using this
  · obtain ⟨q, hq, hbest⟩ := exists_norm_sub_eq_infDist_of_finiteDimensional S (f + p)
    have := minimaxError_le_norm_sub f (S.sub_mem hq hp)
    have heq : f - (q - p) = f + p - q := by abel
    simpa [heq, S, minimaxError, hbest] using this

/-- Uniform polynomial approximation error is subadditive.
Source: Cheney (1966), Chapter 2; ATAP, Chapter 10.
atlas: minimax-error-def (partial) -/
theorem minimaxError_add_le {s : Set ℝ} [CompactSpace s] (n : ℕ) (f g : C(s, ℝ)) :
    minimaxError n (f + g) ≤ minimaxError n f + minimaxError n g := by
  let S := polynomialApproximationSpace s n
  obtain ⟨p, hp, hfp⟩ := exists_norm_sub_eq_infDist_of_finiteDimensional S f
  obtain ⟨q, hq, hgq⟩ := exists_norm_sub_eq_infDist_of_finiteDimensional S g
  have heq : f + g - (p + q) = (f - p) + (g - q) := by abel
  calc
    minimaxError n (f + g) ≤ ‖f + g - (p + q)‖ :=
      minimaxError_le_norm_sub _ (S.add_mem hp hq)
    _ ≤ ‖f - p‖ + ‖g - q‖ := by rw [heq]; exact norm_add_le _ _
    _ = minimaxError n f + minimaxError n g := by rw [hfp, hgq]; rfl

/-- Scaling a function scales its minimax error by the absolute value of the scalar.
Source: Cheney (1966), Chapter 2; ATAP, Chapter 10.
atlas: minimax-error-def (partial) -/
theorem minimaxError_smul {s : Set ℝ} [CompactSpace s] (n : ℕ) (c : ℝ) (f : C(s, ℝ)) :
    minimaxError n (c • f) = |c| * minimaxError n f := by
  let S := polynomialApproximationSpace s n
  have hle : ∀ (c : ℝ) (f : C(s, ℝ)),
      minimaxError n (c • f) ≤ |c| * minimaxError n f := by
    intro c f
    obtain ⟨p, hp, hfp⟩ := exists_norm_sub_eq_infDist_of_finiteDimensional S f
    calc
      minimaxError n (c • f) ≤ ‖c • f - c • p‖ :=
        minimaxError_le_norm_sub _ (S.smul_mem c hp)
      _ = |c| * minimaxError n f := by rw [← smul_sub, norm_smul, Real.norm_eq_abs, hfp]; rfl
  by_cases hc : c = 0
  · subst c
    apply le_antisymm
    · simpa using hle 0 f
    · simp [minimaxError_nonneg]
  · apply le_antisymm (hle c f)
    have hi := hle c⁻¹ (c • f)
    rw [inv_smul_smul₀ hc] at hi
    have ha : 0 < |c| := abs_pos.mpr hc
    have hi' := mul_le_mul_of_nonneg_left hi ha.le
    simpa [abs_inv, hc, ha.ne', mul_assoc] using hi'

/-- Best uniform polynomial errors tend to zero on a real interval.
Source: Weierstrass approximation, as used in ATAP, Chapter 10.
atlas: minimax-error-def (partial) -/
theorem tendsto_minimaxError_atTop {a b : ℝ} (f : C(Set.Icc a b, ℝ)) :
    Filter.Tendsto (fun n => minimaxError n f) Filter.atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap a b f ε hε
  refine ⟨p.natDegree, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (minimaxError_nonneg n f)]
  have hpdeg : p.degree ≤ (n : WithBot ℕ) :=
    p.degree_le_natDegree.trans (by exact_mod_cast hn)
  exact lt_of_le_of_lt (minimaxError_le_norm_sub f
    (mem_polynomialApproximationSpace_iff.mpr ⟨p, hpdeg, rfl⟩))
      (by simpa [norm_sub_rev] using hp)

/-- A linear projection with bound `B` is within `1+B` of the best uniform polynomial error.
Source: Trefethen, ATAP, Theorem 15.1. -/
theorem norm_sub_projection_le_minimaxError {s : Set ℝ} [CompactSpace s]
    (n : ℕ) (L : C(s, ℝ) →ₗ[ℝ] C(s, ℝ)) (B : ℝ)
    (hL : ∀ p ∈ polynomialApproximationSpace s n, L p = p)
    (hB : ∀ g, ‖L g‖ ≤ B * ‖g‖) (f : C(s, ℝ)) :
    ‖f - L f‖ ≤ (1 + B) * minimaxError n f := by
  obtain ⟨p, hp, hfp⟩ := exists_degree_le_norm_sub_eq_minimaxError n f
  have hLp := hL _ (mem_polynomialApproximationSpace_iff.mpr ⟨p, hp, rfl⟩)
  have heq : f - L f = (f - p.toContinuousMapOn s) - L (f - p.toContinuousMapOn s) := by
    rw [map_sub, hLp]; abel
  calc
    ‖f - L f‖ ≤ ‖f - p.toContinuousMapOn s‖ + ‖L (f - p.toContinuousMapOn s)‖ :=
      by rw [heq]; exact norm_sub_le _ _
    _ ≤ (1 + B) * ‖f - p.toContinuousMapOn s‖ := by
      have := hB (f - p.toContinuousMapOn s); nlinarith
    _ = (1 + B) * minimaxError n f := by rw [hfp]

end NLAlib
