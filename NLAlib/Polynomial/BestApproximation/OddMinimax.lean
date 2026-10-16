import NLAlib.Polynomial.BestApproximation.OddUpdates
import NLAlib.ForMathlib.Analysis.Normed.Approximation
import Mathlib.Topology.ContinuousMap.Compact
/-!+# Actual uniform minimax problems for odd polynomial updates

The admissible functions are the finite-dimensional image of their odd
coefficient map. Finite-dimensional best approximation gives existence,
without any coefficient-conditioning or Vandermonde assumptions.
-/
noncomputable section
open Polynomial Finset Set
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- A coefficient-defined odd update as a continuous map on an interval. -/
def oddUpdateOn (q : ℕ) (c : ℕ → ℝ) (a b : ℝ) : C(Icc a b, ℝ) :=
  ⟨fun x => oddScalarUpdate q c x, (continuous_oddScalarUpdate q c).comp continuous_subtype_val⟩

/-- The actual uniform error when approximating the constant one. -/
def oddUniformError (q : ℕ) (c : ℕ → ℝ) (a b : ℝ) : ℝ :=
  ‖(1 : C(Icc a b, ℝ)) - oddUpdateOn q c a b‖

/-- Genuine minimax optimality among all odd updates of the allowed degree. -/
def IsOddMinimaxOn (q : ℕ) (c : ℕ → ℝ) (a b : ℝ) : Prop :=
  ∀ d : ℕ → ℝ, oddUniformError q c a b ≤ oddUniformError q d a b

/-- The uniform error is nonnegative, including degenerate intervals. -/
theorem oddUniformError_nonneg (q : ℕ) (c : ℕ → ℝ) (a b : ℝ) :
    0 ≤ oddUniformError q c a b := norm_nonneg _

/-- The uniform error bounds every actual point of the interval. -/
theorem abs_one_sub_oddScalarUpdate_le (q : ℕ) (c : ℕ → ℝ) (a b x : ℝ)
    (hx : x ∈ Icc a b) : |1 - oddScalarUpdate q c x| ≤ oddUniformError q c a b := by
  exact ((1 : C(Icc a b, ℝ)) - oddUpdateOn q c a b).norm_coe_le_norm ⟨x, hx⟩

/-- Pointwise bounds imply the corresponding uniform bound. -/
theorem oddUniformError_le_of_forall {q : ℕ} {c : ℕ → ℝ} {a b E : ℝ}
    (hE : 0 ≤ E) (h : ∀ x ∈ Icc a b, |1 - oddScalarUpdate q c x| ≤ E) :
    oddUniformError q c a b ≤ E := by
  apply (ContinuousMap.norm_le _ hE).mpr
  intro x
  exact h x x.property

/-- Every compact interval has an actual odd minimax update, including a
singleton interval. The chosen coefficients are ordinary scalar data. -/
theorem exists_isOddMinimaxOn (q : ℕ) (a b : ℝ) : ∃ c : ℕ → ℝ, IsOddMinimaxOn q c a b := by
  let L : (Fin (q + 1) → ℝ) →ₗ[ℝ] C(Icc a b, ℝ) :=
    { toFun := fun c =>
        ⟨fun x => ∑ j : Fin (q + 1), c j * (x : ℝ) ^ (2 * (j : ℕ) + 1), by fun_prop⟩
      map_add' := by
        intro c d
        ext x
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro t c
        ext x
        simp [Finset.mul_sum, mul_assoc] }
  have : FiniteDimensional ℝ (LinearMap.range L) := inferInstance
  obtain ⟨f, hf, hbest⟩ := exists_norm_sub_eq_infDist_of_finiteDimensional
    (LinearMap.range L) (1 : C(Icc a b, ℝ))
  obtain ⟨c, rfl⟩ := hf
  let c' : ℕ → ℝ := fun j => if hj : j < q + 1 then c ⟨j, hj⟩ else 0
  have hmap (d : ℕ → ℝ) : L (fun j : Fin (q + 1) => d j) = oddUpdateOn q d a b := by
    ext x
    change (∑ j : Fin (q + 1), d j * (x : ℝ) ^ (2 * (j : ℕ) + 1)) =
      ∑ j ∈ range (q + 1), d j * (x : ℝ) ^ (2 * j + 1)
    simpa only using (Fin.sum_univ_eq_sum_range (fun j => d j * (x : ℝ) ^ (2 * j + 1)) (q + 1))
  have hc : (fun j : Fin (q + 1) => c' j) = c := by
    funext j
    dsimp only [c']
    rw [dif_pos j.isLt]
  refine ⟨c', fun d => ?_⟩
  have hp : oddUpdateOn q c' a b = L c := by rw [← hmap, hc]
  rw [oddUniformError, hp, hbest]
  simpa only [oddUniformError, dist_eq_norm, hmap] using
    (Metric.infDist_le_dist_of_mem (x := (1 : C(Icc a b, ℝ)))
      (show L (fun j : Fin (q + 1) => d j) ∈ LinearMap.range L from ⟨_, rfl⟩))

/-- Scaling all coefficients scales the actual update. -/
theorem oddScalarUpdate_smul_coeff (q : ℕ) (c : ℕ → ℝ) (t x : ℝ) :
    oddScalarUpdate q (fun j => t * c j) x = t * oddScalarUpdate q c x := by
  simp [oddScalarUpdate, Finset.mul_sum, mul_assoc]

/-- Rescaling input and output stays inside the same odd polynomial class. -/
theorem oddScalarUpdate_rescale (q : ℕ) (c : ℕ → ℝ) (t b x : ℝ) :
    oddScalarUpdate q (fun j => t * c j / b ^ (2 * j + 1)) x =
      t * oddScalarUpdate q c (x / b) := by
  simp only [oddScalarUpdate, div_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end NLAlib
