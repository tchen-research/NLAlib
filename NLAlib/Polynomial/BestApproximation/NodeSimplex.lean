import NLAlib.Polynomial.BestApproximation.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Contractible

/-!
# The canonical ordered interpolation-node simplex

The interior coordinates form a nonempty open convex set. Its affine node map
keeps the two endpoints fixed. Helpers for `lebesgue-constant-lower-bound`.
-/

noncomputable section

open Set Finset

namespace NLAlib

/-- The left endpoint of the canonical grid is fixed.
Source: the definition; helper for `lebesgue-constant-lower-bound`. -/
@[simp] theorem canonicalIntervalNodes_zero (n : ℕ) (t : Fin n → ℝ) :
    canonicalIntervalNodes n t 0 = -1 := rfl

/-- The right endpoint of the canonical grid is fixed.
Source: the definition; helper for `lebesgue-constant-lower-bound`. -/
@[simp] theorem canonicalIntervalNodes_last (n : ℕ) (t : Fin n → ℝ) :
    canonicalIntervalNodes n t (Fin.last (n + 1)) = 1 := by
  rw [show Fin.last (n + 1) = (Fin.last n).succ by rfl]
  simp only [canonicalIntervalNodes, Fin.cases_succ, Fin.lastCases_last]

/-- Each supplied interior coordinate is the corresponding canonical grid node.
Source: the definition; helper for `lebesgue-constant-lower-bound`. -/
@[simp] theorem canonicalIntervalNodes_interior (n : ℕ) (t : Fin n → ℝ) (j : Fin n) :
    canonicalIntervalNodes n t j.castSucc.succ = t j := by
  simp [canonicalIntervalNodes]

/-- Each canonical node is a continuous function of the interior coordinates.
Source: the affine node parametrization; helper for `lebesgue-constant-lower-bound`. -/
theorem continuous_canonicalIntervalNodes (n : ℕ) (i : Fin (n + 2)) :
    Continuous (fun t : Fin n → ℝ => canonicalIntervalNodes n t i) := by
  refine Fin.cases (by simp only [canonicalIntervalNodes_zero]; fun_prop) (fun j => ?_) i
  refine Fin.lastCases (by simpa using (continuous_const : Continuous (fun _ : Fin n → ℝ => (1 : ℝ))))
    (fun k => ?_) j
  simpa only [canonicalIntervalNodes_interior] using (continuous_apply k : Continuous (fun t : Fin n → ℝ => t k))

/-- The strict-order constraints define an open node simplex.
Source: finite open half spaces; helper for `lebesgue-constant-lower-bound`. -/
theorem isOpen_interiorNodeSimplex (n : ℕ) : IsOpen (interiorNodeSimplex n) := by
  have heq : interiorNodeSimplex n = ⋂ i : Fin (n + 2), ⋂ j : Fin (n + 2),
      ⋂ (_ : i < j), {t | canonicalIntervalNodes n t i < canonicalIntervalNodes n t j} := by
    ext t
    simp only [interiorNodeSimplex, mem_ofPred_eq, mem_iInter, StrictMono]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro _
  exact isOpen_lt (continuous_canonicalIntervalNodes n i) (continuous_canonicalIntervalNodes n j)

/-- Canonical nodes preserve convex combinations of the interior coordinates.
Source: affine parametrization; helper for `lebesgue-constant-lower-bound`. -/
theorem canonicalIntervalNodes_convex_combination (n : ℕ) (t u : Fin n → ℝ)
    (a b : ℝ) (hab : a + b = 1) (i : Fin (n + 2)) :
    canonicalIntervalNodes n (a • t + b • u) i =
      a * canonicalIntervalNodes n t i + b * canonicalIntervalNodes n u i := by
  refine Fin.cases (by simp; linarith) (fun j => ?_) i
  refine Fin.lastCases (by simp; linarith) (fun k => ?_) j
  simp

/-- The strict-order node simplex is convex.
Source: positive convex combinations preserve strict inequalities;
helper for `lebesgue-constant-lower-bound`. -/
theorem convex_interiorNodeSimplex (n : ℕ) : Convex ℝ (interiorNodeSimplex n) := by
  intro t ht u hu a b ha hb hab i j hij
  rw [canonicalIntervalNodes_convex_combination n t u a b hab i,
    canonicalIntervalNodes_convex_combination n t u a b hab j]
  have hti := ht hij
  have hui := hu hij
  rcases ha.eq_or_lt with ha0 | ha0
  · have hbpos : 0 < b := by linarith
    have h := mul_lt_mul_of_pos_left hui hbpos
    simp only [← ha0, zero_mul, zero_add]
    exact h
  · have h1 := mul_lt_mul_of_pos_left hti ha0
    have h2 := mul_le_mul_of_nonneg_left hui.le hb
    linarith

/-- The canonical grid at equally spaced interior coordinates is exactly the equally spaced grid.
Source: affine parametrization; helper for `lebesgue-constant-lower-bound`. -/
theorem canonicalIntervalNodes_equispaced (n : ℕ) (j : Fin (n + 2)) :
    canonicalIntervalNodes n (fun i => -1 + 2 * ((i : ℝ) + 1) / (n + 1)) j =
      -1 + 2 * (j : ℝ) / (n + 1) := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  refine Fin.cases (by simp) (fun i => ?_) j
  refine Fin.lastCases (by simp; field_simp; ring) (fun k => ?_) i
  simp only [canonicalIntervalNodes_interior, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]

/-- The canonical node simplex is nonempty, including the zero-dimensional case.
Source: the equally spaced grid; helper for `lebesgue-constant-lower-bound`. -/
theorem nonempty_interiorNodeSimplex (n : ℕ) : (interiorNodeSimplex n).Nonempty := by
  refine ⟨fun i => -1 + 2 * ((i : ℝ) + 1) / (n + 1), ?_⟩
  intro i j hij
  rw [canonicalIntervalNodes_equispaced, canonicalIntervalNodes_equispaced]
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hijreal : (i : ℝ) < j := by exact_mod_cast hij
  exact add_lt_add_right (div_lt_div_of_pos_right
    (mul_lt_mul_of_pos_left hijreal (by norm_num : (0 : ℝ) < 2)) hn) (-1)

end NLAlib
