import NLAlib.Polynomial.SawtoothDerivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Max

/-!
# Exact critical points of the sawtooth error

Rolle supplies one critical point in every consecutive pair of positive half-period grid
nodes. Their distinct cosines exhaust the roots of the nonzero degree-`n` derivative
polynomial. This proves the interpolation zeros are simple without any assumed sign rule.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Finset Real Set

namespace NLAlib

/-- The uniform half-period grid angle `jπ/(n+1)` for the sharp Jackson kernel.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
def sawtoothGridAngle (n j : ℕ) : ℝ := (j : ℝ) * Real.pi / (n + 1)

/-- The sawtooth error on a single unwrapped period.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
def sawtoothError (n : ℕ) (t : ℝ) : ℝ := Real.pi - t - sawtoothApprox n t

/-- Half-period grid angles are strictly increasing in the natural index.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem strictMono_sawtoothGridAngle (n : ℕ) : StrictMono (sawtoothGridAngle n) := by
  intro i j hij
  unfold sawtoothGridAngle
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right (by exact_mod_cast hij) Real.pi_pos)
    (by positivity)

/-- The full positive half-period grid lies in `[0,π]`.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem sawtoothGridAngle_mem_Icc {n j : ℕ} (hj : j ≤ n + 1) :
    sawtoothGridAngle n j ∈ Icc (0 : ℝ) Real.pi := by
  constructor
  · unfold sawtoothGridAngle; positivity
  · have h := (strictMono_sawtoothGridAngle n).monotone hj
    have hlast : sawtoothGridAngle n (n + 1) = Real.pi := by
      unfold sawtoothGridAngle
      push_cast
      field_simp
    rwa [hlast] at h

/-- Every positive half-period grid point is an actual sawtooth interpolation zero.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem sawtoothError_grid_eq_zero {n j : ℕ} (hj0 : 0 < j) (hj : j ≤ n + 1) :
    sawtoothError n (sawtoothGridAngle n j) = 0 := by
  rcases eq_or_lt_of_le hj with rfl | hj
  · have hlast : sawtoothGridAngle n (n + 1) = Real.pi := by
      unfold sawtoothGridAngle
      push_cast
      field_simp
    simp [sawtoothError, hlast]
  · have hidx : j - 1 + 1 = j := by omega
    have h := sawtoothApprox_grid_eq (n := n) (j := j - 1) (by omega)
    rw [hidx] at h
    unfold sawtoothError sawtoothGridAngle
    rw [h]
    ring

/-- The unwrapped sawtooth error is continuously differentiable in particular continuous.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem continuous_sawtoothError (n : ℕ) : Continuous (sawtoothError n) :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_sawtoothError n t).continuousAt)

/-- Rolle gives a genuine critical point between every pair of consecutive positive grid
zeros, with no assumed critical-point or sign certificate.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem exists_sawtoothCriticalPoint (n : ℕ) (j : Fin n) :
    ∃ t ∈ Ioo (sawtoothGridAngle n (j.val + 1)) (sawtoothGridAngle n (j.val + 2)),
      (sawtoothErrorDerivativePolynomial n).eval (cos t) = 0 := by
  have hlt := strictMono_sawtoothGridAngle n (show j.val + 1 < j.val + 2 by omega)
  have hzero1 := sawtoothError_grid_eq_zero (n := n) (j := j.val + 1) (by omega) (by omega)
  have hzero2 := sawtoothError_grid_eq_zero (n := n) (j := j.val + 2) (by omega) (by omega)
  obtain ⟨t, ht, hder⟩ := exists_hasDerivAt_eq_zero hlt (continuous_sawtoothError n).continuousOn
    (hzero1.trans hzero2.symm) (fun t _ => hasDerivAt_sawtoothError n t)
  exact ⟨t, ht, neg_eq_zero.mp hder⟩

/-- The critical point chosen from Rolle's actual existence theorem.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
def sawtoothCriticalPoint (n : ℕ) (j : Fin n) : ℝ := Classical.choose (exists_sawtoothCriticalPoint n j)

/-- The chosen critical point lies strictly between its specified grid nodes and is a root
of the actual derivative polynomial.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem sawtoothCriticalPoint_spec (n : ℕ) (j : Fin n) :
    sawtoothCriticalPoint n j ∈ Ioo (sawtoothGridAngle n (j.val + 1)) (sawtoothGridAngle n (j.val + 2)) ∧
      (sawtoothErrorDerivativePolynomial n).eval (cos (sawtoothCriticalPoint n j)) = 0 :=
  Classical.choose_spec (exists_sawtoothCriticalPoint n j)

/-- All selected critical points are in the open positive half-period.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem sawtoothCriticalPoint_mem_Ioo (n : ℕ) (j : Fin n) :
    sawtoothCriticalPoint n j ∈ Ioo (0 : ℝ) Real.pi := by
  have h := (sawtoothCriticalPoint_spec n j).1
  have h1 := sawtoothGridAngle_mem_Icc (n := n) (j := j.val + 1) (by omega)
  have h2 := sawtoothGridAngle_mem_Icc (n := n) (j := j.val + 2) (by omega)
  exact ⟨h1.1.trans_lt h.1, h.2.trans_le h2.2⟩

/-- Ordered critical points are strictly increasing in their finite index.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem strictMono_sawtoothCriticalPoint (n : ℕ) : StrictMono (sawtoothCriticalPoint n) := by
  intro i j hij
  have hi := (sawtoothCriticalPoint_spec n i).1.2
  have hj := (sawtoothCriticalPoint_spec n j).1.1
  have hm := (strictMono_sawtoothGridAngle n).monotone (show i.val + 2 ≤ j.val + 1 by
    have hh : i.val < j.val := hij
    omega)
  exact hi.trans_le hm |>.trans hj

/-- The cosines of the ordered critical points are distinct.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem injective_cos_sawtoothCriticalPoint (n : ℕ) :
    Function.Injective (fun j : Fin n => cos (sawtoothCriticalPoint n j)) := by
  have ha : StrictAnti (fun j : Fin n => cos (sawtoothCriticalPoint n j)) := by
    intro i j hij
    have hi := sawtoothCriticalPoint_mem_Ioo n i
    have hj := sawtoothCriticalPoint_mem_Ioo n j
    exact strictAntiOn_cos ⟨hi.1.le, hi.2.le⟩ ⟨hj.1.le, hj.2.le⟩
      (strictMono_sawtoothCriticalPoint n hij)
  exact ha.injective

/-- The finite set of cosine roots furnished by Rolle between the interpolation nodes.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
def sawtoothCriticalCosines (n : ℕ) : Finset ℝ :=
  univ.image (fun j : Fin n => cos (sawtoothCriticalPoint n j))

/-- The selected cosine roots are all distinct, hence their cardinality is exactly `n`.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem card_sawtoothCriticalCosines (n : ℕ) : (sawtoothCriticalCosines n).card = n := by
  rw [sawtoothCriticalCosines, card_image_of_injective _ (injective_cos_sawtoothCriticalPoint n)]
  simp

/-- All selected cosine values are roots of the actual nonzero error-derivative polynomial.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem sawtoothCriticalCosines_subset_roots (n : ℕ) :
    sawtoothCriticalCosines n ⊆ (sawtoothErrorDerivativePolynomial n).roots.toFinset := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (sawtoothErrorDerivativePolynomial_ne_zero n)]
  exact (sawtoothCriticalPoint_spec n j).2

/-- The polynomial degree bound makes Rolle's `n` distinct roots exhaustive.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem sawtoothCriticalCosines_eq_roots (n : ℕ) :
    sawtoothCriticalCosines n = (sawtoothErrorDerivativePolynomial n).roots.toFinset := by
  apply Finset.eq_of_subset_of_card_le (sawtoothCriticalCosines_subset_roots n)
  have h1 := Multiset.toFinset_card_le (sawtoothErrorDerivativePolynomial n).roots
  have h2 := Polynomial.card_roots' (sawtoothErrorDerivativePolynomial n)
  have h3 := natDegree_le_of_degree_le (degree_sawtoothErrorDerivativePolynomial_le n)
  rw [card_sawtoothCriticalCosines]
  exact h1.trans (h2.trans h3)

/-- Every zero of the error derivative in `[0,π]` is one of the actual chosen Rolle points.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem exists_sawtoothCriticalPoint_eq_of_eval_eq_zero {n : ℕ} {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) Real.pi) (hroot : (sawtoothErrorDerivativePolynomial n).eval (cos t) = 0) :
    ∃ j : Fin n, t = sawtoothCriticalPoint n j := by
  have hr : cos t ∈ (sawtoothErrorDerivativePolynomial n).roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (sawtoothErrorDerivativePolynomial_ne_zero n)]
    exact hroot
  rw [← sawtoothCriticalCosines_eq_roots, sawtoothCriticalCosines] at hr
  obtain ⟨j, hj, hcos⟩ := mem_image.mp hr
  have hj' := sawtoothCriticalPoint_mem_Ioo n j
  exact ⟨j, strictAntiOn_cos.injOn ht ⟨hj'.1.le, hj'.2.le⟩ hcos.symm⟩

/-- The error derivative does not vanish at any interpolation grid point, including the
half-period endpoint. Thus every prescribed error zero is simple.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem eval_sawtoothErrorDerivativePolynomial_grid_ne_zero {n j : ℕ} (hj : j ≤ n + 1) :
    (sawtoothErrorDerivativePolynomial n).eval (cos (sawtoothGridAngle n j)) ≠ 0 := by
  intro hzero
  obtain ⟨i, hi⟩ := exists_sawtoothCriticalPoint_eq_of_eval_eq_zero (sawtoothGridAngle_mem_Icc hj) hzero
  have hpoint := (sawtoothCriticalPoint_spec n i).1
  rw [← hi] at hpoint
  have h1 := (strictMono_sawtoothGridAngle n).lt_iff_lt.mp hpoint.1
  have h2 := (strictMono_sawtoothGridAngle n).lt_iff_lt.mp hpoint.2
  omega

/-- The finite set of actual angular critical points.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
def sawtoothCriticalAngles (n : ℕ) : Finset ℝ := univ.image (sawtoothCriticalPoint n)

/-- The actual angular critical points have cardinality exactly `n`.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem card_sawtoothCriticalAngles (n : ℕ) : (sawtoothCriticalAngles n).card = n := by
  rw [sawtoothCriticalAngles, card_image_of_injective _ (strictMono_sawtoothCriticalPoint n).injective]
  simp

/-- Every finite set of half-period sawtooth-error zeros has at most `n+1` points.
Rolle's theorem interleaves those zeros with the already exhausted `n` critical points.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem card_le_succ_of_sawtoothError_eq_zero {n : ℕ} {s : Finset ℝ}
    (hs : ∀ t ∈ s, t ∈ Icc (0 : ℝ) Real.pi) (hz : ∀ t ∈ s, sawtoothError n t = 0) :
    s.card ≤ n + 1 := by
  have hcard : s.card ≤ (sawtoothCriticalAngles n \ s).card + 1 := by
    apply Finset.card_le_sdiff_of_interleaved
    intro x hx y hy hxy _
    obtain ⟨t, ht, hd⟩ := exists_hasDerivAt_eq_zero hxy (continuous_sawtoothError n).continuousOn
      ((hz x hx).trans (hz y hy).symm) (fun t _ => hasDerivAt_sawtoothError n t)
    have ht' : t ∈ Icc (0 : ℝ) Real.pi := ⟨(hs x hx).1.trans ht.1.le, ht.2.le.trans (hs y hy).2⟩
    obtain ⟨j, hj⟩ := exists_sawtoothCriticalPoint_eq_of_eval_eq_zero ht' (neg_eq_zero.mp hd)
    refine ⟨t, ?_, ht⟩
    exact mem_image.mpr ⟨j, mem_univ _, hj.symm⟩
  have hdiff := Finset.card_le_card (Finset.sdiff_subset : sawtoothCriticalAngles n \ s ⊆ sawtoothCriticalAngles n)
  rw [card_sawtoothCriticalAngles] at hdiff
  omega

/-- The finite positive half-period interpolation-zero grid.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
def sawtoothZeroGrid (n : ℕ) : Finset ℝ := (range (n + 1)).image (fun j => sawtoothGridAngle n (j + 1))

/-- The positive half-period grid has exactly `n+1` distinct error zeros.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem card_sawtoothZeroGrid (n : ℕ) : (sawtoothZeroGrid n).card = n + 1 := by
  have hinj : Function.Injective (fun j => sawtoothGridAngle n (j + 1)) := by
    intro i j hij
    have h := (strictMono_sawtoothGridAngle n).injective hij
    omega
  rw [sawtoothZeroGrid, card_image_of_injective _ hinj, card_range]

/-- There are no extra sawtooth-error zeros in the closed positive half-period.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem mem_sawtoothZeroGrid_of_sawtoothError_eq_zero {n : ℕ} {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) Real.pi) (hz : sawtoothError n t = 0) : t ∈ sawtoothZeroGrid n := by
  by_contra hnot
  have hcard := card_le_succ_of_sawtoothError_eq_zero (s := insert t (sawtoothZeroGrid n))
    (fun z hz' => by
      rcases mem_insert.mp hz' with rfl | hgrid
      · exact ht
      · obtain ⟨j, hj, rfl⟩ := mem_image.mp hgrid
        exact sawtoothGridAngle_mem_Icc (by have := mem_range.mp hj; omega))
    (fun z hz' => by
      rcases mem_insert.mp hz' with rfl | hgrid
      · exact hz
      · obtain ⟨j, hj, rfl⟩ := mem_image.mp hgrid
        exact sawtoothError_grid_eq_zero (by omega) (by have := mem_range.mp hj; omega))
  rw [Finset.card_insert_of_notMem hnot, card_sawtoothZeroGrid] at hcard
  omega

end NLAlib
