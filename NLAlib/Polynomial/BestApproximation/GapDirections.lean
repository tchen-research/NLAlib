import NLAlib.Polynomial.BestApproximation.InterpolationPeakMaxima
import NLAlib.Polynomial.BestApproximation.GapWronskian

/-!
# Divided derivatives of the actual interpolation peaks

Choose the unique critical point of each gap polynomial and divide its derivative by the
critical linear factor. Their evaluations form the finite Laplacian certificate.
Source: focused rederivations, equations `polyretry:q-signs` and `polyretry:peak-jacobian`.
-/

noncomputable section

open Polynomial Finset Set

namespace NLAlib

/-- The unique actual gap critical point on a nontrivial ordered canonical grid.
Source: nondegeneracy and uniqueness of the actual interpolation gap maximum. -/
def interpolationGapCriticalPoint (n : ℕ) (t : Fin n → ℝ) (i : Fin (n + 1)) : ℝ := by
  classical
  exact if h : 0 < n ∧ t ∈ interiorNodeSimplex n then
    Classical.choose (exists_interpolationGapPeak_nondegenerate h.1 h.2 i) else 0

/-- The chosen actual critical point has all the nondegenerate peak properties.
Source: the actual compact gap maximum theorem. -/
theorem interpolationGapCriticalPoint_spec {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) :
    let τ := interpolationGapCriticalPoint n t i
    τ ∈ Ioo (canonicalIntervalNodes n t i.castSucc) (canonicalIntervalNodes n t i.succ) ∧
      (interpolationGapPolynomial n t i).derivative.eval τ = 0 ∧
      (interpolationGapPolynomial n t i).derivative.derivative.eval τ < 0 ∧
      1 < (interpolationGapPolynomial n t i).eval τ ∧
      interpolationGapPeak n t i = (interpolationGapPolynomial n t i).eval τ ∧
      (∀ y ∈ Ioo (canonicalIntervalNodes n t i.castSucc) (canonicalIntervalNodes n t i.succ),
        (interpolationGapPolynomial n t i).derivative.eval y = 0 → y = τ) := by
  classical
  simp only [interpolationGapCriticalPoint, dif_pos (show 0 < n ∧ t ∈ interiorNodeSimplex n from ⟨hn, ht⟩)]
  exact Classical.choose_spec (exists_interpolationGapPeak_nondegenerate hn ht i)

/-- The actual gap critical points are strictly ordered.
Source: each lies strictly inside its own ordered node gap. -/
theorem strictMono_interpolationGapCriticalPoint {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) : StrictMono (interpolationGapCriticalPoint n t) := by
  intro i j hij
  have hi := (interpolationGapCriticalPoint_spec hn ht i).1
  have hj := (interpolationGapCriticalPoint_spec hn ht j).1
  have hnodes := ht.monotone (show i.succ ≤ j.castSucc by have h := hij; exact Fin.mk_le_mk.mpr (by omega))
  exact hi.2.trans_le hnodes |>.trans hj.1

/-- The derivative of a gap polynomial divided by its actual critical linear factor.
Source: focused rederivations, the polynomial `q_i`. -/
def interpolationGapDividedDerivative (n : ℕ) (t : Fin n → ℝ) (i : Fin (n + 1)) : ℝ[X] :=
  (interpolationGapPolynomial n t i).derivative /ₘ (X - C (interpolationGapCriticalPoint n t i))

/-- The critical-point factor divides the actual gap derivative exactly.
Source: the polynomial factor theorem. -/
theorem mul_interpolationGapDividedDerivative {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) :
    (X - C (interpolationGapCriticalPoint n t i)) * interpolationGapDividedDerivative n t i =
      (interpolationGapPolynomial n t i).derivative := by
  exact mul_divByMonic_eq_iff_isRoot.mpr (interpolationGapCriticalPoint_spec hn ht i).2.1

/-- Dividing the gap derivative by its critical factor leaves degree strictly below `n`.
Source: the derivative and monic division degree bounds. -/
theorem degree_interpolationGapDividedDerivative_lt {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) :
    (interpolationGapDividedDerivative n t i).degree < n := by
  have hdeg : (interpolationGapPolynomial n t i).degree ≤ (n + 1 : ℕ) := by
    simpa only [interpolationGapPolynomial, card_univ, Fintype.card_fin,
      show n + 2 - 1 = n + 1 by omega] using
      Lagrange.degree_interpolate_le (s := univ) (interpolationGapSign n i) ht.injective.injOn
  have hnat := natDegree_le_of_degree_le hdeg
  have hder : (interpolationGapPolynomial n t i).derivative.degree ≤ n :=
    degree_le_of_natDegree_le ((natDegree_derivative_le _).trans (by omega))
  exact (degree_divByMonic_lt _ _ (derivative_interpolationGapPolynomial_ne_zero hn ht i)
    (by rw [degree_X_sub_C]; exact_mod_cast (show 0 < 1 by omega))).trans_le hder

/-- At its own critical point, the divided derivative is the strictly negative second derivative.
Source: differentiation of the exact critical-factor identity. -/
theorem eval_interpolationGapDividedDerivative_self {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) :
    (interpolationGapDividedDerivative n t i).eval (interpolationGapCriticalPoint n t i) =
      (interpolationGapPolynomial n t i).derivative.derivative.eval (interpolationGapCriticalPoint n t i) := by
  have h := congrArg (fun p : ℝ[X] => p.derivative.eval (interpolationGapCriticalPoint n t i))
    (mul_interpolationGapDividedDerivative hn ht i)
  simpa only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero,
    eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, eval_one, one_mul, add_zero] using h

/-- The actual divided derivatives are negative on the diagonal of the peak evaluation grid.
Source: nondegeneracy of each actual gap maximum. -/
theorem eval_interpolationGapDividedDerivative_self_neg {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) :
    (interpolationGapDividedDerivative n t i).eval (interpolationGapCriticalPoint n t i) < 0 := by
  rw [eval_interpolationGapDividedDerivative_self hn ht i]
  exact (interpolationGapCriticalPoint_spec hn ht i).2.2.1

/-- The actual divided derivatives have strict alternating off-diagonal signs at the peak points.
Source: the strict pairwise Wronskian certificate.
atlas: lebesgue-constant-lower-bound (partial) -/
theorem eval_interpolationGapDividedDerivative_offdiag_pos {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i j : Fin (n + 1)) (hij : i ≠ j) :
    0 < (-1 : ℝ) ^ (i.val + j.val) *
      (interpolationGapDividedDerivative n t i).eval (interpolationGapCriticalPoint n t j) := by
  let τ := interpolationGapCriticalPoint n t
  have hfactor := congrArg (fun p : ℝ[X] => p.eval (τ j)) (mul_interpolationGapDividedDerivative hn ht i)
  simp only [eval_mul, eval_sub, eval_X, eval_C] at hfactor
  have hjcrit := (interpolationGapCriticalPoint_spec hn ht j).2.1
  have hjpos : 0 < (interpolationGapPolynomial n t j).eval (τ j) :=
    zero_lt_one.trans (interpolationGapCriticalPoint_spec hn ht j).2.2.2.1
  have hτ := strictMono_interpolationGapCriticalPoint hn ht
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have h := interpolationGapPolynomial_wronskian_sign ht i j hlt (τ j)
    rw [hjcrit, mul_zero, sub_zero, ← hfactor] at h
    have hpow : (-1 : ℝ) ^ (j.val - i.val) = (-1 : ℝ) ^ (i.val + j.val) := by
      rw [show i.val + j.val = j.val - i.val + 2 * i.val by have := hlt; omega, pow_add, pow_mul]
      norm_num
    rw [hpow] at h
    have hd : 0 < (τ j - τ i) * (interpolationGapPolynomial n t j).eval (τ j) :=
      mul_pos (sub_pos.mpr (hτ hlt)) hjpos
    have hrew : (-1 : ℝ) ^ (i.val + j.val) *
        ((τ j - τ i) * (interpolationGapDividedDerivative n t i).eval (τ j) *
          (interpolationGapPolynomial n t j).eval (τ j)) =
        ((-1 : ℝ) ^ (i.val + j.val) * (interpolationGapDividedDerivative n t i).eval (τ j)) *
          ((τ j - τ i) * (interpolationGapPolynomial n t j).eval (τ j)) := by ring
    rw [hrew] at h
    exact (mul_pos_iff.mp h).resolve_right (by intro hh; linarith [hh.2]) |>.1
  · have h := interpolationGapPolynomial_wronskian_sign ht j i hgt (τ j)
    rw [hjcrit, zero_mul, zero_sub, ← hfactor] at h
    have hpow : (-1 : ℝ) ^ (i.val - j.val) = (-1 : ℝ) ^ (i.val + j.val) := by
      rw [show i.val + j.val = i.val - j.val + 2 * j.val by have := hgt; omega, pow_add, pow_mul]
      norm_num
    rw [hpow] at h
    have hd : 0 < (τ i - τ j) * (interpolationGapPolynomial n t j).eval (τ j) :=
      mul_pos (sub_pos.mpr (hτ hgt)) hjpos
    have hrew : (-1 : ℝ) ^ (i.val + j.val) *
        (-((interpolationGapPolynomial n t j).eval (τ j) *
          ((τ j - τ i) * (interpolationGapDividedDerivative n t i).eval (τ j)))) =
        ((-1 : ℝ) ^ (i.val + j.val) * (interpolationGapDividedDerivative n t i).eval (τ j)) *
          ((τ i - τ j) * (interpolationGapPolynomial n t j).eval (τ j)) := by ring
    rw [hrew] at h
    exact (mul_pos_iff.mp h).resolve_right (by intro hh; linarith [hh.2]) |>.1

end NLAlib
