import NLAlib.ForMathlib.Analysis.BinaryLog
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# A finite logarithmic bound for bounded diagonal coefficients

Concavity reduces each coefficient to the two endpoints of `[-1,1]`.
The finite mean then gives binary relative entropy, whose quadratic lower
bound supplies the sharp dimension factor in Gaussian-ratio Chernoff estimates.
-/

noncomputable section
open Real Finset

/-- The optimizing positive transform parameter for an upper-tail threshold. -/
def sphereChernoffParameter (m x : ℝ) : ℝ := (x-m) / (2*(1-x^2))

/-- The optimizing transform stays in the exact Laplace-transform domain at
every bounded diagonal entry. -/
theorem sphereChernoffParameter_mul_sub_lt_half {m x d : ℝ}
    (hm : -1 < m) (hmx : m < x) (hx : x < 1) (hd : d ≤ 1) :
    sphereChernoffParameter m x * (d-x) < 1/2 := by
  have hx0 : 0 < 1+x := by linarith
  have hx1 : 0 < 1-x := by linarith
  have hs : 0 < 1-x^2 := by nlinarith
  have ht : 0 < sphereChernoffParameter m x := by unfold sphereChernoffParameter; positivity
  have he : 1 - 2 * sphereChernoffParameter m x * (1-x) = (1+m)/(1+x) := by
    unfold sphereChernoffParameter
    field_simp
    ring
  have hp : 0 < (1+m)/(1+x) := div_pos (by linarith) hx0
  have hh := mul_le_mul_of_nonneg_left hd ht.le
  nlinarith

/-- A bounded finite coefficient list with prescribed mean has the exact
logarithmic Chernoff lower bound. No random variables occur in this lemma. -/
theorem card_mul_sub_sq_div_two_le_sum_log_affine {ι : Type*} [Fintype ι]
    (d : ι → ℝ) {m x : ℝ} (hm : -1 < m) (_hm1 : m < 1)
    (hmx : m < x) (hx : x < 1) (hd : ∀ i, d i ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∑ i, d i = Fintype.card ι * m) :
    (Fintype.card ι : ℝ) * (x-m)^2 / 2 ≤
      ∑ i, log (1 - 2*sphereChernoffParameter m x*(d i-x)) := by
  have hm0 : 0 < 1+m := by linarith
  have hm1' : 0 < 1-m := by linarith
  have hx0 : 0 < 1+x := by linarith
  have hx1 : 0 < 1-x := by linarith
  let a := (1+m)/(1+x)
  let b := (1-m)/(1-x)
  have ha : 0 < a := div_pos hm0 hx0
  have hb : 0 < b := div_pos hm1' hx1
  have hi (i : ι) :
      ((1+d i)/2)*log a + ((1-d i)/2)*log b ≤
        log (1 - 2*sphereChernoffParameter m x*(d i-x)) := by
    have hc := strictConcaveOn_log_Ioi.concaveOn.2 ha hb
      (show 0 ≤ (1+d i)/2 by linarith [(hd i).1])
      (show 0 ≤ (1-d i)/2 by linarith [(hd i).2]) (by ring)
    simp only [smul_eq_mul] at hc
    have he : 1 - 2*sphereChernoffParameter m x*(d i-x) =
        ((1+d i)/2)*a + ((1-d i)/2)*b := by
      have hs : 0 < 1-x^2 := by nlinarith
      dsimp [a,b,sphereChernoffParameter]
      field_simp [ne_of_gt hx0, ne_of_gt hx1, ne_of_gt hs]
      ring
    rwa [he]
  have hsplus : ∑ i, (1+d i)/2 = (Fintype.card ι : ℝ)*(1+m)/2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, hmean]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    ring
  have hsminus : ∑ i, (1-d i)/2 = (Fintype.card ι : ℝ)*(1-m)/2 := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, hmean]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    ring
  have hsum : (Fintype.card ι : ℝ) *
      (((1+m)/2)*log a + ((1-m)/2)*log b) ≤
      ∑ i, log (1 - 2*sphereChernoffParameter m x*(d i-x)) := by
    apply le_trans _ (Finset.sum_le_sum fun i _ => hi i)
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hsplus, hsminus]
    exact le_of_eq (by ring)
  have hkl := two_mul_sub_sq_le_binary_log
    (p := (1+m)/2) (q := (1+x)/2) (by linarith) (by linarith)
    (by linarith) (by linarith)
  have he₁ : ((1+m)/2)/((1+x)/2) = a := by dsimp [a]; field_simp
  have he₂ : (1-(1+m)/2)/(1-(1+x)/2) = b := by
    rw [show 1-(1+m)/2 = (1-m)/2 by ring, show 1-(1+x)/2 = (1-x)/2 by ring]
    dsimp [b]
    field_simp
  rw [he₁,he₂] at hkl
  have he₃ : 1-(1+m)/2 = (1-m)/2 := by ring
  rw [he₃] at hkl
  apply le_trans _ hsum
  have hmul := mul_le_mul_of_nonneg_left hkl (Nat.cast_nonneg (Fintype.card ι))
  nlinarith
