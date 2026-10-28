import NLAlib.Krylov.Solvers.GMRESCurveGeometry

/-!
# Prescribed residual lengths as coordinate tails

The coordinates `sqrt(f_j²-f_(j+1)²)` realize every nonincreasing positive
finite sequence after appending zero. Plateaus give zero coordinates and do not
prevent the final coordinate from being positive.
Source: Greenbaum--Pták--Strakoš (1996), constructive proof.
-/

noncomputable section
open scoped Matrix
open Finset
namespace NLAlib

/-- The real square-root differences, embedded into the complex vector space. -/
def gmresCurveVector (f : ℕ → ℝ) (n : ℕ) : Fin n → ℂ :=
  fun i => (Real.sqrt (f i.val^2-f (i.val+1)^2) : ℂ)

private theorem sum_curve_tail_differences (f : ℕ → ℝ) (n k : ℕ) (hk : k ≤ n) :
    (∑ i ∈ range n, if i < k then (0 : ℝ) else (f i^2-f (i+1)^2)) = f k^2-f n^2 := by
  induction n generalizing k with
  | zero =>
    have he : k = 0 := by omega
    subst k
    simp
  | succ n ih =>
    by_cases hkn : k ≤ n
    · rw [sum_range_succ,ih k hkn,if_neg (Nat.not_lt.mpr hkn)]
      ring
    · have he : k = n+1 := by omega
      subst k
      rw [sub_self]
      apply sum_eq_zero
      intro i hi
      exact if_pos (mem_range.mp hi)

/-- The prescribed curve is the Euclidean norm of the corresponding coordinate
tail, including plateaus and the one-dimensional case.
atlas: gmres-any-convergence-curve (partial) -/
theorem norm_gmresCurveVector_tail {n k : ℕ} (f : ℕ → ℝ) (hk : k < n)
    (hpos : ∀ j < n, 0 ≤ f j) (hmono : ∀ j < n, f (j+1) ≤ f j) (hfn : f n = 0) :
    ‖WithLp.toLp 2 (gmresCurveVector f n-coordinateHead (gmresCurveVector f n) k)‖ = f k := by
  have hterm (i : Fin n) :
      ‖(gmresCurveVector f n-coordinateHead (gmresCurveVector f n) k) i‖^2 =
        if i.val < k then 0 else f i.val^2-f (i.val+1)^2 := by
    by_cases hi : i.val < k
    · simp [coordinateHead,hi]
    · have hnext : 0 ≤ f (i.val+1) := by
        by_cases hn : i.val+1 < n
        · exact hpos _ hn
        · have he : i.val+1 = n := by have := i.isLt; omega
          rw [he,hfn]
      have hdiff : 0 ≤ f i.val^2-f (i.val+1)^2 := by
        nlinarith [hpos _ i.isLt,hmono _ i.isLt]
      simp only [Pi.sub_apply,coordinateHead,if_neg hi,sub_zero,gmresCurveVector]
      simpa only [Complex.norm_real,Real.norm_eq_abs,sq_abs] using Real.sq_sqrt hdiff
  have hsq : ‖WithLp.toLp 2 (gmresCurveVector f n-coordinateHead (gmresCurveVector f n) k)‖^2 = f k^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ i : Fin n, ‖(gmresCurveVector f n-coordinateHead (gmresCurveVector f n) k) i‖^2) = _
    simp_rw [hterm]
    rw [Fin.sum_univ_eq_sum_range (fun i => if i < k then (0 : ℝ) else f i^2-f (i+1)^2),
      sum_curve_tail_differences f n k hk.le,hfn,zero_pow (by decide : 2 ≠ 0),sub_zero]
  nlinarith [norm_nonneg (WithLp.toLp 2 (gmresCurveVector f n-coordinateHead (gmresCurveVector f n) k)),
    hpos k hk]

/-- The last coordinate is the positive final prescribed residual, despite
arbitrary earlier stagnation. This is what makes the companion change of basis
invertible. -/
theorem gmresCurveVector_last {n : ℕ} (hn : 0 < n) (f : ℕ → ℝ)
    (hpos : 0 ≤ f (n-1)) (hfn : f n = 0) :
    gmresCurveVector f n ⟨n-1,by omega⟩ = (f (n-1) : ℂ) := by
  simp only [gmresCurveVector,show n-1+1=n by omega,hfn,zero_pow (by decide : 2 ≠ 0),sub_zero,
    Real.sqrt_sq hpos]

end NLAlib
