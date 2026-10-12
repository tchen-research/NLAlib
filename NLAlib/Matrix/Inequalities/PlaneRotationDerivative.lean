import NLAlib.Matrix.Inequalities.PlaneRotation
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Scalar first variation of a real plane rotation

The rational unit-circle parametrization yields the coordinate stationarity
equation for a squared diagonal error minimum. Source: Schur–Horn variational
rederivation, equations (1)–(2), supporting atlas `schur-horn`.
-/
noncomputable section
open scoped Matrix BigOperators
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] in
/-- The rational rotation curve has entrywise derivative twice its skew
generator at zero. Schur–Horn variational rederivation, step (2). -/
theorem hasDerivAt_planeRotation_rational_apply (u v : n → ℝ) (i j : n) :
    HasDerivAt (fun t : ℝ =>
      planeRotation u v ((1 - t ^ 2) / (1 + t ^ 2)) (2 * t / (1 + t ^ 2)) i j)
      (2 * (u i * v j - v i * u j)) 0 := by
  have ht := hasDerivAt_id' (0 : ℝ)
  have hc : HasDerivAt (fun t : ℝ => (1 - t ^ 2) / (1 + t ^ 2)) 0 0 := by
    simpa using ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).fun_sub (ht.pow 2)).fun_div
      ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).fun_add (ht.pow 2)) (by norm_num)
  have hs : HasDerivAt (fun t : ℝ => 2 * t / (1 + t ^ 2)) 2 0 := by
    simpa using (ht.const_mul 2).fun_div
      ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).fun_add (ht.pow 2)) (by norm_num)
  simpa [planeRotation, Matrix.vecMulVec_apply, mul_add] using
    ((hasDerivAt_const (0 : ℝ) ((1 : Matrix n n ℝ) i j)).fun_add
      ((hc.sub_const 1).mul_const (u i * u j + v i * v j))).fun_add
      (hs.mul_const (u i * v j - v i * u j))

/-- The diagonal first variation of orthogonal conjugation by a rational plane
rotation is four times the associated row contraction. Schur–Horn variational
rederivation, equation (2). -/
theorem hasDerivAt_planeRotation_rational_conjugation_diag
    (A : Matrix n n ℝ) (hA : Aᵀ = A) (u v : n → ℝ) (i : n) :
    HasDerivAt (fun t : ℝ =>
      let R := planeRotation u v ((1 - t ^ 2) / (1 + t ^ 2)) (2 * t / (1 + t ^ 2))
      (R * A * Rᵀ) i i)
      (4 * ∑ j, A i j * (u i * v j - v i * u j)) 0 := by
  let R (t : ℝ) := planeRotation u v ((1 - t ^ 2) / (1 + t ^ 2))
    (2 * t / (1 + t ^ 2))
  have hR0 : R 0 = 1 := by simp [R, planeRotation]
  have hd := HasDerivAt.fun_sum (u := (Finset.univ : Finset n)) fun j _ =>
    HasDerivAt.fun_sum (u := (Finset.univ : Finset n)) fun k _ =>
      ((hasDerivAt_planeRotation_rational_apply u v i k).mul_const (A k j)).mul
        (hasDerivAt_planeRotation_rational_apply u v i j)
  change HasDerivAt (fun t => ∑ j, ∑ k, (R t i k * A k j) * R t i j)
    (∑ j, ∑ k, (2 * (u i * v k - v i * u k) * A k j * R 0 i j +
      R 0 i k * A k j * (2 * (u i * v j - v i * u j)))) 0 at hd
  convert hd using 1
  · funext t
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rfl
  · rw [hR0]
    simp only [Finset.sum_add_distrib]
    have hfirst : (∑ j, ∑ k, 2 * (u i * v k - v i * u k) * A k j *
        (1 : Matrix n n ℝ) i j) = ∑ k, 2 * (u i * v k - v i * u k) * A k i := by
      rw [Finset.sum_comm]
      simp [Matrix.one_apply]
    have hsecond : (∑ j, ∑ k, (1 : Matrix n n ℝ) i k * A k j *
        (2 * (u i * v j - v i * u j))) =
        ∑ j, A i j * (2 * (u i * v j - v i * u j)) := by
      simp [Matrix.one_apply]
    rw [hfirst, hsecond]
    have hs : ∀ j, A j i = A i j := fun j => congrArg (fun M => M i j) hA
    simp_rw [hs]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- A minimum of squared diagonal error on an orthogonal orbit satisfies the
coordinate stationarity equation `(rᵢ-rⱼ)Aᵢⱼ=0`. Schur–Horn variational
rederivation, equation (2); only ordinary real scalar differentiation is used. -/
theorem diagonal_error_stationarity_of_min
    (A : Matrix n n ℝ) (hA : Aᵀ = A) (d : n → ℝ)
    (hmin : ∀ R : Matrix n n ℝ, Rᵀ * R = 1 →
      (∑ i, (A i i - d i) ^ 2) ≤ ∑ i, ((R * A * Rᵀ) i i - d i) ^ 2)
    (i j : n) : ((A i i - d i) - (A j j - d j)) * A i j = 0 := by
  by_cases hij : i = j
  · subst j
    ring
  let u : n → ℝ := Pi.single i 1
  let v : n → ℝ := Pi.single j 1
  let R (t : ℝ) := planeRotation u v ((1 - t ^ 2) / (1 + t ^ 2))
    (2 * t / (1 + t ^ 2))
  have hR0 : R 0 = 1 := by simp [R, planeRotation]
  have horth (t : ℝ) : (R t)ᵀ * R t = 1 := by
    apply transpose_planeRotation_mul_self
    · simp [u, dotProduct_single]
    · simp [v, dotProduct_single]
    · simp [u, v, dotProduct_single, hij]
    · exact sq_rational_rotation_coefficients t
  let f (t : ℝ) : ℝ := ∑ k, ((R t * A * (R t)ᵀ) k k - d k) ^ 2
  have hlocal : IsLocalMin f 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa [f, hR0] using hmin (R t) (horth t)
  have hd := HasDerivAt.fun_sum (u := (Finset.univ : Finset n)) fun k _ =>
    ((hasDerivAt_planeRotation_rational_conjugation_diag A hA u v k).sub_const (d k)).pow 2
  change HasDerivAt f _ 0 at hd
  have hzero := hlocal.hasDerivAt_eq_zero hd
  have hzero' : (∑ k, 2 * (A k k - d k) *
      (4 * ∑ l, A k l * (u k * v l - v k * u l))) = 0 := by
    simpa [planeRotation] using hzero
  have hsum : (∑ k, 2 * (A k k - d k) *
      (4 * ∑ l, A k l * (u k * v l - v k * u l))) =
      8 * (((A i i - d i) - (A j j - d j)) * A i j) := by
    have hrow (k : n) : (∑ l, A k l * (u k * v l - v k * u l)) =
        u k * A k j - v k * A k i := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      have h1 : (∑ l, A k l * (u k * v l)) = u k * A k j := by
        calc
          _ = u k * ((fun l => A k l) ⬝ᵥ v) := by
            simp only [dotProduct, Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; ring
          _ = _ := by simp [v, dotProduct_single]
      have h2 : (∑ l, A k l * (v k * u l)) = v k * A k i := by
        calc
          _ = v k * ((fun l => A k l) ⬝ᵥ u) := by
            simp only [dotProduct, Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; ring
          _ = _ := by simp [u, dotProduct_single]
      rw [h1, h2]
    simp_rw [hrow]
    have hpoint (k : n) : 2 * (A k k - d k) * (4 * (u k * A k j - v k * A k i)) =
        u k * (8 * (A k k - d k) * A k j) -
          v k * (8 * (A k k - d k) * A k i) := by ring
    simp_rw [hpoint]
    rw [Finset.sum_sub_distrib]
    change u ⬝ᵥ (fun k => 8 * (A k k - d k) * A k j) -
      v ⬝ᵥ (fun k => 8 * (A k k - d k) * A k i) = _
    simp only [u, v, single_dotProduct, one_mul]
    rw [show A j i = A i j from congrArg (fun M => M i j) hA]
    ring
  rw [hsum] at hzero'
  linarith

end NLAlib
