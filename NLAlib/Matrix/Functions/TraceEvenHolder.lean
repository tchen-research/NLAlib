import NLAlib.Matrix.Functions.TraceYoung
import NLAlib.ForMathlib.Analysis.FiniteWeightedHolder

/-! # Hölder for even Hermitian trace moments

Two separate eigenbases and their doubly stochastic overlap weights reduce
the trace bound to finite weighted Hölder. No commutation is assumed.
Source: Tropp 2022, Section 8.5; `schatten-even-moment-smoothness`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Even moment trace Hölder in the precise form needed for the Hessian of
an even matrix power. The quadratic endpoint includes zero matrices.
atlas: schatten-even-moment-smoothness (partial) -/
theorem re_trace_sq_mul_pow_le_even_moments
    (H A : Matrix ι ι ℂ) (hH : H.IsHermitian) (hA : A.IsHermitian)
    {p : ℕ} (hp : Even p) (hp2 : 2 ≤ p) :
    (H ^ 2 * A ^ (p - 2)).trace.re ≤
      (A ^ p).trace.re ^ (1 - 2 / (p : ℝ)) *
        (H ^ p).trace.re ^ (2 / (p : ℝ)) := by
  by_cases heq : p = 2
  · subst p
    simp
  have hpgt : (2 : ℝ) < p := by exact_mod_cast (show 2 < p by omega)
  have hp0 : (0 : ℝ) < p := by linarith
  have hm : (0 : ℝ) < p - 2 := by linarith
  have hsub : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by norm_cast
  have hpq : ((p : ℝ) / 2).HolderConjugate ((p : ℝ) / ((p : ℝ) - 2)) := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · linarith
    · field_simp
      ring
  let W : Matrix.unitaryGroup ι ℂ := star hH.eigenvectorUnitary * hA.eigenvectorUnitary
  let w (z : ι × ι) := norm ((W : Matrix ι ι ℂ) z.1 z.2) ^ 2
  let f (z : ι × ι) := |hH.eigenvalues z.1| ^ 2
  let g (z : ι × ι) := |hA.eigenvalues z.2| ^ (p - 2)
  have hpowH (i : ι) : (|hH.eigenvalues i| ^ 2) ^ ((p : ℝ) / 2) =
      hH.eigenvalues i ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    norm_num only [Nat.cast_ofNat]
    have he : (2 : ℝ) * ((p : ℝ) / 2) = p := by ring
    rw [he, Real.rpow_natCast, hp.pow_abs]
  have hpowA (j : ι) : (|hA.eigenvalues j| ^ (p - 2)) ^
      ((p : ℝ) / ((p : ℝ) - 2)) = hA.eigenvalues j ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), hsub]
    have he : ((p : ℝ) - 2) * ((p : ℝ) / ((p : ℝ) - 2)) = p := by field_simp
    rw [he, Real.rpow_natCast, hp.pow_abs]
  have hrow (i : ι) : ∑ j, w (i,j) = 1 := sum_norm_sq_unitary_row W i
  have hcol (j : ι) : ∑ i, w (i,j) = 1 := sum_norm_sq_unitary_col W j
  have hS : (∑ z : ι × ι, w z * f z ^ ((p : ℝ) / 2)) = (H ^ p).trace.re := by
    rw [Fintype.sum_prod_type, re_trace_pow_eq_sum_eigenvalues_pow H hH]
    simp only [f, hpowH]
    simp_rw [← Finset.sum_mul, hrow, one_mul]
  have hT : (∑ z : ι × ι, w z * g z ^ ((p : ℝ) / ((p : ℝ) - 2))) =
      (A ^ p).trace.re := by
    rw [Fintype.sum_prod_type, Finset.sum_comm, re_trace_pow_eq_sum_eigenvalues_pow A hA]
    simp only [g, hpowA]
    simp_rw [← Finset.sum_mul, hcol, one_mul]
  have h := sum_mul_mul_le_rpow_sum_mul_rpow Finset.univ w f g hpq
    (fun _ _ => sq_nonneg _) (fun _ _ => sq_nonneg _)
    (fun _ _ => pow_nonneg (abs_nonneg _) _)
  have hmEven : Even (p - 2) := by
    obtain ⟨k, hk⟩ := hp
    have hk1 : 1 ≤ k := by omega
    exact ⟨k - 1, by omega⟩
  have hleft : (∑ z : ι × ι, w z * f z * g z) =
      (H ^ 2 * A ^ (p - 2)).trace.re := by
    rw [Fintype.sum_prod_type, re_trace_pow_mul_pow_eq_sum_overlap H A hH hA]
    simp only [w, f, g, Even.pow_abs even_two, hmEven.pow_abs, W]
  rw [hleft, hS, hT] at h
  have he1 : 1 / ((p : ℝ) / 2) = 2 / (p : ℝ) := by field_simp
  have he2 : 1 / ((p : ℝ) / ((p : ℝ) - 2)) = 1 - 2 / (p : ℝ) := by field_simp
  simpa only [he1, he2, mul_comm] using h

end NLAlib
