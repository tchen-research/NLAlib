import NLAlib.Matrix.TracePowers
import Mathlib.Analysis.Matrix.PosDef

/-!
# Trace Young inequalities without commutativity

Separate Hermitian eigenbases give nonnegative overlap weights whose rows
and columns sum to one. Integer scalar Young inequalities therefore lift to
traces without assuming the two matrices commute.
Source: operator manuscript `lem:traceyoung`, for `noncommutative-khintchine`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
open Matrix
namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every row of a complex unitary matrix has squared norm one.
Source: the unitary identity; supports the overlap proof of
`noncommutative-khintchine`. -/
theorem sum_norm_sq_unitary_row (U : Matrix.unitaryGroup ι ℂ) (i : ι) :
    ∑ j, ‖(U : Matrix ι ι ℂ) i j‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (Unitary.coe_mul_star_self U) i) i
  have hs : ∀ j, (U : Matrix ι ι ℂ) i j *
      star ((U : Matrix ι ι ℂ) i j) = ((‖(U : Matrix ι ι ℂ) i j‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    simpa only [Complex.normSq_eq_norm_sq] using! Complex.mul_conj ((U : Matrix ι ι ℂ) i j)
  simpa only [Matrix.mul_apply, Unitary.coe_star, Matrix.star_apply,
    hs, Matrix.one_apply_eq, Complex.re_sum, Complex.ofReal_re, Complex.one_re] using congrArg Complex.re h

/-- Every column of a complex unitary matrix has squared norm one.
Source: the unitary identity; supports the overlap proof of
`noncommutative-khintchine`. -/
theorem sum_norm_sq_unitary_col (U : Matrix.unitaryGroup ι ℂ) (j : ι) :
    ∑ i, ‖(U : Matrix ι ι ℂ) i j‖ ^ 2 = 1 := by
  simpa only [Unitary.coe_star, Matrix.star_apply, Matrix.conjTranspose_apply, norm_star]
    using sum_norm_sq_unitary_row (star U) j

/-- A diagonal matrix times a conjugated diagonal matrix has trace given by
the squared unitary overlap weights. Source: separate eigenbases in
manuscript `lem:traceyoung`; supports `noncommutative-khintchine`. -/
theorem re_trace_diagonal_mul_conj_diagonal
    (U : Matrix.unitaryGroup ι ℂ) (a b : ι → ℝ) :
    (diagonal (fun i => (a i : ℂ)) *
      ((U : Matrix ι ι ℂ) * diagonal (fun j => (b j : ℂ)) *
        star (U : Matrix ι ι ℂ))).trace.re =
      ∑ i, ∑ j, ‖(U : Matrix ι ι ℂ) i j‖ ^ 2 * a i * b j := by
  have hentry (i : ι) : (diagonal (fun i => (a i : ℂ)) *
      ((U : Matrix ι ι ℂ) * diagonal (fun j => (b j : ℂ)) *
        star (U : Matrix ι ι ℂ))) i i =
      (a i : ℂ) * ∑ j, (U : Matrix ι ι ℂ) i j * (b j : ℂ) *
        star ((U : Matrix ι ι ℂ) i j) := by
    rw [Matrix.diagonal_mul, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.star_apply]
  simp only [Matrix.trace, Matrix.diag, hentry, Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hn : (U : Matrix ι ι ℂ) i j * star ((U : Matrix ι ι ℂ) i j) =
      ((‖(U : Matrix ι ι ℂ) i j‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [Complex.normSq_eq_norm_sq] using! Complex.mul_conj ((U : Matrix ι ι ℂ) i j)
  have he : (a i : ℂ) * ((U : Matrix ι ι ℂ) i j * (b j : ℂ) *
      star ((U : Matrix ι ι ℂ) i j)) =
      ((U : Matrix ι ι ℂ) i j * star ((U : Matrix ι ι ℂ) i j)) *
        (((a i * b j : ℝ)) : ℂ) := by push_cast; ring
  rw [he, hn, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- Products of natural Hermitian powers have real trace given by the
overlap weights of their two eigenbases. Source: separate spectral
decompositions in manuscript `lem:traceyoung`; supports
`noncommutative-khintchine`. -/
theorem re_trace_pow_mul_pow_eq_sum_overlap
    (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (r s : ℕ) :
    (A ^ r * B ^ s).trace.re =
      ∑ i, ∑ j,
        ‖((star hA.eigenvectorUnitary * hB.eigenvectorUnitary :
          Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) i j‖ ^ 2 *
          hA.eigenvalues i ^ r * hB.eigenvalues j ^ s := by
  let UA := hA.eigenvectorUnitary
  let UB := hB.eigenvectorUnitary
  let W : Matrix.unitaryGroup ι ℂ := star UA * UB
  have hAp : A ^ r = (UA : Matrix ι ι ℂ) *
      diagonal (fun i => ((hA.eigenvalues i ^ r : ℝ) : ℂ)) * star (UA : Matrix ι ι ℂ) := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [← map_pow, Matrix.diagonal_pow]
    simp only [Unitary.conjStarAlgAut_apply, Complex.ofReal_pow]
    rfl
  have hBp : B ^ s = (UB : Matrix ι ι ℂ) *
      diagonal (fun j => ((hB.eigenvalues j ^ s : ℝ) : ℂ)) * star (UB : Matrix ι ι ℂ) := by
    conv_lhs => rw [hB.spectral_theorem]
    rw [← map_pow, Matrix.diagonal_pow]
    simp only [Unitary.conjStarAlgAut_apply, Complex.ofReal_pow]
    rfl
  rw [hAp, hBp]
  have ht : (((UA : Matrix ι ι ℂ) *
      diagonal (fun i => ((hA.eigenvalues i ^ r : ℝ) : ℂ)) * star (UA : Matrix ι ι ℂ)) *
      ((UB : Matrix ι ι ℂ) * diagonal (fun j => ((hB.eigenvalues j ^ s : ℝ) : ℂ)) *
        star (UB : Matrix ι ι ℂ))).trace =
      (diagonal (fun i => ((hA.eigenvalues i ^ r : ℝ) : ℂ)) *
        ((W : Matrix ι ι ℂ) * diagonal (fun j => ((hB.eigenvalues j ^ s : ℝ) : ℂ)) *
          star (W : Matrix ι ι ℂ))).trace := by
    simp only [W, Submonoid.coe_mul, Unitary.coe_star, star_mul, star_star,
      Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm (UA : Matrix ι ι ℂ)]
    simp only [Matrix.mul_assoc]
  rw [ht, re_trace_diagonal_mul_conj_diagonal]

/-- Every natural Hermitian power has real trace equal to the corresponding
power sum of its real eigenvalues. Source: spectral theorem; supports the
integer trace method for `noncommutative-khintchine`. -/
theorem re_trace_pow_eq_sum_eigenvalues_pow
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (r : ℕ) :
    (A ^ r).trace.re = ∑ i, hA.eigenvalues i ^ r := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_pow, trace_conjStarAlgAut_complex,
    Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp only [Complex.re_sum, Pi.pow_apply, Function.comp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  change ((hA.eigenvalues i : ℂ) ^ r).re = _
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- Every even natural Hermitian trace moment is nonnegative. Source:
the real eigenvalue power sum; supports `noncommutative-khintchine`. -/
theorem re_trace_pow_nonneg_of_even (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    {r : ℕ} (hr : Even r) : 0 ≤ (A ^ r).trace.re := by
  rw [re_trace_pow_eq_sum_eigenvalues_pow A hA]
  exact Finset.sum_nonneg fun i _ => hr.pow_nonneg (hA.eigenvalues i)

/-- Every natural PSD trace power is nonnegative. Source: its nonnegative
eigenvalues; supports `noncommutative-khintchine`. -/
theorem re_trace_pow_nonneg_of_posSemidef (A : Matrix ι ι ℂ) (hA : A.PosSemidef)
    (r : ℕ) : 0 ≤ (A ^ r).trace.re := by
  rw [re_trace_pow_eq_sum_eigenvalues_pow A hA.isHermitian]
  exact Finset.sum_nonneg fun i _ => pow_nonneg (hA.eigenvalues_nonneg i) r

/-- **Polynomial trace Young inequality.** For PSD `V`, Hermitian `H` and
integer `p≥1`, the factor `q=2p-1` can be absorbed into the two endpoint
trace moments. No commutativity hypothesis is used. Source: manuscript
`lem:traceyoung`; supports `noncommutative-khintchine`. -/
theorem nat_mul_mul_re_trace_mul_pow_le
    (V H : Matrix ι ι ℂ) (hV : V.PosSemidef) (hH : H.IsHermitian)
    {p : ℕ} (hp : 1 ≤ p) :
    (p : ℝ) * (2 * p - 1 : ℕ) * (V * H ^ (2 * p - 2)).trace.re ≤
      (2 * p - 1 : ℕ) ^ p * (V ^ p).trace.re +
        (p - 1 : ℕ) * (H ^ (2 * p)).trace.re := by
  let W : Matrix.unitaryGroup ι ℂ := star hV.isHermitian.eigenvectorUnitary * hH.eigenvectorUnitary
  let w (i j : ι) := ‖(W : Matrix ι ι ℂ) i j‖ ^ 2
  have hrow (i) : ∑ j, w i j = 1 := sum_norm_sq_unitary_row W i
  have hcol (j) : ∑ i, w i j = 1 := sum_norm_sq_unitary_col W j
  have hev (i) : 0 ≤ hV.isHermitian.eigenvalues i := hV.eigenvalues_nonneg i
  have hpow (j) : (hH.eigenvalues j ^ 2) ^ (p - 1) = hH.eigenvalues j ^ (2 * p - 2) := by
    rw [← pow_mul]
    congr 1
    omega
  have hpow' (j) : (hH.eigenvalues j ^ 2) ^ p = hH.eigenvalues j ^ (2 * p) := by rw [← pow_mul]
  have hpoint (i j) :
      (p : ℝ) * (2 * p - 1 : ℕ) * hV.isHermitian.eigenvalues i *
        hH.eigenvalues j ^ (2 * p - 2) ≤
      (2 * p - 1 : ℕ) ^ p * hV.isHermitian.eigenvalues i ^ p +
        (p - 1 : ℕ) * hH.eigenvalues j ^ (2 * p) := by
    have h := nat_mul_mul_pow_le_pow_add
      (mul_nonneg (Nat.cast_nonneg (2 * p - 1)) (hev i)) (sq_nonneg (hH.eigenvalues j)) hp
    simpa only [hpow, hpow', mul_pow, mul_assoc] using h
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
      mul_le_mul_of_nonneg_left (hpoint i j) (sq_nonneg ‖(W : Matrix ι ι ℂ) i j‖)
  have hright :
      (∑ i, ∑ j, w i j * ((2 * p - 1 : ℕ) ^ p * hV.isHermitian.eigenvalues i ^ p +
        (p - 1 : ℕ) * hH.eigenvalues j ^ (2 * p))) =
      (2 * p - 1 : ℕ) ^ p * (∑ i, hV.isHermitian.eigenvalues i ^ p) +
        (p - 1 : ℕ) * (∑ j, hH.eigenvalues j ^ (2 * p)) := by
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    · simp_rw [← Finset.sum_mul, hrow, one_mul]
      rw [Finset.mul_sum]
    · rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hcol, one_mul]
      rw [Finset.mul_sum]
  rw [show V * H ^ (2 * p - 2) = V ^ 1 * H ^ (2 * p - 2) by rw [pow_one],
    re_trace_pow_mul_pow_eq_sum_overlap V H hV.isHermitian hH]
  rw [re_trace_pow_eq_sum_eigenvalues_pow V hV.isHermitian,
    re_trace_pow_eq_sum_eigenvalues_pow H hH]
  simpa only [w, W, pow_one, mul_assoc, mul_left_comm, Finset.mul_sum, hright] using hsum

end NLAlib
