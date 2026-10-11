import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import NLAlib.Matrix.Norms
import NLAlib.ForMathlib.Analysis.PowerInequalities

/-!
# Polynomial traces in Hermitian eigenbases

Real parts of complex traces reduce to nonnegative squared entry weights.
These identities support the deterministic mixed-power and trace Young steps
of the integer noncommutative Khintchine proof.
Source: operator manuscript `lem:mixed`, `lem:meanvalue`, `lem:traceyoung`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix Matrix.Norms.L2Operator
open Matrix
namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Complex trace is invariant under unitary conjugation, including empty
matrices. Source: trace cyclicity; supports `noncommutative-khintchine`. -/
theorem trace_conjStarAlgAut_complex (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    (Unitary.conjStarAlgAut ℂ _ U A).trace = A.trace := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]

/-- Two powers of a real diagonal matrix, separated by a Hermitian matrix,
have real trace equal to a sum weighted by squared complex entry norms.
Source: the eigenbasis expansion in manuscript `lem:mixed`. -/
theorem re_trace_mul_diagonal_pow_mul_mul_diagonal_pow
    (C : Matrix ι ι ℂ) (hC : C.IsHermitian) (ev : ι → ℝ) (a b : ℕ) :
    (C * (Matrix.diagonal (fun i => (ev i : ℂ))) ^ a * C *
      (Matrix.diagonal (fun i => (ev i : ℂ))) ^ b).trace.re =
      ∑ i, ∑ j, ‖C i j‖ ^ 2 * ev j ^ a * ev i ^ b := by
  rw [Matrix.diagonal_pow, Matrix.diagonal_pow,
    Matrix.mul_assoc C (Matrix.diagonal ((fun i => (ev i : ℂ)) ^ a)) C]
  have hentry (i : ι) :
      (C * (Matrix.diagonal ((fun i => (ev i : ℂ)) ^ a) * C)) i i =
        ∑ j, C i j * ((ev j : ℂ) ^ a * C j i) := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [Matrix.diagonal_mul]; rfl
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal, Complex.re_sum]
  simp_rw [hentry, Finset.sum_mul, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have hs : C j i = star (C i j) := by
    have hh := congrFun (congrFun hC j) i
    simpa only [Matrix.conjTranspose_apply] using hh.symm
  rw [hs]
  change (C i j * ((ev j : ℂ) ^ a * star (C i j)) * (ev i : ℂ) ^ b).re = _
  have he : C i j * ((ev j : ℂ) ^ a * star (C i j)) * (ev i : ℂ) ^ b =
      (C i j * star (C i j)) * ((ev j ^ a * ev i ^ b : ℝ) : ℂ) := by
    push_cast
    ring
  have hn : C i j * star (C i j) = ((‖C i j‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [Complex.normSq_eq_norm_sq] using! Complex.mul_conj (C i j)
  rw [he, hn, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- Unitary conjugation simultaneously preserves every polynomial product
trace. Source: trace cyclicity and the star-algebra automorphism;
supports the eigenbasis reduction in `noncommutative-khintchine`. -/
theorem trace_mul_pow_mul_mul_pow_conjStarAlgAut
    (U : Matrix.unitaryGroup ι ℂ) (C H : Matrix ι ι ℂ) (a b : ℕ) :
    let E := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
    (E C * E H ^ a * E C * E H ^ b).trace = (C * H ^ a * C * H ^ b).trace := by
  dsimp only
  rw [← map_pow, ← map_pow, ← map_mul, ← map_mul, ← map_mul,
    trace_conjStarAlgAut_complex]

/-- Even mixed powers in a Hermitian diagonal basis are bounded by the endpoint
quadratic trace. Negative eigenvalues and exponent zero are included.
Source: manuscript `lem:mixed`; supports `noncommutative-khintchine`. -/
theorem re_trace_mul_diagonal_pow_mul_le
    (C : Matrix ι ι ℂ) (hC : C.IsHermitian) (ev : ι → ℝ)
    {m l : ℕ} (hm : Even m) (hl : l ≤ m) :
    (C * (diagonal (fun i => (ev i : ℂ))) ^ l * C *
      (diagonal (fun i => (ev i : ℂ))) ^ (m - l)).trace.re ≤
        (C ^ 2 * (diagonal (fun i => (ev i : ℂ))) ^ m).trace.re := by
  let T (a b : ℕ) := ∑ i, ∑ j, ‖C i j‖ ^ 2 * ev j ^ a * ev i ^ b
  have hs (i j) : ‖C i j‖ = ‖C j i‖ := by
    have hh := congrFun (congrFun hC j) i
    simpa only [Matrix.conjTranspose_apply, norm_star] using congrArg norm hh
  have hsym (a b) : T a b = T b a := by
    dsimp [T]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hs j i]
    ring
  have hbound : T l (m - l) + T (m - l) l ≤ T m 0 + T 0 m := by
    have hb : ∀ i j,
        ‖C i j‖ ^ 2 * (ev j ^ l * ev i ^ (m - l) + ev j ^ (m - l) * ev i ^ l) ≤
          ‖C i j‖ ^ 2 * (ev j ^ m + ev i ^ m) := by
      intro i j
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      calc ev j ^ l * ev i ^ (m - l) + ev j ^ (m - l) * ev i ^ l ≤
          |ev j| ^ l * |ev i| ^ (m - l) + |ev j| ^ (m - l) * |ev i| ^ l := by
            apply add_le_add
            · simpa only [abs_mul, abs_pow] using le_abs_self (ev j ^ l * ev i ^ (m - l))
            · simpa only [abs_mul, abs_pow] using le_abs_self (ev j ^ (m - l) * ev i ^ l)
        _ ≤ |ev j| ^ m + |ev i| ^ m := mixed_pow_add_mixed_pow_le (abs_nonneg _) (abs_nonneg _) hl
        _ = ev j ^ m + ev i ^ m := by rw [hm.pow_abs, hm.pow_abs]
    have h := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
      Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset ι)) => hb i j
    simpa only [T, mul_add, Finset.sum_add_distrib, mul_assoc, pow_zero, mul_one, one_mul] using h
  rw [hsym (m - l) l, hsym m 0] at hbound
  have hscalar : T l (m - l) ≤ T 0 m := by linarith
  rw [re_trace_mul_diagonal_pow_mul_mul_diagonal_pow C hC]
  have he : C ^ 2 * (diagonal (fun i => (ev i : ℂ))) ^ m =
      C * (diagonal (fun i => (ev i : ℂ))) ^ 0 * C *
        (diagonal (fun i => (ev i : ℂ))) ^ m := by simp [pow_two]
  rw [he, re_trace_mul_diagonal_pow_mul_mul_diagonal_pow C hC]
  exact hscalar

/-- **Mixed-power trace inequality.** For Hermitian `C,H`, even `m` and `l≤m`,
`re tr(C Hˡ C H^(m-l))≤re tr(C² Hᵐ)`. Source: manuscript `lem:mixed`;
Tropp's polynomial trace method, supporting `noncommutative-khintchine`. -/
theorem re_trace_mul_pow_mul_le_trace_sq_mul_pow
    (C H : Matrix ι ι ℂ) (hC : C.IsHermitian) (hH : H.IsHermitian)
    {m l : ℕ} (hm : Even m) (hl : l ≤ m) :
    (C * H ^ l * C * H ^ (m - l)).trace.re ≤ (C ^ 2 * H ^ m).trace.re := by
  let U := star hH.eigenvectorUnitary
  let E := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  have hEC : (E C).IsHermitian := by
    change ((U : Matrix ι ι ℂ) * C * star (U : Matrix ι ι ℂ)).IsHermitian
    exact Matrix.isHermitian_mul_mul_conjTranspose _ hC
  have hdiag : E H = diagonal (fun i => (hH.eigenvalues i : ℂ)) :=
    hH.conjStarAlgAut_star_eigenvectorUnitary
  have hleft := trace_mul_pow_mul_mul_pow_conjStarAlgAut U C H l (m - l)
  have hright := trace_mul_pow_mul_mul_pow_conjStarAlgAut U C H 0 m
  dsimp only at hleft hright
  rw [hdiag] at hleft hright
  simp only [pow_zero, Matrix.mul_one, ← pow_two] at hright
  rw [← hleft, ← hright]
  exact re_trace_mul_diagonal_pow_mul_le (E C) hEC hH.eigenvalues hm hl

end NLAlib
