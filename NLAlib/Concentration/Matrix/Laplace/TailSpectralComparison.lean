import NLAlib.Concentration.Matrix.Defs.Spectral
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Trace exponential dominates exponentials of extremal eigenvalues

Main declaration: `NLAlib.exp_mul_lambdaMax_lambdaMin_le_traceExp_smul`.

Atlas: `matrix-laplace`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015), https://arxiv.org/abs/1501.01571v1; Section 3.2, equation (3.2.3) and the lower-tail proof, printed p. 33.
-/
open scoped Matrix.Norms.L2Operator
set_option autoImplicit false
namespace NLAlib

private lemma traceExp_smul_eq_sum {d : ℕ} [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (θ : ℝ) :
    traceExp (θ • A) = ∑ i, Real.exp (θ * hA.eigenvalues i) := by
  rw [traceExp, matrixExp, ← CFC.real_exp_eq_normedSpace_exp (hA.smul (isSelfAdjoint_iff.mpr (star_trivial θ)))]
  rw [← cfc_comp_const_mul θ Real.exp A (by fun_prop) hA.isSelfAdjoint, hA.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.ofReal_re]

end NLAlib

open NLAlib

/-- `traceExp (θ • A)` is nonnegative and dominates `exp (θ λmax A)` for `θ > 0` and `exp (θ λmin A)`
for `θ < 0`.

Tropp 2015, §3.2, eq. (3.2.3). Atlas: `matrix-laplace`. Ported from the Prove2me mission *An
Introduction to Matrix Concentration Inequalities, Ch 3*. -/
theorem NLAlib.exp_mul_lambdaMax_lambdaMin_le_traceExp_smul {d : ℕ} [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (θ : ℝ) :
    0 ≤ traceExp (θ • A) ∧
    (0 < θ → Real.exp (θ * lambdaMax A) ≤ traceExp (θ • A)) ∧
    (θ < 0 → Real.exp (θ * lambdaMin A) ≤ traceExp (θ • A)) := by
  rw [traceExp_smul_eq_sum A hA θ]
  have hn : (Set.range hA.eigenvalues).Nonempty := Set.range_nonempty _
  have hf : (Set.range hA.eigenvalues).Finite := Set.finite_range _
  have hmax : lambdaMax A ∈ Set.range hA.eigenvalues := by
    simpa only [lambdaMax, hA.spectrum_real_eq_range_eigenvalues] using hn.csSup_mem hf
  have hmin : lambdaMin A ∈ Set.range hA.eigenvalues := by
    simpa only [lambdaMin, hA.spectrum_real_eq_range_eigenvalues] using hn.csInf_mem hf
  constructor
  · exact Finset.sum_nonneg (fun i _ => (Real.exp_pos _).le)
  constructor
  · intro _
    obtain ⟨i, hi⟩ := hmax
    rw [← hi]
    exact Finset.single_le_sum (fun j _ => (Real.exp_pos (θ * hA.eigenvalues j)).le) (Finset.mem_univ i)
  · intro _
    obtain ⟨i, hi⟩ := hmin
    rw [← hi]
    exact Finset.single_le_sum (fun j _ => (Real.exp_pos (θ * hA.eigenvalues j)).le) (Finset.mem_univ i)
