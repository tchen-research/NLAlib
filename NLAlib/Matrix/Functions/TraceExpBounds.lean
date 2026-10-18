import NLAlib.Matrix.Functions.TraceExpMonotone
import NLAlib.Matrix.Functions.UnitaryCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import NLAlib.ForMathlib.Analysis.Matrix.Order
/-!
# Finite-label trace exponential bounds and scalar shifts

Exact scalar-shift identities and trace monotonicity control changes in a predictable
Hermitian offset without imposing a lower spectral bound. Also: positivity and dimensional bounds
for `traceExp`, its continuity (`continuous_traceExp`), the crossing bound
`exp_sub_le_traceExp_compensated_of_crossing` (moved from
`Concentration/Martingales/TracePotentialCrossing`), and convexity on bundled Hermitian matrices
(`convexOn_traceExp_smul_selfAdjoint`, moved from `Concentration/Matrix/SamplingWithoutReplacement`).
-/

noncomputable section

open Matrix Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A real scalar identity exponentiates exactly as a scalar identity for any finite labels.
Source: scalar continuous functional calculus; helper for `matrix-freedman` (partial). -/
theorem matrixExp_smul_one_eq_exp_smul_one (t : ℝ) :
    matrixExp (t • (1 : Matrix n n ℂ)) = Real.exp t • (1 : Matrix n n ℂ) := by
  have ht : (t • (1 : Matrix n n ℂ)).IsHermitian :=
    Matrix.isHermitian_one.smul (IsSelfAdjoint.all _)
  rw [matrixExp, ← CFC.real_exp_eq_normedSpace_exp ht]
  have heq : t • (1 : Matrix n n ℂ) = algebraMap ℝ (Matrix n n ℂ) t := by
    simp only [Algebra.algebraMap_eq_smul_one]
  rw [heq, cfc_algebraMap]
  simp only [Algebra.algebraMap_eq_smul_one]

/-- Adding a real scalar identity multiplies the trace exponential by its scalar
exponential. No Hermitian premise is needed.
Source: the commuting exponential identity; helper for `matrix-freedman` (partial). -/
theorem traceExp_add_smul_one_eq_exp_mul (A : Matrix n n ℂ) (t : ℝ) :
    traceExp (A + t • (1 : Matrix n n ℂ)) = Real.exp t * traceExp A := by
  let : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hc : Commute A (t • (1 : Matrix n n ℂ)) := (Commute.one_right A).smul_right t
  have he : matrixExp (A + t • (1 : Matrix n n ℂ)) =
      matrixExp A * matrixExp (t • (1 : Matrix n n ℂ)) := NormedSpace.exp_add_of_commute hc
  rw [traceExp_complex, traceExp_complex, he, matrixExp_smul_one_eq_exp_smul_one, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul]
  simp only [Complex.smul_re, smul_eq_mul]

/-- The trace exponential changes by at most the multiplicative factor `exp δ` when
Hermitian inputs differ in operator norm by at most `δ`.
Source: Loewner norm comparison and the exact scalar shift; helper for the predictable
offset passage in operator rederivations `eq:condlieb`. Atlas `matrix-freedman` (partial). -/
theorem traceExp_le_exp_mul_traceExp_of_norm_sub_le [Nonempty n]
    (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) {δ : ℝ}
    (hδ : ‖A - B‖ ≤ δ) : traceExp A ≤ Real.exp δ * traceExp B := by
  have hd : A - B ≤ algebraMap ℝ (Matrix n n ℂ) δ := by
    apply le_algebraMap_of_spectrum_le _ (hA.sub hB)
    intro x hx
    have hnorm : |x| ≤ ‖A - B‖ := by
      simpa only [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem hx
    exact (le_abs_self x).trans (hnorm.trans hδ)
  have hle : A ≤ B + δ • (1 : Matrix n n ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one, add_comm] using sub_le_iff_le_add.mp hd
  have hh : (B + δ • (1 : Matrix n n ℂ)).IsHermitian :=
    hB.add (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _))
  exact (traceExp_le_traceExp A _ hA hh hle).trans_eq
    (traceExp_add_smul_one_eq_exp_mul B δ)

/-- Hermitian trace exponentials are nonnegative, including the empty finite matrix.
Source: positivity of the actual matrix exponential and its trace;
helper for `matrix-freedman` (partial). -/
theorem traceExp_nonneg_of_isHermitian (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    0 ≤ traceExp A := by
  have h := (posDef_matrixExp_and_matrixLog_matrixExp A hA).1.posSemidef.trace_nonneg
  exact (RCLike.nonneg_iff.mp h).1

/-- A scalar identity has trace exponential `card(n) exp(t)` for any finite labels.
Source: the exact scalar exponential identity; helper for `matrix-freedman` (partial). -/
theorem traceExp_smul_one_eq_card_mul_exp (t : ℝ) :
    traceExp (t • (1 : Matrix n n ℂ)) = Fintype.card n * Real.exp t := by
  rw [traceExp_complex, matrixExp_smul_one_eq_exp_smul_one, Matrix.trace_smul]
  simp only [Matrix.trace_one, Complex.smul_re, Complex.natCast_re, smul_eq_mul, mul_comm]

/-- `traceExp (θ • A)` is nonnegative and dominates `exp (θ λmax A)` for `θ > 0` and `exp (θ λmin A)`
for `θ < 0`.

Tropp 2015, §3.2, eq. (3.2.3). Atlas: `matrix-laplace`. Ported from the Prove2me mission *An
Introduction to Matrix Concentration Inequalities, Ch 3*. -/
theorem exp_mul_lambdaMax_lambdaMin_le_traceExp_smul {d : Type*} [Fintype d] [DecidableEq d]
    [Nonempty d] (A : Matrix d d ℂ) (hA : A.IsHermitian) (θ : ℝ) :
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

/-- The trace exponential is bounded by the matrix dimension times the
exponential of the largest eigenvalue. Empty dimension gives zero on both
sides; no matrix norm or positivity of the largest eigenvalue is needed. -/
theorem traceExp_le_card_mul_exp_lambdaMax (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    traceExp A ≤ (Fintype.card n : ℝ) * Real.exp (lambdaMax A) := by
  have he := traceExp_smul_eq_sum A hA 1
  rw [one_smul] at he
  rw [he]
  simp only [one_mul]
  calc
    _ ≤ ∑ _i : n, Real.exp (lambdaMax A) := by
      apply Finset.sum_le_sum
      intro i _
      apply Real.exp_le_exp.mpr
      exact le_of_mem_spectrum_of_lambdaMax_le A hA le_rfl _
        (hA.eigenvalues_mem_spectrum_real i)
    _ = _ := by simp

/-- The trace exponential of a Hermitian matrix on a nonempty index type is positive.
Tropp 2015, §3.1. Atlas: `matrix-laplace` (helper). -/
theorem traceExp_pos_of_isHermitian {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (H : Matrix d d ℂ) (hH : H.IsHermitian) : 0 < traceExp H := by
  have h := traceExp_smul_eq_sum H hH 1
  rw [one_smul] at h
  rw [h]
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

/-- `traceExp (c • B) ≤ d · exp (c ‖B‖)` for Hermitian `B` of size `d` and `c ≥ 0`.
Tropp 2015, §4.6 and §6.6 (dimensional factor). Atlas: `matrix-gaussian-series`,
`matrix-bernstein` (helper). -/
theorem traceExp_smul_le_mul_exp_mul_norm {d : ℕ} [NeZero d] (B : Matrix (Fin d) (Fin d) ℂ)
    (hB : B.IsHermitian) {c : ℝ} (hc : 0 ≤ c) : traceExp (c • B) ≤ d * Real.exp (c * ‖B‖) := by
  rw [traceExp_smul_eq_sum B hB c]
  calc ∑ i, Real.exp (c * hB.eigenvalues i) ≤ ∑ _i : Fin d, Real.exp (c * ‖B‖) := by
        apply Finset.sum_le_sum
        intro i _
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ hc
        exact (le_abs_self _).trans
          (abs_le_norm_of_mem_spectrum B (hB.eigenvalues_mem_spectrum_real i))
    _ = d * Real.exp (c * ‖B‖) := by simp

/-- `‖exp (∑ₖ Aₖ)‖ ≤ ∏ₖ (1 + ‖exp Aₖ‖)` for Hermitian summands. Tropp 2015, §3.5 (integrability
of the master bound). Atlas: `matrix-laplace` (helper). -/
theorem norm_matrixExp_sum_le_prod {d N : ℕ}
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ k, (A k).IsHermitian) :
    ‖matrixExp (∑ k, A k)‖ ≤ ∏ k, (1 + ‖matrixExp (A k)‖) := by
  let b : Fin N → ℝ := fun k => Real.log (1 + ‖matrixExp (A k)‖)
  have hb (k : Fin N) : A k ≤ algebraMap ℝ _ (b k) := by
    apply le_algebraMap_of_spectrum_le _ (hA k)
    intro x hx
    apply Real.le_log_iff_exp_le (by positivity) |>.2
    have hx' := norm_apply_le_norm_cfc Real.exp (A k) hx Real.continuous_exp.continuousOn (hA k)
    rw [CFC.real_exp_eq_normedSpace_exp (hA k)] at hx'
    have hx'' : Real.exp x ≤ ‖matrixExp (A k)‖ := by
      simpa [matrixExp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)] using hx'
    exact hx''.trans (le_add_of_nonneg_left zero_le_one)
  have hsum : (∑ k, A k).IsHermitian := isSelfAdjoint_sum _ (fun k _ => hA k)
  have hsumle : (∑ k, A k) ≤ algebraMap ℝ _ (∑ k, b k) := by
    simpa only [map_sum] using Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hb k)
  calc
    ‖matrixExp (∑ k, A k)‖ = ‖cfc Real.exp (∑ k, A k)‖ := by
      rw [CFC.real_exp_eq_normedSpace_exp hsum, matrixExp]
    _ ≤ Real.exp (∑ k, b k) := by
      apply norm_cfc_le (Real.exp_pos _).le
      intro x hx
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
      exact Real.exp_le_exp.mpr ((le_algebraMap_iff_spectrum_le hsum).1 hsumle x hx)
    _ = ∏ k, (1 + ‖matrixExp (A k)‖) := by
      rw [Real.exp_sum]
      apply Finset.prod_congr rfl
      intro k hk
      exact Real.exp_log (by positivity)

section Continuity

/-- The trace exponential is continuous on all finite complex matrices.
Source: continuous matrix exponential and linear trace; helper for `matrix-freedman` (partial). -/
theorem continuous_traceExp : Continuous (traceExp : Matrix n n ℂ → ℝ) := by
  let : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact Complex.continuous_re.comp
    ((Matrix.traceLinearMap n ℂ ℂ).toContinuousLinearMap.continuous.comp NormedSpace.exp_continuous)

end Continuity

section Crossing

variable [Nonempty n]

/-- At the original crossing `lambdaMax(Y)≥t` and `‖W‖≤v`, the actual compensated
trace potential is at least `exp(θt-gv)`. No deterministic substitute for the random
variation is assumed outside this event.
Source: operator rederivations Section 3.4, crossing bound;
atlas `matrix-freedman` (partial). -/
theorem exp_sub_le_traceExp_compensated_of_crossing (Y W : Matrix n n ℂ)
    (hY : Y.IsHermitian) (hW : W.IsHermitian) {θ g t v : ℝ}
    (hθ : 0 < θ) (hg : 0 ≤ g) (ht : t ≤ lambdaMax Y) (hv : ‖W‖ ≤ v) :
    Real.exp (θ * t - g * v) ≤ traceExp (θ • Y - g • W) := by
  have hWUpper : W ≤ algebraMap ℝ (Matrix n n ℂ) v := by
    apply le_algebraMap_of_spectrum_le _ hW
    intro x hx
    have hnorm : |x| ≤ ‖W‖ := by simpa only [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem hx
    exact (le_abs_self x).trans (hnorm.trans hv)
  have hscale := matrix_smul_le_smul_of_nonneg hWUpper hg
  have hscale' : g • W ≤ (g * v) • (1 : Matrix n n ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one, smul_smul] using hscale
  have hLoewner : θ • Y - (g * v) • (1 : Matrix n n ℂ) ≤ θ • Y - g • W :=
    sub_le_sub_left hscale' _
  have hleft : (θ • Y - (g * v) • (1 : Matrix n n ℂ)).IsHermitian :=
    (hY.smul (IsSelfAdjoint.all _)).sub (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _))
  have hright : (θ • Y - g • W).IsHermitian :=
    (hY.smul (IsSelfAdjoint.all _)).sub (hW.smul (IsSelfAdjoint.all _))
  have hmono := traceExp_le_traceExp _ _ hleft hright hLoewner
  have hshift : traceExp (θ • Y - (g * v) • (1 : Matrix n n ℂ)) =
      Real.exp (-(g * v)) * traceExp (θ • Y) := by
    simpa only [sub_eq_add_neg, neg_smul] using traceExp_add_smul_one_eq_exp_mul (θ • Y) (-(g * v))
  rw [hshift] at hmono
  calc
    Real.exp (θ * t - g * v) = Real.exp (-(g * v)) * Real.exp (θ * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(g * v)) * Real.exp (θ * lambdaMax Y) := by gcongr
    _ ≤ Real.exp (-(g * v)) * traceExp (θ • Y) :=
      mul_le_mul_of_nonneg_left ((exp_mul_lambdaMax_lambdaMin_le_traceExp_smul Y hY θ).2.1 hθ) (Real.exp_pos _).le
    _ ≤ traceExp (θ • Y - g • W) := hmono

end Crossing

section Convexity

/-- Convexity of the actual trace exponential on bundled Hermitian matrices,
at either sign of the Laplace parameter. Source: `sh:convex-sampling`. -/
theorem convexOn_traceExp_smul_selfAdjoint {d : ℕ} [NeZero d] (θ : ℝ) :
    ConvexOn ℝ Set.univ
      (fun A : selfAdjoint (Matrix (Fin d) (Fin d) ℂ) => traceExp (θ • A.val)) := by
  refine ⟨convex_univ, ?_⟩
  intro A _ B _ a b ha hb hab
  have hA : (θ • A.val).IsHermitian :=
    (Matrix.isHermitian_iff_isSelfAdjoint.mpr selfAdjoint.isSelfAdjoint).smul (IsSelfAdjoint.all θ)
  have hB : (θ • B.val).IsHermitian :=
    (Matrix.isHermitian_iff_isSelfAdjoint.mpr selfAdjoint.isSelfAdjoint).smul (IsSelfAdjoint.all θ)
  have hh := (convexOn_traceExp_isHermitian (d := d)).2 hA hB ha hb hab
  simpa only [selfAdjoint.val_smul, AddSubgroup.coe_add, smul_add, smul_smul,
    mul_comm θ] using hh

end Convexity

end NLAlib
