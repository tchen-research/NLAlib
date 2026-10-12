import NLAlib.Matrix.Functions.HermitianCalculus
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Intrinsic dimension

The intrinsic dimension `intdim A = tr A / ‖A‖` of a complex matrix, trace functions
`tr φ(A)`, and their deterministic theory:

* `intrinsicDimension`, `traceFunction`, `traceFunction_eq_sum` (Tropp 2015, Def. 7.1.1, §7.4);
* `traceFunction_le_intrinsicDimension_mul`: `tr φ(A) ≤ intdim A · φ ‖A‖` for convex `φ` with
  `φ 0 = 0` and PSD `A` (Tropp 2015, Lemma 7.5.1);
* `intrinsicDimension_fromBlocks`: the intrinsic dimension of a block-diagonal variance
  (Tropp 2015, eq. (7.3.4) and §7.7.3).

Atlas: `intrinsic-dimension`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1
(7 January 2015); Def. 7.1.1, §7.4, Lemma 7.5.1 (printed pp. 112–113), eq. (7.3.4) (p. 109),
§7.7.3 (p. 117). Ported from the Prove2me missions *An Introduction to Matrix Concentration
Inequalities, Ch 3–8*. Merged from `NLAlib.Probability.Concentration.Basic.IntrinsicDimension`,
`NLAlib.Probability.Concentration.Matrix.IntrinsicDimension` and
`NLAlib.Probability.Concentration.Matrix.BlockIntrinsic` (dedup round 2026-10-12).
-/

open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section
namespace NLAlib

section Defs

/-- The intrinsic dimension `tr A / ‖A‖`. Tropp 2015, Def. 7.1.1. Atlas: `intrinsic-dimension`.
atlas: intrinsic-dimension -/
def intrinsicDimension {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) : ℝ := (Matrix.trace A).re / ‖A‖

/-- The trace function `re (tr φ(A))`, with `φ(A)` from the continuous functional calculus. Tropp
2015, §7.4.
atlas: intrinsic-dimension -/
def traceFunction {d : Type*} [Fintype d] [DecidableEq d]
    (φ : ℝ → ℝ) (A : Matrix d d ℂ) : ℝ := (Matrix.trace (cfc φ A)).re

/-- The trace function of a Hermitian matrix is the sum of `φ` over its eigenvalues:
`traceFunction φ A = ∑ᵢ φ (λᵢ A)`. Tropp 2015, §7.4. Atlas: `intrinsic-dimension` (helper). -/
theorem traceFunction_eq_sum {d : Type*} [Fintype d] [DecidableEq d] (φ : ℝ → ℝ)
    (A : Matrix d d ℂ) (hA : A.IsHermitian) :
    traceFunction φ A = ∑ i, φ (hA.eigenvalues i) := by
  rw [traceFunction, hA.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp

end Defs

section TraceFunction

private lemma eigenvalue_le_norm {d : ℕ} [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (i : Fin d) :
    hA.eigenvalues i ≤ ‖A‖ := by
  have h := spectrum.norm_le_norm_of_mem (hA.eigenvalues_mem_spectrum_real i)
  exact (le_abs_self _).trans (by simpa using h)

end TraceFunction

section Blocks

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
private lemma trace_fromBlocks_diag (P : Matrix m m ℂ) (Q : Matrix n n ℂ) :
    trace (fromBlocks P 0 0 Q) = trace P + trace Q := by
  simp [trace, Fintype.sum_sum_type]

/-- The scalar inequalities behind the block bounds. -/
private lemma scalar {t₁ t₂ n₁ n₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) (hn₁ : 0 ≤ n₁) (hn₂ : 0 ≤ n₂)
    (h₁ : n₁ = 0 → t₁ = 0) (h₂ : n₂ = 0 → t₂ = 0) :
    min (t₁ / n₁) (t₂ / n₂) ≤ (t₁ + t₂) / max n₁ n₂ ∧
      (t₁ + t₂) / max n₁ n₂ ≤ t₁ / n₁ + t₂ / n₂ := by
  rcases hn₁.eq_or_lt with e₁ | p₁
  · subst e₁
    have := h₁ rfl; subst this
    rw [max_eq_right hn₂]; simp
  rcases hn₂.eq_or_lt with e₂ | p₂
  · subst e₂
    have := h₂ rfl; subst this
    rw [max_eq_left hn₁]; simp
  rcases le_total n₂ n₁ with h | h
  · rw [max_eq_left h, add_div]
    refine ⟨?_, ?_⟩
    · exact (min_le_left _ _).trans (le_add_of_nonneg_right (div_nonneg ht₂ hn₁))
    · gcongr
  · rw [max_eq_right h, add_div]
    refine ⟨?_, ?_⟩
    · exact (min_le_right _ _).trans (le_add_of_nonneg_left (div_nonneg ht₁ hn₂))
    · gcongr

end Blocks

end NLAlib

open NLAlib

/-- For convex `φ` on `[0, ∞)` with `φ 0 = 0` and PSD `A`, `tr φ(A) ≤ intdim A · φ ‖A‖`.

Tropp 2015, Lemma 7.5.1. Atlas: `intrinsic-dimension`. Ported from the Prove2me mission *An
Introduction to Matrix Concentration Inequalities, Ch 7*. -/
theorem NLAlib.traceFunction_le_intrinsicDimension_mul {d : ℕ} [NeZero d]
    (φ : ℝ → ℝ) (hConvex : ConvexOn ℝ (Set.Ici 0) φ) (hZero : φ 0 = 0)
    (A : Matrix (Fin d) (Fin d) ℂ) (hPSD : A.PosSemidef) :
    traceFunction φ A ≤ intrinsicDimension A * φ (‖A‖) := by
  have hA : A.IsHermitian := hPSD.isHermitian
  rw [traceFunction_eq_sum φ A hA]
  have htr : (Matrix.trace A).re = ∑ i, hA.eigenvalues i := by
    rw [hA.trace_eq_sum_eigenvalues]
    simp
  have hnn : ∀ i, 0 ≤ hA.eigenvalues i := fun i => hPSD.eigenvalues_nonneg i
  have hle : ∀ i, hA.eigenvalues i ≤ ‖A‖ :=
    eigenvalue_le_norm A hA
  set N := ‖A‖ with hN
  rw [intrinsicDimension, ← hN, htr]
  have hN0 : 0 ≤ N := le_trans (hnn ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩) (hle _)
  rcases hN0.eq_or_lt with h0 | hpos
  · have : ∀ i, hA.eigenvalues i = 0 := fun i => le_antisymm (h0 ▸ hle i) (hnn i)
    simp [this, hZero, ← h0]
  · have key : ∀ i, φ (hA.eigenvalues i) ≤ (hA.eigenvalues i / N) * φ N := by
      intro i
      set x := hA.eigenvalues i
      have hb0 : 0 ≤ x / N := div_nonneg (hnn i) hpos.le
      have hb1 : x / N ≤ 1 := (div_le_one hpos).mpr (hle i)
      have h := hConvex.2 (Set.mem_Ici.mpr (le_refl (0:ℝ))) (Set.mem_Ici.mpr hpos.le)
        (by linarith : (0:ℝ) ≤ 1 - x / N) hb0 (by ring : 1 - x / N + x / N = 1)
      have hx : (1 - x / N) • (0 : ℝ) + (x / N) • N = x := by
        simp [smul_eq_mul]; field_simp
      rw [hx, hZero] at h
      simpa [smul_eq_mul] using h
    calc ∑ i, φ (hA.eigenvalues i) ≤ ∑ i, (hA.eigenvalues i / N) * φ N :=
          Finset.sum_le_sum (fun i _ => key i)
      _ = (∑ i, hA.eigenvalues i) / N * φ N := by
          rw [← Finset.sum_mul, Finset.sum_div]

/-- For positive semidefinite `V₁`, `V₂`, the block-diagonal `V = fromBlocks V₁ 0 0 V₂` is positive
semidefinite, `‖V‖ = max ‖V₁‖ ‖V₂‖`, and `intdim V` lies between `min (intdim V₁) (intdim V₂)` and
`intdim V₁ + intdim V₂`.

Tropp 2015, eq. (7.3.4) and §7.7.3. Atlas: `intrinsic-dimension`. Ported from the Prove2me mission
*An Introduction to Matrix Concentration Inequalities, Ch 7*. -/
theorem NLAlib.intrinsicDimension_fromBlocks {m n : ℕ} [NeZero m] [NeZero n]
    (V₁ : Matrix (Fin m) (Fin m) ℂ) (V₂ : Matrix (Fin n) (Fin n) ℂ)
    (hV₁ : V₁.PosSemidef) (hV₂ : V₂.PosSemidef) :
    let V := Matrix.fromBlocks V₁ 0 0 V₂
    V.PosSemidef ∧
    ‖V‖ = max (‖V₁‖) (‖V₂‖) ∧
    intrinsicDimension V =
      ((Matrix.trace V₁).re + (Matrix.trace V₂).re) /
        max (‖V₁‖) (‖V₂‖) ∧
    min (intrinsicDimension V₁) (intrinsicDimension V₂) ≤ intrinsicDimension V ∧
    intrinsicDimension V ≤ intrinsicDimension V₁ + intrinsicDimension V₂ := by
  intro V
  have hnorm : ‖V‖ = max (‖V₁‖) (‖V₂‖) :=
    norm_fromBlocks_diag V₁ V₂
  have hdim : intrinsicDimension V =
      ((Matrix.trace V₁).re + (Matrix.trace V₂).re) /
        max (‖V₁‖) (‖V₂‖) := by
    unfold intrinsicDimension
    rw [hnorm, show V = Matrix.fromBlocks V₁ 0 0 V₂ from rfl, trace_fromBlocks_diag,
      Complex.add_re]
  have hz : ∀ {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ), ‖A‖ = 0 →
      (Matrix.trace A).re = 0 := by
    intro k A h
    have : A = 0 := norm_eq_zero.mp h
    simp [this]
  have hs := scalar (Complex.nonneg_iff.mp hV₁.trace_nonneg).1
    (Complex.nonneg_iff.mp hV₂.trace_nonneg).1
    (norm_nonneg V₁) (norm_nonneg V₂) (hz V₁) (hz V₂)
  refine ⟨posSemidef_fromBlocks_diag hV₁ hV₂, hnorm, hdim, ?_, ?_⟩
  · rw [hdim]; exact hs.1
  · rw [hdim]; exact hs.2
