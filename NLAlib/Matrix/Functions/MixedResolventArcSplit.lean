import NLAlib.Matrix.Functions.MixedResolventDerivatives
import NLAlib.Matrix.Functions.CoefficientCrossingTrace
import NLAlib.Matrix.Functions.CoefficientCrossingResolvent
import NLAlib.Matrix.Norms.NormalizedModulusMoments
import Mathlib.Tactic.FinCases

/-! # Positive arc bookkeeping for genuine mixed-resolvent derivatives

Each differentiated inverse factor splits a mixed arc into two nonempty
arcs. Two such derivative insertions produce the four actual alternating
coefficient arcs used by the Gaussian covariance crossing estimate.
Source: arXiv:2108.06312v2, Lemma 6.3.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace NLAlib
open scoped Matrix MatrixOrder ComplexOrder

/-- Exponents of the arc preceding the differentiated factor. -/
def mixedResolventSplitLeft (a b : ℕ) : Fin (a + b) → ℕ × ℕ :=
  Fin.append (fun i : Fin a => (a - i, 0)) (fun j : Fin b => (a, b - j))

/-- Exponents of the arc following the differentiated factor. -/
def mixedResolventSplitRight (a b : ℕ) : Fin (a + b) → ℕ × ℕ :=
  Fin.append (fun i : Fin a => (i + 1, b)) (fun j : Fin b => (0, j + 1))

/-- Every genuine derivative split has two positive arc lengths and increases
the total inverse degree by exactly one. -/
theorem mixedResolventSplit_lengths (a b : ℕ) (i : Fin (a + b)) :
    0 < (mixedResolventSplitLeft a b i).1 + (mixedResolventSplitLeft a b i).2 ∧
    0 < (mixedResolventSplitRight a b i).1 + (mixedResolventSplitRight a b i).2 ∧
    (mixedResolventSplitLeft a b i).1 + (mixedResolventSplitLeft a b i).2 +
      ((mixedResolventSplitRight a b i).1 + (mixedResolventSplitRight a b i).2) = a + b + 1 := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [mixedResolventSplitLeft, mixedResolventSplitRight, Fin.append_left]
    have hj := j.isLt
    omega
  · simp only [mixedResolventSplitLeft, mixedResolventSplitRight, Fin.append_right]
    have hj := j.isLt
    omega

/-- First-shift powers in the four genuine arcs produced by two derivative
insertions, in their original alternating coefficient order. -/
def mixedResolventCrossingFirstPowers (a b c e : ℕ)
    (i : Fin (a + b)) (j : Fin (c + e)) : Fin 4 → ℕ :=
  ![(mixedResolventSplitLeft a b i).1, (mixedResolventSplitRight a b i).1,
    (mixedResolventSplitLeft c e j).1, (mixedResolventSplitRight c e j).1]

/-- Conjugate-shift powers in the four genuine derivative arcs. -/
def mixedResolventCrossingSecondPowers (a b c e : ℕ)
    (i : Fin (a + b)) (j : Fin (c + e)) : Fin 4 → ℕ :=
  ![(mixedResolventSplitLeft a b i).2, (mixedResolventSplitRight a b i).2,
    (mixedResolventSplitLeft c e j).2, (mixedResolventSplitRight c e j).2]

/-- The four actual derivative arcs are all nonempty and add exactly two to
the original pair's total inverse degree. -/
theorem mixedResolventCrossingPowers_lengths (a b c e : ℕ)
    (i : Fin (a + b)) (j : Fin (c + e)) :
    (∀ r : Fin 4, 0 < mixedResolventCrossingFirstPowers a b c e i j r +
      mixedResolventCrossingSecondPowers a b c e i j r) ∧
    (∑ r : Fin 4, (mixedResolventCrossingFirstPowers a b c e i j r +
      mixedResolventCrossingSecondPowers a b c e i j r)) = a + b + c + e + 2 := by
  have hi := mixedResolventSplit_lengths a b i
  have hj := mixedResolventSplit_lengths c e j
  have hisum := hi.2.2
  have hjsum := hj.2.2
  constructor
  · intro r
    fin_cases r
    · simpa [mixedResolventCrossingFirstPowers, mixedResolventCrossingSecondPowers] using hi.1
    · simpa [mixedResolventCrossingFirstPowers, mixedResolventCrossingSecondPowers] using hi.2.1
    · simpa [mixedResolventCrossingFirstPowers, mixedResolventCrossingSecondPowers] using hj.1
    · simpa [mixedResolventCrossingFirstPowers, mixedResolventCrossingSecondPowers] using hj.2.1
  · simp only [Fin.sum_univ_succ, mixedResolventCrossingFirstPowers,
      mixedResolventCrossingSecondPowers, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero]
    omega

variable {d : Type*} [Fintype d] [DecidableEq d]
local notation "M" => Matrix d d ℂ

/-- The two ordered derivative insertion sums are exactly the single finite
positive-arc split sum. This uses no commutativity or inverse hypothesis. -/
theorem mixed_power_insertion_sum_eq_sum_split (R S H : M) (a b : ℕ) :
    ((∑ i ∈ Finset.range a, R ^ (a - i) * H * R ^ (i + 1) * S ^ b) +
      ∑ j ∈ Finset.range b, R ^ a * S ^ (b - j) * H * S ^ (j + 1)) =
      ∑ i : Fin (a + b),
        (R ^ (mixedResolventSplitLeft a b i).1 * S ^ (mixedResolventSplitLeft a b i).2) * H *
          (R ^ (mixedResolventSplitRight a b i).1 * S ^ (mixedResolventSplitRight a b i).2) := by
  simp only [Fin.sum_univ_add, mixedResolventSplitLeft, mixedResolventSplitRight,
    Fin.append_left, Fin.append_right, pow_zero, one_mul, Matrix.mul_assoc]
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => R ^ (a - i) * (H * (R ^ (i + 1) * S ^ b))) a,
    Fin.sum_univ_eq_sum_range
    (fun j : ℕ => R ^ a * (S ^ (b - j) * (H * S ^ (j + 1)))) b]

open scoped Matrix.Norms.L2Operator in
/-- The exact mixed-power matrix derivative written with its actual finite
positive-arc split. No commutation involving the inserted coefficient is
assumed, and the two curves need not commute. -/
theorem hasDerivAt_mixed_powers_eq_sum_split
    {R S : ℝ → M} {t : ℝ} (H : M)
    (hR : HasDerivAt R (R t * H * R t) t)
    (hS : HasDerivAt S (S t * H * S t) t) (a b : ℕ) :
    HasDerivAt (fun u : ℝ => R u ^ a * S u ^ b)
      (∑ i : Fin (a + b),
        (R t ^ (mixedResolventSplitLeft a b i).1 * S t ^ (mixedResolventSplitLeft a b i).2) * H *
          (R t ^ (mixedResolventSplitRight a b i).1 * S t ^ (mixedResolventSplitRight a b i).2)) t := by
  have hd := hasDerivAt_mixed_powers_of_sandwich H hR hS a b
  exact hd.congr_deriv (mixed_power_insertion_sum_eq_sum_split (R t) (S t) H a b)

open scoped Matrix.Norms.L2Operator in
/-- Expanding the two genuine derivative insertion sums gives the literal
alternating coefficient crossing functional. Matrix order is unchanged;
the equality is finite bilinearity and cyclic normalization only. -/
theorem sum_trace_sandwich_sums_eq_sum_coefficientCrossingTraceMultilinear
    {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    [DecidableEq ι] [DecidableEq κ]
    (A : ι → M) (B : κ → M) (U V : α → M) (W Z : β → M) :
    (∑ i, ∑ j, (A i * (∑ l, U l * B j * V l) * A i *
      (∑ m, W m * B j * Z m)).trace) =
      ∑ l, ∑ m, coefficientCrossingTraceMultilinear A B ![U l, V l, W m, Z m] := by
  simp only [Finset.mul_sum, Finset.sum_mul, Matrix.trace_sum,
    coefficientCrossingTraceMultilinear_apply, coefficientCrossingSum,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.mul_assoc]
  calc
    (∑ i, ∑ j, ∑ m, ∑ l, (A i * (U l * (B j * (V l * (A i * (W m * (B j * Z m))))))).trace)
      = ∑ i, ∑ j, ∑ l, ∑ m,
          (A i * (U l * (B j * (V l * (A i * (W m * (B j * Z m))))))).trace := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact Finset.sum_comm
    _
      = ∑ i, ∑ l, ∑ j, ∑ m,
          (A i * (U l * (B j * (V l * (A i * (W m * (B j * Z m))))))).trace := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
    _ = ∑ l, ∑ i, ∑ j, ∑ m,
        (A i * (U l * (B j * (V l * (A i * (W m * (B j * Z m))))))).trace := Finset.sum_comm
    _ = ∑ l, ∑ i, ∑ m, ∑ j,
        (A i * (U l * (B j * (V l * (A i * (W m * (B j * Z m))))))).trace := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ l, ∑ m, ∑ i, ∑ j,
        (A i * (U l * (B j * (V l * (A i * (W m * (B j * Z m))))))).trace := by
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.sum_comm

open scoped Matrix.Norms.L2Operator in
/-- The normalized genuine derivative crossing has exactly one reciprocal
dimension factor on the actual crossing functional. -/
theorem sum_normalizedTrace_sandwich_sums_eq_inv_card_mul_sum_crossing
    {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    [DecidableEq ι] [DecidableEq κ]
    (A : ι → M) (B : κ → M) (U V : α → M) (W Z : β → M) :
    (∑ i, ∑ j, normalizedTrace (A i * (∑ l, U l * B j * V l) * A i *
      (∑ m, W m * B j * Z m))) =
      (Fintype.card d : ℂ)⁻¹ *
        ∑ l, ∑ m, coefficientCrossingTraceMultilinear A B ![U l, V l, W m, Z m] := by
  have h := sum_trace_sandwich_sums_eq_sum_coefficientCrossingTraceMultilinear A B U V W Z
  simpa only [normalizedTrace, Finset.mul_sum] using
    congrArg (fun z : ℂ => (Fintype.card d : ℂ)⁻¹ * z) h

open scoped Matrix.Norms.L2Operator in
/-- Normalization of the actual four-arc crossing estimate divides every
ordinary trace by the same dimension; empty matrices use their native zero
normalization and require no exceptional hypothesis. -/
theorem norm_inv_card_mul_coefficientCrossingTrace_resolvent_le_sum_normalizedTrace
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : ι → M) (B : κ → M) (hA : ∀ i, (A i).IsHermitian)
    (hB : ∀ j, (B j).IsHermitian) (X : Fin 4 → M) (hX : ∀ j, (X j).IsHermitian)
    (ζ : ℂ) (a b : Fin 4 → ℕ) {L : ℕ} (hL : ∑ j, (a j + b j) = L)
    (hLpos : 0 < L) (hArc : ∀ j, 0 < a j + b j) :
    ‖(Fintype.card d : ℂ)⁻¹ * coefficientCrossingTraceMultilinear A B
      (fun j => resolvent (X j) ζ ^ a j * resolvent (X j) (star ζ) ^ b j)‖ ≤
      (Real.sqrt (specNorm (coefficientVariance A)) *
        Real.sqrt (specNorm (coefficientCovariance A)) *
        Real.sqrt (specNorm (coefficientCovariance B)) *
        Real.sqrt (specNorm (coefficientVariance B))) *
        ∑ j, (((a j + b j : ℕ) : ℝ) / L) *
          (normalizedTrace (CFC.abs (resolvent (X j) ζ) ^ L)).re := by
  have htrace (j : Fin 4) : (CFC.abs (resolvent (X j) ζ) ^ L).trace.re /
      (Fintype.card d : ℝ) = (normalizedTrace (CFC.abs (resolvent (X j) ζ) ^ L)).re := by
    have h := re_normalizedTrace_cfcAbs_pow_eq_sum_div_card (resolvent (X j) ζ) L
    rw [← re_trace_cfcAbs_pow_eq_sum_singularValues (resolvent (X j) ζ) L] at h
    simpa only [RCLike.re_eq_complex_re] using h.symm
  rw [norm_mul, norm_inv, Complex.norm_natCast, mul_comm, ← div_eq_mul_inv]
  have h := div_le_div_of_nonneg_right
    (norm_coefficientCrossingTraceMultilinear_resolvent_le_sum_trace
      A B hA hB X hX ζ a b hL hLpos hArc) (Nat.cast_nonneg (α := ℝ) (Fintype.card d))
  simpa only [mul_div_assoc, Finset.sum_div, htrace] using h

end NLAlib
