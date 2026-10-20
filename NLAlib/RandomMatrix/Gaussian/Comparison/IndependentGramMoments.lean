import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import NLAlib.ForMathlib.LinearAlgebra.Matrix.TraceWords
import NLAlib.ForMathlib.Combinatorics.BipartiteLeafSum
import NLAlib.Probability.Gaussian.Comparison.IndependentMoments
import NLAlib.RandomMatrix.Gaussian.Basic.GaussianMatrix
import NLAlib.RandomMatrix.Gaussian.Moments.FourthMoment

/-!
# Independent-entry Gram trace moment comparison

For a real `m × n` matrix `A` and `p ≥ 1`, the trace of its `p`-th Gram power
`tr ((A Aᴴ)^p)` expands into the sum over all row assignments
`r : Fin p → m` and column assignments `c : Fin p → n` of the closed
entry product `∏ t, A (r t) (c t) * A (r (finRotate p t)) (c t)`.
Regrouping the entries of the `2p` occurrences by `m × n` kind gives a
sum of monomials in the entries of `A`, with the deterministic profile
`b` absorbed into the nonnegative coefficients.

For independent symmetric real entries `X ij` whose even moments are
dominated by the standard Gaussian even moments, and a deterministic
nonnegative profile `b`, the moment comparison gives

```
∫ tr (((b .* X) (b .* X)ᴴ)^p) ≤ ∫ tr (((b .* G) (b .* G)ᴴ)^p)
```

with `G` having the genuine `gaussianMatrix m n` law. The case `p = 0`
is included separately: both sides equal the row count `Fintype.card m`.

The integrability of both Gram-trace integrands is exposed explicitly for
every natural `p`, including `p = 0`; it follows from the integrability of
the underlying monomial products in the matrix entries.

This is the finite trace expansion and independent-moment comparison step
supporting `independent-entry-gaussian-extremum` and
`independent-entry-small-deviation`. The Gaussian comparator retains the
original profile and dimensions; comparison with a smaller iid matrix and
eventwise tail bounds are separate results.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- The occurrence kind of each of the `2(q+1)` edges of the closed
`(q+1)`-cycle Gram trace expansion with row assignment `r` and column
assignment `c`: `Sum.inl t` is the left factor `A (r t) (c t)` and
`Sum.inr t` the right factor `A (r (finRotate (q+1) t)) (c t)`. -/
def gramOccurrenceIdx (q : ℕ)
    (r : Fin (q + 1) → m) (c : Fin (q + 1) → n) :
    Fin (q + 1) ⊕ Fin (q + 1) → m × n := fun x =>
  match x with
  | Sum.inl t => (r t, c t)
  | Sum.inr t => (r (finRotate (q + 1) t), c t)

/-- Number of occurrences of the entry `e` among the `2(q+1)` edges of the
closed `(q+1)`-cycle Gram trace expansion with row assignment `r` and
column assignment `c`. -/
def gramOccurrenceCount (q : ℕ)
    (r : Fin (q + 1) → m) (c : Fin (q + 1) → n) (e : m × n) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin (q + 1) ⊕ Fin (q + 1))).filter
    (fun x => gramOccurrenceIdx q r c x = e)).card

/-- The closed entry product of the Gram trace expansion equals the
regrouped product over `m × n` entry kinds. -/
theorem prod_gram_entries_eq_prod_pow_gramOccurrenceCount
    (A : Matrix m n ℝ) (q : ℕ)
    (v : Fin (q + 1) → m) (c : Fin (q + 1) → n) :
    (∏ t : Fin (q + 1), A (v t) (c t) * A (v (finRotate (q + 1) t)) (c t)) =
      ∏ e : m × n, A e.1 e.2 ^ gramOccurrenceCount q v c e := by
  classical
  let f : Fin (q + 1) → ℝ := fun t => A (v t) (c t)
  let g : Fin (q + 1) → ℝ := fun t => A (v (finRotate (q + 1) t)) (c t)
  calc
    (∏ t : Fin (q + 1), A (v t) (c t) * A (v (finRotate (q + 1) t)) (c t))
        = (∏ t : Fin (q + 1), f t) * (∏ t : Fin (q + 1), g t) := by
          simp [f, g, Finset.prod_mul_distrib]
    _ = ∏ x : Fin (q + 1) ⊕ Fin (q + 1), Sum.elim f g x := by
          exact (Fintype.prod_sumElim f g).symm
    _ = ∏ x : Fin (q + 1) ⊕ Fin (q + 1),
          A (gramOccurrenceIdx q v c x).1 (gramOccurrenceIdx q v c x).2 := by
          apply Finset.prod_congr rfl
          intro x _
          cases x <;> simp [gramOccurrenceIdx, f, g]
    _ = ∏ e : m × n,
          A e.1 e.2 ^ ((Finset.univ : Finset (Fin (q + 1) ⊕ Fin (q + 1))).filter (fun x => gramOccurrenceIdx q v c x = e)).card := by
          exact Fintype.prod_fiber_pow (R := Fin (q + 1) ⊕ Fin (q + 1)) (E := m × n)
            (idx := gramOccurrenceIdx q v c) (z := fun e : m × n => A e.1 e.2)
    _ = ∏ e : m × n, A e.1 e.2 ^ gramOccurrenceCount q v c e := by
          apply Finset.prod_congr rfl
          intro e _
          simp [gramOccurrenceCount]

/-- The trace of `(A Aᴴ)^(q+1)` is the exact finite sum over row and
column assignments of the regrouped monomial in the entries of `A`. -/
theorem trace_mul_conjTranspose_pow_eq_sum_gramOccurrence
    (A : Matrix m n ℝ) (q : ℕ) :
    ((A * Aᴴ) ^ (q + 1)).trace =
      ∑ r : Fin (q + 1) → m, ∑ c : Fin (q + 1) → n,
        ∏ e : m × n, A e.1 e.2 ^ gramOccurrenceCount q r c e := by
  classical
  have hpow : ((A * Aᴴ) ^ (q + 1)).trace =
      (List.ofFn (fun _ : Fin (q + 1) => A * Aᴴ)).prod.trace := by
    congr 1
    rw [List.ofFn_const, List.prod_replicate]
  have hmul : ∀ i j, (A * Aᴴ) i j = ∑ k : n, A i k * A j k := by
    intro i j
    simp [Matrix.mul_apply]
  have hprodsum : ∀ v : Fin (q + 1) → m,
      (∏ t : Fin (q + 1), ∑ k : n, A (v t) k * A (v (finRotate (q + 1) t)) k) =
        ∑ c : Fin (q + 1) → n, ∏ t : Fin (q + 1),
          A (v t) (c t) * A (v (finRotate (q + 1) t)) (c t) := by
    intro v
    calc
      (∏ t : Fin (q + 1), ∑ k : n, A (v t) k * A (v (finRotate (q + 1) t)) k)
          = ∏ t : Fin (q + 1), ∑ k ∈ (Finset.univ : Finset n),
              A (v t) k * A (v (finRotate (q + 1) t)) k := by simp
      _ = ∑ c ∈ Fintype.piFinset (fun _ : Fin (q + 1) => (Finset.univ : Finset n)),
            ∏ t : Fin (q + 1), A (v t) (c t) * A (v (finRotate (q + 1) t)) (c t) := by
            exact Finset.prod_univ_sum (fun _ : Fin (q + 1) => (Finset.univ : Finset n))
              (fun t k => A (v t) k * A (v (finRotate (q + 1) t)) k)
      _ = ∑ c : Fin (q + 1) → n, ∏ t : Fin (q + 1),
            A (v t) (c t) * A (v (finRotate (q + 1) t)) (c t) := by simp
  rw [hpow, Matrix.trace_list_ofFn_prod_eq_sum_cyclic (R := ℝ) (m := q) (n := m)
    (A := fun _ : Fin (q + 1) => A * Aᴴ)]
  simp_rw [hmul]
  apply Finset.sum_congr rfl
  intro v _
  rw [hprodsum v]
  apply Finset.sum_congr rfl
  intro c _
  exact prod_gram_entries_eq_prod_pow_gramOccurrenceCount A q v c

/-- The coefficient of a monomial in the entries of the independent matrix
in the expanded Gram trace: the profile powers for the occurrences of each
entry. -/
private def gramCoeff (b : m → n → ℝ) (q : ℕ)
    (r : Fin (q + 1) → m) (c : Fin (q + 1) → n) : ℝ :=
  ∏ e : m × n, b e.1 e.2 ^ gramOccurrenceCount q r c e

/-- Profile coefficients are nonnegative for a nonnegative profile. -/
private lemma gramCoeff_nonneg {b : m → n → ℝ}
    (hb : ∀ e : m × n, 0 ≤ b e.1 e.2) (q : ℕ)
    (r : Fin (q + 1) → m) (c : Fin (q + 1) → n) :
    0 ≤ gramCoeff b q r c := by
  unfold gramCoeff
  exact Finset.prod_nonneg (fun e _ => pow_nonneg (hb e) _)

/-- For `A = b .* X` the expanded Gram trace is the weighted sum of
monomials in the entries of `X`. -/
private theorem trace_gram_pow_eq_sum_coeff_mul_monomial
    (b X : m → n → ℝ) (q : ℕ) :
    (((Matrix.of (fun i j => b i j * X i j)) *
        (Matrix.of (fun i j => b i j * X i j))ᴴ) ^ (q + 1)).trace =
      ∑ r : Fin (q + 1) → m, ∑ c : Fin (q + 1) → n,
        gramCoeff b q r c * ∏ e : m × n,
          X e.1 e.2 ^ gramOccurrenceCount q r c e := by
  classical
  rw [trace_mul_conjTranspose_pow_eq_sum_gramOccurrence (A := Matrix.of (fun i j => b i j * X i j))]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro c _
  simp only [Matrix.of_apply]
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  rfl

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : m → n → Ω → ℝ}

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- Symmetry together with finite even moments gives finite natural moments
for every entry of the independent matrix. -/
private lemma hasFiniteNatMoments_entry_of_symm_even
    {e : m × n}
    (hsym : IdentDistrib (X e.1 e.2) (fun w => -X e.1 e.2 w) μ μ)
    (h2 : ∀ p, 0 < p → Integrable (fun w => (X e.1 e.2 w) ^ (2 * p)) μ) :
    HasFiniteNatMoments (fun w => X e.1 e.2 w) μ := by
  intro p
  cases p with
  | zero =>
    simp
  | succ p =>
    have hmeas := hsym.aemeasurable_fst.aestronglyMeasurable.pow (p + 1)
    have hsq : Integrable (fun w => ((X e.1 e.2 w) ^ (p + 1)) ^ 2) μ := by
      simpa only [← pow_mul, Nat.mul_comm] using h2 (p + 1) (Nat.succ_pos p)
    exact ((memLp_two_iff_integrable_sq hmeas).2 hsq).integrable (by norm_num)

/-- Monomial products in the entries of the independent matrix are integrable
as soon as every entry has finite natural moments. -/
private lemma integrable_prod_gramOccurrenceCount
    (hsym : ∀ e : m × n, IdentDistrib (X e.1 e.2) (fun w => -X e.1 e.2 w) μ μ)
    (h2 : ∀ e : m × n, ∀ p, 0 < p →
      Integrable (fun w => (X e.1 e.2 w) ^ (2 * p)) μ)
    (q : ℕ) (r : Fin (q + 1) → m) (c : Fin (q + 1) → n) :
    Integrable (fun w => ∏ e : m × n,
      (X e.1 e.2 w) ^ gramOccurrenceCount q r c e) μ := by
  have hf : ∀ e ∈ (Finset.univ : Finset (m × n)),
      HasFiniteNatMoments (fun w => (X e.1 e.2 w) ^ gramOccurrenceCount q r c e) μ := fun e _ =>
    (hasFiniteNatMoments_entry_of_symm_even (hsym e) (fun p hp => h2 e p hp)).pow
      (gramOccurrenceCount q r c e)
  exact (HasFiniteNatMoments.prod (Finset.univ) hf).integrable

/-- Weighted Gram monomials in the independent entries are integrable. -/
private lemma integrable_mul_prod_gramOccurrenceCount
    (hsym : ∀ e : m × n, IdentDistrib (X e.1 e.2) (fun w => -X e.1 e.2 w) μ μ)
    (h2 : ∀ e : m × n, ∀ p, 0 < p →
      Integrable (fun w => (X e.1 e.2 w) ^ (2 * p)) μ)
    (b : m → n → ℝ) (q : ℕ)
    (r : Fin (q + 1) → m) (c : Fin (q + 1) → n) :
    Integrable (fun w => gramCoeff b q r c * ∏ e : m × n,
      (X e.1 e.2 w) ^ gramOccurrenceCount q r c e) μ :=
  (integrable_prod_gramOccurrenceCount hsym h2 q r c).const_mul (gramCoeff b q r c)

/-- The expanded Gram trace of `b .* X` is integrable. -/
private theorem integrable_trace_gram_pow
    (hsym : ∀ e : m × n, IdentDistrib (X e.1 e.2) (fun w => -X e.1 e.2 w) μ μ)
    (h2 : ∀ e : m × n, ∀ p, 0 < p →
      Integrable (fun w => (X e.1 e.2 w) ^ (2 * p)) μ)
    (b : m → n → ℝ) (q : ℕ) :
    Integrable (fun w => (((Matrix.of (fun i j => b i j * X i j w)) *
        (Matrix.of (fun i j => b i j * X i j w))ᴴ) ^ (q + 1)).trace) μ := by
  have h : (fun w => (((Matrix.of (fun i j => b i j * X i j w)) *
        (Matrix.of (fun i j => b i j * X i j w))ᴴ) ^ (q + 1)).trace) =
      fun w => ∑ r : Fin (q + 1) → m, ∑ c : Fin (q + 1) → n,
        gramCoeff b q r c * ∏ e : m × n,
          (X e.1 e.2 w) ^ gramOccurrenceCount q r c e := by
    funext w
    exact trace_gram_pow_eq_sum_coeff_mul_monomial (b := b) (X := fun i j => X i j w) q
  rw [h]
  exact integrable_finsetSum Finset.univ (fun r _ =>
    integrable_finsetSum Finset.univ (fun c _ =>
      integrable_mul_prod_gramOccurrenceCount hsym h2 b q r c))

omit [DecidableEq n] in
/-- The `p = 0` Gram trace integrand on the independent side is integrable
(it equals the constant row count). -/
private theorem integrable_trace_gram_pow_zero
    (b : m → n → ℝ) :
    Integrable (fun w => (((Matrix.of (fun i j => b i j * X i j w)) *
        (Matrix.of (fun i j => b i j * X i j w))ᴴ) ^ 0).trace) μ := by
  have h : (fun w => (((Matrix.of (fun i j => b i j * X i j w)) *
        (Matrix.of (fun i j => b i j * X i j w))ᴴ) ^ 0).trace) =
      fun _ : Ω => (Fintype.card m : ℝ) := by
    funext w
    simp [Matrix.trace_one]
  rw [h]
  exact (integrable_const (α := Ω) (β := ℝ) (μ := μ)
    (c := ((Fintype.card m : ℕ) : ℝ)))

/-- The profiled Gram trace is integrable for every natural power, including
zero, when the entries are symmetric and have finite even moments.
Independence, Gaussian moment bounds, and a nonnegative profile are unnecessary. -/
theorem integrable_trace_gram_pow_nat
    (hsym : ∀ e : m × n, IdentDistrib (X e.1 e.2) (fun w => -X e.1 e.2 w) μ μ)
    (h2 : ∀ e : m × n, ∀ p, 0 < p →
      Integrable (fun w => (X e.1 e.2 w) ^ (2 * p)) μ)
    (b : m → n → ℝ) (p : ℕ) :
    Integrable (fun w => (((Matrix.of (fun i j => b i j * X i j w)) *
        (Matrix.of (fun i j => b i j * X i j w))ᴴ) ^ p).trace) μ := by
  cases p with
  | zero => exact integrable_trace_gram_pow_zero b
  | succ q => exact integrable_trace_gram_pow hsym h2 b q

/-- **Independent-entry Gram trace moment comparison (vector form)**: for
independent symmetric real entries with Gaussian-dominated even moments and
a deterministic nonnegative profile `b`,
`∫ tr ((b .* X)(b .* X)ᴴ)^(q+1) ≤ ∫` of the matching monomial sum against
the standard Gaussian vector law on `m × n`, which is the curried
`gaussianMatrix m n` law. -/
private theorem integral_trace_gram_pow_le_integral_gaussianVector
    (hX : iIndepFun (fun e : m × n => X e.1 e.2) μ)
    (hsym : ∀ e : m × n, IdentDistrib (X e.1 e.2) (fun w => -X e.1 e.2 w) μ μ)
    (h2 : ∀ e : m × n, ∀ p, 0 < p →
      Integrable (fun w => (X e.1 e.2 w) ^ (2 * p)) μ ∧
      ∫ w, (X e.1 e.2 w) ^ (2 * p) ∂μ ≤ gaussianEvenMoment p)
    (b : m → n → ℝ) (hb : ∀ e : m × n, 0 ≤ b e.1 e.2)
    (q : ℕ) :
    ∫ w, (((Matrix.of (fun i j => b i j * X i j w)) *
        (Matrix.of (fun i j => b i j * X i j w))ᴴ) ^ (q + 1)).trace ∂μ ≤
      ∫ x : m × n → ℝ, ∑ r : Fin (q + 1) → m, ∑ c : Fin (q + 1) → n,
        gramCoeff b q r c * ∏ e : m × n,
          x e ^ gramOccurrenceCount q r c e ∂(gaussianVector (m × n)) := by
  calc
    ∫ w, (((Matrix.of (fun i j => b i j * X i j w)) *
          (Matrix.of (fun i j => b i j * X i j w))ᴴ) ^ (q + 1)).trace ∂μ
        = ∫ w, ∑ r : Fin (q + 1) → m, ∑ c : Fin (q + 1) → n,
            gramCoeff b q r c * ∏ e : m × n,
              (X e.1 e.2 w) ^ gramOccurrenceCount q r c e ∂μ := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro w
      dsimp only
      exact trace_gram_pow_eq_sum_coeff_mul_monomial (b := b) (X := fun i j => X i j w) q
    _ ≤ ∫ x : m × n → ℝ, ∑ r : Fin (q + 1) → m, ∑ c : Fin (q + 1) → n,
          gramCoeff b q r c * ∏ e : m × n,
            x e ^ gramOccurrenceCount q r c e ∂(gaussianVector (m × n)) := by
      have hle := integral_sum_mul_prod_pow_le_integral_sum_mul_prod_pow_gaussianVector
        (E := m × n) (τ := (Fin (q + 1) → m) × (Fin (q + 1) → n))
        (X := fun e : m × n => X e.1 e.2)
        hX hsym h2
        (c := fun rc => gramCoeff b q rc.1 rc.2)
        (k := fun rc e => gramOccurrenceCount q rc.1 rc.2 e)
        (hc := fun rc => gramCoeff_nonneg hb q rc.1 rc.2)
      convert hle using 1
      · apply integral_congr_ae
        refine Filter.Eventually.of_forall ?_
        intro w
        dsimp only
        exact (Fintype.sum_prod_type' (f := fun r c =>
          gramCoeff b q r c * ∏ e : m × n,
            (X e.1 e.2 w) ^ gramOccurrenceCount q r c e)).symm
      · apply integral_congr_ae
        refine Filter.Eventually.of_forall ?_
        intro x
        dsimp only
        exact (Fintype.sum_prod_type' (f := fun r c =>
          gramCoeff b q r c * ∏ e : m × n, x e ^ gramOccurrenceCount q r c e)).symm

/-- The Gaussian-matrix moment of the Gram trace equals the monomial-sum
moment against the standard Gaussian vector law on `m × n`. -/
private theorem integral_trace_gram_pow_gaussianMatrix_eq_integral_gaussianVector_monomial
    (b : m → n → ℝ) (q : ℕ) :
    (∫ G : Matrix m n ℝ,
        (((Matrix.of (fun i j => b i j * G i j)) *
            (Matrix.of (fun i j => b i j * G i j))ᴴ) ^ (q + 1)).trace
        ∂(gaussianMatrix m n)) =
      ∫ x : m × n → ℝ, ∑ r : Fin (q + 1) → m, ∑ c : Fin (q + 1) → n,
        gramCoeff b q r c * ∏ e : m × n,
          x e ^ gramOccurrenceCount q r c e ∂(gaussianVector (m × n)) := by
  let e : MeasurableEquiv (m × n → ℝ) (Matrix m n ℝ) :=
    (MeasurableEquiv.curry m n ℝ).trans Matrix.ofMeasurableEquiv
  have hmp : MeasurePreserving e (gaussianVector (m × n)) (gaussianMatrix m n) :=
    ⟨e.measurable, gaussianMatrix_eq_map_curry.symm⟩
  calc
    ∫ G : Matrix m n ℝ,
        (((Matrix.of (fun i j => b i j * G i j)) *
            (Matrix.of (fun i j => b i j * G i j))ᴴ) ^ (q + 1)).trace
        ∂(gaussianMatrix m n)
        = ∫ x : m × n → ℝ,
            (((Matrix.of (fun i j => b i j * (e x) i j)) *
                (Matrix.of (fun i j => b i j * (e x) i j))ᴴ) ^ (q + 1)).trace
            ∂(gaussianVector (m × n)) := by
          exact (hmp.integral_comp' (fun G : Matrix m n ℝ =>
            (((Matrix.of (fun i j => b i j * G i j)) *
                (Matrix.of (fun i j => b i j * G i j))ᴴ) ^ (q + 1)).trace)).symm
    _ = ∫ x : m × n → ℝ, ∑ r : Fin (q + 1) → m, ∑ c : Fin (q + 1) → n,
          gramCoeff b q r c * ∏ e : m × n,
            x e ^ gramOccurrenceCount q r c e ∂(gaussianVector (m × n)) := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro x
      dsimp only
      simp only [e, MeasurableEquiv.trans_apply, Matrix.coe_ofMeasurableEquiv,
        MeasurableEquiv.curry_apply, Matrix.of_apply]
      rw [trace_gram_pow_eq_sum_coeff_mul_monomial (b := b) (X := fun i j => x (i, j)) q]

/-- Monomial products in the entries of the Gaussian matrix are integrable
under the genuine `gaussianMatrix m n` law. -/
private lemma integrable_prod_gramOccurrenceCount_gaussianMatrix
    (q : ℕ) (r : Fin (q + 1) → m) (c : Fin (q + 1) → n) :
    Integrable (fun G : Matrix m n ℝ => ∏ e : m × n,
      G e.1 e.2 ^ gramOccurrenceCount q r c e) (gaussianMatrix m n) := by
  exact integrable_prod_entry_gaussianMatrix (p := m) (m := n)
    (f := fun e : m × n => fun x : ℝ => x ^ gramOccurrenceCount q r c e)
    (fun e => integrable_pow_gaussianReal (gramOccurrenceCount q r c e))

/-- Weighted Gram monomials in the entries of the Gaussian matrix are
integrable under `gaussianMatrix m n`. -/
private lemma integrable_mul_prod_gramOccurrenceCount_gaussianMatrix
    (b : m → n → ℝ) (q : ℕ)
    (r : Fin (q + 1) → m) (c : Fin (q + 1) → n) :
    Integrable (fun G : Matrix m n ℝ => gramCoeff b q r c * ∏ e : m × n,
      G e.1 e.2 ^ gramOccurrenceCount q r c e) (gaussianMatrix m n) :=
  (integrable_prod_gramOccurrenceCount_gaussianMatrix q r c).const_mul (gramCoeff b q r c)

/-- The expanded Gram trace of `b .* G` is integrable under the genuine
`gaussianMatrix m n` law. -/
private theorem integrable_trace_gram_pow_gaussianMatrix
    (b : m → n → ℝ) (q : ℕ) :
    Integrable (fun G : Matrix m n ℝ =>
      (((Matrix.of (fun i j => b i j * G i j)) *
          (Matrix.of (fun i j => b i j * G i j))ᴴ) ^ (q + 1)).trace)
      (gaussianMatrix m n) := by
  have h : (fun G : Matrix m n ℝ =>
      (((Matrix.of (fun i j => b i j * G i j)) *
          (Matrix.of (fun i j => b i j * G i j))ᴴ) ^ (q + 1)).trace) =
      fun G : Matrix m n ℝ => ∑ r : Fin (q + 1) → m, ∑ c : Fin (q + 1) → n,
        gramCoeff b q r c * ∏ e : m × n,
          G e.1 e.2 ^ gramOccurrenceCount q r c e := by
    funext G
    exact trace_gram_pow_eq_sum_coeff_mul_monomial (b := b) (X := fun i j => G i j) q
  rw [h]
  exact integrable_finsetSum Finset.univ (fun r _ =>
    integrable_finsetSum Finset.univ (fun c _ =>
      integrable_mul_prod_gramOccurrenceCount_gaussianMatrix b q r c))

omit [DecidableEq n] in
/-- The `p = 0` Gram trace integrand on the Gaussian-matrix side is
integrable (it equals the constant row count). -/
private theorem integrable_trace_gram_pow_zero_gaussianMatrix
    (b : m → n → ℝ) :
    Integrable (fun G : Matrix m n ℝ =>
      (((Matrix.of (fun i j => b i j * G i j)) *
          (Matrix.of (fun i j => b i j * G i j))ᴴ) ^ 0).trace)
      (gaussianMatrix m n) := by
  have h : (fun G : Matrix m n ℝ =>
      (((Matrix.of (fun i j => b i j * G i j)) *
          (Matrix.of (fun i j => b i j * G i j))ᴴ) ^ 0).trace) =
      fun _ : Matrix m n ℝ => (Fintype.card m : ℝ) := by
    funext G
    simp [Matrix.trace_one]
  rw [h]
  exact (integrable_const (α := Matrix m n ℝ) (β := ℝ) (μ := gaussianMatrix m n)
    (c := ((Fintype.card m : ℕ) : ℝ)))

/-- The Gram trace integrand on the Gaussian-matrix side is integrable for
every natural power `p`, including `p = 0`, with any real profile.
Empty row and column index types are included. -/
theorem integrable_trace_gram_pow_gaussianMatrix_nat
    (b : m → n → ℝ) (p : ℕ) :
    Integrable (fun G : Matrix m n ℝ =>
      (((Matrix.of (fun i j => b i j * G i j)) *
          (Matrix.of (fun i j => b i j * G i j))ᴴ) ^ p).trace)
      (gaussianMatrix m n) := by
  cases p with
  | zero => exact integrable_trace_gram_pow_zero_gaussianMatrix b
  | succ q => exact integrable_trace_gram_pow_gaussianMatrix b q

/-- **Independent-entry Gram trace moment comparison**: for independent
symmetric real entries with Gaussian-dominated even moments and a
deterministic nonnegative profile `b`, the `(q+1)`-th Gram trace moment
of `b .* X` is at most the same moment of `b .* G`, where `G` has the
genuine `gaussianMatrix m n` law. -/
private theorem integral_trace_gram_pow_le_integral_gaussianMatrix
    (hX : iIndepFun (fun e : m × n => X e.1 e.2) μ)
    (hsym : ∀ e : m × n, IdentDistrib (X e.1 e.2) (fun w => -X e.1 e.2 w) μ μ)
    (h2 : ∀ e : m × n, ∀ p, 0 < p →
      Integrable (fun w => (X e.1 e.2 w) ^ (2 * p)) μ ∧
      ∫ w, (X e.1 e.2 w) ^ (2 * p) ∂μ ≤ gaussianEvenMoment p)
    (b : m → n → ℝ) (hb : ∀ e : m × n, 0 ≤ b e.1 e.2)
    (q : ℕ) :
    ∫ w, (((Matrix.of (fun i j => b i j * X i j w)) *
        (Matrix.of (fun i j => b i j * X i j w))ᴴ) ^ (q + 1)).trace ∂μ ≤
      ∫ G : Matrix m n ℝ,
        (((Matrix.of (fun i j => b i j * G i j)) *
            (Matrix.of (fun i j => b i j * G i j))ᴴ) ^ (q + 1)).trace
        ∂(gaussianMatrix m n) := by
  calc
    ∫ w, (((Matrix.of (fun i j => b i j * X i j w)) *
          (Matrix.of (fun i j => b i j * X i j w))ᴴ) ^ (q + 1)).trace ∂μ
        ≤ ∫ x : m × n → ℝ, ∑ r : Fin (q + 1) → m, ∑ c : Fin (q + 1) → n,
            gramCoeff b q r c * ∏ e : m × n,
              x e ^ gramOccurrenceCount q r c e ∂(gaussianVector (m × n)) :=
          integral_trace_gram_pow_le_integral_gaussianVector hX hsym h2 b hb q
    _ = ∫ G : Matrix m n ℝ,
          (((Matrix.of (fun i j => b i j * G i j)) *
              (Matrix.of (fun i j => b i j * G i j))ᴴ) ^ (q + 1)).trace
          ∂(gaussianMatrix m n) := by
          rw [integral_trace_gram_pow_gaussianMatrix_eq_integral_gaussianVector_monomial b q]

omit [DecidableEq n] in
/-- The `p = 0` case of the independent-entry Gram trace moment comparison:
both sides equal the row count `Fintype.card m`. -/
private theorem integral_trace_gram_pow_zero_le_integral_gaussianMatrix
    (b : m → n → ℝ) :
    ∫ w, (((Matrix.of (fun i j => b i j * X i j w)) *
        (Matrix.of (fun i j => b i j * X i j w))ᴴ) ^ 0).trace ∂μ ≤
      ∫ G : Matrix m n ℝ,
        (((Matrix.of (fun i j => b i j * G i j)) *
            (Matrix.of (fun i j => b i j * G i j))ᴴ) ^ 0).trace
        ∂(gaussianMatrix m n) := by
  have hleft : (∫ w, (((Matrix.of (fun i j => b i j * X i j w)) *
        (Matrix.of (fun i j => b i j * X i j w))ᴴ) ^ 0).trace ∂μ) =
      (Fintype.card m : ℝ) := by
    simp [Matrix.trace_one]
  have hright :
      (∫ G : Matrix m n ℝ,
        (((Matrix.of (fun i j => b i j * G i j)) *
            (Matrix.of (fun i j => b i j * G i j))ᴴ) ^ 0).trace
        ∂(gaussianMatrix m n)) = (Fintype.card m : ℝ) := by
    simp [Matrix.trace_one]
  rw [hleft, hright]

/-- **Independent-entry Gram trace moment comparison, every natural power**:
for independent symmetric real entries with Gaussian-dominated even moments
and a deterministic nonnegative profile `b`, for every natural `p`,
`∫ tr (((b .* X)(b .* X)ᴴ)^p) ≤ ∫ tr (((b .* G)(b .* G)ᴴ)^p)` with `G` of law
`gaussianMatrix m n`. The case `p = 0` and empty index types are included.
The integrands are integrable by `integrable_trace_gram_pow_nat` and
`integrable_trace_gram_pow_gaussianMatrix_nat`; this is a moment comparison,
not eventwise stochastic domination. -/
theorem integral_trace_gram_pow_le_integral_gaussianMatrix_nat
    (hX : iIndepFun (fun e : m × n => X e.1 e.2) μ)
    (hsym : ∀ e : m × n, IdentDistrib (X e.1 e.2) (fun w => -X e.1 e.2 w) μ μ)
    (h2 : ∀ e : m × n, ∀ p, 0 < p →
      Integrable (fun w => (X e.1 e.2 w) ^ (2 * p)) μ ∧
      ∫ w, (X e.1 e.2 w) ^ (2 * p) ∂μ ≤ gaussianEvenMoment p)
    (b : m → n → ℝ) (hb : ∀ e : m × n, 0 ≤ b e.1 e.2)
    (p : ℕ) :
    ∫ w, (((Matrix.of (fun i j => b i j * X i j w)) *
        (Matrix.of (fun i j => b i j * X i j w))ᴴ) ^ p).trace ∂μ ≤
      ∫ G : Matrix m n ℝ,
        (((Matrix.of (fun i j => b i j * G i j)) *
            (Matrix.of (fun i j => b i j * G i j))ᴴ) ^ p).trace
        ∂(gaussianMatrix m n) := by
  cases p with
  | zero => exact integral_trace_gram_pow_zero_le_integral_gaussianMatrix b
  | succ q =>
      have h := integral_trace_gram_pow_le_integral_gaussianMatrix hX hsym h2 b hb q
      simpa using h

end NLAlib
