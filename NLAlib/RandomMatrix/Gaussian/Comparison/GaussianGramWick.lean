import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import NLAlib.RandomMatrix.Gaussian.Comparison.IndependentGramMoments
import NLAlib.Probability.Gaussian.Moments.Isserlis
import NLAlib.Probability.Gaussian.Moments.WickPairingEdges

/-!
# Gaussian Gram trace moment: exact Wick expansion

For a real deterministic profile `b : I → J → ℝ` and `G` having the genuine
`NLAlib.gaussianMatrix I J` law, with `B(G) = Matrix.of (fun i j => b i j * G i j)`,
we prove the exact equality

```
∫ G, trace ((B(G) * B(G)ᴴ) ^ p) ∂ gaussianMatrix I J
  = ∑ π : GaussianPairings (p + p),
      ∑ x : Fin p → I, ∑ y : Fin p → J,
        gaussianPairingWeight (gramCyclePairCovariance b p x y) π
```

for every `p > 0`. The occurrence labels are the original alternating Gram
cycle: `O = Fin p ⊕ Fin p` with
`idx_xy (inl t) = (x t, y t)` and `idx_xy (inr t) = (x (finRotate p t), y t)`,
transported to `Fin (p + p)` by the explicit equivalence `gramCycleEquiv p`
(= `finSumFinEquiv.symm`). The pairing covariance is
`C_b (x,y) (a,b') = if idx_xy a = idx_xy b' then (b at idx_xy a)^2 else 0`.

The proof is the native Gaussian Wick expansion:

* first a weighted-entry adapter: the vector
`G ↦ (b (idx t).1 (idx t).2 * G (idx t).1 (idx t).2)ₜ` (t ranges over `Fin k`)
is a centered Gaussian vector under the Gaussian matrix law, obtained as the
image of the identity Gaussian matrix by the continuous linear map
`gramEntryLinearMap`; the Isserlis theorem then gives the pairing sum;
* then the closed Gram cycle product over `Fin p` is rewritten as the product
over `Fin (p + p)` of the weighted entries via `Fintype.prod_sumElim` and the
equivalence `gramCycleEquiv p`, the finite sums are interchanged using the
explicitly proven integrability, placing the pairing sum outermost.

The case `p = 0` is separate: the integrand equals the constant `Fintype.card I`
(`integral_trace_gram_zero_pow_gaussianMatrix`); extending the positive-cycle
formula to `p = 0` would be false because the empty cycle label product is `1`
and loses the free root.

A second presentation of each pairing contribution is exposed as the product
over the edge list `gaussianPairingEdges π` using
`gaussianPairingWeight_eq_prod_gaussianPairingEdges`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Matrix

namespace NLAlib

variable {I J : Type*} [Fintype I] [Fintype J]
variable [DecidableEq I] [DecidableEq J]

/-- The occurrence index of the closed Gram cycle: `Sum.inl t` is the left
factor `(x t, y t)` and `Sum.inr t` the right factor
`(x (finRotate p t), y t)`. -/
def gramCycleIdx (p : ℕ) (x : Fin p → I) (y : Fin p → J) : Fin p ⊕ Fin p → I × J
  | Sum.inl t => (x t, y t)
  | Sum.inr t => (x (finRotate p t), y t)

/-- The explicit equivalence `Fin (p + p) ≃ Fin p ⊕ Fin p` used to transport the
occurrence labels of the closed Gram cycle: `finSumFinEquiv.symm`. -/
def gramCycleEquiv (p : ℕ) : Fin (p + p) ≃ Fin p ⊕ Fin p :=
  finSumFinEquiv.symm

/-- The pairing covariance of the weighted Gaussian Gram occurrences: two
occurrences `a`, `b'` of the cycle contribute `(b at idx_xy a)^2` exactly when
they sit at the same matrix entry, and `0` otherwise. -/
noncomputable def gramCyclePairCovariance (b : I → J → ℝ) (p : ℕ)
    (x : Fin p → I) (y : Fin p → J) : Fin (p + p) → Fin (p + p) → ℝ := by
  classical
  exact fun a b' =>
    if gramCycleIdx p x y (gramCycleEquiv p a) = gramCycleIdx p x y (gramCycleEquiv p b')
      then (b (gramCycleIdx p x y (gramCycleEquiv p a)).1
              (gramCycleIdx p x y (gramCycleEquiv p a)).2) ^ 2
      else 0

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- At `p = q + 1` the closed Gram cycle index coincides exactly with the
public `gramOccurrenceIdx q` of the integrated Gram trace expansion. -/
lemma gramCycleIdx_eq_gramOccurrenceIdx (q : ℕ)
    (x : Fin (q + 1) → I) (y : Fin (q + 1) → J) :
    gramCycleIdx (q + 1) x y = gramOccurrenceIdx q x y := by
  funext s
  cases s <;> rfl

/-- Evaluation of the matrix entry `(i, j)` as a continuous linear functional. -/
private def gramEntryEval {i : I} {j : J} : Matrix I J ℝ →L[ℝ] ℝ :=
  ((ContinuousLinearMap.proj j : (J → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj i : (I → J → ℝ) →L[ℝ] (J → ℝ)))

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
private lemma gramEntryEval_apply {i : I} {j : J} (G : Matrix I J ℝ) :
    (gramEntryEval (i := i) (j := j)) G = G i j := by
  unfold gramEntryEval
  change (ContinuousLinearMap.proj j : (J → ℝ) →L[ℝ] ℝ)
    ((ContinuousLinearMap.proj i : (I → J → ℝ) →L[ℝ] (J → ℝ)) G) = G i j
  rfl

/-- The continuous linear map sending a matrix `G` to the weighted vector of the
`k` occurrences `(b (idx t).1 (idx t).2 * G (idx t).1 (idx t).2)ₜ` in
`EuclideanSpace ℝ (Fin k)`. -/
private def gramEntryLinearMap {k : ℕ} (b : I → J → ℝ) (idx : Fin k → I × J) :
    Matrix I J ℝ →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k => ℝ)).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi fun t =>
      (gramEntryEval (i := (idx t).1) (j := (idx t).2)).smulRight (b (idx t).1 (idx t).2))

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
private lemma gramEntryLinearMap_apply {k : ℕ} (b : I → J → ℝ) (idx : Fin k → I × J)
    (G : Matrix I J ℝ) (t : Fin k) :
    gramEntryLinearMap b idx G t = b (idx t).1 (idx t).2 * G (idx t).1 (idx t).2 := by
  unfold gramEntryLinearMap
  change (gramEntryEval (i := (idx t).1) (j := (idx t).2)).smulRight
    (b (idx t).1 (idx t).2) G = b (idx t).1 (idx t).2 * G (idx t).1 (idx t).2
  rw [ContinuousLinearMap.smulRight_apply]
  rw [gramEntryEval_apply]
  ring

omit [DecidableEq I] [DecidableEq J] in
/-- The image of the identity Gaussian matrix by the weighted-occurrence linear
map is a Gaussian vector. -/
private theorem hasGaussianLaw_gramEntryLinearMap {k : ℕ} (b : I → J → ℝ)
    (idx : Fin k → I × J) :
    HasGaussianLaw (fun G : Matrix I J ℝ => gramEntryLinearMap b idx G)
      (gaussianMatrix I J) := by
  simpa [Function.comp_def] using ((hasGaussianLaw_id_gaussianMatrix I J).map_of_measurable
    (gramEntryLinearMap b idx) (gramEntryLinearMap b idx).continuous.measurable)

omit [DecidableEq I] [DecidableEq J] in
/-- The weighted-occurrence vector is integrable under the Gaussian matrix law. -/
private theorem integrable_gramEntryLinearMap {k : ℕ} (b : I → J → ℝ)
    (idx : Fin k → I × J) :
    Integrable (fun G : Matrix I J ℝ => gramEntryLinearMap b idx G)
      (gaussianMatrix I J) := by
  have hLG := hasGaussianLaw_gramEntryLinearMap b idx
  have hI : Integrable (fun x : EuclideanSpace ℝ (Fin k) => x)
      ((gaussianMatrix I J).map (fun G : Matrix I J ℝ => gramEntryLinearMap b idx G)) := by
    have hG : IsGaussian ((gaussianMatrix I J).map
        (fun G : Matrix I J ℝ => gramEntryLinearMap b idx G)) :=
      hLG.isGaussian_map
    exact IsGaussian.integrable_id
  exact hI.comp_measurable (gramEntryLinearMap b idx).continuous.measurable

omit [DecidableEq I] [DecidableEq J] in
/-- The weighted-occurrence vector is centered: each coordinate integral vanishes. -/
private theorem integral_gramEntryLinearMap_eq_zero {k : ℕ} (b : I → J → ℝ)
    (idx : Fin k → I × J) :
    ∫ G : Matrix I J ℝ, gramEntryLinearMap b idx G ∂ gaussianMatrix I J = 0 := by
  have hIntL := integrable_gramEntryLinearMap b idx
  have hproj (t : Fin k) :
      (∫ G : Matrix I J ℝ, gramEntryLinearMap b idx G ∂ gaussianMatrix I J) t =
        ∫ G, (gramEntryLinearMap b idx G) t ∂ gaussianMatrix I J := by
    exact ((EuclideanSpace.proj t : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).integral_comp_comm
      hIntL).symm
  have hzero (t : Fin k) :
      ∫ G, (gramEntryLinearMap b idx G) t ∂ gaussianMatrix I J = 0 := by
    simp_rw [gramEntryLinearMap_apply]
    rw [integral_const_mul]
    rw [integral_gaussianMatrix_entry_eq_zero]
    simp
  rw [WithLp.ext_iff]
  funext t
  rw [hproj t]
  exact hzero t

/-- The covariance of two weighted occurrences of the Gaussian matrix is exactly
`if idx a = idx b' then (b (idx a).1 (idx a).2)^2 else 0`. -/
private theorem integral_gramEntryLinearMap_mul {k : ℕ} (b : I → J → ℝ)
    (idx : Fin k → I × J) (a b' : Fin k) :
    (∫ G : Matrix I J ℝ,
        (gramEntryLinearMap b idx G) a * (gramEntryLinearMap b idx G) b'
      ∂ gaussianMatrix I J) =
      if idx a = idx b' then (b (idx a).1 (idx a).2) ^ 2 else 0 := by
  simp_rw [gramEntryLinearMap_apply]
  have hre : (fun G : Matrix I J ℝ =>
      (b (idx a).1 (idx a).2 * G (idx a).1 (idx a).2) *
        (b (idx b').1 (idx b').2 * G (idx b').1 (idx b').2)) =
      fun G => (b (idx a).1 (idx a).2 * b (idx b').1 (idx b').2) *
        (G (idx a).1 (idx a).2 * G (idx b').1 (idx b').2) := by
    funext G
    ring
  rw [hre]
  rw [integral_const_mul]
  rw [integral_gaussianMatrix_entry_mul (idx a).1 (idx b').1 (idx a).2 (idx b').2]
  by_cases h : idx a = idx b'
  · rw [h]
    simp [sq]
  · have hne : ¬((idx a).1 = (idx b').1 ∧ (idx a).2 = (idx b').2) := by
      rintro ⟨h1, h2⟩
      exact h (Prod.ext h1 h2)
    simp [hne, h]

/-- **Weighted-entry Gaussian Wick adapter**: for any finite family `idx : Fin k → I × J`
of occurrence positions in the Gaussian matrix and any real profile `b`, the
expectation of the weighted product `∏ t, b (idx t).1 (idx t).2 * G (idx t).1 (idx t).2`
is the finite sum over the canonical Gaussian pairings of the pairing weight of
the square covariance `if idx a = idx b' then (b (idx a).1 (idx a).2)^2 else 0`.
This is the native Gaussian Wick expansion for arbitrary correlated and repeated
occurrence coordinates; no independence or moment-comparison input is used. -/
theorem integral_prod_gaussianMatrix_entry_weighted_eq_sum_pairings {k : ℕ}
    (b : I → J → ℝ) (idx : Fin k → I × J) :
    (∫ G : Matrix I J ℝ,
        ∏ t : Fin k, b (idx t).1 (idx t).2 * G (idx t).1 (idx t).2 ∂ gaussianMatrix I J) =
      ∑ π : GaussianPairings k,
        gaussianPairingWeight
          (fun a b' => if idx a = idx b' then (b (idx a).1 (idx a).2) ^ 2 else 0) π := by
  classical
  let L := gramEntryLinearMap b idx
  have hLG : HasGaussianLaw (fun G : Matrix I J ℝ => L G) (gaussianMatrix I J) :=
    hasGaussianLaw_gramEntryLinearMap b idx
  have hmean : ∫ G : Matrix I J ℝ, L G ∂ gaussianMatrix I J = 0 :=
    integral_gramEntryLinearMap_eq_zero b idx
  have hic := integral_prod_gaussianVector_eq_sum_pairings
    (Ω := Matrix I J ℝ) (P := gaussianMatrix I J) (G := fun G : Matrix I J ℝ => L G)
    (hG := hLG) (hmean := hmean) (idx := fun t : Fin k => t)
  have hcov (a b' : Fin k) :
      (∫ G : Matrix I J ℝ, (L G) a * (L G) b' ∂ gaussianMatrix I J) =
        if idx a = idx b' then (b (idx a).1 (idx a).2) ^ 2 else 0 :=
    integral_gramEntryLinearMap_mul b idx a b'
  calc
    (∫ G : Matrix I J ℝ,
        ∏ t : Fin k, b (idx t).1 (idx t).2 * G (idx t).1 (idx t).2 ∂ gaussianMatrix I J)
        = ∫ G : Matrix I J ℝ, ∏ r : Fin k, (L G) r ∂ gaussianMatrix I J := by
          apply integral_congr_ae
          refine Filter.Eventually.of_forall ?_
          intro G
          apply Finset.prod_congr rfl
          intro t _
          rw [gramEntryLinearMap_apply]
    _ = ∑ π : GaussianPairings k,
          gaussianPairingWeight
            (fun a b' => ∫ G : Matrix I J ℝ, (L G) a * (L G) b' ∂ gaussianMatrix I J) π := by
          simpa using hic
    _ = ∑ π : GaussianPairings k,
          gaussianPairingWeight
            (fun a b' => if idx a = idx b' then (b (idx a).1 (idx a).2) ^ 2 else 0) π := by
          apply Finset.sum_congr rfl
          intro π _
          congr 1
          funext a
          funext b'
          exact hcov a b'

omit [DecidableEq I] [DecidableEq J] in
/-- The weighted entry product of the Gaussian matrix is integrable for any
finite occurrence family (needed to interchange the finite sums and the integral). -/
theorem integrable_prod_gaussianMatrix_entry_weighted {k : ℕ}
    (b : I → J → ℝ) (idx : Fin k → I × J) :
    Integrable (fun G : Matrix I J ℝ =>
        ∏ t : Fin k, b (idx t).1 (idx t).2 * G (idx t).1 (idx t).2) (gaussianMatrix I J) := by
  classical
  let L := gramEntryLinearMap b idx
  have hLG : HasGaussianLaw (fun G : Matrix I J ℝ => L G) (gaussianMatrix I J) :=
    hasGaussianLaw_gramEntryLinearMap b idx
  have hmean : ∫ G : Matrix I J ℝ, L G ∂ gaussianMatrix I J = 0 :=
    integral_gramEntryLinearMap_eq_zero b idx
  have hIntV := integrable_prod_gaussianVector_of_centered
    (Ω := Matrix I J ℝ) (P := gaussianMatrix I J) (G := fun G : Matrix I J ℝ => L G)
    (hG := hLG) (hmean := hmean) (idx := fun t : Fin k => t)
  convert hIntV using 1
  funext G
  apply Finset.prod_congr rfl
  intro t _
  rw [gramEntryLinearMap_apply]

/-- The trace of `(A Aᴴ)^(q+1)` is the exact finite sum over row and column
assignments of the closed cycle product (matching `gramOccurrenceIdx`). This
is the cycle form of the public `trace_mul_conjTranspose_pow_eq_sum_gramOccurrence`. -/
theorem trace_mul_conjTranspose_pow_eq_sum_gram_cycle (A : Matrix I J ℝ) (q : ℕ) :
    Matrix.trace ((A * Aᴴ) ^ (q + 1)) =
      ∑ r : Fin (q + 1) → I, ∑ c : Fin (q + 1) → J,
        ∏ t : Fin (q + 1),
          A (r t) (c t) * A (r (finRotate (q + 1) t)) (c t) := by
  classical
  rw [trace_mul_conjTranspose_pow_eq_sum_gramOccurrence A q]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro c _
  exact (prod_gram_entries_eq_prod_pow_gramOccurrenceCount A q r c).symm

/-- **Exact Gaussian Gram trace Wick expansion**: for every `p > 0`, the
expectation of `trace ((B(G) B(G)ᴴ)^p)` under the genuine Gaussian matrix law
is the finite sum over the canonical Gaussian pairings (with `p + p`
occurrences) of the pairing weight of the square covariance of the closed Gram
cycle occurrences. -/
theorem integral_trace_gram_pow_gaussianMatrix_eq_sum_pairings (b : I → J → ℝ)
    (p : ℕ) (hp : 0 < p) :
    (∫ G : Matrix I J ℝ,
        Matrix.trace (((Matrix.of (fun i j => b i j * G i j)) *
          (Matrix.of (fun i j => b i j * G i j))ᴴ)^p) ∂ gaussianMatrix I J) =
      ∑ π : GaussianPairings (p + p), ∑ x : Fin p → I, ∑ y : Fin p → J,
        gaussianPairingWeight (gramCyclePairCovariance b p x y) π := by
  classical
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hp)
  have hprod (x : Fin (q + 1) → I) (y : Fin (q + 1) → J) (G : Matrix I J ℝ) :
      (∏ t : Fin (q + 1),
          (b (x t) (y t) * G (x t) (y t)) *
            (b (x (finRotate (q + 1) t)) (y t) * G (x (finRotate (q + 1) t)) (y t))) =
        ∏ a : Fin ((q + 1) + (q + 1)),
          b (gramOccurrenceIdx q x y (gramCycleEquiv (q + 1) a)).1
            (gramOccurrenceIdx q x y (gramCycleEquiv (q + 1) a)).2 *
          G (gramOccurrenceIdx q x y (gramCycleEquiv (q + 1) a)).1
            (gramOccurrenceIdx q x y (gramCycleEquiv (q + 1) a)).2 := by
    let f : Fin (q + 1) → ℝ := fun t =>
      b (x t) (y t) * G (x t) (y t)
    let g : Fin (q + 1) → ℝ := fun t =>
      b (x (finRotate (q + 1) t)) (y t) * G (x (finRotate (q + 1) t)) (y t)
    calc
      (∏ t : Fin (q + 1),
          (b (x t) (y t) * G (x t) (y t)) *
            (b (x (finRotate (q + 1) t)) (y t) * G (x (finRotate (q + 1) t)) (y t)))
          = ∏ t : Fin (q + 1), f t * g t := by simp [f, g]
      _ = (∏ t : Fin (q + 1), f t) * (∏ t : Fin (q + 1), g t) := by
            rw [Finset.prod_mul_distrib]
      _ = ∏ s : Fin (q + 1) ⊕ Fin (q + 1), Sum.elim f g s := by
            exact (Fintype.prod_sumElim f g).symm
      _ = ∏ a : Fin ((q + 1) + (q + 1)), Sum.elim f g (gramCycleEquiv (q + 1) a) := by
            exact Fintype.prod_equiv (gramCycleEquiv (q + 1)).symm
              (fun s => Sum.elim f g s)
              (fun a => Sum.elim f g (gramCycleEquiv (q + 1) a))
              (fun s => by simp)
      _ = ∏ a : Fin ((q + 1) + (q + 1)),
            b (gramOccurrenceIdx q x y (gramCycleEquiv (q + 1) a)).1
              (gramOccurrenceIdx q x y (gramCycleEquiv (q + 1) a)).2 *
            G (gramOccurrenceIdx q x y (gramCycleEquiv (q + 1) a)).1
              (gramOccurrenceIdx q x y (gramCycleEquiv (q + 1) a)).2 := by
            apply Finset.prod_congr rfl
            intro a _
            cases h : gramCycleEquiv (q + 1) a with
            | inl t =>
                simp [f, g, gramOccurrenceIdx]
            | inr t =>
                simp [f, g, gramOccurrenceIdx]
  have htrace (G : Matrix I J ℝ) :
      Matrix.trace (((Matrix.of (fun i j => b i j * G i j)) *
        (Matrix.of (fun i j => b i j * G i j))ᴴ)^(q + 1)) =
        ∑ x : Fin (q + 1) → I, ∑ y : Fin (q + 1) → J,
          ∏ t : Fin (q + 1),
            (b (x t) (y t) * G (x t) (y t)) *
              (b (x (finRotate (q + 1) t)) (y t) * G (x (finRotate (q + 1) t)) (y t)) := by
    let A : Matrix I J ℝ := Matrix.of (fun i j => b i j * G i j)
    rw [trace_mul_conjTranspose_pow_eq_sum_gramOccurrence A q]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [← prod_gram_entries_eq_prod_pow_gramOccurrenceCount A q x y]
    simp [A]
  have hin (x : Fin (q + 1) → I) (y : Fin (q + 1) → J) :
      Integrable (fun G : Matrix I J ℝ =>
          ∏ t : Fin (q + 1),
            (b (x t) (y t) * G (x t) (y t)) *
              (b (x (finRotate (q + 1) t)) (y t) * G (x (finRotate (q + 1) t)) (y t)))
        (gaussianMatrix I J) := by
    have hI := integrable_prod_gaussianMatrix_entry_weighted (k := (q + 1) + (q + 1)) b
      (fun a => gramOccurrenceIdx q x y (gramCycleEquiv (q + 1) a))
    convert hI using 1
    funext G
    exact hprod x y G
  have hinSum (x : Fin (q + 1) → I) :
      Integrable (fun G : Matrix I J ℝ =>
          ∑ y : Fin (q + 1) → J,
            ∏ t : Fin (q + 1),
              (b (x t) (y t) * G (x t) (y t)) *
                (b (x (finRotate (q + 1) t)) (y t) * G (x (finRotate (q + 1) t)) (y t)))
        (gaussianMatrix I J) := by
    exact integrable_finsetSum (s := Finset.univ)
      (f := fun y : Fin (q + 1) → J => fun G : Matrix I J ℝ =>
        ∏ t : Fin (q + 1),
          (b (x t) (y t) * G (x t) (y t)) *
            (b (x (finRotate (q + 1) t)) (y t) * G (x (finRotate (q + 1) t)) (y t)))
      (fun y _ => hin x y)
  calc
    (∫ G : Matrix I J ℝ,
        Matrix.trace (((Matrix.of (fun i j => b i j * G i j)) *
          (Matrix.of (fun i j => b i j * G i j))ᴴ)^(q + 1)) ∂ gaussianMatrix I J)
        = ∫ G : Matrix I J ℝ, ∑ x : Fin (q + 1) → I, ∑ y : Fin (q + 1) → J,
            ∏ t : Fin (q + 1),
              (b (x t) (y t) * G (x t) (y t)) *
                (b (x (finRotate (q + 1) t)) (y t) * G (x (finRotate (q + 1) t)) (y t))
            ∂ gaussianMatrix I J := by
          apply integral_congr_ae
          refine Filter.Eventually.of_forall ?_
          intro G
          exact htrace G
    _ = ∑ x : Fin (q + 1) → I, ∑ y : Fin (q + 1) → J,
          ∫ G : Matrix I J ℝ,
            ∏ t : Fin (q + 1),
              (b (x t) (y t) * G (x t) (y t)) *
                (b (x (finRotate (q + 1) t)) (y t) * G (x (finRotate (q + 1) t)) (y t))
            ∂ gaussianMatrix I J := by
          rw [integral_finsetSum (s := Finset.univ)
            (f := fun x : Fin (q + 1) → I => fun G : Matrix I J ℝ =>
              ∑ y : Fin (q + 1) → J,
                ∏ t : Fin (q + 1),
                  (b (x t) (y t) * G (x t) (y t)) *
                    (b (x (finRotate (q + 1) t)) (y t) * G (x (finRotate (q + 1) t)) (y t)))
            (fun x _ => hinSum x)]
          apply Finset.sum_congr rfl
          intro x _
          rw [integral_finsetSum (s := Finset.univ)
            (f := fun y : Fin (q + 1) → J => fun G : Matrix I J ℝ =>
              ∏ t : Fin (q + 1),
                (b (x t) (y t) * G (x t) (y t)) *
                  (b (x (finRotate (q + 1) t)) (y t) * G (x (finRotate (q + 1) t)) (y t)))
            (fun y _ => hin x y)]
    _ = ∑ x : Fin (q + 1) → I, ∑ y : Fin (q + 1) → J,
          ∑ π : GaussianPairings ((q + 1) + (q + 1)),
            gaussianPairingWeight (gramCyclePairCovariance b (q + 1) x y) π := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          have hw := integral_prod_gaussianMatrix_entry_weighted_eq_sum_pairings
            (k := (q + 1) + (q + 1)) b
            (fun a => gramOccurrenceIdx q x y (gramCycleEquiv (q + 1) a))
          calc
            ∫ G : Matrix I J ℝ,
                ∏ t : Fin (q + 1),
                  (b (x t) (y t) * G (x t) (y t)) *
                    (b (x (finRotate (q + 1) t)) (y t) * G (x (finRotate (q + 1) t)) (y t))
                ∂ gaussianMatrix I J
                = ∫ G : Matrix I J ℝ,
                    ∏ a : Fin ((q + 1) + (q + 1)),
                      b (gramOccurrenceIdx q x y (gramCycleEquiv (q + 1) a)).1
                        (gramOccurrenceIdx q x y (gramCycleEquiv (q + 1) a)).2 *
                      G (gramOccurrenceIdx q x y (gramCycleEquiv (q + 1) a)).1
                        (gramOccurrenceIdx q x y (gramCycleEquiv (q + 1) a)).2
                    ∂ gaussianMatrix I J := by
                  apply integral_congr_ae
                  refine Filter.Eventually.of_forall ?_
                  intro G
                  exact hprod x y G
                _ = ∑ π : GaussianPairings ((q + 1) + (q + 1)),
                      gaussianPairingWeight
                        (fun a b' =>
                          if (gramOccurrenceIdx q x y (gramCycleEquiv (q + 1) a)) =
                               (gramOccurrenceIdx q x y (gramCycleEquiv (q + 1) b'))
                            then (b (gramOccurrenceIdx q x y (gramCycleEquiv (q + 1) a)).1
                                    (gramOccurrenceIdx q x y (gramCycleEquiv (q + 1) a)).2)^2
                            else 0) π := hw
                _ = ∑ π : GaussianPairings ((q + 1) + (q + 1)),
                      gaussianPairingWeight (gramCyclePairCovariance b (q + 1) x y) π := by
                  apply Finset.sum_congr rfl
                  intro π _
                  congr 1
                  funext a
                  funext b'
                  simp [gramCyclePairCovariance, gramCycleIdx_eq_gramOccurrenceIdx]
    _ = ∑ π : GaussianPairings ((q + 1) + (q + 1)), ∑ x : Fin (q + 1) → I,
          ∑ y : Fin (q + 1) → J,
            gaussianPairingWeight (gramCyclePairCovariance b (q + 1) x y) π := by
          calc
            (∑ x : Fin (q + 1) → I, ∑ y : Fin (q + 1) → J,
                ∑ π : GaussianPairings ((q + 1) + (q + 1)),
                  gaussianPairingWeight (gramCyclePairCovariance b (q + 1) x y) π)
                = ∑ x : Fin (q + 1) → I,
                    (∑ π : GaussianPairings ((q + 1) + (q + 1)),
                      ∑ y : Fin (q + 1) → J,
                        gaussianPairingWeight (gramCyclePairCovariance b (q + 1) x y) π) := by
                  apply Finset.sum_congr rfl
                  intro x _
                  exact Finset.sum_comm
            _ = ∑ π : GaussianPairings ((q + 1) + (q + 1)), ∑ x : Fin (q + 1) → I,
                  ∑ y : Fin (q + 1) → J,
                    gaussianPairingWeight (gramCyclePairCovariance b (q + 1) x y) π := by
                  exact Finset.sum_comm

/-- The per-pairing contribution of the exact Gaussian Gram trace expansion, as
a transparent finite sum over row and column assignments. -/
noncomputable def gramPairingContribution (b : I → J → ℝ) (p : ℕ)
    (π : GaussianPairings (p + p)) : ℝ :=
  ∑ x : Fin p → I, ∑ y : Fin p → J,
    gaussianPairingWeight (gramCyclePairCovariance b p x y) π

/-- The exact Gaussian Gram trace expansion with the pairing sum outermost,
identified as the finite sum of the per-pairing contributions. -/
theorem integral_trace_gram_pow_gaussianMatrix_eq_sum_pairings_outer (b : I → J → ℝ)
    (p : ℕ) (hp : 0 < p) :
    (∫ G : Matrix I J ℝ,
        Matrix.trace (((Matrix.of (fun i j => b i j * G i j)) *
          (Matrix.of (fun i j => b i j * G i j))ᴴ)^p) ∂ gaussianMatrix I J) =
      ∑ π : GaussianPairings (p + p), gramPairingContribution b p π := by
  rw [integral_trace_gram_pow_gaussianMatrix_eq_sum_pairings b p hp]
  rfl

omit [Fintype I] [Fintype J] in
/-- For fixed row and column labels, each pairing weight is the product over the edge list
`gaussianPairingEdges π` of the square covariances of the paired occurrences. -/
theorem gaussianPairingWeight_gramCyclePairCovariance_eq_prod_edges (b : I → J → ℝ)
    (p : ℕ) (x : Fin p → I) (y : Fin p → J) (π : GaussianPairings (p + p)) :
    gaussianPairingWeight (gramCyclePairCovariance b p x y) π =
      ((gaussianPairingEdges π).map (fun e =>
        if gramCycleIdx p x y (gramCycleEquiv p e.1) = gramCycleIdx p x y (gramCycleEquiv p e.2)
          then (b (gramCycleIdx p x y (gramCycleEquiv p e.1)).1
                   (gramCycleIdx p x y (gramCycleEquiv p e.1)).2)^2
          else 0)).prod := by
  rw [gaussianPairingWeight_eq_prod_gaussianPairingEdges]
  rfl

omit [DecidableEq J] in
/-- The `p = 0` case is separate: the empty Gram power has trace `Fintype.card I`
(the identity), not the empty-cycle pairing sum (whose label product is `1`). -/
theorem integral_trace_gram_zero_pow_gaussianMatrix (b : I → J → ℝ) :
    (∫ G : Matrix I J ℝ,
        Matrix.trace (((Matrix.of (fun i j => b i j * G i j)) *
          (Matrix.of (fun i j => b i j * G i j))ᴴ)^0) ∂ gaussianMatrix I J) =
      (Fintype.card I : ℝ) := by
  have h : (fun G : Matrix I J ℝ =>
      Matrix.trace (((Matrix.of (fun i j => b i j * G i j)) *
        (Matrix.of (fun i j => b i j * G i j))ᴴ)^0)) =
      fun _ : Matrix I J ℝ => (Fintype.card I : ℝ) := by
    funext G
    simp [Matrix.trace_one]
  rw [h]
  simp
