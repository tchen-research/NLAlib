import NLAlib.Sketching.Sampling.LEnsembleMarginals
import NLAlib.ForMathlib.LinearAlgebra.Matrix.SmallPrincipalMinors
import Mathlib.Probability.Moments.Variance

/-!
# L-ensemble singleton, covariance and size moments

All random variables here live on the actual finite-subset law. Inclusion
probabilities give the first two indicator moments and hence the covariance
and cardinality variance. Source: Dereziński–Mahoney 2020, §3.
Atlas: `l-ensemble-marginals`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace NLAlib

set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n] [DecidableEq n]

private def inclusionIndicator (i : n) (S : Finset n) : ℝ := if i ∈ S then 1 else 0

private theorem memLp_inclusionIndicator (L : Matrix n n ℝ) (hL : L.PosSemidef) (i : n) :
    MemLp (inclusionIndicator i) 2 (lEnsembleLaw L hL) := by
  classical
  refine MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable 1
    (ae_of_all _ fun S => ?_)
  simp only [inclusionIndicator]
  split_ifs <;> norm_num

/-- The singleton inclusion probability is the marginal-kernel diagonal.
Dereziński–Mahoney 2020, §3.
atlas: l-ensemble-marginals (partial)-/
theorem measureReal_mem_lEnsembleLaw (L : Matrix n n ℝ) (hL : L.PosSemidef) (i : n) :
    (lEnsembleLaw L hL).real {S | i ∈ S} = lEnsembleKernel L i i := by
  have h := measureReal_subset_lEnsembleLaw L hL {i}
  simpa only [Finset.singleton_subset_iff, principalMinor, Matrix.toBlock,
    Matrix.det_submatrix_singleton] using h

private theorem integral_inclusionIndicator (L : Matrix n n ℝ) (hL : L.PosSemidef) (i : n) :
    ∫ S, inclusionIndicator i S ∂lEnsembleLaw L hL = lEnsembleKernel L i i := by
  have h := integral_subset_indicator_lEnsembleLaw L hL {i}
  simpa only [Finset.singleton_subset_iff, inclusionIndicator, principalMinor, Matrix.toBlock,
    Matrix.det_submatrix_singleton] using h

private theorem integral_inclusionIndicator_mul (L : Matrix n n ℝ) (hL : L.PosSemidef)
    {i j : n} (hij : i ≠ j) :
    ∫ S, inclusionIndicator i S * inclusionIndicator j S ∂lEnsembleLaw L hL =
      lEnsembleKernel L i i * lEnsembleKernel L j j - lEnsembleKernel L i j ^ 2 := by
  classical
  have he : (fun S => inclusionIndicator i S * inclusionIndicator j S) =
      fun S => if ({i, j} : Finset n) ⊆ S then (1 : ℝ) else 0 := by
    funext S
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
      simp [inclusionIndicator, Finset.insert_subset_iff, hi, hj]
  rw [he, integral_subset_indicator_lEnsembleLaw]
  change ((lEnsembleKernel L).submatrix
    (Subtype.val : ↥({i, j} : Finset n) → n)
    (Subtype.val : ↥({i, j} : Finset n) → n)).det = _
  rw [Matrix.det_submatrix_pair _ hij]
  have hs : lEnsembleKernel L j i = lEnsembleKernel L i j := by
    have hh := congrArg (fun A : Matrix n n ℝ => A i j) (lEnsembleKernel_isHermitian hL).eq
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_apply] using hh
  rw [hs, pow_two]

/-- Distinct L-ensemble inclusion indicators have covariance `-Kᵢⱼ²`.
Dereziński–Mahoney 2020, §3, negative-correlation identity.
atlas: l-ensemble-marginals (partial)-/
theorem covariance_mem_lEnsembleLaw (L : Matrix n n ℝ) (hL : L.PosSemidef)
    {i j : n} (hij : i ≠ j) :
    covariance (fun S : Finset n => if i ∈ S then (1 : ℝ) else 0)
      (fun S : Finset n => if j ∈ S then (1 : ℝ) else 0) (lEnsembleLaw L hL) =
      -lEnsembleKernel L i j ^ 2 := by
  change covariance (inclusionIndicator i) (inclusionIndicator j) _ = _
  rw [covariance_eq_sub (memLp_inclusionIndicator L hL i) (memLp_inclusionIndicator L hL j)]
  change (∫ S, inclusionIndicator i S * inclusionIndicator j S ∂lEnsembleLaw L hL) - _ = _
  rw [integral_inclusionIndicator_mul L hL hij,
    integral_inclusionIndicator L hL, integral_inclusionIndicator L hL]
  ring

private theorem card_eq_sum_inclusionIndicator (S : Finset n) :
    (S.card : ℝ) = ∑ i, inclusionIndicator i S := by
  classical
  simp only [inclusionIndicator, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The expected cardinality of the variable-size L-ensemble is `tr K`.
This is not an identity for a law conditioned on a fixed cardinality.
Dereziński–Mahoney 2020, §3.
atlas: l-ensemble-marginals (partial)-/
theorem integral_card_lEnsembleLaw (L : Matrix n n ℝ) (hL : L.PosSemidef) :
    ∫ S, (S.card : ℝ) ∂lEnsembleLaw L hL = (lEnsembleKernel L).trace := by
  simp_rw [card_eq_sum_inclusionIndicator]
  rw [integral_finsetSum _ fun i _ => (memLp_inclusionIndicator L hL i).integrable (by norm_num)]
  simp only [integral_inclusionIndicator, Matrix.trace, Matrix.diag]

/-- The cardinality variance is `tr (K - K²)`, including singular kernels
and an empty ambient index set. Dereziński–Mahoney 2020, §3.
atlas: l-ensemble-marginals (partial)-/
theorem variance_card_lEnsembleLaw (L : Matrix n n ℝ) (hL : L.PosSemidef) :
    variance (fun S : Finset n => (S.card : ℝ)) (lEnsembleLaw L hL) =
      (lEnsembleKernel L - lEnsembleKernel L * lEnsembleKernel L).trace := by
  classical
  have hcov (i j : n) : covariance (inclusionIndicator i) (inclusionIndicator j)
      (lEnsembleLaw L hL) =
      (if i = j then lEnsembleKernel L i i else 0) -
        lEnsembleKernel L i j * lEnsembleKernel L j i := by
    by_cases hij : i = j
    · subst j
      rw [covariance_eq_sub (memLp_inclusionIndicator L hL i) (memLp_inclusionIndicator L hL i)]
      have he : inclusionIndicator i * inclusionIndicator i = inclusionIndicator i := by
        funext S
        simp only [Pi.mul_apply, inclusionIndicator]
        split_ifs <;> norm_num
      rw [he, integral_inclusionIndicator L hL]
      simp only [ite_true]
    · have hh := covariance_mem_lEnsembleLaw L hL hij
      change covariance (inclusionIndicator i) (inclusionIndicator j) _ = _ at hh
      have hs : lEnsembleKernel L j i = lEnsembleKernel L i j := by
        have he := congrArg (fun A : Matrix n n ℝ => A i j) (lEnsembleKernel_isHermitian hL).eq
        simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_apply] using he
      simpa only [if_neg hij, zero_sub, hs, pow_two] using hh
  simp_rw [card_eq_sum_inclusionIndicator]
  rw [variance_fun_sum (fun i => memLp_inclusionIndicator L hL i), Matrix.trace_sub]
  simp only [hcov, Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp

end NLAlib
