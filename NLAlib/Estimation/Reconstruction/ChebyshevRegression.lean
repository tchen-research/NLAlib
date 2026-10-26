import NLAlib.Estimation.Reconstruction.ChebyshevGrid
import NLAlib.Probability.Sampling.FiniteSampling
import NLAlib.Probability.Transforms.ChebyshevMomentWasserstein
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Probability-simplex regression of Chebyshev moments

The objective is the weighted residual norm, rather than its square. The grid
law is an actual finite probability measure. Compactness supplies a minimizer;
the approximation guarantee also allows a residual-norm optimization tolerance.

Source: Musco--Musco--Rosenblatt--Singh, Corollary 2 and Appendix C.
-/

noncomputable section
open MeasureTheory Polynomial Polynomial.Chebyshev

namespace NLAlib

/-- The positive degree Chebyshev coordinates, divided by their degrees. -/
def weightedChebyshevVector (k : ℕ) (a : ℕ → ℝ) :
    EuclideanSpace ℝ {j // j ∈ Finset.Icc 1 k} :=
  WithLp.toLp 2 (fun j => a j.1 / j.1)

/-- The weighted moment residual norm, with degree weights `1 / j²`. -/
def weightedChebyshevError (k : ℕ) (a b : ℕ → ℝ) : ℝ :=
  dist (weightedChebyshevVector k a) (weightedChebyshevVector k b)

theorem weightedChebyshevError_eq_sqrt_sum (k : ℕ) (a b : ℕ → ℝ) :
    weightedChebyshevError k a b =
      Real.sqrt (∑ j ∈ Finset.Icc 1 k, ((a j - b j) / j) ^ 2) := by
  simp only [weightedChebyshevError, dist_eq_norm, weightedChebyshevVector,
    ← WithLp.toLp_sub, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, Pi.sub_apply,
    ← sub_div]
  congr 1
  exact Finset.sum_attach (Finset.Icc 1 k) (fun j => ((a j - b j) / j) ^ 2)

theorem weightedChebyshevError_triangle (k : ℕ) (a b c : ℕ → ℝ) :
    weightedChebyshevError k a c ≤
      weightedChebyshevError k a b + weightedChebyshevError k b c := dist_triangle _ _ _

theorem weightedChebyshevError_comm (k : ℕ) (a b : ℕ → ℝ) :
    weightedChebyshevError k a b = weightedChebyshevError k b a := dist_comm _ _

/-- The actual Chebyshev moment sequence of a real measure. -/
def chebyshevMoments (μ : Measure ℝ) (j : ℕ) : ℝ := ∫ x, (T ℝ (j : ℤ)).eval x ∂μ

theorem chebyshevMomentError_eq_weightedChebyshevError (μ ν : Measure ℝ) (k : ℕ) :
    chebyshevMomentError μ ν k = weightedChebyshevError k (chebyshevMoments μ) (chebyshevMoments ν) := by
  rw [weightedChebyshevError_eq_sqrt_sum]
  rfl

private def simplexProb {g : ℕ} (z : stdSimplex ℝ (Fin g)) (i : Fin g) : NNReal :=
  ⟨z.val i, z.property.1 i⟩

private theorem sum_simplexProb {g : ℕ} (z : stdSimplex ℝ (Fin g)) : ∑ i, simplexProb z i = 1 := by
  apply NNReal.coe_injective
  change ((∑ i, simplexProb z i : NNReal) : ℝ) = 1
  rw [NNReal.coe_sum]
  exact z.property.2

/-- A simplex vector interpreted as masses at the prescribed Chebyshev zeros. -/
def chebyshevGridLaw {g : ℕ} (z : stdSimplex ℝ (Fin g)) : Measure ℝ :=
  (finiteSamplingLaw (simplexProb z) (sum_simplexProb z)).map (chebyshevZero g)

instance chebyshevGridLaw_isProbabilityMeasure {g : ℕ} (z : stdSimplex ℝ (Fin g)) :
    IsProbabilityMeasure (chebyshevGridLaw z) :=
  Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

/-- Every grid law is supported in the approximation interval. -/
theorem ae_mem_Icc_chebyshevGridLaw {g : ℕ} (z : stdSimplex ℝ (Fin g)) :
    ∀ᵐ x ∂chebyshevGridLaw z, x ∈ Set.Icc (-1 : ℝ) 1 := by
  apply (ae_map_iff (measurable_of_finite _).aemeasurable measurableSet_Icc).2
  exact ae_of_all _ fun i => chebyshevZero_mem_Icc g i

/-- The finite matrix-vector product in the moment regression objective. -/
def chebyshevGridMoments {g : ℕ} (z : Fin g → ℝ) (j : ℕ) : ℝ :=
  ∑ i, z i * (T ℝ (j : ℤ)).eval (chebyshevZero g i)

theorem chebyshevMoments_gridLaw {g : ℕ} (z : stdSimplex ℝ (Fin g)) :
    chebyshevMoments (chebyshevGridLaw z) = chebyshevGridMoments z.val := by
  funext j
  rw [chebyshevMoments, chebyshevGridLaw,
    integral_map (measurable_of_finite _).aemeasurable (T ℝ (j : ℤ)).continuous.aestronglyMeasurable,
    integral_finiteSamplingLaw]
  rfl

/-- The weighted residual objective is continuous on all real grid weights. -/
theorem continuous_weightedChebyshevError_gridMoments (g k : ℕ) (mhat : ℕ → ℝ) :
    Continuous (fun z : Fin g → ℝ => weightedChebyshevError k (chebyshevGridMoments z) mhat) := by
  rw [show (fun z : Fin g → ℝ => weightedChebyshevError k (chebyshevGridMoments z) mhat) =
    (fun z => Real.sqrt (∑ j ∈ Finset.Icc 1 k, ((chebyshevGridMoments z j - mhat j) / j) ^ 2))
    from funext fun z => weightedChebyshevError_eq_sqrt_sum _ _ _]
  unfold chebyshevGridMoments
  fun_prop

/-- A residual-norm minimizer exists on every nonempty probability simplex.
atlas: chebyshev-moment-simplex-regression (partial) -/
theorem exists_minimizer_weightedChebyshevError_gridMoments (g k : ℕ) (hg : 0 < g)
    (mhat : ℕ → ℝ) : ∃ z ∈ stdSimplex ℝ (Fin g), ∀ a ∈ stdSimplex ℝ (Fin g),
      weightedChebyshevError k (chebyshevGridMoments z) mhat ≤
        weightedChebyshevError k (chebyshevGridMoments a) mhat := by
  have hne : (stdSimplex ℝ (Fin g)).Nonempty :=
    ⟨Pi.single ⟨0, hg⟩ 1, single_mem_stdSimplex ℝ _⟩
  exact (isCompact_stdSimplex ℝ (Fin g)).exists_isMinOn hne
    (continuous_weightedChebyshevError_gridMoments g k mhat).continuousOn

private theorem integrable_chebyshev_of_ae_mem_Icc
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc (-1 : ℝ) 1)
    (j : ℕ) : Integrable (fun x => (T ℝ (j : ℤ)).eval x) μ := by
  have h : IntegrableOn (fun x => (T ℝ (j : ℤ)).eval x) (Set.Icc (-1 : ℝ) 1) μ :=
    (T ℝ (j : ℤ)).continuous.continuousOn.integrableOn_compact isCompact_Icc
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμ] at h

/-- Moving each angular cell's mass to its midpoint constructs an actual simplex
competitor whose weighted moment error is at most `π sqrt(k) / (2g)`. -/
theorem exists_gridMoments_approximation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc (-1 : ℝ) 1) (k g : ℕ) (hg : 0 < g) :
    ∃ a : stdSimplex ℝ (Fin g),
      weightedChebyshevError k (chebyshevMoments μ) (chebyshevGridMoments a.val) ≤
        Real.pi * Real.sqrt k / (2 * g) := by
  let I := chebyshevGridIndex g hg
  have hI : Measurable I := measurable_chebyshevGridIndex g hg
  let ν := μ.map I
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hI.aemeasurable
  let a : stdSimplex ℝ (Fin g) := ⟨fun i => ν.real {i},
    ⟨fun _ => measureReal_nonneg, by
      simp⟩⟩
  refine ⟨a, ?_⟩
  have hmoment (j : ℕ) : chebyshevGridMoments a.val j =
      ∫ x, (T ℝ (j : ℤ)).eval (chebyshevZero g (I x)) ∂μ := by
    have hm : Measurable (fun i : Fin g => (T ℝ (j : ℤ)).eval (chebyshevZero g i)) :=
      measurable_of_finite _
    rw [← integral_map hI.aemeasurable hm.aestronglyMeasurable,
      integral_fintype (Integrable.of_finite : Integrable _ ν)]
    rfl
  have hcoord (j : ℕ) : |chebyshevMoments μ j - chebyshevGridMoments a.val j| ≤
      j * Real.pi / (2 * g) := by
    have hi : Integrable (fun x => (T ℝ (j : ℤ)).eval (chebyshevZero g (I x))) μ :=
      (Integrable.of_finite : Integrable (fun i => (T ℝ (j : ℤ)).eval (chebyshevZero g i)) ν).comp_aemeasurable
        hI.aemeasurable
    rw [chebyshevMoments, hmoment,
      ← integral_sub (integrable_chebyshev_of_ae_mem_Icc μ hμ j) hi, ← Real.norm_eq_abs]
    apply (norm_integral_le_of_norm_le_const (C := j * Real.pi / (2 * g)) ?_).trans_eq (by simp)
    filter_upwards [hμ] with x hx
    exact abs_eval_chebyshev_sub_grid_le g hg hx j
  have hsum : (∑ j ∈ Finset.Icc 1 k,
      ((chebyshevMoments μ j - chebyshevGridMoments a.val j) / j) ^ 2) ≤
        (k : ℝ) * (Real.pi / (2 * g)) ^ 2 := by
    calc
      _ ≤ ∑ _j ∈ Finset.Icc 1 k, (Real.pi / (2 * g)) ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hjpos : (0 : ℝ) < j := Nat.cast_pos.mpr (by have := (Finset.mem_Icc.mp hj).1; omega)
        have hd : |(chebyshevMoments μ j - chebyshevGridMoments a.val j) / j| ≤
            Real.pi / (2 * g) := by
          rw [abs_div, abs_of_pos hjpos]
          apply (div_le_iff₀ hjpos).2
          exact (hcoord j).trans_eq (by ring)
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hd
      _ = _ := by simp
  rw [weightedChebyshevError_eq_sqrt_sum]
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  apply hsum.trans_eq
  simp only [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
  ring

/-- Approximate minimization in residual norm yields the native probability-law
Wasserstein guarantee, with an additive optimization tolerance `η`.
Source: MMRS Corollary 2 and Appendix C, using unnormalized Chebyshev moments.
atlas: chebyshev-moment-simplex-regression (partial) -/
theorem wassersteinEDistOne_gridLaw_le_of_weightedChebyshevError_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc (-1 : ℝ) 1) {k g : ℕ} (hk : 1 ≤ k) (hg : 0 < g)
    (mhat : ℕ → ℝ) {Γ η : ℝ}
    (hnoise : weightedChebyshevError k mhat (chebyshevMoments μ) ≤ Γ)
    (z : stdSimplex ℝ (Fin g))
    (hfit : ∀ a : stdSimplex ℝ (Fin g),
      weightedChebyshevError k (chebyshevGridMoments z.val) mhat ≤
        weightedChebyshevError k (chebyshevGridMoments a.val) mhat + η) :
    wassersteinEDistOne μ (chebyshevGridLaw z) ≤
      ENNReal.ofReal (36 / k + 2 * Γ + Real.pi * Real.sqrt k / (2 * g) + η) := by
  obtain ⟨a, ha⟩ := exists_gridMoments_approximation μ hμ k g hg
  have htri₁ := weightedChebyshevError_triangle k (chebyshevGridMoments z.val) mhat (chebyshevMoments μ)
  have htri₂ := weightedChebyshevError_triangle k (chebyshevGridMoments a.val) (chebyshevMoments μ) mhat
  have ha' : weightedChebyshevError k (chebyshevGridMoments a.val) (chebyshevMoments μ) ≤
      Real.pi * Real.sqrt k / (2 * g) := by rwa [weightedChebyshevError_comm]
  have hn' : weightedChebyshevError k (chebyshevMoments μ) mhat ≤ Γ := by
    rwa [weightedChebyshevError_comm]
  apply (wassersteinEDistOne_le_thirtySix_div_add_chebyshevMomentError
    μ (chebyshevGridLaw z) hμ (ae_mem_Icc_chebyshevGridLaw z) hk).trans
  apply ENNReal.ofReal_le_ofReal
  rw [chebyshevMomentError_eq_weightedChebyshevError, chebyshevMoments_gridLaw,
    weightedChebyshevError_comm k (chebyshevMoments μ)]
  linarith [hfit a]

/-- The source grid choice `g = ceil(k^(3/2))` gives the stated `1/k` error,
without requiring an exact numerical optimizer.
Source: MMRS Corollary 2 and Appendix C, with a residual-norm tolerance.
atlas: chebyshev-moment-simplex-regression (partial) -/
theorem wassersteinEDistOne_gridLaw_le_of_ceil_rpow_three_div_two
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc (-1 : ℝ) 1) {k : ℕ} (hk : 1 ≤ k)
    (mhat : ℕ → ℝ) {Γ η : ℝ}
    (hnoise : weightedChebyshevError k mhat (chebyshevMoments μ) ≤ Γ)
    (z : stdSimplex ℝ (Fin ⌈(k : ℝ) ^ (3 / 2 : ℝ)⌉₊))
    (hfit : ∀ a : stdSimplex ℝ (Fin ⌈(k : ℝ) ^ (3 / 2 : ℝ)⌉₊),
      weightedChebyshevError k (chebyshevGridMoments z.val) mhat ≤
        weightedChebyshevError k (chebyshevGridMoments a.val) mhat + η) :
    wassersteinEDistOne μ (chebyshevGridLaw z) ≤
      ENNReal.ofReal ((36 + Real.pi / 2) / k + 2 * Γ + η) := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hg : 0 < ⌈(k : ℝ) ^ (3 / 2 : ℝ)⌉₊ :=
    (Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos hkpos _))
  have hrpow : (k : ℝ) ^ (3 / 2 : ℝ) = (k : ℝ) * Real.sqrt k := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_one_add' hkpos.le (by norm_num), ← Real.sqrt_eq_rpow]
  have hscale : (k : ℝ) * Real.sqrt k ≤ ⌈(k : ℝ) ^ (3 / 2 : ℝ)⌉₊ := by
    rw [← hrpow]
    exact Nat.le_ceil _
  have hgrid : Real.pi * Real.sqrt k / (2 * (⌈(k : ℝ) ^ (3 / 2 : ℝ)⌉₊ : ℝ)) ≤
      Real.pi / (2 * k) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_left hscale Real.pi_pos.le]
  apply (wassersteinEDistOne_gridLaw_le_of_weightedChebyshevError_le μ hμ hk hg mhat hnoise z hfit).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ 36 / k + 2 * Γ + Real.pi / (2 * k) + η := by linarith
    _ = _ := by ring

end NLAlib
