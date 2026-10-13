import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Interval integration for bounded variation functions

Finite variation controls the error of left-endpoint quadrature and
oscillatory integrals. Helpers for `chebyshev-coeff-bv-decay`.
-/

noncomputable section

open Set Finset MeasureTheory
open scoped ENNReal

namespace NLAlib

/-- A real bounded-variation function on an interval is interval integrable.
Source: Jordan decomposition into two monotone functions; operator derivations `polyseries:bv`,
helper for `chebyshev-coeff-bv-decay`. -/
theorem intervalIntegrable_of_boundedVariationOn {h : ℝ → ℝ} {a b : ℝ}
    (hh : BoundedVariationOn h (uIcc a b)) : IntervalIntegrable h volume a b := by
  obtain ⟨p, q, hp, hq, rfl⟩ := hh.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  exact hp.intervalIntegrable.sub hq.intervalIntegrable

/-- The sum of the real variations of adjacent partition cells is the total variation.
Source: Mathlib `eVariationOn.sum'`; operator derivations `polyseries:bv`,
helper for `chebyshev-coeff-bv-decay`. -/
theorem sum_variationOn_cells_eq {h : ℝ → ℝ} {t : ℕ → ℝ} {N : ℕ}
    (ht : Monotone t) (hh : BoundedVariationOn h (Icc (t 0) (t N))) :
    ∑ j ∈ range N, (eVariationOn h (Icc (t j) (t (j + 1)))).toReal =
      (eVariationOn h (Icc (t 0) (t N))).toReal := by
  have hfinite : ∀ j ∈ range N, eVariationOn h (Icc (t j) (t (j + 1))) ≠ ⊤ := by
    intro j hj
    apply hh.mono
    intro x hx
    exact ⟨(ht (Nat.zero_le j)).trans hx.1,
      hx.2.trans (ht (Nat.succ_le_of_lt (Finset.mem_range.mp hj)))⟩
  rw [← ENNReal.toReal_sum hfinite, eVariationOn.sum' h ht]

/-- The sum of sampled absolute increments is at most total variation.
Source: Mathlib variation along monotone partitions; operator derivations `polyseries:bv`,
helper for `chebyshev-coeff-bv-decay`. -/
theorem sum_abs_sub_le_variationOn {h : ℝ → ℝ} {t : ℕ → ℝ} {N : ℕ}
    (ht : Monotone t) (hh : BoundedVariationOn h (Icc (t 0) (t N))) :
    ∑ j ∈ range N, |h (t (j + 1)) - h (t j)| ≤
      (eVariationOn h (Icc (t 0) (t N))).toReal := by
  have he := eVariationOn.sum_le_of_monotoneOn_Iic (f := h) (n := N)
    (s := Icc (t 0) (t N)) (ht.monotoneOn _) (fun i hi =>
      ⟨ht (Nat.zero_le i), ht hi⟩)
  have hleft : (∑ j ∈ range N, edist (h (t (j + 1))) (h (t j))) ≠ (⊤ : ℝ≥0∞) :=
    ne_top_of_le_ne_top hh he
  have hr := (ENNReal.toReal_le_toReal hleft hh).mpr he
  rw [ENNReal.toReal_sum (fun j _ => edist_ne_top (h (t (j + 1))) (h (t j)))] at hr
  simpa only [edist_dist,
    Real.dist_eq, ENNReal.toReal_ofReal (abs_nonneg _)] using hr

/-- Left-endpoint quadrature against a bounded continuous integrand has error
at most mesh times integrand bound times total variation.
Source: the finite partition estimate in operator derivations `polyseries:bvbase`;
helper for `chebyshev-coeff-bv-decay`. -/
theorem abs_integral_sub_left_sum_le_mesh_mul_variation {h g : ℝ → ℝ}
    {t : ℕ → ℝ} {N : ℕ} {ε B : ℝ} (ht : Monotone t)
    (hh : BoundedVariationOn h (Icc (t 0) (t N)))
    (hg : ContinuousOn g (Icc (t 0) (t N))) (hB : 0 ≤ B) (_hε : 0 ≤ ε)
    (hgB : ∀ x ∈ Icc (t 0) (t N), |g x| ≤ B)
    (hmesh : ∀ j < N, t (j + 1) - t j ≤ ε) :
    |(∫ x in t 0..t N, h x * g x) -
        ∑ j ∈ range N, h (t j) * ∫ x in t j..t (j + 1), g x| ≤
      ε * B * (eVariationOn h (Icc (t 0) (t N))).toReal := by
  have hcellsub : ∀ j < N, Icc (t j) (t (j + 1)) ⊆ Icc (t 0) (t N) := by
    intro j hj x hx
    exact ⟨(ht (Nat.zero_le _)).trans hx.1, hx.2.trans (ht (Nat.succ_le_of_lt hj))⟩
  have hcellBV : ∀ j < N, BoundedVariationOn h (Icc (t j) (t (j + 1))) :=
    fun j hj => hh.mono (hcellsub j hj)
  have hgi : ∀ j < N, IntervalIntegrable g volume (t j) (t (j + 1)) := by
    intro j hj
    exact (hg.mono (hcellsub j hj)).intervalIntegrable_of_Icc (ht (Nat.le_succ _))
  have hhi : ∀ j < N, IntervalIntegrable h volume (t j) (t (j + 1)) := by
    intro j hj
    apply intervalIntegrable_of_boundedVariationOn
    rw [uIcc_of_le (ht (Nat.le_succ _))]
    exact hcellBV j hj
  have hhgi : ∀ j < N, IntervalIntegrable (fun x => h x * g x) volume (t j) (t (j + 1)) := by
    intro j hj
    exact (hhi j hj).mul_continuousOn (by
      rw [uIcc_of_le (ht (Nat.le_succ _))]
      exact hg.mono (hcellsub j hj))
  have hcell : ∀ j < N,
      |(∫ x in t j..t (j + 1), h x * g x) -
        h (t j) * ∫ x in t j..t (j + 1), g x| ≤
        ε * B * (eVariationOn h (Icc (t j) (t (j + 1)))).toReal := by
    intro j hj
    have heq : (∫ x in t j..t (j + 1), h x * g x) -
        h (t j) * ∫ x in t j..t (j + 1), g x =
        ∫ x in t j..t (j + 1), (h x - h (t j)) * g x := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub (hhgi j hj)
        ((hgi j hj).const_mul (h (t j)))]
      congr 1
      funext x
      ring
    rw [heq, ← Real.norm_eq_abs]
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := t j) (b := t (j + 1))
      (C := (eVariationOn h (Icc (t j) (t (j + 1)))).toReal * B) (f := fun x => (h x - h (t j)) * g x)
      (fun x hx => by
        have hx' : x ∈ Icc (t j) (t (j + 1)) := by
          rw [uIoc_of_le (ht (Nat.le_succ _))] at hx
          exact Ioc_subset_Icc_self hx
        rw [Real.norm_eq_abs, abs_mul]
        have hdist := (hcellBV j hj).dist_le hx' ⟨le_rfl, ht (Nat.le_succ _)⟩
        rw [Real.dist_eq] at hdist
        exact mul_le_mul hdist (hgB x (hcellsub j hj hx')) (abs_nonneg _) ENNReal.toReal_nonneg)
    rw [abs_of_nonneg (sub_nonneg.mpr (ht (Nat.le_succ _)))] at hnorm
    refine hnorm.trans ?_
    have hv := ENNReal.toReal_nonneg (a := eVariationOn h (Icc (t j) (t (j + 1))))
    nlinarith [mul_le_mul_of_nonneg_left (hmesh j hj) (mul_nonneg hv hB)]
  rw [← intervalIntegral.sum_integral_adjacent_intervals hhgi, ← sum_sub_distrib]
  calc |∑ j ∈ range N, ((∫ x in t j..t (j + 1), h x * g x) -
      h (t j) * ∫ x in t j..t (j + 1), g x)| ≤
      ∑ j ∈ range N, |(∫ x in t j..t (j + 1), h x * g x) -
        h (t j) * ∫ x in t j..t (j + 1), g x| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range N, ε * B * (eVariationOn h (Icc (t j) (t (j + 1)))).toReal :=
      sum_le_sum fun j hj => hcell j (Finset.mem_range.mp hj)
    _ = ε * B * (eVariationOn h (Icc (t 0) (t N))).toReal := by
      rw [← mul_sum, sum_variationOn_cells_eq ht hh]

/-- Endpoint-zero sampled primitives give an Abel bound by total variation.
Source: finite summation by parts; operator derivations `polyseries:bvbase`,
helper for `chebyshev-coeff-bv-decay`. -/
theorem abs_sum_mul_primitive_sub_le_variation {h G : ℝ → ℝ} {t : ℕ → ℝ}
    {N : ℕ} {M : ℝ} (ht : Monotone t)
    (hh : BoundedVariationOn h (Icc (t 0) (t N))) (hM : 0 ≤ M)
    (hG : ∀ x ∈ Icc (t 0) (t N), |G x| ≤ M) (hG0 : G (t 0) = 0) (hGN : G (t N) = 0) :
    |∑ j ∈ range N, h (t j) * (G (t (j + 1)) - G (t j))| ≤
      M * (eVariationOn h (Icc (t 0) (t N))).toReal := by
  have hAbel := Finset.sum_range_by_parts (fun j => h (t j))
    (fun j => G (t (j + 1)) - G (t j)) N
  simp only [smul_eq_mul] at hAbel
  simp_rw [Finset.sum_range_sub (fun i => G (t i))] at hAbel
  simp only [hG0, hGN, sub_zero, mul_zero, zero_sub] at hAbel
  rw [hAbel, abs_neg]
  calc |∑ j ∈ range (N - 1), (h (t (j + 1)) - h (t j)) * G (t (j + 1))| ≤
      ∑ j ∈ range (N - 1), |(h (t (j + 1)) - h (t j)) * G (t (j + 1))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range (N - 1), |h (t (j + 1)) - h (t j)| * M := by
      apply sum_le_sum
      intro j hj
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply hG
      exact ⟨ht (Nat.zero_le _), ht (by have := Finset.mem_range.mp hj; omega)⟩
    _ = M * ∑ j ∈ range (N - 1), |h (t (j + 1)) - h (t j)| := by rw [← sum_mul]; ring
    _ ≤ M * ∑ j ∈ range N, |h (t (j + 1)) - h (t j)| := by
      apply mul_le_mul_of_nonneg_left _ hM
      exact sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le _ _))
        (fun _ _ _ => abs_nonneg _)
    _ ≤ M * (eVariationOn h (Icc (t 0) (t N))).toReal :=
      mul_le_mul_of_nonneg_left (sum_abs_sub_le_variationOn ht hh) hM

/-- Integrating a bounded-variation function against a continuous derivative with
a bounded endpoint-zero primitive costs only primitive bound times total variation.
Source: operator derivations `polyseries:bvbase`; finite partition error and Abel's lemma.
Helper for `chebyshev-coeff-bv-decay`. -/
theorem abs_integral_mul_le_primitive_bound_mul_variation {h g G : ℝ → ℝ}
    {a b B M : ℝ} (hab : a < b) (hh : BoundedVariationOn h (Icc a b))
    (hg : ContinuousOn g (Icc a b)) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hgB : ∀ x ∈ Icc a b, |g x| ≤ B) (hGM : ∀ x ∈ Icc a b, |G x| ≤ M)
    (hGa : G a = 0) (hGb : G b = 0) (hder : ∀ x ∈ Icc a b, HasDerivAt G (g x) x) :
    |∫ x in a..b, h x * g x| ≤ M * (eVariationOn h (Icc a b)).toReal := by
  let V := (eVariationOn h (Icc a b)).toReal
  have hbound : ∀ n : ℕ, |∫ x in a..b, h x * g x| ≤
      M * V + ((b - a) / (n + 1 : ℕ)) * B * V := by
    intro n
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    let t : ℕ → ℝ := fun j => a + (b - a) * j / (n + 1 : ℕ)
    have ht : Monotone t := by
      intro i j hij
      dsimp [t]
      gcongr
    have ht0 : t 0 = a := by simp [t]
    have htN : t (n + 1) = b := by dsimp [t]; push_cast; field_simp; ring
    have hht : BoundedVariationOn h (Icc (t 0) (t (n + 1))) := by rw [ht0, htN]; exact hh
    have hgt : ContinuousOn g (Icc (t 0) (t (n + 1))) := by rw [ht0, htN]; exact hg
    have hmesh : ∀ j < n + 1, t (j + 1) - t j ≤ (b - a) / (n + 1 : ℕ) := by
      intro j hj
      dsimp [t]
      push_cast
      exact le_of_eq (by ring)
    have hB' : ∀ x ∈ Icc (t 0) (t (n + 1)), |g x| ≤ B := by rw [ht0, htN]; exact hgB
    have hM' : ∀ x ∈ Icc (t 0) (t (n + 1)), |G x| ≤ M := by rw [ht0, htN]; exact hGM
    have herr := abs_integral_sub_left_sum_le_mesh_mul_variation ht hht hgt hB
      (by positivity : 0 ≤ (b - a) / (n + 1 : ℕ)) hB' hmesh
    have hsamp := abs_sum_mul_primitive_sub_le_variation ht hht hM hM'
      (by rwa [ht0]) (by rwa [htN])
    have hprimitive : ∀ j < n + 1,
        ∫ x in t j..t (j + 1), g x = G (t (j + 1)) - G (t j) := by
      intro j hj
      have hsub : Icc (t j) (t (j + 1)) ⊆ Icc a b := by
        rw [← ht0, ← htN]
        exact Set.Icc_subset_Icc (ht (Nat.zero_le _)) (ht (Nat.succ_le_of_lt hj))
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x hx
        rw [uIcc_of_le (ht (Nat.le_succ _))] at hx
        exact hder x (hsub hx)
      · exact (hg.mono hsub).intervalIntegrable_of_Icc (ht (Nat.le_succ _))
    have heq : (∑ j ∈ range (n + 1), h (t j) * ∫ x in t j..t (j + 1), g x) =
        ∑ j ∈ range (n + 1), h (t j) * (G (t (j + 1)) - G (t j)) := by
      apply sum_congr rfl
      intro j hj
      rw [hprimitive j (Finset.mem_range.mp hj)]
    rw [ht0, htN] at herr
    rw [heq] at herr
    rw [ht0, htN] at hsamp
    have htri : |∫ x in a..b, h x * g x| ≤
        |(∫ x in a..b, h x * g x) -
          ∑ j ∈ range (n + 1), h (t j) * (G (t (j + 1)) - G (t j))| +
        |∑ j ∈ range (n + 1), h (t j) * (G (t (j + 1)) - G (t j))| := by
      have := abs_add_le
        ((∫ x in a..b, h x * g x) - ∑ j ∈ range (n + 1), h (t j) * (G (t (j + 1)) - G (t j)))
        (∑ j ∈ range (n + 1), h (t j) * (G (t (j + 1)) - G (t j)))
      simpa only [sub_add_cancel] using this
    exact htri.trans ((add_le_add herr hsamp).trans_eq (by dsimp [V]; ring))
  have hrate : Filter.Tendsto (fun n : ℕ => ((b - a) / (n + 1 : ℕ)) * B * V)
      Filter.atTop (nhds 0) := by
    have h := ((tendsto_const_div_atTop_nhds_zero_nat (b - a)).comp
      (Filter.tendsto_add_atTop_nat 1)).mul_const B |>.mul_const V
    simpa only [Function.comp_apply, zero_mul] using h
  have hlimit : Filter.Tendsto (fun n : ℕ => M * V + ((b - a) / (n + 1 : ℕ)) * B * V)
      Filter.atTop (nhds (M * V)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hrate
  exact ge_of_tendsto hlimit (Filter.Eventually.of_forall hbound)

end NLAlib
