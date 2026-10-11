import NLAlib.Sketching.SubGaussianJL
import NLAlib.Concentration.Scalar.Net
import NLAlib.Matrix.Spectral
import NLAlib.Matrix.GramSingularBounds

/-!
# Extreme singular values of independent isotropic sub-Gaussian rows

The Gram error is controlled by a quadratic sphere net and the proved
Hanson–Wright specialization. Coordinates within each row may be dependent.
Source: operator re-derivation `pg:row-bound`, Vershynin 2012, Theorem 5.39.
Atlas: `subgaussian-matrix-norm`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- A quadratic sphere net turns squared-projection concentration into a Gram
operator bound. Source: operator re-derivation `pg:fixed-projection-tail` and
`pg:quadratic-net`; helper for `subgaussian-matrix-norm`. -/
theorem measure_lt_specNorm_gram_sub_card_le_of_independent_isotropic_rows
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [Nonempty m]
    (A : m → Ω → n → ℝ) (K : ℝ) (hK : 0 < K) (hind : iIndepFun A μ)
    (hmgf : ∀ i u, u ⬝ᵥ u = 1 → HasSubgaussianMGF (fun ω => A i ω ⬝ᵥ u)
      ⟨K ^ 2, sq_nonneg K⟩ μ)
    (hiso : ∀ i u, u ⬝ᵥ u = 1 → ∫ ω, (A i ω ⬝ᵥ u) ^ 2 ∂μ = 1)
    {v : ℝ} (hv : 0 ≤ v) :
    μ {ω | v < specNorm ((Matrix.of (fun i => A i ω))ᵀ *
        Matrix.of (fun i => A i ω) - (Fintype.card m : ℝ) • 1)} ≤
      ENNReal.ofReal (2 * (9 : ℝ) ^ Fintype.card n *
        Real.exp (-(1 / (256 * Real.exp 1 ^ 2)) *
          min ((v / 2) ^ 2 / ((Fintype.card m : ℝ) * K ^ 4)) ((v / 2) / K ^ 2))) := by
  classical
  obtain ⟨N, hNunit, hNcard, hNnet⟩ :=
    exists_finset_sphere_net n (show (0 : ℝ) < 1 / 4 by norm_num)
  norm_num only [show (1 + 2 / (1 / 4 : ℝ)) = 9 by norm_num] at hNcard
  let H : Ω → Matrix n n ℝ := fun ω =>
    (Matrix.of (fun i => A i ω))ᵀ * Matrix.of (fun i => A i ω) -
      (Fintype.card m : ℝ) • 1
  have hsym : ∀ ω, (H ω).IsSymm := by
    intro ω
    simp only [H, Matrix.IsSymm, Matrix.transpose_sub, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.transpose_one]
  have hquad : ∀ ω x, quadForm (H ω) x =
      ∑ i, (A i ω ⬝ᵥ x) ^ 2 - (Fintype.card m : ℝ) * (x ⬝ᵥ x) := by
    intro ω x
    change x ⬝ᵥ ((H ω) *ᵥ x) = _
    dsimp only [H]
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_smul, smul_eq_mul,
      ← mulVec_dotProduct_mulVec_self]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, pow_two]
  have hsub : {ω | v < specNorm (H ω)} ⊆
      ⋃ x ∈ N, {ω | v / 2 < |quadForm (H ω) x|} := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt] at hnot
    have h := specNorm_le_div_of_net_quadForm (hsym ω) N
      (by norm_num) (by norm_num) (by positivity) hNunit hNnet hnot
    have heq : (v / 2) / (1 - 2 * (1 / 4 : ℝ)) = v := by ring
    rw [heq] at h
    exact (not_lt_of_ge h) hω
  have hterm : ∀ x ∈ N, μ {ω | v / 2 < |quadForm (H ω) x|} ≤
      ENNReal.ofReal (2 * Real.exp (-(1 / (256 * Real.exp 1 ^ 2)) *
        min ((v / 2) ^ 2 / ((Fintype.card m : ℝ) * K ^ 4)) ((v / 2) / K ^ 2))) := by
    intro x hx
    let Y : m → Ω → ℝ := fun i ω => A i ω ⬝ᵥ x
    have hYind : iIndepFun Y μ := by
      simpa only [Y, Function.comp_def] using
        hind.comp (fun (_ : m) (u : n → ℝ) => u ⬝ᵥ x)
          (fun _ => by simp only [dotProduct]; fun_prop)
    have hYmgf : ∀ i, HasSubgaussianMGF (Y i) ⟨K ^ 2, sq_nonneg K⟩ μ := by
      intro i
      exact hmgf i x (hNunit x hx)
    have hYsq : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ = 1 := by
      intro i
      exact hiso i x (hNunit x hx)
    have h := measure_le_abs_sum_sq_sub_card_of_hasSubgaussianMGF Y K hK hYind
      hYmgf hYsq (show 0 ≤ v / 2 by positivity)
    calc μ {ω | v / 2 < |quadForm (H ω) x|}
        ≤ μ {ω | v / 2 ≤ |∑ i, Y i ω ^ 2 - (Fintype.card m : ℝ)|} := by
          apply measure_mono
          intro ω hω
          change v / 2 < |quadForm (H ω) x| at hω
          simpa only [Set.mem_ofPred_eq, hquad, hNunit x hx, mul_one, Y] using hω.le
      _ = ENNReal.ofReal ((μ {ω | v / 2 ≤ |∑ i, Y i ω ^ 2 -
          (Fintype.card m : ℝ)|}).toReal) :=
          (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h
  calc μ {ω | v < specNorm (H ω)}
      ≤ μ (⋃ x ∈ N, {ω | v / 2 < |quadForm (H ω) x|}) := measure_mono hsub
    _ ≤ ∑ x ∈ N, μ {ω | v / 2 < |quadForm (H ω) x|} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ N, ENNReal.ofReal (2 * Real.exp (-(1 / (256 * Real.exp 1 ^ 2)) *
          min ((v / 2) ^ 2 / ((Fintype.card m : ℝ) * K ^ 4)) ((v / 2) / K ^ 2))) :=
        Finset.sum_le_sum hterm
    _ = ENNReal.ofReal ((N.card : ℝ) * (2 * Real.exp (-(1 / (256 * Real.exp 1 ^ 2)) *
          min ((v / 2) ^ 2 / ((Fintype.card m : ℝ) * K ^ 4)) ((v / 2) / K ^ 2)))) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg N.card), ENNReal.ofReal_natCast]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      calc _ ≤ (9 : ℝ) ^ Fintype.card n * (2 * Real.exp _) :=
        mul_le_mul_of_nonneg_right hNcard (by positivity)
        _ = _ := by ring)

/-- Both domain-based extreme singular values of independent isotropic rows
lie in `√N ± (32 exp(1) K² √(log 9) √n + t)` except on a set of probability
at most `2 exp(-t²/(1024 exp(1)² K⁴))`. Coordinates inside a row may be
dependent, and no tall-matrix hypothesis is needed.
Source: operator re-derivation Theorem `pg:row-bound`, with its exact constants;
Vershynin 2012, Theorem 5.39.
atlas: subgaussian-matrix-norm -/
theorem measure_extreme_singular_failure_le_of_independent_isotropic_rows
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Nonempty m] [Nonempty n]
    (A : m → Ω → n → ℝ) (K : ℝ) (hK : 1 ≤ K) (hind : iIndepFun A μ)
    (hmgf : ∀ i u, u ⬝ᵥ u = 1 → HasSubgaussianMGF (fun ω => A i ω ⬝ᵥ u)
      ⟨K ^ 2, sq_nonneg K⟩ μ)
    (hiso : ∀ i u, u ⬝ᵥ u = 1 → ∫ ω, (A i ω ⬝ᵥ u) ^ 2 ∂μ = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | sigmaMin (Matrix.of (fun i => A i ω)) <
        Real.sqrt (Fintype.card m : ℝ) -
          (32 * Real.exp 1 * K ^ 2 * Real.sqrt (Real.log 9) *
            Real.sqrt (Fintype.card n : ℝ) + t) ∨
      Real.sqrt (Fintype.card m : ℝ) +
        (32 * Real.exp 1 * K ^ 2 * Real.sqrt (Real.log 9) *
          Real.sqrt (Fintype.card n : ℝ) + t) <
        specNorm (Matrix.of (fun i => A i ω))} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (1024 * Real.exp 1 ^ 2 * K ^ 4))) := by
  classical
  have hN : (0 : ℝ) < Fintype.card m := by exact_mod_cast Fintype.card_pos
  have hn : (0 : ℝ) ≤ Fintype.card n := Nat.cast_nonneg _
  have hKpos : 0 < K := by linarith
  have hlog : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  let D := 32 * Real.exp 1 * K ^ 2 * Real.sqrt (Real.log 9) *
    Real.sqrt (Fintype.card n : ℝ) + t
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let v := max (Real.sqrt (Fintype.card m : ℝ) * D) (D ^ 2)
  have hv : 0 ≤ v := (sq_nonneg D).trans (le_max_right _ _)
  have hs : 0 < Real.sqrt (Fintype.card m : ℝ) := Real.sqrt_pos.mpr hN
  have hs2 := Real.sq_sqrt hN.le
  have hfirst : D ^ 2 / (4 * K ^ 4) ≤
      (v / 2) ^ 2 / ((Fintype.card m : ℝ) * K ^ 4) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hvl : Real.sqrt (Fintype.card m : ℝ) * D ≤ v := le_max_left _ _
    have hv2 : (Fintype.card m : ℝ) * D ^ 2 ≤ v ^ 2 := by
      have h := pow_le_pow_left₀ (mul_nonneg hs.le hD) hvl 2
      rwa [mul_pow, hs2] at h
    nlinarith [mul_nonneg (sq_nonneg K) (sq_nonneg K),
      mul_nonneg (show 0 ≤ K ^ 4 by positivity) (sub_nonneg.mpr hv2)]
  have hsecond : D ^ 2 / (4 * K ^ 4) ≤ (v / 2) / K ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hvr : D ^ 2 ≤ v := le_max_right _ _
    have hK2 : 1 ≤ K ^ 2 := by nlinarith
    have hp : K ^ 2 ≤ 2 * K ^ 4 := by nlinarith [sq_nonneg (K ^ 2)]
    have hmul := mul_le_mul_of_nonneg_left hp (sq_nonneg D)
    have hmulv := mul_le_mul_of_nonneg_right hvr (show 0 ≤ 2 * K ^ 4 by positivity)
    nlinarith
  have hmin : D ^ 2 / (4 * K ^ 4) ≤
      min ((v / 2) ^ 2 / ((Fintype.card m : ℝ) * K ^ 4)) ((v / 2) / K ^ 2) :=
    le_min hfirst hsecond
  have hbase : 2 * (9 : ℝ) ^ Fintype.card n *
      Real.exp (-(1 / (256 * Real.exp 1 ^ 2)) *
        min ((v / 2) ^ 2 / ((Fintype.card m : ℝ) * K ^ 4)) ((v / 2) / K ^ 2)) ≤
      2 * Real.exp (-t ^ 2 / (1024 * Real.exp 1 ^ 2 * K ^ 4)) := by
    have hn2 := Real.sq_sqrt hn
    have hl2 := Real.sq_sqrt hlog
    have hD2 : 1024 * Real.exp 1 ^ 2 * K ^ 4 *
        ((Fintype.card n : ℝ) * Real.log 9) + t ^ 2 ≤ D ^ 2 := by
      have hc2 : (32 * Real.exp 1 * K ^ 2 * Real.sqrt (Real.log 9) *
          Real.sqrt (Fintype.card n : ℝ)) ^ 2 =
          1024 * Real.exp 1 ^ 2 * K ^ 4 * ((Fintype.card n : ℝ) * Real.log 9) := by
        simp only [mul_pow]
        rw [hl2, hn2]
        ring
      dsimp [D]
      have hp : 0 ≤ 32 * Real.exp 1 * K ^ 2 * Real.sqrt (Real.log 9) *
          Real.sqrt (Fintype.card n : ℝ) * t := by positivity
      nlinarith only [hc2, hp]
    have hexp : Real.exp (-(1 / (256 * Real.exp 1 ^ 2)) *
        min ((v / 2) ^ 2 / ((Fintype.card m : ℝ) * K ^ 4)) ((v / 2) / K ^ 2)) ≤
        Real.exp (-((Fintype.card n : ℝ) * Real.log 9)) *
          Real.exp (-t ^ 2 / (1024 * Real.exp 1 ^ 2 * K ^ 4)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      calc _ ≤ -(1 / (256 * Real.exp 1 ^ 2)) * (D ^ 2 / (4 * K ^ 4)) :=
            mul_le_mul_of_nonpos_left hmin (neg_nonpos.mpr (by positivity))
        _ = -D ^ 2 / (1024 * Real.exp 1 ^ 2 * K ^ 4) := by ring
        _ ≤ _ := by
          have hd : (Fintype.card n : ℝ) * Real.log 9 +
              t ^ 2 / (1024 * Real.exp 1 ^ 2 * K ^ 4) ≤
              D ^ 2 / (1024 * Real.exp 1 ^ 2 * K ^ 4) := by
            apply (le_div_iff₀ (by positivity)).mpr
            calc _ = 1024 * Real.exp 1 ^ 2 * K ^ 4 *
                ((Fintype.card n : ℝ) * Real.log 9) + t ^ 2 := by field_simp
              _ ≤ D ^ 2 := hD2
          simp only [neg_div]
          linarith only [hd]
    calc _ ≤ 2 * (9 : ℝ) ^ Fintype.card n *
        (Real.exp (-((Fintype.card n : ℝ) * Real.log 9)) *
          Real.exp (-t ^ 2 / (1024 * Real.exp 1 ^ 2 * K ^ 4))) := by gcongr
      _ = _ := by
        have hp9 : (9 : ℝ) ^ Fintype.card n =
            Real.exp ((Fintype.card n : ℝ) * Real.log 9) := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
        rw [hp9, ← mul_assoc, mul_assoc 2, ← Real.exp_add, add_neg_cancel,
          Real.exp_zero, mul_one]
  have hsub : {ω | sigmaMin (Matrix.of (fun i => A i ω)) <
        Real.sqrt (Fintype.card m : ℝ) - D ∨
        Real.sqrt (Fintype.card m : ℝ) + D < specNorm (Matrix.of (fun i => A i ω))} ⊆
      {ω | v < specNorm ((Matrix.of (fun i => A i ω))ᵀ *
        Matrix.of (fun i => A i ω) - (Fintype.card m : ℝ) • 1)} := by
    intro ω hω
    change _ < _ ∨ _ < _ at hω
    by_contra hnot
    simp only [Set.mem_ofPred_eq, not_lt] at hnot
    have heq : (Fintype.card m : ℝ) *
        max (D / Real.sqrt (Fintype.card m : ℝ))
          ((D / Real.sqrt (Fintype.card m : ℝ)) ^ 2) = v := by
      rw [mul_max_of_nonneg _ _ hN.le]
      dsimp [v]
      congr 1
      · rw [← mul_div_assoc]
        apply (div_eq_iff hs.ne').mpr
        nlinarith [hs2]
      · rw [div_pow, hs2]
        field_simp
    rw [← heq] at hnot
    obtain ⟨hlow, hhigh⟩ := sigmaMin_specNorm_bounds_of_gram_error
      (Matrix.of (fun i => A i ω)) hN.le (div_nonneg hD hs.le) hnot
    have hl : Real.sqrt (Fintype.card m : ℝ) *
        (1 - D / Real.sqrt (Fintype.card m : ℝ)) =
        Real.sqrt (Fintype.card m : ℝ) - D := by field_simp
    have hu : Real.sqrt (Fintype.card m : ℝ) *
        (1 + D / Real.sqrt (Fintype.card m : ℝ)) =
        Real.sqrt (Fintype.card m : ℝ) + D := by field_simp
    rw [hl] at hlow
    rw [hu] at hhigh
    rcases hω with hω | hω <;> linarith
  exact (measure_mono hsub).trans
    ((measure_lt_specNorm_gram_sub_card_le_of_independent_isotropic_rows
      A K hKpos hind hmgf hiso hv).trans (ENNReal.ofReal_le_ofReal hbase))

end NLAlib
