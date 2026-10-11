import NLAlib.Concentration.SquaredProjections
import NLAlib.Concentration.Scalar.SubGaussian
import Mathlib.Probability.Independence.InfinitePi

/-!
# Distributional Johnson–Lindenstrauss for sub-Gaussian sketches

Independent isotropic rows with directional MGF proxy `K²` preserve each fixed
squared norm after normalization by the square root of the row count. The explicit
constant is exactly `1/(256 * exp(1)²)` from the live Hanson–Wright theorem.

Source: `open_problems_operator_rederivations.tex`, Theorem `pg:jl` and
Lemma `pg:linear-proxy`; Vershynin 2018, Theorem 6.2.1.
Atlas: `jl-subgaussian`.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- Independent isotropic rows with directional MGF proxy `K²` give distributional
JL with the exact constant `1/(256 exp(1)²)`. Coordinates within a row may be dependent.
The sketch is `(card m)^(-1/2) A`; all finite row and column types are allowed.
For a zero vector the strict failure event is empty; for zero rows the totalized
normalization is zero and the numerical bound is the trivial bound `2`.
Source: operator re-derivation Theorem `pg:jl` (independent-row extension),
using Lemma `pg:squares`. The independent-entry hypotheses are discharged separately.
atlas: jl-subgaussian (partial) -/
theorem measure_lt_abs_mulVec_sq_sub_le_of_independent_isotropic_rows
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (A : m → Ω → n → ℝ) (K : ℝ) (hK : 1 ≤ K) (hind : iIndepFun A μ)
    (hmgf : ∀ i u, HasSubgaussianMGF (fun ω => A i ω ⬝ᵥ u)
      ⟨K ^ 2 * (u ⬝ᵥ u), mul_nonneg (sq_nonneg K) (dotProduct_self_nonneg u)⟩ μ)
    (hiso : ∀ i u, ∫ ω, (A i ω ⬝ᵥ u) ^ 2 ∂μ = u ⬝ᵥ u)
    (x : n → ℝ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    (μ {ω | |((1 / Real.sqrt (Fintype.card m : ℝ)) • Matrix.of (fun i => A i ω)) *ᵥ x ⬝ᵥ
          ((1 / Real.sqrt (Fintype.card m : ℝ)) • Matrix.of (fun i => A i ω)) *ᵥ x
          - x ⬝ᵥ x| > ε * (x ⬝ᵥ x)}).toReal ≤
      2 * Real.exp (-((Fintype.card m : ℝ) * ε ^ 2 / (256 * Real.exp 1 ^ 2 * K ^ 4))) := by
  classical
  rcases isEmpty_or_nonempty m with hm | hm
  · refine measureReal_le_one.trans ?_
    simp only [Fintype.card_eq_zero, Nat.cast_zero, zero_mul, zero_div, neg_zero, Real.exp_zero]
    norm_num
  by_cases hx0 : x ⬝ᵥ x = 0
  · have hx : x = 0 := dotProduct_self_eq_zero.mp hx0
    subst x
    simp only [Matrix.mulVec_zero, dotProduct_zero, sub_zero, mul_zero, abs_zero,
      lt_self_iff_false, Set.ofPred_false, measure_empty, ENNReal.toReal_zero]
    positivity
  have hkpos : (0 : ℝ) < Fintype.card m := by exact_mod_cast Fintype.card_pos
  have hpos : 0 < x ⬝ᵥ x := lt_of_le_of_ne (dotProduct_self_nonneg _) (Ne.symm hx0)
  set r := Real.sqrt (x ⬝ᵥ x) with hr_def
  have hr : 0 < r := Real.sqrt_pos.2 hpos
  set u := r⁻¹ • x with hu_def
  have hu : u ⬝ᵥ u = 1 := by
    rw [hu_def, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      ← sq, inv_pow, hr_def, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hx0]
  have hxu : x = r • u := by rw [hu_def, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  let Y : m → Ω → ℝ := fun i ω => A i ω ⬝ᵥ u
  have hindY : iIndepFun Y μ := by
    simpa only [Y, Function.comp_def] using
      hind.comp (fun (_ : m) (v : n → ℝ) => v ⬝ᵥ u)
        (fun _ => by simp only [dotProduct]; fun_prop)
  have hmgfY : ∀ i, HasSubgaussianMGF (Y i) ⟨K ^ 2, sq_nonneg K⟩ μ := by
    intro i
    simpa only [Y, hu, mul_one] using hmgf i u
  have hsqY : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ = 1 := by
    intro i
    simpa only [Y, hu] using hiso i u
  have hid : ∀ ω,
      ((1 / Real.sqrt (Fintype.card m : ℝ)) • Matrix.of (fun i => A i ω)) *ᵥ x ⬝ᵥ
        ((1 / Real.sqrt (Fintype.card m : ℝ)) • Matrix.of (fun i => A i ω)) *ᵥ x =
      (x ⬝ᵥ x) / Fintype.card m * ∑ i, Y i ω ^ 2 := by
    intro ω
    have hscale : (1 / Real.sqrt (Fintype.card m : ℝ)) ^ 2 = 1 / Fintype.card m := by
      rw [div_pow, Real.sq_sqrt hkpos.le, one_pow]
    have hr2 : r ^ 2 = x ⬝ᵥ x := Real.sq_sqrt hpos.le
    conv_lhs => rw [hxu]
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq, mul_pow, hscale, hr2]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Y, ← sq]
    ring
  have hsub : {ω | |((1 / Real.sqrt (Fintype.card m : ℝ)) •
        Matrix.of (fun i => A i ω)) *ᵥ x ⬝ᵥ
        ((1 / Real.sqrt (Fintype.card m : ℝ)) • Matrix.of (fun i => A i ω)) *ᵥ x
        - x ⬝ᵥ x| > ε * (x ⬝ᵥ x)} ⊆
      {ω | (Fintype.card m : ℝ) * ε ≤ |∑ i, Y i ω ^ 2 - Fintype.card m|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, hid] at hω ⊢
    have heq : (x ⬝ᵥ x) / Fintype.card m * ∑ i, Y i ω ^ 2 - x ⬝ᵥ x =
        (x ⬝ᵥ x) / Fintype.card m * (∑ i, Y i ω ^ 2 - Fintype.card m) := by
      field_simp
    rw [heq, abs_mul, abs_of_pos (div_pos hpos hkpos)] at hω
    have hcancel : ε * (x ⬝ᵥ x) =
        (x ⬝ᵥ x) / Fintype.card m * ((Fintype.card m : ℝ) * ε) := by field_simp
    rw [hcancel] at hω
    exact (lt_of_mul_lt_mul_left hω (div_nonneg hpos.le hkpos.le)).le
  have hKpos : 0 < K := by linarith
  have hK2 : ε ≤ K ^ 2 := by nlinarith [sq_nonneg (K - 1)]
  have hfirst : ((Fintype.card m : ℝ) * ε) ^ 2 /
      ((Fintype.card m : ℝ) * K ^ 4) = (Fintype.card m : ℝ) * ε ^ 2 / K ^ 4 := by
    field_simp
  have hmin : min (((Fintype.card m : ℝ) * ε) ^ 2 /
      ((Fintype.card m : ℝ) * K ^ 4)) (((Fintype.card m : ℝ) * ε) / K ^ 2) =
      (Fintype.card m : ℝ) * ε ^ 2 / K ^ 4 := by
    rw [hfirst, min_eq_left]
    calc (Fintype.card m : ℝ) * ε ^ 2 / K ^ 4 =
        ((Fintype.card m : ℝ) * ε / K ^ 2) * (ε / K ^ 2) := by field_simp
      _ ≤ ((Fintype.card m : ℝ) * ε / K ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left ((div_le_one (by positivity)).2 hK2) (by positivity)
      _ = (Fintype.card m : ℝ) * ε / K ^ 2 := mul_one _
  have h := measure_le_abs_sum_sq_sub_card_of_hasSubgaussianMGF Y K hKpos hindY hmgfY hsqY
    (u := (Fintype.card m : ℝ) * ε) (by positivity)
  rw [hmin] at h
  refine (measureReal_mono hsub).trans (h.trans_eq ?_)
  congr 2
  ring

/-- Mutually independent centered unit-second-moment entries give distributional
JL with MGF proxy `K²` and the explicit constant `1/(256 exp(1)²)`.
Row independence, directional proxies and isotropy are derived from the entry
assumptions. Identical entry distributions are not required. All finite index types,
zero vectors and the trivial zero-row numerical extension are included.
Source: operator re-derivation Theorem `pg:jl` and Lemma `pg:linear-proxy`;
the source states positive row count, while this theorem additionally totalizes zero rows.
atlas: jl-subgaussian -/
theorem measure_lt_abs_mulVec_sq_sub_le_of_independent_subgaussian_entries
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : m → Ω → n → ℝ) (K : ℝ) (hK : 1 ≤ K)
    (hind : iIndepFun (fun e : m × n => fun ω => A e.1 ω e.2) μ)
    (hmgf : ∀ i j, HasSubgaussianMGF (fun ω => A i ω j) ⟨K ^ 2, sq_nonneg K⟩ μ)
    (hmean : ∀ i j, ∫ ω, A i ω j ∂μ = 0)
    (hsq : ∀ i j, ∫ ω, A i ω j ^ 2 ∂μ = 1)
    (x : n → ℝ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    (μ {ω | |((1 / Real.sqrt (Fintype.card m : ℝ)) • Matrix.of (fun i => A i ω)) *ᵥ x ⬝ᵥ
          ((1 / Real.sqrt (Fintype.card m : ℝ)) • Matrix.of (fun i => A i ω)) *ᵥ x
          - x ⬝ᵥ x| > ε * (x ⬝ᵥ x)}).toReal ≤
      2 * Real.exp (-((Fintype.card m : ℝ) * ε ^ 2 / (256 * Real.exp 1 ^ 2 * K ^ 4))) := by
  classical
  have hmeas : ∀ i j, AEMeasurable (fun ω => A i ω j) μ :=
    fun i j => (hmgf i j).integrable.aemeasurable
  have hrow : ∀ i, iIndepFun (fun j ω => A i ω j) μ := fun i =>
    hind.precomp (g := fun j => (i, j)) (fun _ _ h => (Prod.mk.inj h).2)
  have hrowlaw : ∀ i, μ.map (A i) = Measure.pi (fun j => μ.map (fun ω => A i ω j)) :=
    fun i => (hrow i).map_fun_eq_pi_map (hmeas i)
  have : ∀ i j, IsProbabilityMeasure (μ.map (fun ω => A i ω j)) :=
    fun i j => Measure.isProbabilityMeasure_map (hmeas i j)
  have hflat : AEMeasurable (fun ω (e : m × n) => A e.1 ω e.2) μ :=
    aemeasurable_pi_lambda _ fun e => hmeas e.1 e.2
  have hflatlaw : μ.map (fun ω (e : m × n) => A e.1 ω e.2) =
      Measure.pi (fun e : m × n => μ.map (fun ω => A e.1 ω e.2)) :=
    hind.map_fun_eq_pi_map (fun e : m × n => hmeas e.1 e.2)
  have hcurried : μ.map (fun ω i => A i ω) =
      Measure.pi (fun i => Measure.pi (fun j => μ.map (fun ω => A i ω j))) := by
    change μ.map ((MeasurableEquiv.curry m n ℝ) ∘ (fun ω (e : m × n) => A e.1 ω e.2)) = _
    rw [← AEMeasurable.map_map_of_aemeasurable
      (MeasurableEquiv.curry m n ℝ).measurable.aemeasurable hflat,
      hflatlaw]
    simpa only [Measure.infinitePi_eq_pi] using
      Measure.infinitePi_map_curry (fun i j => μ.map (fun ω => A i ω j))
  have hindRows : iIndepFun A μ := by
    apply (iIndepFun_iff_map_fun_eq_pi_map
      (fun i => aemeasurable_pi_lambda _ fun j => hmeas i j)).2
    simpa only [hrowlaw] using hcurried
  apply measure_lt_abs_mulVec_sq_sub_le_of_independent_isotropic_rows
    A K hK hindRows ?_ ?_ x hε0 hε1
  · intro i u
    let c : NNReal := ⟨K ^ 2, sq_nonneg K⟩
    have h := hasSubgaussianMGF_finset_sum_mul_of_iIndepFun (hrow i)
      (c := fun _ => c) (s := Finset.univ)
      (fun j _ => hmgf i j) u
    have hproxy : (∑ j : n, (u j ^ 2).toNNReal * c) =
        ⟨K ^ 2 * (u ⬝ᵥ u), mul_nonneg (sq_nonneg K) (dotProduct_self_nonneg u)⟩ := by
      ext
      simp only [NNReal.coe_sum, NNReal.coe_mul]
      change (∑ j, ((u j ^ 2).toNNReal : ℝ) * K ^ 2) = K ^ 2 * (u ⬝ᵥ u)
      simp only [Real.coe_toNNReal _ (sq_nonneg _)]
      simp only [dotProduct, ← sq]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hproxy] at h
    simpa only [dotProduct, mul_comm] using h
  · intro i u
    have hLp : ∀ j, MemLp (fun ω => A i ω j) 2 μ := by
      intro j
      simpa using (hmgf i j).memLp 2
    have hprod : ∀ j l, Integrable (fun ω => A i ω j * A i ω l) μ := fun j l =>
      (hLp j).integrable_mul (hLp l)
    have hcross : ∀ j l, ∫ ω, A i ω j * A i ω l ∂μ = if j = l then 1 else 0 := by
      intro j l
      split_ifs with h
      · subst l
        simpa only [sq] using hsq i j
      · rw [((hrow i).indepFun h).integral_fun_mul_eq_mul_integral
          (hmgf i j).integrable.aestronglyMeasurable
          (hmgf i l).integrable.aestronglyMeasurable,
          hmean i j, zero_mul]
    have hexpand : ∀ ω, (A i ω ⬝ᵥ u) ^ 2 =
        ∑ j, ∑ l, (u j * u l) * (A i ω j * A i ω l) := by
      intro ω
      rw [sq, dotProduct, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    calc
      (∫ ω, (A i ω ⬝ᵥ u) ^ 2 ∂μ) =
        ∑ j, ∑ l, (∫ ω, (u j * u l) * (A i ω j * A i ω l) ∂μ) := by
        simp_rw [hexpand]
        rw [integral_finsetSum _ fun j _ =>
          integrable_finsetSum _ fun l _ => (hprod j l).const_mul (u j * u l)]
        exact Finset.sum_congr rfl fun j _ =>
          integral_finsetSum _ fun l _ => (hprod j l).const_mul (u j * u l)
      _ = ∑ j, ∑ l, (u j * u l) * (if j = l then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro l _
        rw [integral_const_mul, hcross]
      _ = u ⬝ᵥ u := by simp [dotProduct]

end NLAlib
