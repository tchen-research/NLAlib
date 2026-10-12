import NLAlib.ForMathlib.Probability.BoundedDifferences
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Sharp bounded-differences concentration by coordinate averaging

Finite product averaging preserves remaining coordinate oscillations. Peeling
off one coordinate and using Hoeffding with its actual range diameter yields
the exponent `θ² ∑ cᵢ²/8`, including heterogeneous measurable coordinates.

Source: operator manuscript `thm:mcdiarmidmgf` and `cor:mcdiarmid`;
Boucheron–Lugosi–Massart 2013, Theorem 6.2.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory

namespace NLAlib

/-- Bounded measurable scalar functions have integrable exponential moments on
probability spaces. Supports the product averaging proof of `mcdiarmid`. -/
theorem integrable_exp_mul_of_abs_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) (θ : ℝ) :
    Integrable (fun x => Real.exp (θ * f x)) μ := by
  refine Integrable.of_bound (by fun_prop) (Real.exp (|θ| * M))
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg _))

/-- The bounded finite-coordinate averaging calculation before centring.
The auxiliary uniform bound is discharged from coordinate oscillation in the
public product theorem. Source: manuscript `thm:mcdiarmidmgf`. -/
theorem integral_exp_mul_le_exp_of_fin_coordinate_oscillation
    (N : ℕ) {S : Fin N → Type*} [∀ i, MeasurableSpace (S i)]
    (μ : ∀ i, Measure (S i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, S i) → ℝ) (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    (c : Fin N → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hcoord : ∀ i (x : ∀ j, S j) (y : S i),
      |f (Function.update x i y) - f x| ≤ c i) (θ : ℝ) :
    ∫ x, Real.exp (θ * f x) ∂Measure.pi μ ≤
      Real.exp (θ * (∫ x, f x ∂Measure.pi μ) + θ ^ 2 * (∑ i, c i ^ 2) / 8) := by
  induction N with
  | zero =>
    let x₀ : ∀ i : Fin 0, S i := fun i => Fin.elim0 i
    have he : f = fun _ => f x₀ := funext fun _ => congrArg f (Subsingleton.elim _ _)
    rw [he]
    simp
  | succ N ih =>
    let ν := Measure.pi (fun i : Fin N => μ i.succ)
    let F (p : S 0 × (∀ i : Fin N, S i.succ)) := f (Fin.cons p.1 p.2)
    have hcons : Measurable (fun p : S 0 × (∀ i : Fin N, S i.succ) => Fin.cons p.1 p.2) := by
      refine measurable_pi_lambda _ fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using measurable_fst
      · simpa only [Fin.cons_succ, Function.comp_def] using
          (measurable_pi_apply j).comp measurable_snd
    have hFm : Measurable F := hf.comp hcons
    have hFM (p) : |F p| ≤ M := hM _
    have hFi : Integrable F ((μ 0).prod ν) :=
      Integrable.of_bound hFm.aestronglyMeasurable M (Filter.Eventually.of_forall hFM)
    have hFsection (y : ∀ i : Fin N, S i.succ) : Integrable (fun z => F (z, y)) (μ 0) :=
      Integrable.of_bound (hFm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
        M (Filter.Eventually.of_forall fun z => hFM _)
    let g (y : ∀ i : Fin N, S i.succ) := ∫ z, F (z, y) ∂μ 0
    have hgm : Measurable g := hFm.stronglyMeasurable.integral_prod_left'.measurable
    have hgM (y) : |g y| ≤ M := by
      calc |g y| ≤ ∫ z, |F (z, y)| ∂μ 0 := by
            simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z => F (z, y))
        _ ≤ ∫ _ : S 0, M ∂μ 0 :=
            integral_mono (hFsection y).abs (integrable_const _) (fun _ => hFM _)
        _ = M := by simp
    have hgcoord : ∀ i (y : ∀ j : Fin N, S j.succ) (z : S i.succ),
        |g (Function.update y i z) - g y| ≤ c i.succ := by
      intro i y z
      rw [show g (Function.update y i z) - g y =
        ∫ a, F (a, Function.update y i z) - F (a, y) ∂μ 0 from
          (integral_sub (hFsection _) (hFsection _)).symm]
      have hi := (hFsection (Function.update y i z)).sub (hFsection y)
      calc |∫ a, F (a, Function.update y i z) - F (a, y) ∂μ 0| ≤
          ∫ a, |F (a, Function.update y i z) - F (a, y)| ∂μ 0 := by
            simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
              (fun a => F (a, Function.update y i z) - F (a, y))
        _ ≤ ∫ _ : S 0, c i.succ ∂μ 0 := by
            refine integral_mono hi.abs (integrable_const _) fun a => ?_
            simpa only [F, Fin.cons_update] using hcoord i.succ (Fin.cons a y) z
        _ = c i.succ := by simp
    have hrec := ih (fun i => μ i.succ) g hgm hgM (fun i => c i.succ)
      (fun i => hc i.succ) hgcoord
    have heqf : (∫ x, f x ∂Measure.pi μ) = ∫ y, g y ∂ν := by
      rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).integral_comp']
      refine Eq.trans ?_ (integral_prod_symm (μ := μ 0) (ν := ν) _ hFi)
      apply integral_congr_ae
      filter_upwards with p
      apply congrArg f
      change Fin.insertNth 0 p.1 p.2 = Fin.cons p.1 p.2
      exact Fin.insertNth_zero _ _
    have heqexp : (∫ x, Real.exp (θ * f x) ∂Measure.pi μ) =
        ∫ y, ∫ z, Real.exp (θ * F (z, y)) ∂μ 0 ∂ν := by
      rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).integral_comp']
      refine Eq.trans ?_ (integral_prod_symm (μ := μ 0) (ν := ν) _
        (integrable_exp_mul_of_abs_le hFm hFM θ))
      apply integral_congr_ae
      filter_upwards with p
      congr 2
      apply congrArg f
      change Fin.insertNth 0 p.1 p.2 = Fin.cons p.1 p.2
      exact Fin.insertNth_zero _ _
    have hfiber (y : ∀ i : Fin N, S i.succ) :
        (∫ z, Real.exp (θ * F (z, y)) ∂μ 0) ≤
          Real.exp (θ * g y + θ ^ 2 * c 0 ^ 2 / 8) := by
      have hd : ∀ a b, |F (a, y) - F (b, y)| ≤ c 0 := by
        intro a b
        simpa only [F, Fin.update_cons_zero] using hcoord 0 (Fin.cons b y) a
      have hsg := hasSubgaussianMGF_of_range_oscillation (μ := μ 0) (fun z => F (z, y))
        (hFm.comp (measurable_id.prodMk measurable_const)).aemeasurable (hc 0) hd
      have h := hsg.mgf_le θ
      change (∫ z, Real.exp (θ * (F (z, y) - g y)) ∂μ 0) ≤ _ at h
      have he : ∀ z, Real.exp (θ * (F (z, y) - g y)) =
          Real.exp (-θ * g y) * Real.exp (θ * F (z, y)) := by
        intro z; rw [← Real.exp_add]; congr 1; ring
      simp only [he, integral_const_mul] at h
      have hcanc : Real.exp (-θ * g y) * Real.exp (θ * g y) = 1 := by
        rw [← Real.exp_add]; simp
      have hmul := mul_le_mul_of_nonneg_left h (Real.exp_pos (θ * g y)).le
      calc (∫ z, Real.exp (θ * F (z, y)) ∂μ 0) =
            Real.exp (θ * g y) * (Real.exp (-θ * g y) *
              (∫ z, Real.exp (θ * F (z, y)) ∂μ 0)) := by
                rw [← mul_assoc, mul_comm (Real.exp (θ * g y)) (Real.exp (-θ * g y)),
                  hcanc, one_mul]
        _ ≤ Real.exp (θ * g y) * Real.exp ((c 0 ^ 2 / 4) * θ ^ 2 / 2) := hmul
        _ = Real.exp (θ * g y + θ ^ 2 * c 0 ^ 2 / 8) := by rw [← Real.exp_add]; congr 1; ring
    rw [heqexp, heqf, Fin.sum_univ_succ]
    have hleft : Integrable (fun y => ∫ z, Real.exp (θ * F (z, y)) ∂μ 0) ν :=
      (integrable_exp_mul_of_abs_le (μ := (μ 0).prod ν) hFm hFM θ).integral_prod_right
    have hright : Integrable (fun y => Real.exp (θ * g y + θ ^ 2 * c 0 ^ 2 / 8)) ν := by
      simp_rw [Real.exp_add]
      exact (integrable_exp_mul_of_abs_le hgm hgM θ).mul_const _
    calc (∫ y, ∫ z, Real.exp (θ * F (z, y)) ∂μ 0 ∂ν) ≤
          ∫ y, Real.exp (θ * g y + θ ^ 2 * c 0 ^ 2 / 8) ∂ν :=
            integral_mono hleft hright hfiber
      _ = Real.exp (θ ^ 2 * c 0 ^ 2 / 8) * ∫ y, Real.exp (θ * g y) ∂ν := by
            simp_rw [Real.exp_add, mul_comm _ (Real.exp (θ ^ 2 * c 0 ^ 2 / 8))]
            rw [integral_const_mul]
      _ ≤ Real.exp (θ ^ 2 * c 0 ^ 2 / 8) *
          Real.exp (θ * (∫ y, g y ∂ν) + θ ^ 2 * (∑ i : Fin N, c i.succ ^ 2) / 8) :=
            mul_le_mul_of_nonneg_left hrec (Real.exp_pos _).le
      _ = Real.exp (θ * (∫ y, g y ∂ν) + θ ^ 2 * (c 0 ^ 2 + ∑ i : Fin N, c i.succ ^ 2) / 8) := by
            rw [← Real.exp_add]; congr 1; ring

/-- Relabelled finite-product averaging retains the sharp bounded-differences
MGF constant for arbitrary finite coordinate labels and heterogeneous spaces.
Source: manuscript `thm:mcdiarmidmgf`; auxiliary boundedness is derived below. -/
theorem integral_exp_mul_le_exp_of_coordinate_oscillation
    {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, MeasurableSpace (S i)] (μ : ∀ i, Measure (S i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : (∀ i, S i) → ℝ) (hf : Measurable f)
    {M : ℝ} (hM : ∀ x, |f x| ≤ M) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hcoord : ∀ i (x : ∀ j, S j) (y : S i), |f (Function.update x i y) - f x| ≤ c i)
    (θ : ℝ) :
    ∫ x, Real.exp (θ * f x) ∂Measure.pi μ ≤
      Real.exp (θ * (∫ x, f x ∂Measure.pi μ) + θ ^ 2 * (∑ i, c i ^ 2) / 8) := by
  let e := (Fintype.equivFin ι).symm
  let E := MeasurableEquiv.piCongrLeft S e
  have hu (j) (x : ∀ i : Fin (Fintype.card ι), S (e i)) (y : S (e j)) :
      E (Function.update x j y) = Function.update (E x) (e j) y := by
    change (Equiv.piCongrLeft' S e.symm).symm (Function.update x j y) =
      Function.update ((Equiv.piCongrLeft' S e.symm).symm x) (e j) y
    simpa using Function.piCongrLeft'_symm_update S e.symm x j y
  have h := integral_exp_mul_le_exp_of_fin_coordinate_oscillation (Fintype.card ι)
    (fun i => μ (e i)) (fun x => f (E x)) (hf.comp E.measurable)
    (fun x => hM (E x)) (fun i => c (e i)) (fun i => hc (e i))
    (fun i x y => by rw [hu]; exact hcoord (e i) (E x) y) θ
  have hi (g : (∀ i, S i) → ℝ) :
      (∫ x, g (E x) ∂Measure.pi (fun i => μ (e i))) = ∫ x, g x ∂Measure.pi μ :=
    (measurePreserving_piCongrLeft μ e).integral_comp' g
  rw [hi (fun x => Real.exp (θ * f x)), hi f, e.sum_comp (fun i => c i ^ 2)] at h
  exact h

/-- **Sharp bounded differences on a finite product.** Measurable globally
bounded coordinate oscillations give the centred MGF proxy `∑ cᵢ²/4`, with no
integrability hypotheses. All coordinate spaces may differ; no standard-Borel
assumption is used, and an empty product is included.
Source: operator manuscript `thm:mcdiarmidmgf`, coordinate averaging and sharp
fibre Hoeffding; Boucheron–Lugosi–Massart 2013, Theorem 6.2.
atlas: mcdiarmid (partial) -/
theorem hasSubgaussianMGF_pi_of_coordinate_oscillation
    {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, MeasurableSpace (S i)] (μ : ∀ i, Measure (S i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : (∀ i, S i) → ℝ) (hf : Measurable f)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hcoord : ∀ i (x : ∀ j, S j) (y : S i), |f (Function.update x i y) - f x| ≤ c i) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂Measure.pi μ)
      ⟨(∑ i, c i ^ 2) / 4, by positivity⟩ (Measure.pi μ) := by
  let : ∀ i, Nonempty (S i) := fun i => nonempty_of_isProbabilityMeasure (μ i)
  let x₀ : ∀ i, S i := fun i => Classical.choice (inferInstance : Nonempty (S i))
  let M := |f x₀| + ∑ i, c i
  have hM (x) : |f x| ≤ M := by
    have h := abs_sub_le_sum_of_coordinate_oscillation f c hcoord x₀ x
    calc |f x| ≤ |f x - f x₀| + |f x₀| := by
          simpa only [sub_add_cancel] using abs_add_le (f x - f x₀) (f x₀)
      _ ≤ (∑ i, c i) + |f x₀| := add_le_add h le_rfl
      _ = M := add_comm _ _
  let m := ∫ y, f y ∂Measure.pi μ
  refine ⟨fun θ => integrable_exp_mul_of_abs_le (hf.sub_const m)
    (M := M + |m|) (fun x => ?_) θ, fun θ => ?_⟩
  · calc |f x - m| ≤ |f x| + |m| := by
          simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (f x) 0 m
      _ ≤ M + |m| := add_le_add (hM x) le_rfl
  · have h := integral_exp_mul_le_exp_of_coordinate_oscillation μ f hf hM c hc hcoord θ
    change (∫ x, Real.exp (θ * (f x - m)) ∂Measure.pi μ) ≤
      Real.exp (((∑ i, c i ^ 2) / 4) * θ ^ 2 / 2)
    have he (x) : Real.exp (θ * (f x - m)) = Real.exp (-θ * m) * Real.exp (θ * f x) := by
      rw [← Real.exp_add]; congr 1; ring
    simp only [he, integral_const_mul]
    refine (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le).trans_eq ?_
    rw [← Real.exp_add]
    congr 1
    dsimp only [m]
    ring

/-- The centred bounded-differences MGF transports along the joint law of
independent measurable coordinates on an arbitrary probability space.
The original space and the coordinate spaces need no standard-Borel instances.
Source: the abstract-space paragraph following manuscript `cor:mcdiarmid`.
atlas: mcdiarmid (partial) -/
theorem hasSubgaussianMGF_of_independent_coordinate_oscillation
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, MeasurableSpace (S i)]
    (X : ∀ i, Ω → S i) (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (f : (∀ i, S i) → ℝ) (hf : Measurable f) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hcoord : ∀ i (x : ∀ j, S j) (y : S i), |f (Function.update x i y) - f x| ≤ c i) :
    HasSubgaussianMGF (fun ω => f (fun i => X i ω) - ∫ ω', f (fun i => X i ω') ∂μ)
      ⟨(∑ i, c i ^ 2) / 4, by positivity⟩ μ := by
  let Y (ω : Ω) : ∀ i, S i := fun i => X i ω
  have hY : Measurable Y := measurable_pi_lambda _ hX
  let ν (i : ι) := μ.map (X i)
  let : ∀ i, IsProbabilityMeasure (ν i) := fun i => Measure.isProbabilityMeasure_map (hX i).aemeasurable
  have hlaw : μ.map Y = Measure.pi ν := hind.map_fun_eq_pi_map (fun i => (hX i).aemeasurable)
  have hsg := hasSubgaussianMGF_pi_of_coordinate_oscillation ν f hf c hc hcoord
  have hm : (∫ x, f x ∂Measure.pi ν) = ∫ ω, f (Y ω) ∂μ := by
    rw [← hlaw]
    exact integral_map hY.aemeasurable hf.aestronglyMeasurable
  rw [← hlaw] at hsg
  have h := hsg.of_map hY.aemeasurable
  rw [← hlaw] at hm
  rw [hm] at h
  simpa only [Function.comp_def, Y] using h

/-- The sharp McDiarmid tail, with the positive-threshold zero-oscillation
case written explicitly. Source: manuscript `cor:mcdiarmid`; supports the atlas
result `mcdiarmid`. -/
def mcdiarmidTail (C t : ℝ) : ℝ :=
  if C = 0 then (if 0 < t then 0 else 1) else Real.exp (-2 * t ^ 2 / C)

/-- The sharp tail follows from proxy `C/4`, including the zero-proxy branch.
Source: manuscript `cor:mcdiarmid`; helper for the actual independent-coordinate result. -/
theorem measure_ge_le_mcdiarmidTail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hZ : HasSubgaussianMGF Z ⟨C / 4, by positivity⟩ μ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ Z ω} ≤ mcdiarmidTail C t := by
  by_cases hzero : C = 0
  · subst C
    have hp : (⟨(0 : ℝ) / 4, by positivity⟩ : NNReal) = 0 := by ext; simp
    rw [hp] at hZ
    have hsg : HasSubgaussianMGF Z 0 μ := hZ
    have hz := hsg.ae_eq_zero_of_hasSubgaussianMGF_zero
    have he : μ {ω | t ≤ Z ω} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hz] with ω hω
      simp only [Pi.zero_apply] at hω
      rw [hω]
      exact not_le.mpr ht
    simp [mcdiarmidTail, ht, measureReal_def, he]
  · have h := hZ.measure_ge_le ht.le
    refine h.trans_eq ?_
    simp only [mcdiarmidTail, if_neg hzero]
    change Real.exp (-t ^ 2 / (2 * (C / 4))) = Real.exp (-2 * t ^ 2 / C)
    congr 1
    field_simp
    ring

/-- **McDiarmid's upper tail with exact constant two.** Independent measurable
coordinates and global coordinate bounds give `P(f(X)-E f(X)≥t)≤exp(-2t²/∑cᵢ²)`.
For zero total oscillation and a positive threshold the probability is zero.
No integrability assumptions are required. Source: operator manuscript
`cor:mcdiarmid`; Boucheron–Lugosi–Massart 2013, Theorem 6.2.
atlas: mcdiarmid -/
theorem mcdiarmid_upper_tail
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, MeasurableSpace (S i)]
    (X : ∀ i, Ω → S i) (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (f : (∀ i, S i) → ℝ) (hf : Measurable f) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hcoord : ∀ i (x : ∀ j, S j) (y : S i), |f (Function.update x i y) - f x| ≤ c i)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ f (fun i => X i ω) - ∫ ω', f (fun i => X i ω') ∂μ} ≤
      mcdiarmidTail (∑ i, c i ^ 2) t :=
  measure_ge_le_mcdiarmidTail (by positivity)
    (hasSubgaussianMGF_of_independent_coordinate_oscillation X hX hind f hf c hc hcoord) ht

/-- **McDiarmid's matching lower tail.** The same explicit tail controls
`P(E f(X)-f(X)≥t)`, including zero total oscillation. Source: operator manuscript
`cor:mcdiarmid`, applied to the negative centred variable.
atlas: mcdiarmid -/
theorem mcdiarmid_lower_tail
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, MeasurableSpace (S i)]
    (X : ∀ i, Ω → S i) (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (f : (∀ i, S i) → ℝ) (hf : Measurable f) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hcoord : ∀ i (x : ∀ j, S j) (y : S i), |f (Function.update x i y) - f x| ≤ c i)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ (∫ ω', f (fun i => X i ω') ∂μ) - f (fun i => X i ω)} ≤
      mcdiarmidTail (∑ i, c i ^ 2) t := by
  have hsg := hasSubgaussianMGF_of_independent_coordinate_oscillation X hX hind f hf c hc hcoord
  have h := measure_ge_le_mcdiarmidTail (by positivity) hsg.neg ht
  simpa only [Pi.neg_apply, neg_sub] using h

end NLAlib
