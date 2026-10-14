import NLAlib.Probability.Rademacher.Core
import NLAlib.Sketching.Structured.KhatriRaoBasic
import NLAlib.Sketching.Properties.SubspaceEmbedding.SubspaceEmbedding
import NLAlib.Sketching.Properties.SubspaceEmbedding.Dimension
import NLAlib.Matrix.Basic.LeastSquares
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A bounded-entry Khatri–Rao obstruction

The deterministic isometry with one free coordinate and constant tensor factors gives the
Rademacher lower obstruction in `Khatri_Rao_Embeddings_and_Approximation_Focused.tex`,
Proposition `lower:prop:rademacher`. The sample space below contains the actual independent
Rademacher factors, and the sketch entries are their tensor products.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators

namespace NLAlib

/-- Mode dimensions for the common-factor obstruction: first mode `r`, remaining modes `h`. -/
def khatriRaoCommonDimensions (r h k : ℕ) : Fin (k + 1) → ℕ := Fin.cases r fun _ => h

/-- Package the free and common factors as one dependent tuple of tensor factors. -/
def khatriRaoCommonFactors {r h k : ℕ} (ξ : Fin r → ℝ)
    (η : Fin k → Fin h → ℝ) :
    ∀ j : Fin (k + 1), Fin (khatriRaoCommonDimensions r h k j) → ℝ :=
  Fin.cases ξ η

/-- Package paired tensor coordinates as a dependent multi-index. -/
def khatriRaoCommonIndex {r h k : ℕ} (a : Fin r × (Fin k → Fin h)) :
    ∀ j : Fin (k + 1), Fin (khatriRaoCommonDimensions r h k j) :=
  Fin.cases a.1 a.2

/-- The paired and dependent multi-index coordinates describe exactly the same tensor
ambient space.
atlas: khatri-rao-sharp-growth (partial) -/
theorem bijective_khatriRaoCommonIndex (r h k : ℕ) :
    Function.Bijective (khatriRaoCommonIndex (r := r) (h := h) (k := k)) :=
  (Fin.consEquiv (fun j => Fin (khatriRaoCommonDimensions r h k j))).bijective

/-- The common-factor isometry sends `eₐ` to `eₐ ⊗ b^⊗k`, with
`b = h^(-1/2) (1,…,1)`. The tensor coordinates are paired with their first mode. -/
def khatriRaoCommonIsometry (r h k : ℕ) :
    Matrix (Fin r × (Fin k → Fin h)) (Fin r) ℝ :=
  fun a b => if a.1 = b then (Real.sqrt h)⁻¹ ^ k else 0

/-- The common-factor construction has orthonormal columns whenever its common mode is
nonempty.
atlas: khatri-rao-sharp-growth (partial) -/
theorem hasOrthonormalCols_khatriRaoCommonIsometry (r k : ℕ) {h : ℕ} (hh : 0 < h) :
    HasOrthonormalCols (khatriRaoCommonIsometry r h k) := by
  have hs : Real.sqrt (h : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hnorm : (h : ℝ) ^ k * ((Real.sqrt h)⁻¹ ^ k * (Real.sqrt h)⁻¹ ^ k) = 1 := by
    rw [← mul_pow, ← mul_pow]
    have he : (h : ℝ) * ((Real.sqrt h)⁻¹ * (Real.sqrt h)⁻¹) = 1 := by
      rw [← mul_inv, ← pow_two, Real.sq_sqrt (by positivity)]
      exact mul_inv_cancel₀ (by positivity)
    rw [he, one_pow]
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    khatriRaoCommonIsometry, star_trivial, Fintype.sum_prod_type]
  by_cases hab : a = b
  · subst b
    simpa using hnorm
  · simp [hab, Ne.symm hab]

/-- A raw tensor row from one free factor and `k` common factors. -/
def khatriRaoCommonRow {r h k : ℕ} (ξ : Fin r → ℝ) (η : Fin k → Fin h → ℝ) :
    (Fin r × (Fin k → Fin h)) → ℝ :=
  fun a => ξ a.1 * ∏ j, η j (a.2 j)

/-- The paired-coordinate witness row is the library's tensor-product probe evaluated in
the corresponding dependent multi-index.
atlas: khatri-rao-sharp-growth (partial) -/
theorem khatriRaoCommonRow_eq_khatriRaoProbe {r h k : ℕ}
    (ξ : Fin r → ℝ) (η : Fin k → Fin h → ℝ) (a : Fin r × (Fin k → Fin h)) :
    khatriRaoCommonRow ξ η a =
      khatriRaoProbe (khatriRaoCommonFactors ξ η) (khatriRaoCommonIndex a) := by
  unfold khatriRaoCommonRow khatriRaoProbe
  rw [Fin.prod_univ_succ]
  rfl

/-- The projected common-factor row is the free sign vector times the product of the
normalized common-factor coordinate sums. -/
def khatriRaoCommonProjection {r h k : ℕ} (ξ : Fin r → ℝ)
    (η : Fin k → Fin h → ℝ) : Fin r → ℝ :=
  fun a => ξ a * ∏ j, ((Real.sqrt h)⁻¹ * ∑ t, η j t)

/-- Tensor contraction against the explicit isometry equals its product-of-sums formula. -/
theorem khatriRaoCommonRow_mul_khatriRaoCommonIsometry {r h k : ℕ}
    (ξ : Fin r → ℝ) (η : Fin k → Fin h → ℝ) (a : Fin r) :
    (∑ t, khatriRaoCommonRow ξ η t * khatriRaoCommonIsometry r h k t a) =
      khatriRaoCommonProjection ξ η a := by
  classical
  simp only [khatriRaoCommonRow, khatriRaoCommonIsometry, Fintype.sum_prod_type]
  simp only [mul_ite, mul_zero, Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [khatriRaoCommonProjection, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← Fintype.prod_sum]
  ring

/-- A normalized tensor sketch with the common-factor coordinate representation. -/
def khatriRaoCommonSketch {r h k m : ℕ}
    (z : Fin m → (Fin r → ℝ) × (Fin k → Fin h → ℝ)) :
    Matrix (Fin m) (Fin r × (Fin k → Fin h)) ℝ :=
  fun i a => (Real.sqrt m)⁻¹ * khatriRaoCommonRow (z i).1 (z i).2 a

/-- The rows of the sketched common-factor isometry are its normalized projected samples. -/
theorem khatriRaoCommonSketch_mul_khatriRaoCommonIsometry {r h k m : ℕ}
    (z : Fin m → (Fin r → ℝ) × (Fin k → Fin h → ℝ)) (i : Fin m) (a : Fin r) :
    (khatriRaoCommonSketch z * khatriRaoCommonIsometry r h k) i a =
      (Real.sqrt m)⁻¹ * khatriRaoCommonProjection (z i).1 (z i).2 a := by
  simp only [Matrix.mul_apply, khatriRaoCommonSketch, mul_assoc, ← Finset.mul_sum,
    khatriRaoCommonRow_mul_khatriRaoCommonIsometry]

private theorem not_isSubspaceEmbedding_of_row_sq_gt {m n r : Type*}
    [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]
    (S : Matrix m n ℝ) (U : Matrix n r ℝ) (hU : HasOrthonormalCols U)
    (i : m) {ε : ℝ} (hε : 0 ≤ ε) (hrow : 1 + ε < ∑ a, (S * U) i a ^ 2) :
    ¬ IsSubspaceEmbedding S U ε := by
  intro h
  let x : r → ℝ := (S * U) i
  let q : ℝ := ∑ a, x a ^ 2
  have hq : 0 ≤ q := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hupper := ((isSubspaceEmbedding_iff_of_hasOrthonormalCols hU).1 h x).2
  have hsingle : q ^ 2 ≤ ((S * U) *ᵥ x) ⬝ᵥ ((S * U) *ᵥ x) := by
    have he : ((S * U) *ᵥ x) i = q := by
      simp only [Matrix.mulVec, dotProduct, q, x, pow_two]
    rw [dotProduct]
    have ht := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => ((S * U) *ᵥ x) j * ((S * U) *ᵥ x) j)
      (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
    simpa only [he, pow_two] using ht
  have hx : x ⬝ᵥ x = q := by simp only [dotProduct, q, pow_two]
  rw [hx] at hupper
  change 1 + ε < q at hrow
  have hqpos : 0 < q := by linarith
  nlinarith

/-- When all the common signs are positive and the free signs have squared value one, the
unscaled projected row has squared norm `r h^k`. -/
theorem sum_sq_khatriRaoCommonProjection_of_all_one {r h k : ℕ} (hh : 0 < h)
    (ξ : Fin r → ℝ) (η : Fin k → Fin h → ℝ)
    (hξ : ∀ a, ξ a ^ 2 = 1) (hη : ∀ j t, η j t = 1) :
    ∑ a, khatriRaoCommonProjection ξ η a ^ 2 = (r : ℝ) * (h : ℝ) ^ k := by
  have hs : Real.sqrt (h : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hc : (Real.sqrt (h : ℝ))⁻¹ * h = Real.sqrt h := by
    calc
      _ = (Real.sqrt (h : ℝ))⁻¹ * (Real.sqrt h * Real.sqrt h) := by
        rw [Real.mul_self_sqrt (Nat.cast_nonneg h)]
      _ = Real.sqrt h := by rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  have hpow : (Real.sqrt (h : ℝ) ^ k) ^ 2 = (h : ℝ) ^ k := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul, Real.sq_sqrt (Nat.cast_nonneg h)]
  simp only [khatriRaoCommonProjection, hη, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, hc, Finset.prod_const, mul_pow, hξ,
    one_mul]
  simp [hpow]

/-- A single all-positive common-factor row obstructs every distortion below one when its
unscaled squared norm is at least twice the sketch size. -/
theorem not_isSubspaceEmbedding_khatriRaoCommonSketch_of_all_one {r h k m : ℕ}
    (hh : 0 < h) (hm : 0 < m)
    (hsize : 2 * m ≤ r * h ^ k)
    (z : Fin m → (Fin r → ℝ) × (Fin k → Fin h → ℝ)) (i : Fin m)
    (hξ : ∀ a, (z i).1 a ^ 2 = 1) (hη : ∀ j t, (z i).2 j t = 1)
    {ε : ℝ} (hε : ε < 1) :
    ¬ IsSubspaceEmbedding (khatriRaoCommonSketch z)
      (khatriRaoCommonIsometry r h k) ε := by
  intro hEmbed
  apply not_isSubspaceEmbedding_of_row_sq_gt _ _
    (hasOrthonormalCols_khatriRaoCommonIsometry r k hh) i (le_max_right ε 0) _
    (hEmbed.mono (le_max_left ε 0))
  simp only [khatriRaoCommonSketch_mul_khatriRaoCommonIsometry, mul_pow,
    ← Finset.mul_sum, sum_sq_khatriRaoCommonProjection_of_all_one hh _ _ hξ hη,
    inv_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  have hmR : 0 < (m : ℝ) := by positivity
  have hsizeR : 2 * (m : ℝ) ≤ (r : ℝ) * (h : ℝ) ^ k := by exact_mod_cast hsize
  have he : (1 : ℝ) + max ε 0 < (m : ℝ)⁻¹ * ((r : ℝ) * (h : ℝ) ^ k) := by
    apply (lt_inv_mul_iff₀ hmR).2
    have hmax : max ε 0 < 1 := max_lt hε zero_lt_one
    nlinarith
  exact he

/-- Independent Rademacher factors for every row: `r` signs in the first mode and `h` signs
in each of the remaining `k` modes. -/
abbrev khatriRaoCommonSignLaw (r h k m : ℕ) :
    Measure (Fin m → (Fin r → ℝ) × (Fin k → Fin h → ℝ)) :=
  Measure.pi fun _ : Fin m => (rademacherVector (Fin r)).prod
    (Measure.pi fun _ : Fin k => rademacherVector (Fin h))

/-- Regrouping the free and common sign vectors has precisely the heterogeneous independent
Rademacher factor law used by the library's tensor-product construction.
atlas: khatri-rao-sharp-growth (partial) -/
theorem measurePreserving_khatriRaoCommonFactors (r h k : ℕ) :
    MeasurePreserving
      (fun z : (Fin r → ℝ) × (Fin k → Fin h → ℝ) => khatriRaoCommonFactors z.1 z.2)
      ((rademacherVector (Fin r)).prod (Measure.pi fun _ : Fin k => rademacherVector (Fin h)))
      (Measure.pi fun j : Fin (k + 1) =>
        rademacherVector (Fin (khatriRaoCommonDimensions r h k j))) := by
  let e : ((Fin r → ℝ) × (Fin k → Fin h → ℝ)) ≃ᵐ
      (∀ j : Fin (k + 1), Fin (khatriRaoCommonDimensions r h k j) → ℝ) :=
    { Fin.consEquiv (fun j => Fin (khatriRaoCommonDimensions r h k j) → ℝ) with
      measurable_toFun := by
        apply measurable_pi_iff.2
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · change Measurable (fun z : (Fin r → ℝ) × (Fin k → Fin h → ℝ) => z.1)
          exact measurable_fst
        · change Measurable (fun z : (Fin r → ℝ) × (Fin k → Fin h → ℝ) => z.2 j)
          exact (measurable_pi_apply j).comp measurable_snd
      measurable_invFun := by
        change Measurable (fun z : ∀ j : Fin (k + 1), Fin (khatriRaoCommonDimensions r h k j) → ℝ =>
          (z 0, fun j : Fin k => z j.succ))
        exact (measurable_pi_apply 0).prodMk
          (measurable_pi_iff.2 fun j => measurable_pi_apply j.succ) }
  change MeasurePreserving e _ _
  refine ⟨e.measurable, (Measure.pi_eq fun s _ => ?_).symm⟩
  rw [e.map_apply, Fin.prod_univ_succ, ← Measure.pi_pi, ← Measure.prod_prod]
  congr 1 with ⟨x, f⟩
  simp only [Set.mem_preimage, Set.mem_univ_pi, Fin.forall_fin_succ]
  change (x ∈ s 0 ∧ ∀ i : Fin k, f i ∈ s i.succ) ↔
    (x, f) ∈ s 0 ×ˢ Set.univ.pi (fun i : Fin k => s i.succ)
  constructor
  · rintro ⟨hx, hf⟩
    exact ⟨hx, fun i _ => hf i⟩
  · rintro ⟨hx, hf⟩
    exact ⟨hx, fun i => hf i (Set.mem_univ i)⟩

private def commonPositiveEvent (r h k : ℕ) :
    Set ((Fin r → ℝ) × (Fin k → Fin h → ℝ)) :=
  Set.univ ×ˢ {fun _ _ => (1 : ℝ)}

private theorem measurableSet_commonPositiveEvent (r h k : ℕ) :
    MeasurableSet (commonPositiveEvent r h k) :=
  MeasurableSet.univ.prod (measurableSet_singleton _)

private theorem measureReal_commonPositiveEvent (r h k : ℕ) :
    ((rademacherVector (Fin r)).prod
      (Measure.pi fun _ : Fin k => rademacherVector (Fin h))).real
      (commonPositiveEvent r h k) = (1 / 2 : ℝ) ^ (h * k) := by
  have hmass : rademacherMeasure {(1 : ℝ)} = (1 / 2 : ENNReal) := by
    norm_num [rademacherMeasure]
  rw [Measure.real, commonPositiveEvent, Measure.prod_prod, measure_univ, one_mul]
  simp only [Measure.pi_singleton, hmass, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  norm_num [ENNReal.toReal_pow, ENNReal.toReal_div, ← pow_mul]

private theorem measureReal_exists_commonPositiveEvent (r h k m : ℕ) :
    (khatriRaoCommonSignLaw r h k m).real
      {z | ∃ i, z i ∈ commonPositiveEvent r h k} =
      1 - (1 - (1 / 2 : ℝ) ^ (h * k)) ^ m := by
  let μ := (rademacherVector (Fin r)).prod
    (Measure.pi fun _ : Fin k => rademacherVector (Fin h))
  have he : {z : Fin m → (Fin r → ℝ) × (Fin k → Fin h → ℝ) |
      ∃ i, z i ∈ commonPositiveEvent r h k} =
      (Set.univ.pi fun _ : Fin m => (commonPositiveEvent r h k)ᶜ)ᶜ := by
    ext z
    simp
  rw [he, measureReal_compl (MeasurableSet.univ_pi fun _ =>
    (measurableSet_commonPositiveEvent r h k).compl)]
  rw [probReal_univ]
  simp only [khatriRaoCommonSignLaw, Measure.real, Measure.pi_pi,
    ENNReal.toReal_pow, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  have hp : μ.real (commonPositiveEvent r h k)ᶜ =
      1 - (1 / 2 : ℝ) ^ (h * k) := by
    rw [measureReal_compl (measurableSet_commonPositiveEvent r h k),
      probReal_univ, measureReal_commonPositiveEvent]
  exact congrArg (fun p : ℝ => 1 - p ^ m) hp

/-- The finite-size Rademacher obstruction: if `r h^k ≥ 2m`, every all-positive common-factor
row forces failure, and such a row occurs with probability `1-(1-2^(-hk))^m`.
This is the explicit construction in Proposition `lower:prop:rademacher` of
`Khatri_Rao_Embeddings_and_Approximation_Focused.tex`.
atlas: khatri-rao-sharp-growth (partial) -/
theorem one_sub_pow_le_measureReal_not_isSubspaceEmbedding_khatriRaoCommonSketch
    {r h k m : ℕ} (hh : 0 < h) (hm : 0 < m)
    (hsize : 2 * m ≤ r * h ^ k) {ε : ℝ} (hε : ε < 1) :
    1 - (1 - (1 / 2 : ℝ) ^ (h * k)) ^ m ≤
      (khatriRaoCommonSignLaw r h k m).real
        {z | ¬ IsSubspaceEmbedding (khatriRaoCommonSketch z)
          (khatriRaoCommonIsometry r h k) ε} := by
  rw [← measureReal_exists_commonPositiveEvent r h k m]
  apply ENNReal.toReal_mono (by finiteness)
  apply measure_mono_ae
  have hrow : ∀ᵐ z ∂khatriRaoCommonSignLaw r h k m,
      ∀ i a, (z i).1 a ^ 2 = 1 := by
    rw [ae_all_iff]
    intro i
    have heval := (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin m => (rademacherVector (Fin r)).prod
        (Measure.pi fun _ : Fin k => rademacherVector (Fin h))) (i := i))
    have hfst : ∀ᵐ w ∂(rademacherVector (Fin r)).prod
        (Measure.pi fun _ : Fin k => rademacherVector (Fin h)),
        ∀ a, w.1 a ^ 2 = 1 :=
      measurePreserving_fst.quasiMeasurePreserving.tendsto_ae.eventually
        ae_forall_sq_eq_one_rademacherVector
    exact heval.eventually hfst
  filter_upwards [hrow] with z hz he
  obtain ⟨i, hi⟩ := he
  apply not_isSubspaceEmbedding_khatriRaoCommonSketch_of_all_one hh hm hsize z i (hz i) _ hε
  have hi' : (z i).2 = fun _ _ => (1 : ℝ) := hi.2
  intro j t
  exact congrFun (congrFun hi' j) t

/-- Below the target dimension the common-factor sketch fails deterministically. -/
theorem measureReal_not_isSubspaceEmbedding_khatriRaoCommonSketch_eq_one_of_lt
    {r h k m : ℕ} (hh : 0 < h) (hmr : m < r) {ε : ℝ} (hε : ε < 1) :
    (khatriRaoCommonSignLaw r h k m).real
      {z | ¬ IsSubspaceEmbedding (khatriRaoCommonSketch z)
        (khatriRaoCommonIsometry r h k) ε} = 1 := by
  have he : {z : Fin m → (Fin r → ℝ) × (Fin k → Fin h → ℝ) |
      ¬ IsSubspaceEmbedding (khatriRaoCommonSketch z)
      (khatriRaoCommonIsometry r h k) ε} = Set.univ := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    intro hz
    have hd := hz.card_le (hasOrthonormalCols_khatriRaoCommonIsometry r k hh)
      hε
    simp only [Fintype.card_fin] at hd
    omega
  rw [he, probReal_univ]

/-- An exponential version of the explicit Rademacher obstruction, uniform in the number
of rows once `m ≥ r`. Its two deterministic side inequalities isolate the floor/log arithmetic
used in the sharp-growth corollary. -/
theorem one_sub_exp_neg_sqrt_le_measureReal_not_isSubspaceEmbedding_khatriRaoCommonSketch
    {r h k m : ℕ} (hh : 0 < h) (hm : 0 < m) (hrm : r ≤ m)
    (hsize : 2 * m ≤ r * h ^ k)
    (hprob : Real.sqrt (r : ℝ) ≤ (r : ℝ) * (1 / 2 : ℝ) ^ (h * k))
    {ε : ℝ} (hε : ε < 1) :
    1 - Real.exp (-Real.sqrt (r : ℝ)) ≤
      (khatriRaoCommonSignLaw r h k m).real
        {z | ¬ IsSubspaceEmbedding (khatriRaoCommonSketch z)
          (khatriRaoCommonIsometry r h k) ε} := by
  apply le_trans _
    (one_sub_pow_le_measureReal_not_isSubspaceEmbedding_khatriRaoCommonSketch hh hm hsize hε)
  have hp0 : 0 ≤ (1 / 2 : ℝ) ^ (h * k) := by positivity
  have hp1 : (1 / 2 : ℝ) ^ (h * k) ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have hb : (1 - (1 / 2 : ℝ) ^ (h * k)) ^ m ≤
      Real.exp (-((m : ℝ) * (1 / 2 : ℝ) ^ (h * k))) := by
    have he : 1 - (1 / 2 : ℝ) ^ (h * k) ≤
        Real.exp (-(1 / 2 : ℝ) ^ (h * k)) := by
      simpa only [sub_eq_add_neg, add_comm] using
        Real.add_one_le_exp (-(1 / 2 : ℝ) ^ (h * k))
    have hp := pow_le_pow_left₀ (sub_nonneg.mpr hp1) he m
    simpa only [← Real.exp_nat_mul, mul_neg] using hp
  have hmr : (r : ℝ) ≤ m := by exact_mod_cast hrm
  have hmp : Real.sqrt (r : ℝ) ≤ (m : ℝ) * (1 / 2 : ℝ) ^ (h * k) :=
    hprob.trans (mul_le_mul_of_nonneg_right hmr hp0)
  have he := Real.exp_le_exp.mpr (neg_le_neg hmp)
  linarith

end NLAlib
