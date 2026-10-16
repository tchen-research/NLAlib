import NLAlib.Matrix.Basic.GeneralTikhonov
/-!+# Generalized singular filters and their endpoint limits

Both limits are finite coordinate limits in a single normalized GSVD.
The small-parameter endpoint retains the nonzero data coordinates; the
large-parameter endpoint retains exactly the zero-penalty coordinates.
-/
noncomputable section
open Matrix Filter Topology
open scoped Matrix ComplexOrder
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*}
  [Fintype m] [Fintype n] [Fintype p] [DecidableEq n]

/-- The explicit general-form Tikhonov solution in a normalized GSVD. -/
def generalTikhonovFilter (A : Matrix m n 𝕜) (X : Matrix n n 𝕜) (c s : n → ℝ)
    (b : m → 𝕜) (β : ℝ) : n → 𝕜 :=
  X *ᵥ (fun i => (Xᴴ *ᵥ (Aᴴ *ᵥ b)) i / ((c i ^ 2 + β * s i ^ 2 : ℝ) : 𝕜))

/-- The zero-parameter endpoint in generalized singular coordinates. -/
def generalTikhonovZeroLimit (A : Matrix m n 𝕜) (X : Matrix n n 𝕜) (c : n → ℝ)
    (b : m → 𝕜) : n → 𝕜 :=
  X *ᵥ (fun i => if c i = 0 then 0 else (Xᴴ *ᵥ (Aᴴ *ᵥ b)) i / (c i : 𝕜) ^ 2)

/-- The infinite-parameter endpoint retains only the penalty kernel. -/
def generalTikhonovInfinityLimit (A : Matrix m n 𝕜) (X : Matrix n n 𝕜)
    (c s : n → ℝ) (b : m → 𝕜) : n → 𝕜 :=
  X *ᵥ (fun i => if s i = 0 then (Xᴴ *ᵥ (Aᴴ *ᵥ b)) i / (c i : 𝕜) ^ 2 else 0)

/-- The explicit filter is an actual global minimizer for every positive
parameter and every stacked rank.
atlas: general-form-tikhonov-gsvd (partial) -/
theorem IsNormalizedGSVD.generalTikhonovFilter_minimizer
    {A : Matrix m n 𝕜} {L : Matrix p n 𝕜} {X : Matrix n n 𝕜} {c s : n → ℝ}
    (h : IsNormalizedGSVD A L X c s) (b : m → 𝕜) {β : ℝ} (hβ : 0 < β) :
    ∀ z, generalTikhonovObjective A L b β (generalTikhonovFilter A X c s b β) ≤
      generalTikhonovObjective A L b β z := by
  intro z
  have he := generalTikhonovObjective_add_of_normal_equation A L b hβ.le
    (generalTikhonovFilter A X c s b β) (h.generalTikhonov_filter_normal_equation b hβ)
    (z - generalTikhonovFilter A X c s b β)
  rw [add_sub_cancel] at he
  have hn := mul_nonneg hβ.le
    (sq_nonneg ‖WithLp.toLp 2 (L *ᵥ (z - generalTikhonovFilter A X c s b β))‖)
  linarith [sq_nonneg ‖WithLp.toLp 2 (A *ᵥ (z - generalTikhonovFilter A X c s b β))‖]

/-- With trivial common kernel, the filter is the unique minimizer and
equals the Moore–Penrose normal formula.
atlas: general-form-tikhonov-gsvd (partial) -/
theorem IsNormalizedGSVD.generalTikhonovFilter_unique
    {A : Matrix m n 𝕜} {L : Matrix p n 𝕜} {X : Matrix n n 𝕜} {c s : n → ℝ}
    (h : IsNormalizedGSVD A L X c s)
    (hN : ∀ v : n → 𝕜, A *ᵥ v = 0 → L *ᵥ v = 0 → v = 0)
    (b : m → 𝕜) {β : ℝ} (hβ : 0 < β) :
    generalTikhonovFilter A X c s b β =
      moorePenroseInverse (generalTikhonovNormal A L β) *ᵥ (Aᴴ *ᵥ b) ∧
    ∀ y, (∀ z, generalTikhonovObjective A L b β y ≤ generalTikhonovObjective A L b β z) →
      y = generalTikhonovFilter A X c s b β := by
  have he (y) (hy : ∀ z, generalTikhonovObjective A L b β y ≤
      generalTikhonovObjective A L b β z) :
      y = moorePenroseInverse (generalTikhonovNormal A L β) *ᵥ (Aᴴ *ᵥ b) := by
    obtain ⟨v, hvA, hvL, hv⟩ := (generalTikhonov_minimizers_iff A L b hβ y).mp hy
    simpa only [hN v hvA hvL, add_zero] using hv
  have hf := he _ (h.generalTikhonovFilter_minimizer b hβ)
  exact ⟨hf, fun y hy => (he y hy).trans hf.symm⟩

/-- The positive-parameter solution converges to its exact zero-parameter
GSVD endpoint. No rank assumption is needed for this coordinate limit.
atlas: general-form-tikhonov-gsvd (partial) -/
theorem IsNormalizedGSVD.tendsto_generalTikhonovFilter_zero
    {A : Matrix m n 𝕜} {L : Matrix p n 𝕜} {X : Matrix n n 𝕜} {c s : n → ℝ}
    (h : IsNormalizedGSVD A L X c s) (b : m → 𝕜) :
    Tendsto (fun β : ℝ => (WithLp.toLp 2 (generalTikhonovFilter A X c s b β) : EuclideanSpace 𝕜 n))
      (𝓝[>] 0) (𝓝 (WithLp.toLp 2 (generalTikhonovZeroLimit A X c b))) := by
  have hcoord : Tendsto (fun β : ℝ => fun i =>
      (Xᴴ *ᵥ (Aᴴ *ᵥ b)) i / ((c i ^ 2 + β * s i ^ 2 : ℝ) : 𝕜)) (𝓝[>] 0)
      (𝓝 (fun i => if c i = 0 then 0 else (Xᴴ *ᵥ (Aᴴ *ᵥ b)) i / (c i : 𝕜) ^ 2)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    by_cases hi : c i = 0
    · simp only [hi, h.coefficient_eq_zero_of_left_eq_zero b i hi, zero_div, ite_true]
      exact tendsto_const_nhds
    · have hc : ContinuousAt (fun β : ℝ =>
          (Xᴴ *ᵥ (Aᴴ *ᵥ b)) i / ((c i ^ 2 + β * s i ^ 2 : ℝ) : 𝕜)) 0 := by
        apply continuousAt_const.div
        · fun_prop
        · simpa using (pow_ne_zero 2 (show (c i : 𝕜) ≠ 0 by exact_mod_cast hi))
      simpa [hi] using! hc.tendsto.mono_left inf_le_left
  have hc : Continuous (fun y : n → 𝕜 => (WithLp.toLp 2 (X *ᵥ y) : EuclideanSpace 𝕜 n)) := by
    fun_prop
  exact hc.continuousAt.tendsto.comp hcoord

/-- The positive-parameter solution converges to the penalty-kernel
endpoint as the parameter tends to infinity.
atlas: general-form-tikhonov-gsvd (partial) -/
theorem IsNormalizedGSVD.tendsto_generalTikhonovFilter_infinity
    {A : Matrix m n 𝕜} {L : Matrix p n 𝕜} {X : Matrix n n 𝕜} {c s : n → ℝ}
    (h : IsNormalizedGSVD A L X c s) (b : m → 𝕜) :
    Tendsto (fun β : ℝ => (WithLp.toLp 2 (generalTikhonovFilter A X c s b β) : EuclideanSpace 𝕜 n))
      atTop (𝓝 (WithLp.toLp 2 (generalTikhonovInfinityLimit A X c s b))) := by
  have hcoord : Tendsto (fun β : ℝ => fun i =>
      (Xᴴ *ᵥ (Aᴴ *ᵥ b)) i / ((c i ^ 2 + β * s i ^ 2 : ℝ) : 𝕜)) atTop
      (𝓝 (fun i => if s i = 0 then (Xᴴ *ᵥ (Aᴴ *ᵥ b)) i / (c i : 𝕜) ^ 2 else 0)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    by_cases hi : s i = 0
    · simpa [hi] using (tendsto_const_nhds : Tendsto
        (fun _ : ℝ => (Xᴴ *ᵥ (Aᴴ *ᵥ b)) i / (c i : 𝕜) ^ 2) atTop (𝓝 _))
    · have hw : Tendsto (fun β : ℝ => c i ^ 2 + β * s i ^ 2) atTop atTop := by
        apply tendsto_const_nhds.add_atTop
        exact tendsto_id.atTop_mul_const (sq_pos_of_ne_zero hi)
      have hinv : Tendsto (fun β : ℝ => ((c i ^ 2 + β * s i ^ 2)⁻¹ : ℝ)) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp hw
      have hcast : Tendsto (fun β : ℝ => (((c i ^ 2 + β * s i ^ 2)⁻¹ : ℝ) : 𝕜))
          atTop (𝓝 0) := by
        simpa only [RCLike.ofReal_zero, Function.comp_def] using
          RCLike.continuous_ofReal.continuousAt.tendsto.comp hinv
      simpa [hi, div_eq_mul_inv] using tendsto_const_nhds.mul hcast
  have hc : Continuous (fun y : n → 𝕜 => (WithLp.toLp 2 (X *ᵥ y) : EuclideanSpace 𝕜 n)) := by
    fun_prop
  exact hc.continuousAt.tendsto.comp hcoord

end NLAlib
