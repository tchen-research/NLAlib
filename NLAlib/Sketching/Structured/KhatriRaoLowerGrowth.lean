import NLAlib.Sketching.Structured.KhatriRaoLower
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# The logarithmic Rademacher lower bound for Khatri–Rao embeddings

The elementary floor/log arithmetic turns the explicit bounded-entry obstruction into the
uniform lower bound of Proposition `lower:prop:rademacher` in
`Khatri_Rao_Embeddings_and_Approximation_Focused.tex`.
-/

noncomputable section

open MeasureTheory

namespace NLAlib

/-- Common-mode dimension `⌊log r / (2k log 2)⌋` for the order-`k+1` Rademacher witness. -/
def khatriRaoLowerMode (r k : ℕ) : ℕ :=
  ⌊Real.log (r : ℝ) / (2 * (k : ℝ) * Real.log 2)⌋₊

/-- The explicit lower sampling constant `1/[2(4k log 2)^k]` for tensor order `k+1`. -/
def khatriRaoLowerConstant (k : ℕ) : ℝ :=
  (2 * (4 * (k : ℝ) * Real.log 2) ^ k)⁻¹

/-- Above the explicit logarithmic threshold, the common mode is positive and lies between
`log r/(4k log 2)` and `log r/(2k log 2)`. Thus the non-free mode dimensions grow only
logarithmically.
atlas: khatri-rao-sharp-growth (partial) -/
theorem khatriRaoLowerMode_bounds {r k : ℕ} (hk : 0 < k)
    (hr : 4 * (k : ℝ) * Real.log 2 ≤ Real.log (r : ℝ)) :
    0 < khatriRaoLowerMode r k ∧
      Real.log (r : ℝ) / (4 * (k : ℝ) * Real.log 2) ≤ khatriRaoLowerMode r k ∧
      (khatriRaoLowerMode r k : ℝ) ≤
        Real.log (r : ℝ) / (2 * (k : ℝ) * Real.log 2) := by
  have hkR : 0 < (k : ℝ) := by positivity
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hd : 0 < 2 * (k : ℝ) * Real.log 2 := by positivity
  have hx : 2 ≤ Real.log (r : ℝ) / (2 * (k : ℝ) * Real.log 2) := by
    apply (le_div_iff₀ hd).2
    nlinarith
  have hfloor := Nat.floor_le (le_trans (by norm_num : (0 : ℝ) ≤ 2) hx)
  have hlt := Nat.lt_floor_add_one
    (Real.log (r : ℝ) / (2 * (k : ℝ) * Real.log 2))
  have hhalf : Real.log (r : ℝ) / (4 * (k : ℝ) * Real.log 2) =
      (Real.log (r : ℝ) / (2 * (k : ℝ) * Real.log 2)) / 2 := by ring
  constructor
  · unfold khatriRaoLowerMode
    exact Nat.floor_pos.2 (by linarith)
  · unfold khatriRaoLowerMode
    exact ⟨by rw [hhalf]; linarith, hfloor⟩

private theorem sqrt_le_mul_pow_lowerMode {r k : ℕ} (hk : 0 < k) (hr : 0 < r)
    (hlog : 4 * (k : ℝ) * Real.log 2 ≤ Real.log (r : ℝ)) :
    Real.sqrt (r : ℝ) ≤
      (r : ℝ) * (1 / 2 : ℝ) ^ (khatriRaoLowerMode r k * k) := by
  have hrR : 0 < (r : ℝ) := by positivity
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hd : 0 < 2 * (k : ℝ) * Real.log 2 := by positivity
  have hf := (le_div_iff₀ hd).1 (khatriRaoLowerMode_bounds hk hlog).2.2
  have harg : Real.log (r : ℝ) / 2 ≤ Real.log (r : ℝ) -
      ((khatriRaoLowerMode r k * k : ℕ) : ℝ) * Real.log 2 := by
    push_cast
    nlinarith
  have he : (1 / 2 : ℝ) ^ (khatriRaoLowerMode r k * k) =
      Real.exp (-(((khatriRaoLowerMode r k * k : ℕ) : ℝ) * Real.log 2)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp [one_div, inv_pow]
  rw [he]
  calc
    Real.sqrt (r : ℝ) = Real.exp (Real.log (r : ℝ) / 2) := by
      rw [Real.exp_half, Real.exp_log hrR]
    _ ≤ Real.exp (Real.log (r : ℝ) -
        ((khatriRaoLowerMode r k * k : ℕ) : ℝ) * Real.log 2) :=
      Real.exp_le_exp.mpr harg
    _ = (r : ℝ) * Real.exp (-(((khatriRaoLowerMode r k * k : ℕ) : ℝ) *
        Real.log 2)) := by rw [Real.exp_sub, Real.exp_log hrR, div_eq_mul_inv, Real.exp_neg]

private theorem two_mul_le_mul_pow_lowerMode {r k m : ℕ} (hk : 0 < k)
    (hlog : 4 * (k : ℝ) * Real.log 2 ≤ Real.log (r : ℝ))
    (hbudget : (m : ℝ) ≤ khatriRaoLowerConstant k * r * Real.log (r : ℝ) ^ k) :
    2 * m ≤ r * khatriRaoLowerMode r k ^ k := by
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hd : 0 < 4 * (k : ℝ) * Real.log 2 := by positivity
  have hdPow : 0 < (4 * (k : ℝ) * Real.log 2) ^ k := pow_pos hd k
  have hlog0 : 0 ≤ Real.log (r : ℝ) := by positivity
  have hf := (khatriRaoLowerMode_bounds hk hlog).2.1
  have hpow := pow_le_pow_left₀ (div_nonneg hlog0 hd.le) hf k
  have hc : (2 : ℝ) * khatriRaoLowerConstant k =
      ((4 * (k : ℝ) * Real.log 2) ^ k)⁻¹ := by
    unfold khatriRaoLowerConstant
    field_simp
  have hbudget2 : 2 * (m : ℝ) ≤
      (r : ℝ) * (Real.log (r : ℝ) / (4 * (k : ℝ) * Real.log 2)) ^ k := by
    calc
      2 * (m : ℝ) ≤ 2 * (khatriRaoLowerConstant k * r * Real.log (r : ℝ) ^ k) := by
        linarith
      _ = (r : ℝ) * (Real.log (r : ℝ) / (4 * (k : ℝ) * Real.log 2)) ^ k := by
        rw [div_pow, div_eq_mul_inv]
        calc
          _ = (2 * khatriRaoLowerConstant k) * r * Real.log (r : ℝ) ^ k := by ring
          _ = _ := by rw [hc]; ring
  have hs : 2 * (m : ℝ) ≤ (r : ℝ) * (khatriRaoLowerMode r k : ℝ) ^ k :=
    hbudget2.trans (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg r))
  exact_mod_cast hs

/-- The explicit lower-growth sampling constant is strictly positive at every positive
tensor-tail order.
atlas: khatri-rao-sharp-growth (partial) -/
theorem khatriRaoLowerConstant_pos {k : ℕ} (hk : 0 < k) :
    0 < khatriRaoLowerConstant k := by
  unfold khatriRaoLowerConstant
  have : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  positivity

/-- For every `r ≥ 2^(4k)`, the order-`k+1` Rademacher tensor sketch fails at every distortion
below one with probability at least `1-exp(-√r)` for every positive integer sample size at most
`r(log r)^k/[2(4k log 2)^k]`. This is Proposition `lower:prop:rademacher` of
`Khatri_Rao_Embeddings_and_Approximation_Focused.tex`; `k=d-1`.
atlas: khatri-rao-sharp-growth (partial) -/
theorem one_sub_exp_neg_sqrt_le_measureReal_not_isSubspaceEmbedding_of_le_lower_growth
    {r k m : ℕ} (hk : 0 < k) (hr : 2 ^ (4 * k) ≤ r) (hm : 0 < m)
    (hbudget : (m : ℝ) ≤ khatriRaoLowerConstant k * r * Real.log (r : ℝ) ^ k)
    {ε : ℝ} (hε : ε < 1) :
    1 - Real.exp (-Real.sqrt (r : ℝ)) ≤
      (khatriRaoCommonSignLaw r (khatriRaoLowerMode r k) k m).real
        {z | ¬ IsSubspaceEmbedding (khatriRaoCommonSketch z)
          (khatriRaoCommonIsometry r (khatriRaoLowerMode r k) k) ε} := by
  have hrpos : 0 < r := (pow_pos (by omega : 0 < (2 : ℕ)) _).trans_le hr
  have hrR : (2 : ℝ) ^ (4 * k) ≤ r := by exact_mod_cast hr
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ (4 * k)) hrR
  rw [Real.log_pow] at hlog
  have hlog' : 4 * (k : ℝ) * Real.log 2 ≤ Real.log (r : ℝ) := by
    push_cast at hlog
    nlinarith
  have hh := (khatriRaoLowerMode_bounds hk hlog').1
  by_cases hmr : m < r
  · rw [measureReal_not_isSubspaceEmbedding_khatriRaoCommonSketch_eq_one_of_lt hh hmr hε]
    linarith [Real.exp_pos (-Real.sqrt (r : ℝ))]
  · exact one_sub_exp_neg_sqrt_le_measureReal_not_isSubspaceEmbedding_khatriRaoCommonSketch
      hh hm (by omega) (two_mul_le_mul_pow_lowerMode hk hlog' hbudget)
      (sqrt_le_mul_pow_lowerMode hk hrpos hlog') hε

end NLAlib
