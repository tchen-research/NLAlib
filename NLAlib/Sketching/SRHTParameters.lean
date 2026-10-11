import NLAlib.Sketching.SRHTFlattening

/-!
# Exact constants for classical SRHT

The manuscript's Hanson–Wright row threshold is explicitly above the sharper
Gaussian-linearization threshold. Source: `sh:flatten-constants`, atlas `srht-ose`.
-/

noncomputable section
set_option autoImplicit false
namespace NLAlib

/-- The manuscript's actual numerical row bound, retaining its Hanson–Wright
coefficient `256 e²`. Source: operator re-derivation `sh:flatten-constants`. -/
def srhtManuscriptRowBound (n d : ℕ) (δ : ℝ) : ℝ :=
  let a := 256 * Real.exp 1 ^ 2 * Real.log (4 * n / δ)
  d + Real.sqrt (a * d) + a

/-- The original sharper additive threshold is below the manuscript's
coarser threshold, with every coefficient explicit. Source: `sh:flatten-constants`. -/
theorem srhtSharpRowBound_le_manuscript {n d : ℕ} [NeZero n]
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    srhtSharpRowBound n d δ ≤ srhtManuscriptRowBound n d δ := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  let t := Real.log (2 * n / δ)
  let a := 256 * Real.exp 1 ^ 2 * Real.log (4 * n / δ)
  have ht : 0 ≤ t := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]
    linarith
  have hlog : t ≤ Real.log (4 * n / δ) := by
    apply Real.log_le_log (by positivity)
    gcongr
    linarith
  have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have he2 : (1 : ℝ) ≤ Real.exp 1 ^ 2 := by nlinarith
  have hlog0 : 0 ≤ Real.log (4 * n / δ) := ht.trans hlog
  have ha : 32 * t ≤ a := by
    have hm := mul_le_mul_of_nonneg_right he2 hlog0
    dsimp only [a]
    nlinarith
  have ha0 : 0 ≤ a := by linarith
  have hsd := Real.sq_sqrt (Nat.cast_nonneg d)
  have hst := Real.sq_sqrt (show 0 ≤ 8 * t by positivity)
  have hsa := Real.sq_sqrt (mul_nonneg ha0 (Nat.cast_nonneg d))
  have hcross : (2 * Real.sqrt (d : ℝ) * Real.sqrt (8 * t)) ^ 2 = 32 * t * d := by
    rw [mul_pow, mul_pow, hsd, hst]
    ring
  have hmul := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg d)
  have hroots : 2 * Real.sqrt (d : ℝ) * Real.sqrt (8 * t) ≤ Real.sqrt (a * d) := by
    nlinarith [Real.sqrt_nonneg (a * d), Real.sqrt_nonneg (8 * t), Real.sqrt_nonneg (d : ℝ)]
  change (Real.sqrt (d : ℝ) + Real.sqrt (8 * t)) ^ 2 ≤ d + Real.sqrt (a * d) + a
  nlinarith

/-- The manuscript threshold has the advertised additive scale.
Source: `sh:flatten-constants`, including dimension zero. -/
theorem srhtManuscriptRowBound_le_additive {n d : ℕ}
    {δ : ℝ} (ha : 0 ≤ 256 * Real.exp 1 ^ 2 * Real.log (4 * n / δ)) :
    srhtManuscriptRowBound n d δ ≤
      (3 / 2 : ℝ) * (d + 256 * Real.exp 1 ^ 2 * Real.log (4 * n / δ)) := by
  let a := 256 * Real.exp 1 ^ 2 * Real.log (4 * n / δ)
  have hs := Real.sq_sqrt (mul_nonneg ha (Nat.cast_nonneg d))
  have hp : 0 ≤ (a - d) ^ 2 := sq_nonneg _
  change (d : ℝ) + Real.sqrt (a * d) + a ≤ (3 / 2 : ℝ) * (d + a)
  nlinarith [Real.sqrt_nonneg (a * d)]

end NLAlib
