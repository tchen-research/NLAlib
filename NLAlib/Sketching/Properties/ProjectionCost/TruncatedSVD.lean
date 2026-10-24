import NLAlib.Matrix.Subspaces.SvdTailCapture
import NLAlib.Sketching.Properties.ProjectionCost.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-! # A leading SVD factor is a fixed-offset projection-cost sketch

The actual ℓ-column factor U_ℓ Σ_ℓ is paired with one offset equal to the discarded
Frobenius mass. Tail averaging yields the sharp k/ℓ route, including the capped exact
endpoint and a separate zero-target-rank theorem. Source: Cohen et al. (2015), Theorem 7.
Atlas: `truncated-svd-projection-cost-sketch`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- Leading-factor cost plus discarded mass differs from the original cost by exactly
the projected tail energy. The same offset works for every projector.
atlas: truncated-svd-projection-cost-sketch (partial) -/
theorem IsSVD.frobSq_leadingFactor_add_tail_eq {p q : ℕ} {A : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜} (h : IsSVD A U V) (ℓ : ℕ)
    {P : Matrix m m 𝕜} (hP : IsStarProjection P) :
    frobSq ((1 - P) * h.leadingFactor ℓ) + frobSq (A - h.truncatedMatrix ℓ) =
      frobSq ((1 - P) * A) + frobSq (P * (A - h.truncatedMatrix ℓ)) := by
  let T := A - h.truncatedMatrix ℓ
  have hs : P.IsHermitian := hP.isSelfAdjoint.star_eq
  have hPT : frobSq (P * T) = RCLike.re (P * (T * Tᴴ)).trace := by
    rw [← frobSq_conjTranspose (P * T), Matrix.conjTranspose_mul, hs.eq,
      frobSq_mul_projector_eq_re_trace_mul hs hP.isIdempotentElem Tᴴ,
      Matrix.conjTranspose_conjTranspose]
  have hDef := frobSq_one_sub_mul_add_sub_eq hP A (h.leadingFactor ℓ) (frobSq T)
  rw [h.sub_leadingFactor_gram_eq_tail_gram ℓ,
    ← frobSq_eq_re_trace_mul_conjTranspose, ← hPT] at hDef
  linarith

/-- A width-and-height admissible leading cutoff satisfying k≤εℓ gives the full
one-sided PCP contract for the actual ℓ-column factor and fixed discarded-mass offset. -/
theorem IsSVD.isProjectionCostPreservingWithOffset_leadingFactor_of_le {p q : ℕ}
    {A : Matrix m n 𝕜} {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜}
    (h : IsSVD A U V) {ℓ k : ℕ} {ε : ℝ} (hℓp : ℓ ≤ p) (hℓ : 0 < ℓ)
    (hkℓ : k ≤ ℓ) (hε : 0 ≤ ε) (hScale : (k : ℝ) ≤ ε * ℓ) :
    IsProjectionCostPreservingWithOffset A (h.leadingFactor ℓ) k 1 (1 + ε)
      (frobSq (A - h.truncatedMatrix ℓ)) := by
  refine ⟨frobSq_nonneg _, ?_⟩
  intro P hP hRank
  have hs : P.IsHermitian := hP.isSelfAdjoint.star_eq
  have hp := hP.isIdempotentElem
  have hExact := h.frobSq_leadingFactor_add_tail_eq ℓ hP
  have hCapture := h.mul_frobSq_projector_tail_le_mul_bestRankFrobSq hℓp hkℓ hs hp hRank.le
  have hBest := bestRankFrobSq_le_frobSq_sub_of_rank_le A (P * A) k
    ((Matrix.rank_mul_le_left P A).trans hRank.le)
  rw [show A - P * A = (1 - P) * A by rw [Matrix.sub_mul, Matrix.one_mul]] at hBest
  have hTail0 : 0 ≤ bestRankFrobSq A k := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> positivity
  have hMul := mul_le_mul_of_nonneg_right hScale hTail0
  have hεBest := mul_le_mul_of_nonneg_left hBest hε
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hProjected : frobSq (P * (A - h.truncatedMatrix ℓ)) ≤ ε * frobSq ((1 - P) * A) := by
    apply (mul_le_mul_iff_of_pos_left hℓpos).mp
    calc
      (ℓ : ℝ) * frobSq (P * (A - h.truncatedMatrix ℓ)) ≤ (k : ℝ) * bestRankFrobSq A k := hCapture
      _ ≤ (ℓ : ℝ) * (ε * bestRankFrobSq A k) := by nlinarith [hMul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hεBest hℓpos.le
  constructor
  · rw [one_mul, hExact]
    exact le_add_of_nonneg_right (frobSq_nonneg _)
  · rw [hExact]
    nlinarith

/-- The source cutoff min(ceil(k/ε),min(height,width)) realizes a one-sided PCP sketch
with ℓ actual columns and one projector-independent discarded-mass offset. All tied
singular bases are allowed; the capped endpoint has exactly zero discarded tail.
Cohen–Elder–Musco–Musco–Persu (2015), Theorem 7; real and complex fields.
atlas: truncated-svd-projection-cost-sketch (partial)-/
theorem IsSVD.isProjectionCostPreservingWithOffset_leadingFactor {p q : ℕ}
    {A : Matrix m n 𝕜} {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜}
    (h : IsSVD A U V) {k : ℕ} {ε : ℝ} (hk : 0 < k)
    (hkm : k ≤ min (Fintype.card m) (Fintype.card n)) (hε0 : 0 < ε) (hε1 : ε < 1) :
    let ℓ := min (Nat.ceil ((k : ℝ) / ε)) (min (Fintype.card m) (Fintype.card n))
    IsProjectionCostPreservingWithOffset A (h.leadingFactor ℓ) k 1 (1 + ε)
      (frobSq (A - h.truncatedMatrix ℓ)) := by
  let M := min (Fintype.card m) (Fintype.card n)
  let ℓ := min (Nat.ceil ((k : ℝ) / ε)) M
  change IsProjectionCostPreservingWithOffset A (h.leadingFactor ℓ) k 1 (1 + ε)
    (frobSq (A - h.truncatedMatrix ℓ))
  have hceil := Nat.le_ceil ((k : ℝ) / ε)
  have hkDiv : (k : ℝ) ≤ (k : ℝ) / ε := by
    apply (le_div_iff₀ hε0).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hε1.le (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hkCeil : k ≤ Nat.ceil ((k : ℝ) / ε) := by exact_mod_cast hkDiv.trans hceil
  have hkℓ : k ≤ ℓ := Nat.le_min.mpr ⟨hkCeil, hkm⟩
  have hℓp : ℓ ≤ p := by
    have hm : M ≤ Fintype.card m := Nat.min_le_left _ _
    have hLM : ℓ ≤ M := Nat.min_le_right _ _
    have hh := hLM.trans hm
    simpa only [h.card_left] using hh
  by_cases hCap : ℓ = M
  · have hz := h.sub_truncatedMatrix_eq_zero_of_min_le (show M ≤ ℓ by omega)
    refine ⟨frobSq_nonneg _, ?_⟩
    intro P hP _
    have he := h.frobSq_leadingFactor_add_tail_eq ℓ hP
    rw [hz, Matrix.mul_zero, frobSq_zero, add_zero, add_zero] at he
    constructor
    · simpa only [hz, frobSq_zero, add_zero, one_mul] using he.ge
    · simp only [hz, frobSq_zero, add_zero, he]
      nlinarith [mul_nonneg hε0.le (frobSq_nonneg ((1 - P) * A))]
  · have hLCeil : ℓ = Nat.ceil ((k : ℝ) / ε) := by dsimp only [ℓ]; omega
    have hScale : (k : ℝ) ≤ ε * ℓ := by
      rw [hLCeil]
      have hh := (div_le_iff₀ hε0).mp hceil
      nlinarith
    exact h.isProjectionCostPreservingWithOffset_leadingFactor_of_le hℓp
      (hk.trans_le hkℓ) hkℓ hε0.le hScale

omit [DecidableEq n] in
/-- The zero-target-rank endpoint uses an empty sketch and the entire original mass
as the exact fixed offset; it requires no division by ε or k.
atlas: truncated-svd-projection-cost-sketch (partial)-/
theorem isProjectionCostPreservingWithOffset_zero_rank (A : Matrix m n 𝕜) :
    IsProjectionCostPreservingWithOffset A (0 : Matrix m (Fin 0) 𝕜) 0 1 1 (frobSq A) := by
  refine ⟨frobSq_nonneg A, ?_⟩
  intro P _ hRank
  have hP : P = 0 := eq_zero_of_matrix_rank_eq_zero hRank
  simp [hP]

end NLAlib
