import NLAlib.Matrix.Norms.LoewnerBounds
import NLAlib.Matrix.Basic.PSDDuality
import NLAlib.Matrix.Spectral.LeadingRightProjector

/-! # Covariance-loss certificates for deterministic sketches

The Loewner bound and a trace-loss budget compose by addition and telescoping.
Their matrix-tail consequences are independent of the stream or merge algorithm.
Source: Ghashami–Liberty–Phillips–Woodruff (2016), §2.
Atlas: `covariance-loss-tail-bound` (consumer interface).
-/

noncomputable section
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib
variable {𝕜 d : Type*} [RCLike 𝕜] [Fintype d] [DecidableEq d]

/-- A deterministic covariance-loss certificate at capacity `ℓ`. The arguments are actual
Gram matrices in algorithmic applications; the certificate itself only records the
Loewner and real-trace inequalities needed for tail bounds and composition. -/
structure CovarianceLossCertificate (ℓ : ℕ) (G H : Matrix d d 𝕜) (Δ : ℝ) : Prop where
  loss_nonneg : 0 ≤ Δ
  sub_nonneg : 0 ≤ G - H
  sub_le : G - H ≤ Δ • (1 : Matrix d d 𝕜)
  trace_loss : (ℓ : ℝ) * Δ ≤ RCLike.re (G - H).trace

namespace CovarianceLossCertificate
variable {ℓ : ℕ} {G H K G₁ G₂ H₁ H₂ : Matrix d d 𝕜} {Δ Δ₁ Δ₂ : ℝ}

/-- The identity approximation has the zero-loss certificate. -/
theorem zero (ℓ : ℕ) (G : Matrix d d 𝕜) : CovarianceLossCertificate ℓ G G 0 := by
  constructor <;> simp

/-- Consecutive covariance losses telescope without increasing the capacity. -/
theorem trans (h₁ : CovarianceLossCertificate ℓ G H Δ₁)
    (h₂ : CovarianceLossCertificate ℓ H K Δ₂) :
    CovarianceLossCertificate ℓ G K (Δ₁ + Δ₂) := by
  have heq : G - K = (G - H) + (H - K) := by abel
  constructor
  · exact add_nonneg h₁.loss_nonneg h₂.loss_nonneg
  · rw [heq]
    exact add_nonneg h₁.sub_nonneg h₂.sub_nonneg
  · rw [heq, add_smul]
    exact add_le_add h₁.sub_le h₂.sub_le
  · rw [heq, Matrix.trace_add, map_add]
    nlinarith [h₁.trace_loss, h₂.trace_loss]

/-- Block covariance losses add with the same capacity and no dependence on a merge depth. -/
theorem add (h₁ : CovarianceLossCertificate ℓ G₁ H₁ Δ₁)
    (h₂ : CovarianceLossCertificate ℓ G₂ H₂ Δ₂) :
    CovarianceLossCertificate ℓ (G₁ + G₂) (H₁ + H₂) (Δ₁ + Δ₂) := by
  have heq : (G₁ + G₂) - (H₁ + H₂) = (G₁ - H₁) + (G₂ - H₂) := by abel
  constructor
  · exact add_nonneg h₁.loss_nonneg h₂.loss_nonneg
  · rw [heq]
    exact add_nonneg h₁.sub_nonneg h₂.sub_nonneg
  · rw [heq, add_smul]
    exact add_le_add h₁.sub_le h₂.sub_le
  · rw [heq, Matrix.trace_add, map_add]
    nlinarith [h₁.trace_loss, h₂.trace_loss]

/-- A PSD covariance loss bounded by `ΔI` has spectral norm at most `Δ`. -/
theorem specNorm_sub_le (h : CovarianceLossCertificate ℓ G H Δ) : specNorm (G - H) ≤ Δ :=
  ((Matrix.nonneg_iff_posSemidef.mp h.sub_nonneg).specNorm_le_iff h.loss_nonneg).mpr h.sub_le

private theorem re_trace_projector_mul_le {P D : Matrix d d 𝕜}
    (hs : P.IsHermitian) (hp : IsIdempotentElem P) {Δ : ℝ}
    (hD : D ≤ Δ • (1 : Matrix d d 𝕜)) :
    RCLike.re (P * D).trace ≤ (P.rank : ℝ) * Δ := by
  have h := trace_mul_nonneg_of_posSemidef (hs.posSemidef_of_isIdempotentElem hp)
    (Matrix.le_iff.mp hD)
  have hr := (RCLike.nonneg_iff.mp h).1
  simp only [Matrix.mul_sub, Matrix.trace_sub, map_sub, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_smul, RCLike.smul_re,
    trace_eq_rank_of_isIdempotentElem P hp, RCLike.natCast_re] at hr
  nlinarith

private theorem re_trace_complement_gram_eq_error {m : Type*} [Fintype m]
    (A : Matrix m d 𝕜) {P : Matrix d d 𝕜} (hs : P.IsHermitian) (hp : IsIdempotentElem P) :
    RCLike.re ((1 - P) * (Aᴴ * A)).trace = frobSq (A - A * P) := by
  have hQ := one_sub_projector_isHermitian_isIdempotentElem hs hp
  rw [← frobSq_mul_projector_eq_re_trace_mul hQ.1 hQ.2 A, Matrix.mul_sub, Matrix.mul_one]

variable {m r : Type*} [Fintype m] [Fintype r] [DecidableEq m]

/-- The trace-loss budget forces the accumulated loss below the best-rank tail divided
by capacity minus target rank. No division by the loss or tail is used.
Ghashami–Liberty–Phillips–Woodruff (2016), proofs of Theorems 1.1–1.2.
atlas: covariance-loss-tail-bound (partial)-/
theorem loss_le_bestRankFrobSq_div {A : Matrix m d 𝕜} {B : Matrix r d 𝕜}
    (h : CovarianceLossCertificate ℓ (Aᴴ * A) (Bᴴ * B) Δ)
    {k : ℕ} (hkℓ : k < ℓ) (hkd : k ≤ Fintype.card d) :
    Δ ≤ bestRankFrobSq A k / ((ℓ - k : ℕ) : ℝ) := by
  obtain ⟨U, V, hA⟩ := exists_isSVD A
  let P := hA.leadingRightProjector k
  let G := Aᴴ * A
  let H := Bᴴ * B
  let D := G - H
  have hs := hA.leadingRightProjector_isHermitian k
  have hp := hA.leadingRightProjector_isIdempotentElem k
  have hrank : P.rank = k := hA.rank_leadingRightProjector_of_le hkd
  have hUpper := re_trace_projector_mul_le hs hp h.sub_le
  rw [hrank] at hUpper
  have hQ := one_sub_projector_isHermitian_isIdempotentElem hs hp
  have hH : H.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self B
  have hCompH := (RCLike.nonneg_iff.mp (trace_mul_nonneg_of_posSemidef
    (hQ.1.posSemidef_of_isIdempotentElem hQ.2) hH)).1
  have hTail : RCLike.re ((1 - P) * G).trace = bestRankFrobSq A k := by
    rw [re_trace_complement_gram_eq_error A hs hp]
    exact hA.frobSq_sub_mul_leadingRightProjector k
  have hSplit : RCLike.re D.trace =
      RCLike.re (P * D).trace + RCLike.re ((1 - P) * D).trace := by
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, map_sub]
    ring
  have hComp : RCLike.re ((1 - P) * D).trace =
      RCLike.re ((1 - P) * G).trace - RCLike.re ((1 - P) * H).trace := by
    dsimp only [D]
    rw [Matrix.mul_sub, Matrix.trace_sub, map_sub]
  have hTrace := h.trace_loss
  change (ℓ : ℝ) * Δ ≤ RCLike.re D.trace at hTrace
  have hden : 0 < ((ℓ - k : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hkℓ
  apply (le_div_iff₀ hden).mpr
  rw [Nat.cast_sub hkℓ.le]
  nlinarith

/-- The actual covariance error has the sharp capacity-tail bound, including zero tails.
Ghashami–Liberty–Phillips–Woodruff (2016), Theorem 1.1.
atlas: covariance-loss-tail-bound (partial)-/
theorem specNorm_sub_gram_le_bestRankFrobSq_div {A : Matrix m d 𝕜} {B : Matrix r d 𝕜}
    (h : CovarianceLossCertificate ℓ (Aᴴ * A) (Bᴴ * B) Δ)
    {k : ℕ} (hkℓ : k < ℓ) (hkd : k ≤ Fintype.card d) :
    specNorm (Aᴴ * A - Bᴴ * B) ≤ bestRankFrobSq A k / ((ℓ - k : ℕ) : ℝ) :=
  h.specNorm_sub_le.trans (h.loss_le_bestRankFrobSq_div hkℓ hkd)

/-- A rank-k maximizing right projector of the sketch loses at most the original best
rank-k tail plus k times the covariance loss. The hypothesis is the genuine Gram-trace
maximization contract, realized by every full SVD leading projector.
Ghashami–Liberty–Phillips–Woodruff (2016), Theorem 1.2.
atlas: covariance-loss-tail-bound (partial)-/
theorem frobSq_error_le_bestRankFrobSq_add {A : Matrix m d 𝕜} {B : Matrix r d 𝕜}
    (h : CovarianceLossCertificate ℓ (Aᴴ * A) (Bᴴ * B) Δ) {k : ℕ}
    (hkd : k ≤ Fintype.card d) (P : Matrix d d 𝕜)
    (hs : P.IsHermitian) (hp : IsIdempotentElem P) (_hRank : P.rank = k)
    (hMax : ∀ Q : Matrix d d 𝕜, Q.IsHermitian → IsIdempotentElem Q → Q.rank = k →
      RCLike.re (Q * (Bᴴ * B)).trace ≤ RCLike.re (P * (Bᴴ * B)).trace) :
    frobSq (A - A * P) ≤ bestRankFrobSq A k + (k : ℝ) * Δ := by
  obtain ⟨U, V, hA⟩ := exists_isSVD A
  let Q := hA.leadingRightProjector k
  let G := Aᴴ * A
  let H := Bᴴ * B
  let D := G - H
  have hsQ := hA.leadingRightProjector_isHermitian k
  have hpQ := hA.leadingRightProjector_isIdempotentElem k
  have hrQ : Q.rank = k := hA.rank_leadingRightProjector_of_le hkd
  have hCompD := (RCLike.nonneg_iff.mp (trace_mul_nonneg_of_posSemidef
    (hs.posSemidef_of_isIdempotentElem hp) (Matrix.nonneg_iff_posSemidef.mp h.sub_nonneg))).1
  have hMaxQ := hMax Q hsQ hpQ hrQ
  have hUpper := re_trace_projector_mul_le hsQ hpQ h.sub_le
  rw [hrQ] at hUpper
  have hError : frobSq (A - A * P) = RCLike.re G.trace - RCLike.re (P * G).trace := by
    rw [← re_trace_complement_gram_eq_error A hs hp]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, map_sub, G]
  have hTail : bestRankFrobSq A k = RCLike.re G.trace - RCLike.re (Q * G).trace := by
    rw [← hA.frobSq_sub_mul_leadingRightProjector k,
      ← re_trace_complement_gram_eq_error A hsQ hpQ]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, map_sub, G]
    rfl
  have hPD : RCLike.re (P * D).trace = RCLike.re (P * G).trace - RCLike.re (P * H).trace := by
    dsimp only [D]
    rw [Matrix.mul_sub, Matrix.trace_sub, map_sub]
  have hQD : RCLike.re (Q * D).trace = RCLike.re (Q * G).trace - RCLike.re (Q * H).trace := by
    dsimp only [D]
    rw [Matrix.mul_sub, Matrix.trace_sub, map_sub]
  nlinarith

/-- Any rank-k Gram-trace maximizer of the sketch has the relative projection bound.
This includes k=0, empty input row sets, deficient ranks, and zero optimal tails.
Ghashami–Liberty–Phillips–Woodruff (2016), Theorem 1.2.
atlas: covariance-loss-tail-bound (partial)-/
theorem frobSq_error_le_capacity_mul_bestRankFrobSq_div {A : Matrix m d 𝕜} {B : Matrix r d 𝕜}
    (h : CovarianceLossCertificate ℓ (Aᴴ * A) (Bᴴ * B) Δ) {k : ℕ}
    (hkℓ : k < ℓ) (hkd : k ≤ Fintype.card d) (P : Matrix d d 𝕜)
    (hs : P.IsHermitian) (hp : IsIdempotentElem P) (hRank : P.rank = k)
    (hMax : ∀ Q : Matrix d d 𝕜, Q.IsHermitian → IsIdempotentElem Q → Q.rank = k →
      RCLike.re (Q * (Bᴴ * B)).trace ≤ RCLike.re (P * (Bᴴ * B)).trace) :
    frobSq (A - A * P) ≤ (ℓ : ℝ) / ((ℓ - k : ℕ) : ℝ) * bestRankFrobSq A k := by
  have hError := h.frobSq_error_le_bestRankFrobSq_add hkd P hs hp hRank hMax
  have hDelta := h.loss_le_bestRankFrobSq_div hkℓ hkd
  have hScale := mul_le_mul_of_nonneg_left hDelta (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hden : 0 < ((ℓ - k : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hkℓ
  have heq : bestRankFrobSq A k + (k : ℝ) * (bestRankFrobSq A k / ((ℓ - k : ℕ) : ℝ)) =
      (ℓ : ℝ) / ((ℓ - k : ℕ) : ℝ) * bestRankFrobSq A k := by
    rw [Nat.cast_sub hkℓ.le] at hden ⊢
    field_simp [ne_of_gt hden]
    ring
  rw [← heq]
  linarith

/-- Every actual SVD of the sketch realizes the rank-k projection guarantee; no
maximization oracle or selector hypothesis is needed. The cutoff only concerns the
width, and the input and sketch may each have fewer than k rows.
Ghashami–Liberty–Phillips–Woodruff (2016), Theorem 1.2.
atlas: covariance-loss-tail-bound (partial)-/
theorem frobSq_error_le_capacity_mul_bestRankFrobSq_div_of_isSVD [DecidableEq r]
    {A : Matrix m d 𝕜}
    {B : Matrix r d 𝕜} {p q : ℕ} {U : Matrix r (Fin p) 𝕜} {V : Matrix d (Fin q) 𝕜}
    (hB : NLAlib.IsSVD B U V) (h : CovarianceLossCertificate ℓ (Aᴴ * A) (Bᴴ * B) Δ)
    {k : ℕ} (hkℓ : k < ℓ) (hkd : k ≤ Fintype.card d) :
    frobSq (A - A * hB.leadingRightProjector k) ≤
      (ℓ : ℝ) / ((ℓ - k : ℕ) : ℝ) * bestRankFrobSq A k := by
  apply h.frobSq_error_le_capacity_mul_bestRankFrobSq_div hkℓ hkd
    (hB.leadingRightProjector k) (hB.leadingRightProjector_isHermitian k)
    (hB.leadingRightProjector_isIdempotentElem k)
    (hB.rank_leadingRightProjector_of_le hkd)
  intro Q hQ hQQ hRank
  exact hB.re_trace_mul_gram_le_leadingRightProjector k hQ hQQ hRank.le

end CovarianceLossCertificate
end NLAlib
