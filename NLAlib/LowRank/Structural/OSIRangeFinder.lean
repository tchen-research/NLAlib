/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Sketching.Properties.ObliviousSubspaceInjection.CrossResidual
import NLAlib.LowRank.Structural.RangeFinder
import NLAlib.Matrix.Spectral.SvdBlocks
import NLAlib.Matrix.Measurability.GramPseudoinverse

/-!
# Frobenius range finding under an oblivious subspace injection

The actual projector onto `range(A Ω)` obeys the `1 + 20/α` squared Frobenius guarantee with
probability at least `9/10`, over real or complex scalars. No Gaussian rotation, independence of
the head and tail blocks, or random choice of orthonormal basis is used.
Source: Camaño–Epperly–Meyer–Tropp (2025), Theorem 2.2; HMT (2011), Theorem 9.1.
Atlas: `osi-range-finder-frobenius`.
-/

noncomputable section
open MeasureTheory
open scoped Matrix
namespace NLAlib
variable {Ω 𝕜 k : Type*} [MeasurableSpace Ω] [RCLike 𝕜] [Fintype k] [DecidableEq k]
  {m n d : ℕ}

omit [DecidableEq k] in
/-- The full sampled-range output has rank at most the sketch width, including deficient
sketches and empty matrices. It need not have rank at most the approximation target.
atlas: osi-range-finder-frobenius (partial) -/
theorem rank_rangeProjector_sampled_mul_le (A : Matrix (Fin m) (Fin n) 𝕜)
    (G : Matrix (Fin n) k 𝕜) :
    (rangeProjector (A * G) * A).rank ≤ Fintype.card k := by
  calc
    (rangeProjector (A * G) * A).rank ≤ (rangeProjector (A * G)).rank :=
      Matrix.rank_mul_le_left _ _
    _ = (A * G).rank := rank_rangeProjector _
    _ ≤ Fintype.card k := Matrix.rank_le_card_width _

/-- The actual OSI range residual has measurable squared Frobenius norm at every rank.
The range projector is measurable through the native Tikhonov limit. -/
theorem measurable_frobSq_osi_rangeResidual {S : Ω → Matrix k (Fin n) 𝕜}
    (hS : Measurable S) (A : Matrix (Fin m) (Fin n) 𝕜) :
    Measurable (fun ω => frobSq (A - rangeProjector (A * (S ω)ᴴ) * A)) := by
  have hP : Measurable (fun ω => rangeProjector (A * (S ω)ᴴ) * A) :=
    (measurable_rangeProjector.comp
      (measurable_const.matrix_mul (Matrix.measurable_conjTranspose.comp hS))).matrix_mul
        measurable_const
  refine measurable_frobSq.comp (Matrix.measurable_iff_entries.mpr fun i j => ?_)
  exact measurable_const.sub ((Matrix.measurable_entry i j).comp hP)

/-- An OSI gives the full-range Frobenius approximation guarantee with the exact factor
`1 + 20/α` and success probability `9/10`. In test-matrix orientation use `S = Ωᴴ`.
The right side is the genuine optimal rank-`d` squared Frobenius tail; the output's rank is
bounded by the sketch width. Camaño–Epperly–Meyer–Tropp (2025), Theorem 2.2.
Atlas: `osi-range-finder-frobenius`.
atlas: osi-range-finder-frobenius (partial) -/
theorem IsObliviousSubspaceInjection.measureReal_frobSq_osi_rangeResidual_le
    {S : Ω → Matrix k (Fin n) 𝕜} {α : ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : IsObliviousSubspaceInjection S d α μ) (hα : 0 < α)
    (A : Matrix (Fin m) (Fin n) 𝕜) (hd : d ≤ n) :
    9 / 10 ≤ μ.real {ω | frobSq (A - rangeProjector (A * (S ω)ᴴ) * A) ≤
      (1 + 20 / α) * bestRankFrobSq A d} := by
  obtain ⟨r, U₁, U₂, V₁, V₂, S₂, hA, hU₂, hV₁, hV₂, hV, htail⟩ :=
    exists_svd_right_blocks A d hd
  have hc := h.measureReal_osiCrossSuccessEvent_ge hα V₁ hV₁ V₂ hV₂ S₂
  refine hc.trans (measureReal_mono ?_)
  intro ω hω
  change ((S ω * V₁)ᴴ).rank = d ∧
    frobSq (S₂ * (S ω * V₂)ᴴ * moorePenroseInverse ((S ω * V₁)ᴴ)) ≤
      (20 / α) * frobSq S₂ at hω
  change frobSq (A - rangeProjector (A * (S ω)ᴴ) * A) ≤ _
  let G₁ := (S ω * V₁)ᴴ
  let G₂ := (S ω * V₂)ᴴ
  have hG₁ : G₁ = V₁ᴴ * (S ω)ᴴ := Matrix.conjTranspose_mul _ _
  have hG₂ : G₂ = V₂ᴴ * (S ω)ᴴ := Matrix.conjTranspose_mul _ _
  have hu : IsUnit (G₁ * G₁ᴴ) := isUnit_mul_conjTranspose_of_rank_eq_card G₁
    (by simpa only [Fintype.card_fin] using hω.1)
  have hb := frobSq_sub_rangeProjector_mul_le_of_svd_blocks
    hA hU₂ hV₁ hV₂ hV hG₁ hG₂ hu
  rw [← moorePenroseInverse_eq_pinvR G₁ hu] at hb
  calc
    frobSq (A - rangeProjector (A * (S ω)ᴴ) * A) ≤
        frobSq S₂ + frobSq (S₂ * G₂ * moorePenroseInverse G₁) := hb
    _ ≤ frobSq S₂ + (20 / α) * frobSq S₂ := add_le_add (le_refl _) hω.2
    _ = (1 + 20 / α) * bestRankFrobSq A d := by rw [htail]; ring

end NLAlib
