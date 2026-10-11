import NLAlib.Sketching.CountSketchExpectation
import NLAlib.Sketching.Gram

/-!
# CountSketch subspace embeddings from the exact second moment

Nonnegative Markov and the Frobenius/spectral norm inequality give the
explicit `(d²+d)/(m ε²)` failure bound for the actual hash-and-sign law.
Source: operator manuscript `sh:count-ose`; supports `sparse-ose`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Matrix
open scoped Matrix
namespace NLAlib

variable {ι ρ d : Type*} [Fintype ι] [Fintype ρ] [Fintype d]
variable [DecidableEq ι] [DecidableEq ρ] [DecidableEq d]
variable [MeasurableSpace ρ] [MeasurableSingletonClass ρ] [Nonempty ρ]

/-- Dropping the nonnegative leverage correction bounds the actual CountSketch
Gram-error second moment by `(d²+d)/m`. Source: manuscript `sh:count-second`;
supports `sparse-ose`. -/
theorem integral_frobSq_countSketch_gram_error_le
    (U : Matrix ι d ℝ) (hU : HasOrthonormalCols U) :
    (∫ z : (ι → ρ) × (ι → ℝ),
      frobSq ((countSketchMatrix z.1 z.2 * U)ᵀ * (countSketchMatrix z.1 z.2 * U) - 1)
        ∂countSketchLaw) ≤
      ((Fintype.card d : ℝ) ^ 2 + Fintype.card d) / Fintype.card ρ := by
  rw [integral_frobSq_countSketch_gram_error_eq U hU]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact sub_le_self _ (by positivity)

/-- **CountSketch Gram tail.** The actual independent uniform hash and sign
law has spectral Gram-error failure probability at most `(d²+d)/(m ε²)`.
Source: manuscript `sh:count-ose`. Zero-dimensional subspaces are included.
atlas: sparse-ose (partial) -/
theorem measure_countSketch_gram_failure_le
    (U : Matrix ι d ℝ) (hU : HasOrthonormalCols U) {ε : ℝ} (hε : 0 < ε) :
    (countSketchLaw (ι := ι) (ρ := ρ)).real
      {z | ε ≤ specNorm ((countSketchMatrix z.1 z.2 * U)ᵀ *
        (countSketchMatrix z.1 z.2 * U) - 1)} ≤
      ((Fintype.card d : ℝ) ^ 2 + Fintype.card d) /
        ((Fintype.card ρ : ℝ) * ε ^ 2) := by
  let E := fun z : (ι → ρ) × (ι → ℝ) =>
    (countSketchMatrix z.1 z.2 * U)ᵀ * (countSketchMatrix z.1 z.2 * U) - 1
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (countSketchLaw (ι := ι) (ρ := ρ)) (fun z => frobSq_nonneg (E z)))
    (integrable_frobSq_countSketch_gram_error U hU) (ε ^ 2)
  have hsubset : {z | ε ≤ specNorm (E z)} ⊆ {z | ε ^ 2 ≤ frobSq (E z)} := by
    intro z hz
    exact (pow_le_pow_left₀ hε.le hz 2).trans (specNorm_sq_le_frobSq (E z))
  calc
    _ ≤ (countSketchLaw (ι := ι) (ρ := ρ)).real {z | ε ^ 2 ≤ frobSq (E z)} :=
      measureReal_mono hsubset
    _ ≤ (((Fintype.card d : ℝ) ^ 2 + Fintype.card d) / Fintype.card ρ) / ε ^ 2 := by
      apply (le_div_iff₀ hεsq).2
      have hh := hmarkov.trans (integral_frobSq_countSketch_gram_error_le U hU)
      simpa only [mul_comm] using hh
    _ = _ := by rw [div_div]

/-- **CountSketch row prescription.** The stated row count gives failure at
most `δ` under the actual sampling law. Source: manuscript `sh:count-ose`.
atlas: sparse-ose (partial) -/
theorem measure_countSketch_gram_failure_le_of_rows
    (U : Matrix ι d ℝ) (hU : HasOrthonormalCols U) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ)
    (hrows : ((Fintype.card d : ℝ) ^ 2 + Fintype.card d) / (δ * ε ^ 2) ≤ Fintype.card ρ) :
    (countSketchLaw (ι := ι) (ρ := ρ)).real
      {z | ε ≤ specNorm ((countSketchMatrix z.1 z.2 * U)ᵀ *
        (countSketchMatrix z.1 z.2 * U) - 1)} ≤ δ := by
  apply (measure_countSketch_gram_failure_le U hU hε).trans
  have hm : (0 : ℝ) < Fintype.card ρ := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ (mul_pos hm (sq_pos_of_pos hε))).2
  have hh := (div_le_iff₀ (mul_pos hδ (sq_pos_of_pos hε))).1 hrows
  simpa only [mul_assoc, mul_left_comm] using hh

/-- The actual CountSketch matrix preserves the full input subspace except
on a set of probability at most `δ`. Source: manuscript `sh:count-ose` and
the proved Gram characterization of `IsSubspaceEmbedding`.
atlas: sparse-ose (partial) -/
theorem measure_countSketch_embedding_failure_le_of_rows
    (U : Matrix ι d ℝ) (hU : HasOrthonormalCols U) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ)
    (hrows : ((Fintype.card d : ℝ) ^ 2 + Fintype.card d) / (δ * ε ^ 2) ≤ Fintype.card ρ) :
    (countSketchLaw (ι := ι) (ρ := ρ)).real
      {z | ¬ IsSubspaceEmbedding (countSketchMatrix z.1 z.2) U ε} ≤ δ := by
  apply le_trans (measureReal_mono (fun z hz => ?_))
    (measure_countSketch_gram_failure_le_of_rows U hU hε hδ hrows)
  by_contra hbad
  apply hz
  exact isSubspaceEmbedding_of_specNorm_transpose_mul_self_sub_one_le hU
    (not_le.mp hbad).le

end NLAlib
