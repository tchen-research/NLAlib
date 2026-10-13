import NLAlib.RandomMatrix.Gaussian.Invariance.LinearImage
import NLAlib.RandomMatrix.Gaussian.Spectral.Deviation
import NLAlib.Matrix.Spectral.SpectralBounds
import NLAlib.Sketching.Properties.SubspaceEmbedding.SubspaceEmbedding
/-!
# Gaussian oblivious subspace embeddings

For a fixed `U ∈ ℝ^{m×d}` with orthonormal columns and a `k × m` standard Gaussian matrix `G`,
the sketch `S = k^{-1/2} G` is an `ε`-subspace embedding for `range U` with probability at least
`1 − δ` as soon as `k ≥ 18 (d + 2 log(2/δ)) / ε²`
(`one_sub_le_measure_isSubspaceEmbedding_gaussianMatrix`).

Proof: `G U` is a `k × d` standard Gaussian matrix (`hasLaw_gaussianMatrix_mul_right`); with
`t = √(2 log(2/δ))`, with probability at least `1 − 2e^{-t²/2} = 1 − δ` its singular values lie in
`[√k − √d − t, √k + √d + t]` (`measure_sigmaMin_le_sqrt_sub_sqrt_sub_le_gaussianMatrix`,
`measure_sqrt_add_sqrt_add_le_specNorm_le_gaussianMatrix`). With `a = (√d + t)/√k`, the hypothesis
on `k` and `(√d + t)² ≤ 2d + 2t²` give `3a ≤ ε`, and the deterministic lemma
`isSubspaceEmbedding_of_forall_sqrt_le` converts `σ(SU) ⊂ [1 − a, 1 + a]` into the embedding.

Source: Woodruff 2014, Thm 2.3 (with explicit constants); Martinsson–Tropp 2020, §8.7
and §9.3 (Gaussian embeddings via Davidson–Szarek). Atlas: `gaussian-ose` (the atlas's
`k ≥ C(d + log(1/δ))/ε²` with the explicit constant `C = 18`, `log(1/δ)` replaced by
`2 log(2/δ)`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- **Deterministic embedding criterion.** If `U` has orthonormal columns and every
`‖SUx‖` lies between `(1 − a)‖x‖` and `(1 + a)‖x‖`, with `0 ≤ a`, `3a ≤ ε ≤ 1`, then `S` is an
`ε`-subspace embedding for `range U` (since `(1 − a)² ≥ 1 − ε` and `(1 + a)² ≤ 1 + ε`).
Woodruff 2014, proof of Thm 2.3; atlas `gaussian-ose` (helper; uses `ose-def`).
atlas: gaussian-ose -/
theorem isSubspaceEmbedding_of_forall_sqrt_le {k m d : Type*} [Fintype k] [Fintype m]
    [Fintype d] [DecidableEq d] {S : Matrix k m ℝ} {U : Matrix m d ℝ}
    (hU : HasOrthonormalCols U) {ε a : ℝ} (hε : ε ≤ 1) (ha : 0 ≤ a) (haε : 3 * a ≤ ε)
    (hlo : ∀ x : d → ℝ,
      (1 - a) * Real.sqrt (x ⬝ᵥ x) ≤ Real.sqrt (((S * U) *ᵥ x) ⬝ᵥ ((S * U) *ᵥ x)))
    (hhi : ∀ x : d → ℝ,
      Real.sqrt (((S * U) *ᵥ x) ⬝ᵥ ((S * U) *ᵥ x)) ≤ (1 + a) * Real.sqrt (x ⬝ᵥ x)) :
    IsSubspaceEmbedding S U ε := by
  rw [isSubspaceEmbedding_iff_of_hasOrthonormalCols hU]
  intro x
  have hx := dotProduct_self_nonneg x
  have hv := dotProduct_self_nonneg ((S * U) *ᵥ x)
  have ha1 : 0 ≤ 1 - a := by linarith
  constructor
  · have h := pow_le_pow_left₀ (mul_nonneg ha1 (Real.sqrt_nonneg _)) (hlo x) 2
    rw [mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hv] at h
    have hc : 1 - ε ≤ (1 - a) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hc hx]
  · have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hhi x) 2
    rw [mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hv] at h
    have hc : (1 + a) ^ 2 ≤ 1 + ε := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hc hx]

/-- **Gaussian oblivious subspace embedding.** Let `U ∈ ℝ^{m×d}` have orthonormal columns,
`0 < ε ≤ 1`, `0 < δ ≤ 1` and `k ≥ 18 (d + 2 log(2/δ)) / ε²`. Then a `k × m` standard Gaussian
matrix `G` makes `S = k^{-1/2} G` an `ε`-subspace embedding for `range U` with probability at least
`1 − δ`.

Woodruff 2014, Thm 2.3 (stated there with unspecified constants); Martinsson–Tropp 2020, §8.7,
§9.3. Atlas `gaussian-ose` (uses `ose-def`, `extreme-singular-values-deviation`,
`rotation-invariance`). Deviations: explicit constant `18` and `2 log(2/δ)` in place of the
atlas's `C` and `log(1/δ)`; the probability is an outer-measure lower bound (no measurability of
the embedding event is claimed); `d = 0` holds trivially.
atlas: gaussian-ose -/
theorem one_sub_le_measure_isSubspaceEmbedding_gaussianMatrix {k m d : ℕ}
    (U : Matrix (Fin m) (Fin d) ℝ) (hU : HasOrthonormalCols U) {ε δ : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hk : 18 * ((d : ℝ) + 2 * Real.log (2 / δ)) / ε ^ 2 ≤ k) :
    1 - δ ≤
      (gaussianMatrix (Fin k) (Fin m)).real
        {G | IsSubspaceEmbedding ((1 / Real.sqrt k) • G) U ε} := by
  set μ := gaussianMatrix (Fin k) (Fin m)
  set E := {G : Matrix (Fin k) (Fin m) ℝ | IsSubspaceEmbedding ((1 / Real.sqrt k) • G) U ε}
  -- It suffices to bound the complement by `δ`.
  suffices hc : μ.real Eᶜ ≤ δ by
    have h1 : (1 : ℝ) ≤ μ.real E + μ.real Eᶜ := by
      calc (1 : ℝ) = μ.real Set.univ := by simp
        _ = μ.real (E ∪ Eᶜ) := by rw [Set.union_compl_self]
        _ ≤ μ.real E + μ.real Eᶜ := measureReal_union_le _ _
    linarith
  rcases Nat.eq_zero_or_pos d with hd | hd
  · -- `d = 0`: every sketch is an embedding of the zero subspace.
    subst hd
    have hE : Eᶜ = ∅ := by
      ext G
      simp only [E, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
        not_not]
      intro x
      have hx : x = 0 := Subsingleton.elim _ _
      subst hx
      simp
    rw [hE, measureReal_empty]
    exact hδ0.le
  -- Parameters.
  have hlog : 0 ≤ Real.log (2 / δ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  set t := Real.sqrt (2 * Real.log (2 / δ)) with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = 2 * Real.log (2 / δ) := Real.sq_sqrt (by linarith)
  have hδeq : 2 * Real.exp (-t ^ 2 / 2) = δ := by
    rw [ht2, show -(2 * Real.log (2 / δ)) / 2 = -Real.log (2 / δ) by ring, Real.exp_neg,
      Real.exp_log (by positivity)]
    field_simp
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hkpos : (0 : ℝ) < k := by
    have : 0 < 18 * ((d : ℝ) + 2 * Real.log (2 / δ)) / ε ^ 2 := by positivity
    linarith
  set sk := Real.sqrt k with hsk
  have hsk0 : 0 < sk := Real.sqrt_pos.2 hkpos
  set a := (Real.sqrt d + t) / sk with ha
  have ha0 : 0 ≤ a := div_nonneg (add_nonneg (Real.sqrt_nonneg _) ht0) hsk0.le
  have haε : 3 * a ≤ ε := by
    -- `(√d + t)² ≤ 2d + 2t² = 2(d + 2 log(2/δ)) ≤ ε² k / 9`.
    have h1 : (Real.sqrt d + t) ^ 2 ≤ 2 * d + 2 * t ^ 2 := by
      have := Real.sq_sqrt hdpos.le
      nlinarith [sq_nonneg (Real.sqrt d - t)]
    have h2 : 18 * ((d : ℝ) + 2 * Real.log (2 / δ)) ≤ ε ^ 2 * k := by
      rw [div_le_iff₀ (by positivity)] at hk; linarith
    have h3 : (3 * (Real.sqrt d + t)) ^ 2 ≤ (ε * sk) ^ 2 := by
      rw [mul_pow, mul_pow, hsk, Real.sq_sqrt hkpos.le]
      nlinarith
    have h4 : 3 * (Real.sqrt d + t) ≤ ε * sk :=
      (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h3
    rw [ha, mul_div_assoc', div_le_iff₀ hsk0]
    exact h4
  -- The good event for `G U` and the pullback.
  set φ : (Matrix (Fin k) (Fin m) ℝ) → (Matrix (Fin k) (Fin d) ℝ) := fun G => (G * U)
  have hφ : Measurable φ := measurable_id.matrix_mul measurable_const
  set S1 := {H : Matrix (Fin k) (Fin d) ℝ | singularValues H (Fintype.card (Fin d) - 1) ≤ Real.sqrt k - Real.sqrt d - t}
  set S2 := {H : Matrix (Fin k) (Fin d) ℝ | Real.sqrt k + Real.sqrt d + t ≤ specNorm H}
  have hsub : Eᶜ ⊆ φ ⁻¹' (S1 ∪ S2) := by
    intro G hG
    by_contra hgood
    simp only [Set.mem_preimage, Set.mem_union, not_or, not_le, S1, S2, Set.mem_ofPred_eq] at hgood
    obtain ⟨hlo, hhi⟩ := hgood
    apply hG
    have hGU : (φ G) = G * U := by simp [φ]
    rw [hGU] at hlo hhi
    have hSU : ∀ x : Fin d → ℝ, ((1 / sk) • G * U) *ᵥ x =
        (1 / sk) • ((G * U) *ᵥ x) := by
      intro x; rw [Matrix.smul_mul, Matrix.smul_mulVec]
    have hnorm : ∀ x : Fin d → ℝ, Real.sqrt ((((1 / sk) • G * U) *ᵥ x) ⬝ᵥ
        (((1 / sk) • G * U) *ᵥ x)) =
        (1 / sk) * Real.sqrt (((G * U) *ᵥ x) ⬝ᵥ ((G * U) *ᵥ x)) := by
      intro x
      rw [hSU, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
        Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self (by positivity)]
    refine isSubspaceEmbedding_of_forall_sqrt_le hU hε1 ha0 haε (fun x => ?_) (fun x => ?_)
    · rw [hnorm]
      have h := singularValues_last_mul_norm_le (G * U) x
      simp only [norm_toLp_eq_sqrt_dotProduct_self] at h
      have hx := Real.sqrt_nonneg (x ⬝ᵥ x)
      have hlo' : (1 - a) * sk ≤ singularValues (G * U) (Fintype.card (Fin d) - 1) := by
        rw [ha, sub_mul, div_mul_cancel₀ _ hsk0.ne']; linarith
      calc (1 - a) * Real.sqrt (x ⬝ᵥ x)
          = ((1 - a) * sk) * Real.sqrt (x ⬝ᵥ x) / sk := by field_simp
        _ ≤ singularValues (G * U) (Fintype.card (Fin d) - 1) * Real.sqrt (x ⬝ᵥ x) / sk := by gcongr
        _ ≤ Real.sqrt (((G * U) *ᵥ x) ⬝ᵥ ((G * U) *ᵥ x)) / sk := by gcongr
        _ = _ := by rw [one_div, inv_mul_eq_div]
    · rw [hnorm]
      have h := sqrt_mulVec_dotProduct_le_specNorm_mul (G * U) x
      have hx := Real.sqrt_nonneg (x ⬝ᵥ x)
      have hhi' : specNorm (G * U) ≤ (1 + a) * sk := by
        rw [ha, add_mul, div_mul_cancel₀ _ hsk0.ne']; linarith
      calc 1 / sk * Real.sqrt (((G * U) *ᵥ x) ⬝ᵥ ((G * U) *ᵥ x))
          ≤ 1 / sk * (specNorm (G * U) * Real.sqrt (x ⬝ᵥ x)) := by gcongr
        _ ≤ 1 / sk * ((1 + a) * sk * Real.sqrt (x ⬝ᵥ x)) := by gcongr
        _ = (1 + a) * Real.sqrt (x ⬝ᵥ x) := by field_simp
  have hpos : 0 ≤ Real.exp (-t ^ 2 / 2) := (Real.exp_pos _).le
  calc μ.real Eᶜ ≤ μ.real (φ ⁻¹' (S1 ∪ S2)) := measureReal_mono hsub
    _ ≤ (μ.map φ).real (S1 ∪ S2) :=
        ENNReal.toReal_mono (measure_ne_top _ _) (Measure.le_map_apply hφ.aemeasurable _)
    _ = (gaussianMatrix (Fin k) (Fin d)).real (S1 ∪ S2) := by
        rw [(hasLaw_gaussianMatrix_mul_right U hU).map_eq]
    _ ≤ (gaussianMatrix (Fin k) (Fin d)).real S1 + (gaussianMatrix (Fin k) (Fin d)).real S2 :=
        measureReal_union_le _ _
    _ ≤ Real.exp (-t ^ 2 / 2) + Real.exp (-t ^ 2 / 2) :=
        add_le_add (measure_sigmaMin_le_sqrt_sub_sqrt_sub_le_gaussianMatrix hd t ht0)
          (measure_sqrt_add_sqrt_add_le_specNorm_le_gaussianMatrix t ht0)
    _ = δ := by rw [← two_mul, hδeq]

end NLAlib
