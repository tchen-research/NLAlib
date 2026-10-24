/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Sketching.Properties.ProjectionCost.Basic

/-!
# Fixed-offset projection costs transfer optimization guarantees

The comparison is proved for an arbitrary feasible family, so no certificate
outside that family or existence of a minimizing projector is needed.
The three-inequality calculation adapts `Sketching/Properties/ProjectionCost.lean`
from NLA-lib/NLAlib commit `6a845a2ec27f37c1a98118c107a06a13ce45273d`
(Apache-2.0). Source: Cohen–Elder–Musco–Musco–Persu 2015, Lemmas 3–4.
Atlas: `projection-cost-optimization-transfer`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n l : Type*}
  [Fintype m] [Fintype n] [Fintype l] [DecidableEq m]

/-- The lower certificate at the returned projector and the upper certificate
at any competitor transfer an unshifted sketch comparison. Nonnegative offset
and `γ ≥ 1` justify discarding `(1 - γ) c`.
Cohen–Elder–Musco–Musco–Persu 2015, Lemmas 3–4, competitor form. -/
theorem mul_frobSq_one_sub_mul_le_of_projection_cost_bounds
    {A : Matrix m n 𝕜} {B : Matrix m l 𝕜} {P P₀ : Matrix m m 𝕜}
    {a b c γ : ℝ} (hc : 0 ≤ c) (hγ : 1 ≤ γ)
    (hlo : a * frobSq ((1 - P) * A) ≤ frobSq ((1 - P) * B) + c)
    (hhi : frobSq ((1 - P₀) * B) + c ≤ b * frobSq ((1 - P₀) * A))
    (hopt : frobSq ((1 - P) * B) ≤ γ * frobSq ((1 - P₀) * B)) :
    a * frobSq ((1 - P) * A) ≤ γ * b * frobSq ((1 - P₀) * A) := by
  have h₂ := mul_le_mul_of_nonneg_left hhi (zero_le_one.trans hγ)
  have h₃ := mul_nonneg (sub_nonneg.mpr hγ) hc
  nlinarith

/-- For any feasible family, a two-sided PCP certificate transfers comparison
with every competitor by `γ (1 + ε) / (1 - ε)`. In particular it applies when
the competitor is an attained original minimum and the returned projector is
a `γ`-approximate minimizer of the unshifted sketch cost. No bounds outside
the feasible family are required. Cohen–Elder–Musco–Musco–Persu 2015, Lemma 3.
atlas: projection-cost-optimization-transfer (partial) -/
theorem frobSq_one_sub_mul_le_of_projection_cost_preserving
    {A : Matrix m n 𝕜} {B : Matrix m l 𝕜} {family : Set (Matrix m m 𝕜)}
    {P P₀ : Matrix m m 𝕜} {ε c γ : ℝ} (hc : 0 ≤ c) (hε : ε < 1)
    (hγ : 1 ≤ γ) (hP : P ∈ family) (hP₀ : P₀ ∈ family)
    (hcost : ∀ Q ∈ family,
      (1 - ε) * frobSq ((1 - Q) * A) ≤ frobSq ((1 - Q) * B) + c ∧
        frobSq ((1 - Q) * B) + c ≤ (1 + ε) * frobSq ((1 - Q) * A))
    (hopt : ∀ Q ∈ family, frobSq ((1 - P) * B) ≤ γ * frobSq ((1 - Q) * B)) :
    frobSq ((1 - P) * A) ≤
      (γ * (1 + ε) / (1 - ε)) * frobSq ((1 - P₀) * A) := by
  have h := mul_frobSq_one_sub_mul_le_of_projection_cost_bounds hc hγ
    (hcost P hP).1 (hcost P₀ hP₀).2 (hopt P₀ hP₀)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sub_pos.mpr hε)).2
  nlinarith [h]

/-- The one-sided PCP contract transfers any feasible-family comparison by
`γ (1 + ε)`, with the same fixed offset. Cohen–Elder–Musco–Musco–Persu 2015,
Lemma 4, including zero-cost and empty-dimensional inputs.
atlas: projection-cost-optimization-transfer (partial) -/
theorem frobSq_one_sub_mul_le_of_one_sided_projection_cost_preserving
    {A : Matrix m n 𝕜} {B : Matrix m l 𝕜} {family : Set (Matrix m m 𝕜)}
    {P P₀ : Matrix m m 𝕜} {ε c γ : ℝ} (hc : 0 ≤ c) (hγ : 1 ≤ γ)
    (hP : P ∈ family) (hP₀ : P₀ ∈ family)
    (hcost : ∀ Q ∈ family,
      frobSq ((1 - Q) * A) ≤ frobSq ((1 - Q) * B) + c ∧
        frobSq ((1 - Q) * B) + c ≤ (1 + ε) * frobSq ((1 - Q) * A))
    (hopt : ∀ Q ∈ family, frobSq ((1 - P) * B) ≤ γ * frobSq ((1 - Q) * B)) :
    frobSq ((1 - P) * A) ≤ γ * (1 + ε) * frobSq ((1 - P₀) * A) := by
  simpa only [one_mul] using mul_frobSq_one_sub_mul_le_of_projection_cost_bounds (a := 1) hc hγ
    (by simpa only [one_mul] using (hcost P hP).1)
    (hcost P₀ hP₀).2 (hopt P₀ hP₀)

private theorem frobSq_sketch_le_of_le_sInf
    {B : Matrix m l 𝕜} {family : Set (Matrix m m 𝕜)}
    {P : Matrix m m 𝕜} {γ : ℝ} (hγ : 0 ≤ γ)
    (hopt : frobSq ((1 - P) * B) ≤
      γ * sInf ((fun Q : Matrix m m 𝕜 => frobSq ((1 - Q) * B)) '' family)) :
    ∀ Q ∈ family, frobSq ((1 - P) * B) ≤ γ * frobSq ((1 - Q) * B) := by
  have hb : BddBelow ((fun Q : Matrix m m 𝕜 => frobSq ((1 - Q) * B)) '' family) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨Q, _, rfl⟩
    exact frobSq_nonneg _
  intro Q hQ
  exact hopt.trans (mul_le_mul_of_nonneg_left (csInf_le hb ⟨Q, hQ, rfl⟩) hγ)

/-- A `γ`-approximate minimizer of the unshifted sketch cost over any feasible
family satisfies the original cost bound relative to any feasible competitor,
in particular an attained original minimum. The infimum is bounded below by
zero, and the competitor makes the family nonempty.
Cohen–Elder–Musco–Musco–Persu 2015, Lemma 3, two-sided form.
atlas: projection-cost-optimization-transfer (partial) -/
theorem frobSq_one_sub_mul_le_of_projection_cost_preserving_of_sInf
    {A : Matrix m n 𝕜} {B : Matrix m l 𝕜} {family : Set (Matrix m m 𝕜)}
    {P P₀ : Matrix m m 𝕜} {ε c γ : ℝ} (hc : 0 ≤ c) (hε : ε < 1)
    (hγ : 1 ≤ γ) (hP : P ∈ family) (hP₀ : P₀ ∈ family)
    (hcost : ∀ Q ∈ family,
      (1 - ε) * frobSq ((1 - Q) * A) ≤ frobSq ((1 - Q) * B) + c ∧
        frobSq ((1 - Q) * B) + c ≤ (1 + ε) * frobSq ((1 - Q) * A))
    (hopt : frobSq ((1 - P) * B) ≤
      γ * sInf ((fun Q : Matrix m m 𝕜 => frobSq ((1 - Q) * B)) '' family)) :
    frobSq ((1 - P) * A) ≤
      (γ * (1 + ε) / (1 - ε)) * frobSq ((1 - P₀) * A) :=
  frobSq_one_sub_mul_le_of_projection_cost_preserving hc hε hγ hP hP₀ hcost
    (frobSq_sketch_le_of_le_sInf (zero_le_one.trans hγ) hopt)

/-- The corresponding infimum-based optimizer guarantee for one-sided PCP
has factor `γ (1 + ε)`. The fixed offset is not added to the solver's
objective. Cohen–Elder–Musco–Musco–Persu 2015, Lemma 4.
atlas: projection-cost-optimization-transfer (partial) -/
theorem frobSq_one_sub_mul_le_of_one_sided_projection_cost_preserving_of_sInf
    {A : Matrix m n 𝕜} {B : Matrix m l 𝕜} {family : Set (Matrix m m 𝕜)}
    {P P₀ : Matrix m m 𝕜} {ε c γ : ℝ} (hc : 0 ≤ c) (hγ : 1 ≤ γ)
    (hP : P ∈ family) (hP₀ : P₀ ∈ family)
    (hcost : ∀ Q ∈ family,
      frobSq ((1 - Q) * A) ≤ frobSq ((1 - Q) * B) + c ∧
        frobSq ((1 - Q) * B) + c ≤ (1 + ε) * frobSq ((1 - Q) * A))
    (hopt : frobSq ((1 - P) * B) ≤
      γ * sInf ((fun Q : Matrix m m 𝕜 => frobSq ((1 - Q) * B)) '' family)) :
    frobSq ((1 - P) * A) ≤ γ * (1 + ε) * frobSq ((1 - P₀) * A) :=
  frobSq_one_sub_mul_le_of_one_sided_projection_cost_preserving hc hγ hP hP₀ hcost
    (frobSq_sketch_le_of_le_sInf (zero_le_one.trans hγ) hopt)

end NLAlib
